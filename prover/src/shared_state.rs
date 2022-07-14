use halo2_proofs::pairing::bn256::G1Affine;
use halo2_proofs::poly::commitment::Params;

use std::collections::HashMap;
use std::fs::File;
use std::sync::Arc;

use tokio::sync::Mutex;

use crate::compute_proof::compute_proof;
use crate::structs::{ProofRequestOptions, Proofs};

#[derive(Debug, Clone)]
pub struct ProofRequest {
    pub options: ProofRequestOptions,
    pub result: Option<Result<Proofs, String>>,
}

pub struct RwState {
    pub tasks: Vec<ProofRequest>,
    pub pending_tasks: u32,
    pub params_cache: HashMap<String, Arc<Params<G1Affine>>>,
}

#[derive(Clone)]
pub struct SharedState {
    pub rw: Arc<Mutex<RwState>>,
}

impl SharedState {
    pub fn new() -> SharedState {
        Self {
            rw: Arc::new(Mutex::new(RwState {
                tasks: Vec::new(),
                pending_tasks: 0,
                params_cache: HashMap::new(),
            })),
        }
    }

    /// Will return the result or error of the task if it's completed.
    /// Otherwise enqueues the task and returns `None`.
    /// `retry_if_error` enqueues the task again if it returned with an error
    /// before.
    pub async fn get_or_enqueue(
        &self,
        options: &ProofRequestOptions,
    ) -> Option<Result<Proofs, String>> {
        let mut rw = self.rw.lock().await;

        // task already pending or completed?
        let task = rw.tasks.iter_mut().find(|e| e.options == *options);

        if task.is_some() {
            let mut task = task.unwrap();

            if task.result.is_some() {
                if options.retry && task.result.as_ref().unwrap().is_err() {
                    log::debug!("retrying: {:#?}", task);
                    // will be a candidate in `duty_cycle` again
                    task.result = None;
                } else {
                    log::debug!("completed: {:#?}", task);
                    return task.result.clone();
                }
            } else {
                log::debug!("pending: {:#?}", task);
                return None;
            }
        } else {
            // enqueue the task
            let task = ProofRequest {
                options: options.clone(),
                result: None,
            };
            log::debug!("enqueue: {:#?}", task);
            rw.tasks.push(task);
        }

        None
    }

    /// Checks if there is anything to do like:
    /// - records if a task completed
    /// - starting a new task
    /// Blocks until completion but releases the lock of `self.rw` in between.
    pub async fn duty_cycle(&self) {
        let mut rw = self.rw.lock().await;

        if rw.pending_tasks > 0 {
            // already computing
            // TODO: can spawn multiple tasks if ever required
            return;
        }

        // find a pending task
        let pending_task = rw.tasks.iter().find(|&e| e.result.is_none());
        if pending_task.is_none() {
            // nothing to do
            return;
        }

        // needs to be cloned because of long running tasks and
        // the possibility that the task gets removed in the meantime
        let mut pending_task = pending_task.unwrap().clone();
        {
            rw.pending_tasks += 1;
            log::info!("compute_proof: {:#?}", pending_task);
            drop(rw);
        }

        // Note: this catches any panics for the task itself but will not help in the
        // situation when the process get itself OOM killed, stack overflows etc.
        // This could be avoided by spawning a subprocess for the proof computation
        // instead.

        let pending_task_copy = pending_task.clone();
        let self_copy = self.clone();
        let task_result: Result<Result<Proofs, String>, tokio::task::JoinError> =
            tokio::spawn(async move {
                // lazily load the file and cache it
                let param = self_copy.load_param(&pending_task_copy.options.param).await;
                let res = compute_proof(
                    param.as_ref(),
                    &pending_task_copy.options.block,
                    &pending_task_copy.options.rpc,
                )
                .await;

                if let Err(err) = res {
                    // cast Error to string
                    return Err(err.to_string());
                }

                Ok(res.unwrap())
            })
            .await;

        // convert the JoinError to string - if applicable
        let task_result: Result<Proofs, String> = match task_result {
            Err(err) => match err.is_panic() {
                true => {
                    let panic = err.into_panic();

                    if let Some(msg) = panic.downcast_ref::<&str>() {
                        Err(msg.to_string())
                    } else if let Some(msg) = panic.downcast_ref::<String>() {
                        Err(msg.to_string())
                    } else {
                        Err("unknown panic".to_string())
                    }
                }
                false => Err(err.to_string()),
            },
            Ok(val) => val,
        };

        {
            // done, update the queue
            log::info!("task_result: {:#?}", task_result);

            let mut rw = self.rw.lock().await;
            rw.pending_tasks -= 1;

            let task = rw
                .tasks
                .iter_mut()
                .find(|e| e.options == pending_task.options);
            if let Some(task) = task {
                // found our task, update result
                task.result = Some(task_result);
            } else {
                // task was already removed in the meantime, insert it again
                pending_task.result = Some(task_result);
                rw.tasks.push(pending_task);
            }
        }
    }

    async fn load_param(&self, params_path: &str) -> Arc<Params<G1Affine>> {
        let mut rw = self.rw.lock().await;

        if !rw.params_cache.contains_key(params_path) {
            // drop, potentially long running
            drop(rw);

            // load polynomial commitment parameters
            let params_fs = File::open(params_path).expect("couldn't open params");
            let params: Arc<Params<G1Affine>> = Arc::new(
                Params::read::<_>(&mut std::io::BufReader::new(params_fs))
                    .expect("Failed to read params"),
            );

            // acquire lock and update
            rw = self.rw.lock().await;
            rw.params_cache.insert(params_path.to_string(), params);

            log::info!("params: initialized {}", params_path);
        }

        rw.params_cache.get(params_path).unwrap().clone()
    }
}

impl Default for SharedState {
    fn default() -> Self {
        Self::new()
    }
}
