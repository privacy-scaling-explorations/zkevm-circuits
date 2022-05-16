use halo2_proofs::pairing::bn256::G1Affine;
use halo2_proofs::poly::commitment::Params;
use std::sync::Arc;
use tokio::sync::Mutex;

use crate::compute_proof::compute_proof;
use crate::structs::Proofs;

#[derive(Debug, Clone)]
pub struct ProofRequest {
    pub block_num: u64,
    pub rpc_url: String,
    pub result: Option<Result<Proofs, String>>,
}

pub struct RwState {
    pub tasks: Vec<ProofRequest>,
    pub pending_tasks: u32,
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
            })),
        }
    }

    /// Will return the result or error of the task if it's completed.
    /// Otherwise enqueues the task and returns `None`.
    /// `retry_if_error` enqueues the task again if it returned with an error
    /// before.
    pub async fn get_or_enqueue(
        &self,
        block_num: &u64,
        rpc_url: &str,
        retry_if_error: &bool,
    ) -> Option<Result<Proofs, String>> {
        let mut rw = self.rw.lock().await;

        // task already pending or completed?
        let task = rw
            .tasks
            .iter_mut()
            .find(|e| e.block_num == *block_num && e.rpc_url == *rpc_url);

        if task.is_some() {
            let mut task = task.unwrap();

            if task.result.is_some() {
                if *retry_if_error && task.result.as_ref().unwrap().is_err() {
                    log::info!("retrying: {:#?}", task);
                    // will be a candidate in `duty_cycle` again
                    task.result = None;
                } else {
                    log::info!("completed: {:#?}", task);
                    return task.result.clone();
                }
            } else {
                log::info!("pending: {:#?}", task);
                return None;
            }
        } else {
            // enqueue the task
            let task = ProofRequest {
                block_num: *block_num,
                rpc_url: rpc_url.to_string(),
                result: None,
            };
            log::info!("enqueue: {:#?}", task);
            rw.tasks.push(task);
        }

        None
    }

    /// Checks if there is anything to do like:
    /// - records if a task completed
    /// - starting a new task
    /// Blocks until completion but releases the lock of `self.rw` in between.
    pub async fn duty_cycle(&self, params: Arc<Params<G1Affine>>) {
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
        let pending_task = pending_task.unwrap().clone();
        {
            rw.pending_tasks += 1;
            log::info!("compute_proof: {:#?}", pending_task);
            drop(rw);
        }

        // Note: this catches any panics for the task itself but will not help in the
        // situation when the process get itself OOM killed, stack overflows etc.
        // This could be avoided by spawning a subprocess for the proof computation
        // instead.

        let _pending_task = pending_task.clone();
        let task_result: Result<Result<Proofs, String>, tokio::task::JoinError> =
            tokio::spawn(async move {
                let res = compute_proof(
                    params.as_ref(),
                    &_pending_task.block_num,
                    &_pending_task.rpc_url,
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
            Err(err) => Err(err.to_string()),
            Ok(val) => val,
        };

        {
            // done, update the queue
            log::info!("task_result: {:#?}", task_result);

            let mut rw = self.rw.lock().await;
            rw.pending_tasks -= 1;

            let task = rw.tasks.iter_mut().find(|e| {
                e.block_num == pending_task.block_num && e.rpc_url == pending_task.rpc_url
            });
            if let Some(task) = task {
                // found our task, update result
                task.result = Some(task_result);
            } else {
                // task was already removed in the meantime, insert it again
                rw.tasks.push(ProofRequest {
                    block_num: pending_task.block_num,
                    rpc_url: pending_task.rpc_url,
                    result: Some(task_result),
                });
            }
        }
    }
}

impl Default for SharedState {
    fn default() -> Self {
        Self::new()
    }
}
