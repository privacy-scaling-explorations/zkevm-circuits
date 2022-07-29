use tokio::time::{sleep, Duration};

use prover::server::serve;
use prover::shared_state::SharedState;
use prover::structs::ProofRequestOptions;

fn init_logger() {
    let _ = env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("debug"))
        .is_test(true)
        .try_init();
}

#[tokio::test]
async fn proverd_simple_signaling() {
    init_logger();

    let node_a = SharedState::new("a".to_string(), "127.0.0.1:11111".to_string());
    let node_b = SharedState::new("b".to_string(), "127.0.0.1:11112".to_string());
    // start http servers
    {
        let _ = serve(&node_a, &node_b.ro.node_lookup);
        let _ = serve(&node_b, &node_a.ro.node_lookup);
    }

    // wait a bit for the rpc server to start
    sleep(Duration::from_millis(300)).await;

    let proof_a = ProofRequestOptions {
        block: 1,
        param: "/none".to_string(),
        retry: false,
        rpc: "http://localhost:1111".to_string(),
    };
    let proof_b = ProofRequestOptions {
        block: 2,
        param: "/none".to_string(),
        retry: false,
        rpc: "http://localhost:1111".to_string(),
    };

    // enqueue tasks
    assert!(node_a.get_or_enqueue(&proof_a).await.is_none());
    assert!(node_b.get_or_enqueue(&proof_b).await.is_none());

    // start work on node_a
    node_a.duty_cycle().await;
    assert!(node_a.get_or_enqueue(&proof_a).await.is_some());

    // node_b didn't sync yet
    assert!(node_b.get_or_enqueue(&proof_a).await.is_none());
    // sync, do work
    let _ = node_b.merge_tasks_from_peers().await;
    // check again
    assert!(node_b.get_or_enqueue(&proof_a).await.is_some());

    // no result yet
    assert!(node_b.get_or_enqueue(&proof_b).await.is_none());
    // sync, do work
    node_b.duty_cycle().await;
    // check again
    assert!(node_b.get_or_enqueue(&proof_b).await.is_some());

    // node_a didn't sync yet
    assert!(node_a.get_or_enqueue(&proof_b).await.is_none());
    // sync node_a
    let _ = node_a.merge_tasks_from_peers().await;
    // check again
    assert!(node_a.get_or_enqueue(&proof_b).await.is_some());
}
