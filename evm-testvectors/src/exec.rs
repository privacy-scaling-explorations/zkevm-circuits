use anyhow::Result;
use bus_mapping::circuit_input_builder::CircuitInputBuilder;
use bus_mapping::mock::BlockData;
use external_tracer::TraceConfig;

use eth_types::U64;
pub fn traceconfig(trace_config: TraceConfig) -> Result<CircuitInputBuilder> {
    // get the geth traces
    let geth_traces = external_tracer::trace(&trace_config)?;

    let transactions = trace_config
        .transactions
        .into_iter()
        .enumerate()
        .map(|(index, tx)| eth_types::Transaction {
            from: tx.from,
            to: tx.to,
            value: tx.value,
            input: tx.call_data,
            gas_price: Some(tx.gas_price),
            access_list: tx.access_list,
            nonce: tx.nonce,
            gas: tx.gas_limit,
            transaction_index: Some(U64::from(index)),
            ..eth_types::Transaction::default()
        })
        .collect();

    let eth_block = eth_types::Block {
        author: trace_config.block_constants.coinbase,
        timestamp: trace_config.block_constants.timestamp,
        number: Some(U64::from(trace_config.block_constants.timestamp.as_u64())),
        difficulty: trace_config.block_constants.difficulty,
        gas_limit: trace_config.block_constants.gas_limit,
        base_fee_per_gas: Some(trace_config.block_constants.base_fee),
        transactions,
        ..eth_types::Block::default()
    };

    // process the transaction
    let geth_data = eth_types::geth_types::GethData {
        chain_id: trace_config.chain_id,
        history_hashes: trace_config.history_hashes,
        geth_traces: geth_traces.clone(),
        accounts: trace_config.accounts.into_values().collect(),
        eth_block: eth_block.clone(),
    };

    let block_data = BlockData::new_from_geth_data(geth_data);
    let mut builder = block_data.new_circuit_input_builder();
    builder.handle_block(&eth_block, &geth_traces)?;
    Ok(builder)
}
