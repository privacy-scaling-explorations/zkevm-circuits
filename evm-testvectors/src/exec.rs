use anyhow::Result;
use bus_mapping::circuit_input_builder::CircuitInputBuilder;
use bus_mapping::mock::BlockData;
use external_tracer::TraceConfig;

use eth_types::U64;
pub fn traceconfig(trace_config: TraceConfig) -> Result<CircuitInputBuilder> {
    // get the geth traces
    let geth_trace = external_tracer::trace(&trace_config)?;

    // process the transaction
    let geth_data = eth_types::geth_types::GethData {
        chain_id: trace_config.chain_id,
        history_hashes: trace_config.history_hashes,
        eth_block: eth_types::Block {
            author: trace_config.block_constants.coinbase,
            timestamp: trace_config.block_constants.timestamp,
            number: Some(U64::from(trace_config.block_constants.timestamp.as_u64())),
            difficulty: trace_config.block_constants.difficulty,
            gas_limit: trace_config.block_constants.gas_limit,
            base_fee_per_gas: Some(trace_config.block_constants.base_fee),
            ..eth_types::Block::default()
        },
        eth_tx: eth_types::Transaction {
            from: trace_config.transaction.from,
            to: trace_config.transaction.to,
            value: trace_config.transaction.value,
            input: trace_config.transaction.call_data,
            gas_price: Some(trace_config.transaction.gas_price),
            access_list: trace_config.transaction.access_list,
            nonce: trace_config.transaction.nonce,
            gas: trace_config.transaction.gas_limit,
            transaction_index: Some(U64::zero()),
            ..eth_types::Transaction::default()
        },
        geth_trace,
        accounts: trace_config.accounts.into_values().collect(),
    };

    let block_data = BlockData::new_from_geth_data(geth_data);
    let mut builder = block_data.new_circuit_input_builder();
    builder.handle_tx(&block_data.eth_tx, &block_data.geth_trace)?;
    Ok(builder)
}
