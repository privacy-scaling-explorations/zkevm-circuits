use eth_types::Field;
use halo2_proofs::plonk::{Error, VirtualCells};

use super::{
    helpers::{MPTConstraintBuilder, ListKeyGadget},
    rlp_gadgets::RLPItemWitness,
    witness_row::Node,
    MPTContext,
};
use crate::{
    circuit,
    circuit_tools::cached_region::{CachedRegion, ChallengeSet},
    mpt_circuit::{
        MPTConfig, MPTState, witness_row::ModExtensionRowType,
    },
};

#[derive(Clone, Debug, Default)]
pub(crate) struct ModExtensionConfig<F> {
    rlp_key: ListKeyGadget<F>,
}

impl<F: Field> ModExtensionConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        cb.base
            .cell_manager
            .as_mut()
            .unwrap()
            .reset(ModExtensionRowType::Count as usize);
        let mut config = ModExtensionConfig::default();

        circuit!([meta, cb], {

        });

        config
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assign<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
        _challenges: &S,
        mpt_config: &MPTConfig<F>,
        pv: &mut MPTState<F>,
        offset: usize,
        node: &Node,
        rlp_values: &[RLPItemWitness],
    ) -> Result<(), Error> {
        let mod_extension = &node.mod_extension.clone().unwrap();

        

        Ok(())
    }
}
