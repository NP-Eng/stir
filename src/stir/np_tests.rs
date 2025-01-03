use ark_std::marker::PhantomData;

use crate::parameters::{Parameters, SoundnessType};
use crate::crypto::{fs::poseidon, merkle_tree::blake3};
use super::parameters::FullParameters;


#[test]
fn create_params() {

    type F = crate::crypto::fields::Field256;

    let (leaf_hash_params, two_to_one_params) = blake3::default_config::<F>(&mut rand::thread_rng(), 0);
    let fiat_shamir_config = poseidon::default_fs_config::<F>();

    let params = Parameters::<F, blake3::MerkleTreeParams<F>, poseidon::Sponge<F>> {
        security_level: 128,
        protocol_security_level: 256,
        starting_degree: 1 << 30,
        stopping_degree: 1 << 2,
        folding_factor: 1 << 4,
        starting_rate: 16,
        soundness_type: SoundnessType::Conjecture,
        leaf_hash_params,
        two_to_one_params,
        fiat_shamir_config,
        _field: PhantomData,
    };

    let full_params = FullParameters::from(params);

    println!("{:?}", full_params);
}

// TODO
// - Different Soundness (conjecture vs proved)
// - Reaching stopping degree exactly and not
// - Stopping degree 1
// - If interested, negative, i. e. bad arguments passed
