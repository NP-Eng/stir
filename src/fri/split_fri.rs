use std::collections::BTreeMap;

use ark_crypto_primitives::{merkle_tree::{Config, MerkleTree}, sponge::{Absorb, CryptographicSponge}};
use ark_ff::{batch_inversion, FftField, PrimeField};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use derivative::Derivative;
use crate::{domain::Domain, fri::common::RoundProofs, ldt::Prover, parameters::Parameters, poly_utils, utils};

use super::{common::{Commitment, Proof}, parameters::FullParameters, prover::Witness};

#[derive(Derivative)]
#[derivative(Clone(bound = "F: Clone"))]
pub struct SplitFriWitness<F: FftField, MerkleConfig: Config> {
    pub(crate) domain: GeneralEvaluationDomain<F>,
    pub(crate) polynomial: DensePolynomial<F>,
    pub(crate) merkle_trees: Vec<MerkleTree<MerkleConfig>>,
    pub(crate) folded_evals: Vec<Vec<F>>,
}

#[derive(Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SplitFriCommitment<MerkleConfig>
where
    MerkleConfig: Config,
{
    pub(crate) roots: Vec<MerkleConfig::InnerDigest>,
}
pub struct SplitFriProver<F, MerkleConfig, FSConfig>
where
    F: FftField,
    MerkleConfig: Config,
    FSConfig: CryptographicSponge,
    FSConfig::Config: Clone,
{
    pub(crate) parameters: FullParameters<F, MerkleConfig, FSConfig>,
}

impl<F, MerkleConfig, FSConfig> SplitFriProver<F, MerkleConfig, FSConfig>
where
    F: FftField + PrimeField + Absorb,
    MerkleConfig: Config<Leaf = Vec<F>>,
    MerkleConfig::InnerDigest: Absorb,
    FSConfig: CryptographicSponge,
    FSConfig::Config: Clone,
{
    fn new(full_parameters: FullParameters<F, MerkleConfig, FSConfig>) -> Self {
        Self {
            parameters: full_parameters,
        }
    }

    // TODO: Better name for testing
    fn commit(
        &self,
        known_evals: Vec<F>,
    ) -> (SplitFriCommitment<MerkleConfig>, SplitFriWitness<F, MerkleConfig>) {
        let rate = 1 << self.parameters.starting_rate;

        let size = self.parameters.starting_degree * rate;
        let domain = GeneralEvaluationDomain::new(size).unwrap();

        // Interpolating small evaluations
        let small_domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(self.parameters.starting_degree).unwrap();

        let mut interpolator_coeffs = small_domain.ifft(&known_evals);
    
        let interpolator = DensePolynomial::<F>::from_coefficients_slice(&interpolator_coeffs);

        interpolator_coeffs.resize(size, F::ZERO);

        let evals = domain.fft(&interpolator_coeffs);

        let folded_evals = utils::stack_evaluations(evals, self.parameters.folding_factor);

        let mut cosets = vec![Vec::new(); rate];

        let mut coset = 0;

        // AN TODO: do better
        // AN TODO if we don't use all of folded evals, into_iter here
        for small_coset in folded_evals.iter() {
            if coset != 0 {
                cosets[coset].push(small_coset);
            }

            coset = (coset + 1) % rate;
        }

        let merkle_trees: Vec<MerkleTree<MerkleConfig>> = cosets
            .into_iter()
            .skip(1)
            .map(|medium_coset|
                MerkleTree::<MerkleConfig>::new(
                    &self.parameters.leaf_hash_params,
                    &self.parameters.two_to_one_params,
                    &medium_coset,
                ).unwrap()
            ).collect();

        let roots = merkle_trees.iter().map(|tree| tree.root()).collect();

        (
            SplitFriCommitment {
                roots,
            },

            SplitFriWitness {
                domain,
                polynomial: interpolator,
                merkle_trees,
                folded_evals,
            },
        )
    }

    fn prove(&self, witness: SplitFriWitness<F, MerkleConfig>) -> Proof<F, MerkleConfig> {
        assert!(witness.polynomial.degree() < self.parameters.starting_degree);

        let mut sponge = FSConfig::new(&self.parameters.fiat_shamir_config);
        for tree in witness.merkle_trees.iter() {
            sponge.absorb(&tree.root());
        }

        let mut g_domain = witness.domain.clone();
        let mut g_poly = witness.polynomial.clone();

        // Commit phase
        let mut commitments = vec![];
        let mut merkle_trees = vec![witness.merkle_trees.clone()];
        let mut folded_evals = vec![witness.folded_evals.clone()];

        let mut folding_randomness = sponge.squeeze_field_elements(1)[0];
        for _ in 0..self.parameters.num_rounds {
            // Fold the initial polynomial
            g_poly = poly_utils::folding::poly_fold(
                &g_poly,
                self.parameters.folding_factor,
                folding_randomness,
            );

            let prev_evals = folded_evals.last().unwrap();

            // The following lines are just precomputations, to avoid having to do inversion
            // and exponentiations in the inner loop
            let domain_size = g_domain.size();
            let generator = g_domain
                .element(domain_size / self.parameters.folding_factor);
            let generator_inv = generator.inverse().unwrap();
            let size_inv = F::from(self.parameters.folding_factor as u64)
                .inverse()
                .unwrap();
            let coset_offsets: Vec<_> = g_domain
                .elements()
                .take(prev_evals.len())
                .collect();
            let mut counter = F::ONE;
            let scale = g_domain.element(1).inverse().unwrap();
            let mut coset_offsets_inv: Vec<_> = vec![];
            for _ in 0..prev_evals.len() {
                coset_offsets_inv.push(counter);
                counter *= scale;
            }

            // Compute the evalations of the folded polynomial
            let g_evaluations: Vec<_> = prev_evals
                .iter()
                .zip(coset_offsets.into_iter())
                .zip(coset_offsets_inv.into_iter())
                .map(|((e, c), ci)| (e, c, ci))
                .map(|(evals, coset_offset, coset_offset_inv)| {
                    poly_utils::interpolation::fft_interpolate(
                        generator,
                        coset_offset,
                        generator_inv,
                        coset_offset_inv,
                        size_inv,
                        evals,
                    )
                    .evaluate(&folding_randomness)
                })
                .collect();

            /*
             * The following codes are other attempts at doing this
            let domain_points = g_domain.backing_domain.elements().collect::<Vec<_>>();
            let folded_domains =
                utils::stack_evaluations(domain_points, self.parameters.folding_factor);
            let g_evaluations = prev_evals
                .iter()
                .enumerate()
                .map(|(i, evals)| {
                    let interpol = evals
                        .iter()
                        .enumerate()
                        .map(|(j, &e)| (folded_domains[i][j], e))
                        .collect();

                    poly_utils::folding::fold(
                        interpol,
                        self.parameters.folding_factor,
                        folding_randomness,
                    )
                })
                .collect();
            */

            g_domain = GeneralEvaluationDomain::<F>::new(g_domain.size() / self.parameters.folding_factor).unwrap();
            //let g_evaluations = g_poly.evaluate_over_domain_by_ref(g_domain.backing_domain).evals;

            let g_folded_evaluations =
                utils::stack_evaluations(g_evaluations, self.parameters.folding_factor);
            let g_merkle = MerkleTree::<MerkleConfig>::new(
                &self.parameters.leaf_hash_params,
                &self.parameters.two_to_one_params,
                &g_folded_evaluations,
            )
            .unwrap();
            let g_root = g_merkle.root();
            sponge.absorb(&g_root);

            folding_randomness = sponge.squeeze_field_elements(1)[0];

            commitments.push(g_root);
            merkle_trees.push(g_merkle);
            folded_evals.push(g_folded_evaluations);
        }

        g_poly = poly_utils::folding::poly_fold(
            &g_poly,
            self.parameters.folding_factor,
            folding_randomness,
        );

        // Query phase
        let mut folded_evals_len = witness.domain.size() / self.parameters.folding_factor;
        let mut query_indexes = utils::dedup(
            (0..self.parameters.repetitions)
                .map(|_| utils::squeeze_integer(&mut sponge, folded_evals_len)),
        );

        // Note that we include final round as well
        let mut round_proofs = vec![];
        for round in 0..=self.parameters.num_rounds {
            let queries_to_prev_ans = query_indexes
                .iter()
                .map(|&index| folded_evals[round][index].clone())
                .collect();
            let queries_to_prev_proof = merkle_trees[round]
                .generate_multi_proof(query_indexes.clone())
                .unwrap();
            let queries_to_prev = (queries_to_prev_ans, queries_to_prev_proof);

            folded_evals_len = folded_evals_len / self.parameters.folding_factor;
            query_indexes = utils::dedup(query_indexes.into_iter().map(|i| i % folded_evals_len));

            round_proofs.push(RoundProofs { queries_to_prev });
        }

        Proof {
            final_polynomial: g_poly,
            commitments,
            round_proofs,
            pow_nonce: utils::proof_of_work(&mut sponge, self.parameters.pow_bits),
        }
    }
}
pub struct SplitFriVerifier<F, MerkleConfig, FSConfig>
where
    F: FftField,
    MerkleConfig: Config,
    FSConfig: CryptographicSponge,
    FSConfig::Config: Clone,
{
    pub(crate) parameters: FullParameters<F, MerkleConfig, FSConfig>,
}

impl<F, MerkleConfig, FSConfig> SplitFriVerifier<F, MerkleConfig, FSConfig>
where
    F: FftField + PrimeField + Absorb,
    MerkleConfig: Config<Leaf = Vec<F>>,
    MerkleConfig::InnerDigest: Absorb,
    FSConfig: CryptographicSponge,
    FSConfig::Config: Clone,
{
    fn new(full_parameters: FullParameters<F, MerkleConfig, FSConfig>) -> Self {
        Self {
            parameters: full_parameters,
        }
    }

    fn verify(
        &self,
        known_evals: Vec<F>,
        commitment: &Commitment<MerkleConfig>,
        proof: &Proof<F, MerkleConfig>,
    ) -> bool {
        if proof.final_polynomial.degree() + 1 > self.parameters.stopping_degree {
            return false;
        }

        // We do FS
        let mut sponge = FSConfig::new(&self.parameters.fiat_shamir_config);
        sponge.absorb(&commitment.root);

        let mut folding_randomnessness: Vec<F> = vec![];
        folding_randomnessness.push(sponge.squeeze_field_elements(1)[0]);
        // Absorb the roots
        for commitment in &proof.commitments {
            sponge.absorb(&commitment);
            folding_randomnessness.push(sponge.squeeze_field_elements(1)[0]);
        }

        // We adjoin the initial commitment
        let commitments: Vec<_> = std::iter::once(commitment.root.clone())
            .chain(proof.commitments.iter().cloned())
            .collect();

        // Verify merkle commitments
        for num_round in 0..=self.parameters.num_rounds {
            let (answers, proof) = &proof.round_proofs[num_round].queries_to_prev;

            if !proof
                .verify(
                    &self.parameters.leaf_hash_params,
                    &self.parameters.two_to_one_params,
                    &commitments[num_round],
                    answers,
                )
                .unwrap()
            {
                return false;
            }
        }

        let mut g_domain = Domain::<F>::new(
            self.parameters.starting_degree,
            self.parameters.starting_rate,
        )
        .unwrap();

        let mut folded_evals_len = g_domain.size() / self.parameters.folding_factor;
        let query_indexes = utils::dedup(
            (0..self.parameters.repetitions)
                .map(|_| utils::squeeze_integer(&mut sponge, folded_evals_len)),
        );

        // Precomputation
        let (generators, coset_offsets) = {
            let mut folded_evals_len = folded_evals_len;
            let mut query_indexes = query_indexes.clone();
            let mut generators = vec![];
            let mut coset_offsets = vec![];
            for _ in 0..=self.parameters.num_rounds {
                let generator = g_domain.element(g_domain.size() / self.parameters.folding_factor);

                generators.push(generator);

                let round_offsets: Vec<_> =
                    query_indexes.iter().map(|i| g_domain.element(*i)).collect();
                coset_offsets.push(round_offsets);

                g_domain = g_domain.scale(self.parameters.folding_factor);
                folded_evals_len = folded_evals_len / self.parameters.folding_factor;
                query_indexes =
                    utils::dedup(query_indexes.into_iter().map(|i| i % folded_evals_len));
            }

            (generators, coset_offsets)
        };

        let size = F::from(self.parameters.folding_factor as u64);

        let mut to_invert: Vec<F> = vec![];

        for co in &coset_offsets {
            to_invert.extend(co);
        }
        to_invert.extend(&generators);
        to_invert.push(size);
        batch_inversion(&mut to_invert);
        let size_inv = to_invert.pop().unwrap();
        let generators_inv = to_invert.split_off(to_invert.len() - generators.len());
        let mut coset_offsets_inv = vec![];
        for co in coset_offsets.iter().rev() {
            let co_inv = to_invert.split_off(to_invert.len() - co.len());
            coset_offsets_inv.push(co_inv);
        }
        coset_offsets_inv.reverse();

        let mut query_indexes: Vec<_> = query_indexes.into_iter().map(|i| (i, 0)).collect();
        let mut folded_answers: Option<Vec<F>> = None;

        for num_round in 0..=self.parameters.num_rounds {
            let folding_randomness = folding_randomnessness[num_round];
            let answers: Vec<_> = query_indexes
                .iter()
                .zip(proof.round_proofs[num_round].queries_to_prev.0.clone())
                .map(|(index, answer)| (index, answer.clone()))
                .collect();

            if let Some(folded_answers) = &folded_answers {
                if !folded_answers.iter().zip(answers.iter()).all(
                    |(folded_answer, ((_, checking_index), answer))| {
                        answer[*checking_index] == *folded_answer
                    },
                ) {
                    return false;
                }
            }

            let generator = generators[num_round];
            let generator_inv = generators_inv[num_round];

            let unordeded_folded_answers: Vec<_> = answers
                .iter()
                .zip(coset_offsets[num_round].iter())
                .zip(coset_offsets_inv[num_round].iter())
                .map(|(((_, answer), coset_offset), coset_offset_inv)| {
                    let folded_answer = poly_utils::interpolation::fft_interpolate(
                        generator,
                        *coset_offset,
                        generator_inv,
                        *coset_offset_inv,
                        size_inv,
                        answer,
                    )
                    .evaluate(&folding_randomness);

                    folded_answer
                })
                .collect();

            folded_evals_len = folded_evals_len / self.parameters.folding_factor;

            // Now we need to sort and dedup
            let query_answers: BTreeMap<_, _> = query_indexes
                .into_iter()
                .zip(unordeded_folded_answers)
                .map(|((i, _), a)| (i % folded_evals_len, (i / folded_evals_len, a)))
                .collect();

            folded_answers = Some(query_answers.values().map(|(_, a)| *a).collect());

            query_indexes = query_answers
                .into_iter()
                .map(|(i, (c, _))| (i, c))
                .collect();
        }

        let folded_answers = folded_answers.unwrap();

        let answers: Vec<_> = query_indexes
            .into_iter()
            .map(|(index, checking_index)| {
                proof
                    .final_polynomial
                    .evaluate(&g_domain.element(index + checking_index * folded_evals_len))
            })
            .collect();
        if !folded_answers
            .iter()
            .zip(answers)
            .all(|(folded_answer, poly_answer)| poly_answer == *folded_answer)
        {
            return false;
        }

        // Proof of work
        utils::proof_of_work_verify(&mut sponge, self.parameters.pow_bits, proof.pow_nonce)
    }
}
