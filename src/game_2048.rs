use bellpepper_core::{num::AllocatedNum, SynthesisError};
use ff::PrimeField;
use nova_snark::traits::circuit::StepCircuit;

use crate::{
    direction_chooser::DirectionChooser, gen_next::GenNext, merge::Merge, restore::Restore,
    sort::SortByZero,
};

#[derive(Debug, Clone)]
pub struct Game2048Circuit<F: PrimeField> {
    pub directions: Vec<[F; 4]>,
}

impl<F: PrimeField> Game2048Circuit<F> {
    pub fn new(directions: &[[F; 4]]) -> Self {
        Self {
            directions: directions.to_vec(),
        }
    }
}

impl<F: PrimeField> StepCircuit<F> for Game2048Circuit<F> {
    fn arity(&self) -> usize {
        16
    }

    fn synthesize<CS: bellpepper_core::ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let mut board = z.to_vec();
        for i in 0..self.directions.len() {
            let mut direction = Vec::new();
            for (j, x) in self.directions[i].iter().enumerate() {
                let var = AllocatedNum::alloc(
                    cs.namespace(|| format!("alloc direction_{}_{}", i, j)),
                    || Ok(*x),
                )?;
                direction.push(var)
            }

            let mut step_1 = DirectionChooser::new(&board, &direction);
            step_1.synthesize(cs.namespace(|| "direction chooser"))?;

            let mut step_2 = SortByZero::new(&step_1.lines, 0);
            step_2.synthesize(cs.namespace(|| "sort"))?;

            let mut step_3 = Merge::new(&step_2.sorted_lines);
            step_3.synthesize(cs.namespace(|| "merge"))?;

            let mut step_4 = SortByZero::new(&step_3.merged_lines, step_2.namespace_index);
            step_4.synthesize(cs.namespace(|| "sort again"))?;

            let mut step_5 = Restore::new(&step_4.sorted_lines, &direction);
            step_5.synthesize(cs.namespace(|| "restore"))?;

            let mut step_6 = GenNext::new(&step_5.board);
            step_6.synthesize(cs.namespace(|| "gen next"))?;

            board = step_6.new_board;

            // println!("---------");
            // use num_bigint::BigUint;
            // for chunks in board.chunks(4) {
            //     for x in chunks.iter() {
            //         let val =
            //             BigUint::from_bytes_le(x.get_value().unwrap_or(F::ZERO).to_repr().as_ref());
            //         print!("{:?},", val);
            //     }
            //     println!();
            // }
            // println!("---------");
        }

        Ok(board)
    }
}

#[cfg(test)]
mod test {
    use ff::Field;
    use flate2::{write::ZlibEncoder, Compression};
    use nova_snark::{
        traits::{circuit::TrivialCircuit, snark::default_ck_hint, Group},
        CompressedSNARK, PublicParams, RecursiveSNARK,
    };
    use std::time::Instant;

    use crate::game_2048::Game2048Circuit;

    type E1 = pasta_curves::pallas::Point;
    type E2 = pasta_curves::vesta::Point;

    const ZERO: <E1 as Group>::Scalar = <E1 as Group>::Scalar::ZERO;
    const ONE: <E1 as Group>::Scalar = <E1 as Group>::Scalar::ONE;
    const UP: [<E1 as Group>::Scalar; 4] = [ONE, ZERO, ZERO, ZERO];
    const DOWN: [<E1 as Group>::Scalar; 4] = [ZERO, ONE, ZERO, ZERO];
    const LEFT: [<E1 as Group>::Scalar; 4] = [ZERO, ZERO, ONE, ZERO];
    const RIGHT: [<E1 as Group>::Scalar; 4] = [ZERO, ZERO, ZERO, ONE];

    #[test]
    fn test_2048() {
        let directions = vec![
            [LEFT, RIGHT, DOWN, LEFT, UP, LEFT, UP, UP, RIGHT, UP],
            [LEFT, LEFT, UP, LEFT, UP, LEFT, UP, UP, LEFT, LEFT],
            [UP, UP, RIGHT, UP, UP, LEFT, LEFT, UP, LEFT, UP],
            [UP, UP, LEFT, LEFT, RIGHT, LEFT, UP, LEFT, UP, LEFT],
            [LEFT, DOWN, LEFT, UP, UP, LEFT, LEFT, UP, UP, UP],
        ];

        let mut circuits_primary = vec![];
        for chunks in directions.iter() {
            circuits_primary.push(Game2048Circuit::new(chunks));
        }

        let circuit_secondary = TrivialCircuit::default();

        let num_steps = directions.len();
        println!("num steps:{num_steps}");

        // produce public parameters
        let start = Instant::now();
        println!("Producing public parameters...");
        let pp = PublicParams::<
            E1,
            E2,
            Game2048Circuit<<E1 as Group>::Scalar>,
            TrivialCircuit<<E2 as Group>::Scalar>,
        >::setup(
            &circuits_primary[0],
            &circuit_secondary,
            &*default_ck_hint(),
            &*default_ck_hint(),
        );
        println!("PublicParams::setup, took {:?} ", start.elapsed());

        println!(
            "Number of constraints per step (primary circuit): {}",
            pp.num_constraints().0
        );
        println!(
            "Number of constraints per step (secondary circuit): {}",
            pp.num_constraints().1
        );

        println!(
            "Number of variables per step (primary circuit): {}",
            pp.num_variables().0
        );
        println!(
            "Number of variables per step (secondary circuit): {}",
            pp.num_variables().1
        );

        let two = ONE + ONE;
        let four = two.double();
        #[rustfmt::skip]
        let z0_primary = vec![
            ZERO, ZERO, two,  ZERO,
            ZERO, four, ZERO, ZERO,
            ZERO, ZERO, ZERO, ZERO,
            ZERO, ZERO, ZERO, ZERO,
        ];
        let z0_secondary = vec![<E2 as Group>::Scalar::zero()];

        type C1 = Game2048Circuit<<E1 as Group>::Scalar>;
        type C2 = TrivialCircuit<<E2 as Group>::Scalar>;
        // produce a recursive SNARK
        println!("Generating a RecursiveSNARK...");
        let mut recursive_snark: RecursiveSNARK<E1, E2, C1, C2> =
            RecursiveSNARK::<E1, E2, C1, C2>::new(
                &pp,
                &circuits_primary[0],
                &circuit_secondary,
                &z0_primary,
                &z0_secondary,
            )
            .unwrap();

        for (i, circuit_primary) in circuits_primary.iter().enumerate() {
            let start = Instant::now();
            let res = recursive_snark.prove_step(&pp, circuit_primary, &circuit_secondary);
            assert!(res.is_ok());
            println!(
                "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
                i,
                res.is_ok(),
                start.elapsed()
            );
        }

        // verify the recursive SNARK
        println!("Verifying a RecursiveSNARK...");
        let start = Instant::now();
        let res = recursive_snark.verify(&pp, num_steps, &z0_primary, &z0_secondary);
        println!(
            "RecursiveSNARK::verify: {:?}, took {:?}",
            res.is_ok(),
            start.elapsed()
        );
        assert!(res.is_ok());

        // produce a compressed SNARK
        println!("Generating a CompressedSNARK using Spartan with IPA-PC...");
        let (pk, vk) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp).unwrap();

        let start = Instant::now();
        type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<E1>;
        type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
        type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>;
        type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;

        let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark);
        println!(
            "CompressedSNARK::prove: {:?}, took {:?}",
            res.is_ok(),
            start.elapsed()
        );
        assert!(res.is_ok());
        let compressed_snark = res.unwrap();

        let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
        bincode::serialize_into(&mut encoder, &compressed_snark).unwrap();
        let compressed_snark_encoded = encoder.finish().unwrap();
        println!(
            "CompressedSNARK::len {:?} bytes",
            compressed_snark_encoded.len()
        );

        // verify the compressed SNARK
        println!("Verifying a CompressedSNARK...");
        let start = Instant::now();
        let res = compressed_snark.verify(&vk, num_steps, &z0_primary, &z0_secondary);
        println!(
            "CompressedSNARK::verify: {:?}, took {:?}",
            res.is_ok(),
            start.elapsed()
        );
        assert!(res.is_ok());
        println!("=========================================================");
    }
}
