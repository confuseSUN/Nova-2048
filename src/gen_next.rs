use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;
use num_bigint::BigUint;
use num_integer::Integer;

use crate::NumConstraintSystem;

pub struct GenNext<F: PrimeField> {
    pub old_board: Vec<AllocatedNum<F>>,

    pub moveable_flag: AllocatedNum<F>,

    pub new_board: Vec<AllocatedNum<F>>,
}

impl<F: PrimeField> GenNext<F> {
    pub fn new(old_board: &[AllocatedNum<F>], moveable_flag: &AllocatedNum<F>) -> Self {
        assert_eq!(old_board.len(), 16);

        Self {
            old_board: old_board.to_vec(),
            moveable_flag: moveable_flag.clone(),
            new_board: vec![],
        }
    }

    pub fn synthesize<CS: ConstraintSystem<F>>(
        &mut self,
        mut cs: CS,
    ) -> Result<(), SynthesisError> {
        let mut flipped_bits = Vec::new();
        for (i, val) in self.old_board.iter().enumerate() {
            let bit = val.is_equal_to_zero(
                cs.namespace(|| format!("flipped_bits_is_equal_to_zero_{}", i)),
            )?;
            flipped_bits.push(bit);
        }

        let mut candidates = Vec::new();
        let mut num_candidates =
            AllocatedNum::zero(cs.namespace(|| "alloc_zero_for_num_candidates"))?;

        for i in 0..self.old_board.len() {
            num_candidates = num_candidates.add(
                cs.namespace(|| format!("num_candidates_add_{}", i)),
                &flipped_bits[i],
            )?;

            candidates.push(num_candidates.mul(
                cs.namespace(|| format!("candidates_mul_{}", i)),
                &flipped_bits[i],
            )?);
        }

        // A simple calculation for n=sum{old_board} + num_candidates,
        //
        // todo! replace n=hash(old_board, direction, ...).
        let mut n = AllocatedNum::sum(cs.namespace(|| "sum_of_board"), &self.old_board)?;
        n = n.add(cs.namespace(|| "add_num_candidates"), &num_candidates)?;
        let n_bytes = n.get_value().unwrap_or(F::ZERO).to_repr();
        let n_big = BigUint::from_bytes_le(n_bytes.as_ref());

        let game_over_flag = {
            // If `num_candidates` is 0, the game is over, and `game_over_flag` is set to 0.
            // If `num_candidates` is not 0, the game is not over, and `game_over_flag` is set to 1.
            let game_over_flag =
                num_candidates.is_not_equal_to_zero(cs.namespace(|| "game_over_flag"))?;

            // If game over, set `candidates[0]` to 1 to keep the game running smoothly.
            // In this case, `new_number` will be 0, so the board state will not change.
            let tmp = if game_over_flag
                .get_value()
                .unwrap_or(F::ZERO)
                .is_zero()
                .into()
            {
                F::ONE
            } else {
                candidates[0].get_value().unwrap()
            };
            let tmp_var = AllocatedNum::alloc(cs.namespace(|| "tmp_0"), || Ok(tmp))?;
            cs.enforce(
                || "enfore_(game_over_flag * candidates[0] = tmp + game_over_flag - 1)",
                |lc| lc + game_over_flag.get_variable(),
                |lc| lc + candidates[0].get_variable(),
                |lc| lc + tmp_var.get_variable() + game_over_flag.get_variable() - CS::one(),
            );
            candidates[0] = tmp_var;

            // If game over, set `num_candidates` to 1 to keep the game running smoothly.
            // In this case, `new_number` will be 0, so the board state will not change.
            let tmp = if game_over_flag
                .get_value()
                .unwrap_or(F::ZERO)
                .is_zero()
                .into()
            {
                F::ONE
            } else {
                num_candidates.get_value().unwrap()
            };
            let tmp_var = AllocatedNum::alloc(cs.namespace(|| "tmp_1"), || Ok(tmp))?;
            cs.enforce(
                || "enfore_(game_over_flag * num_candidates = tmp + game_over_flag - 1)",
                |lc| lc + game_over_flag.get_variable(),
                |lc| lc + num_candidates.get_variable(),
                |lc| lc + tmp_var.get_variable() + game_over_flag.get_variable() - CS::one(),
            );
            num_candidates = tmp_var;

            game_over_flag
        };

        let position = {
            let m_bytes = num_candidates.get_value().unwrap_or(F::ONE).to_repr();
            let m_big: BigUint = BigUint::from_bytes_le(m_bytes.as_ref());

            let (quotient, remainder) = n_big.div_rem(&m_big);
            let quotient = F::from_str_vartime(&quotient.to_string()).unwrap();
            let remainder = F::from_str_vartime(&remainder.to_string()).unwrap();

            let quotient_var =
                AllocatedNum::alloc(cs.namespace(|| "alloc_quotient"), || Ok(quotient))?;

            let position = remainder.add(F::ONE);
            let position_var =
                AllocatedNum::alloc(cs.namespace(|| "alloc_position"), || Ok(position))?;

            cs.enforce(
                || "enforce_(quotient * num_candidates = n + 1 - position)",
                |lc| lc + quotient_var.get_variable(),
                |lc| lc + num_candidates.get_variable(),
                |lc| lc + n.get_variable() + CS::one() - position_var.get_variable(),
            );

            position_var
        };

        let new_number = {
            let m = F::from(2);
            let m_big = BigUint::from_bytes_le(m.to_repr().as_ref());
            let m_var = AllocatedNum::alloc(cs.namespace(|| "alloc_m"), || Ok(m))?;
            cs.enforce(
                || "enforce_(m = 2)",
                |lc| lc,
                |lc| lc,
                |lc| lc + m_var.get_variable() - CS::one() - CS::one(),
            );

            let (quotient, remainder) = n_big.div_rem(&m_big);
            let quotient = F::from_str_vartime(&quotient.to_string()).unwrap();
            let remainder = F::from_str_vartime(&remainder.to_string()).unwrap();
            let quotient_var =
                AllocatedNum::alloc(cs.namespace(|| "alloc_quotient_for_new"), || Ok(quotient))?;
            let remainder_var =
                AllocatedNum::alloc(cs.namespace(|| "alloc_remainder"), || Ok(remainder))?;

            cs.enforce(
                || "enfore_(remainder < 2)",
                |lc| lc + remainder_var.get_variable(),
                |lc| lc + remainder_var.get_variable() - CS::one(),
                |lc| lc,
            );
            cs.enforce(
                || "enfore_(m * quotient = n - remainder)",
                |lc| lc + m_var.get_variable(),
                |lc| lc + quotient_var.get_variable(),
                |lc| lc + n.get_variable() - remainder_var.get_variable(),
            );

            // When the `remainder` is equal to 0, `new_number` is set to 2.
            // When the `remainder` is equal to 1, `new_number` is set to 4.
            //
            // So the new_number = 2 * (remainder +1).
            let new_number = remainder.add(F::ONE).mul(F::from(2));
            let mut new_number_var =
                AllocatedNum::alloc(cs.namespace(|| "alloc_new_number"), || Ok(new_number))?;
            cs.enforce(
                || "enfore_(2 * (remainder +1))",
                |lc| lc + remainder_var.get_variable() + CS::one(),
                |lc| lc + CS::one() + CS::one(),
                |lc| lc + new_number_var.get_variable(),
            );

            new_number_var =
                new_number_var.mul(cs.namespace(|| "mul_moveable"), &self.moveable_flag)?;
            new_number_var =
                new_number_var.mul(cs.namespace(|| "mul_game_over"), &game_over_flag)?;

            new_number_var
        };

        let mut candidates_minus_position = Vec::new();
        for (i, candidate) in candidates.iter().enumerate() {
            let r = candidate.sub(
                cs.namespace(|| format!("candidate_minus_position_{}", i)),
                &position,
            )?;
            candidates_minus_position.push(r)
        }

        let mut bits = Vec::new();
        for (i, x) in candidates_minus_position.iter().enumerate() {
            let bit = x.is_equal_to_zero(
                cs.namespace(|| format!("candidate_minus_position_is_equal_to_zero_{}", i)),
            )?;
            bits.push(bit)
        }

        // Enforce that the sum of bits equals 1,
        let sum_bits = AllocatedNum::sum(cs.namespace(|| "sum_of_bits"), &bits)?;
        cs.enforce(
            || "enfore_(sum_bits = 1)",
            |lc| lc,
            |lc| lc,
            |lc| lc + sum_bits.get_variable() - CS::one(),
        );

        let mut new_number_mul_bits = Vec::new();
        for (i, bit) in bits.iter().enumerate() {
            let r = new_number.mul(cs.namespace(|| format!("new_number_mul_bit_{}", i)), bit)?;
            new_number_mul_bits.push(r);
        }

        let mut new_board = Vec::new();
        for (i, (bit, old_board)) in new_number_mul_bits
            .iter()
            .zip(self.old_board.iter())
            .enumerate()
        {
            let r = bit.add(
                cs.namespace(|| format!("new_number_mul_bit_add_old_board{}", i)),
                old_board,
            )?;
            new_board.push(r);
        }

        self.new_board = new_board;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use bellpepper_core::{num::AllocatedNum, test_cs::TestConstraintSystem, ConstraintSystem};
    use blstrs::Scalar as Fr;
    use ff::Field;

    use super::GenNext;

    #[test]
    fn test_gen_next() {
        let zero = Fr::ZERO;
        let one = Fr::ONE;
        let two = Fr::from(2);
        let four = Fr::from(4);
        let eight = Fr::from(8);

        #[rustfmt::skip]
        let board = vec![
            zero,  zero,   two,   two,
            two,   two,    four,  eight,
            four,  eight,  zero,  zero,
            two,   four,   eight, zero,
        ];

        let mut cs = TestConstraintSystem::<Fr>::new();

        let mut board_vars = Vec::new();
        for (i, x) in board.iter().enumerate() {
            board_vars.push(
                AllocatedNum::alloc(cs.namespace(|| format!("board_{i}")), || Ok(*x)).unwrap(),
            );
        }

        let moveable = AllocatedNum::alloc(cs.namespace(|| "moveable"), || Ok(one)).unwrap();

        let mut circuit = GenNext::new(&board_vars, &moveable);
        circuit.synthesize(&mut cs).unwrap();
        assert!(cs.is_satisfied());

        let mut new_board: Vec<_> = vec![];
        for x in circuit.new_board {
            new_board.push(x.get_value().unwrap())
        }

        #[rustfmt::skip]
        assert_eq!(
            new_board,
            vec![
                zero,  four,   two,   two,
                two,   two,   four,  eight,
                four,  eight, zero,  zero,
                two,   four,  eight, zero,
            ]
        );
    }

    #[test]
    fn test_game_over() {
        let one = Fr::ONE;
        let four = Fr::from(4);

        #[rustfmt::skip]
        let board = vec![
            four,  four,  four,  four,
            four,  four,  four,  four,
            four,  four,  four,  four,
            four,  four,  four,  four,
        ];

        let mut cs = TestConstraintSystem::<Fr>::new();

        let mut board_vars = Vec::new();
        for (i, x) in board.iter().enumerate() {
            board_vars.push(
                AllocatedNum::alloc(cs.namespace(|| format!("board_{i}")), || Ok(*x)).unwrap(),
            );
        }

        let moveable = AllocatedNum::alloc(cs.namespace(|| "moveable"), || Ok(one)).unwrap();

        let mut circuit = GenNext::new(&board_vars, &moveable);
        circuit.synthesize(&mut cs).unwrap();
        assert!(cs.is_satisfied());

        let mut new_board: Vec<_> = vec![];
        for x in circuit.new_board {
            new_board.push(x.get_value().unwrap())
        }

        #[rustfmt::skip]
        assert_eq!(
            new_board,
            board
        );
    }
}
