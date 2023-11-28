use crate::NumConstraintSystem;
use bellpepper_core::{num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError};
use ff::PrimeField;

pub struct CanMove<F: PrimeField> {
    pub old_board: Vec<AllocatedNum<F>>,
    pub restored_board: Vec<AllocatedNum<F>>,
}

impl<F: PrimeField> CanMove<F> {
    pub fn new(old_board: &[AllocatedNum<F>], restored_board: &[AllocatedNum<F>]) -> Self {
        assert_eq!(old_board.len(), 16);

        Self {
            old_board: old_board.to_vec(),
            restored_board: restored_board.to_vec(),
        }
    }

    pub fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let mut diff_bits = Vec::new();
        for (i, (x, y)) in self
            .old_board
            .iter()
            .zip(self.restored_board.iter())
            .enumerate()
        {
            let bit = x.is_equal(
                cs.namespace(|| format!("old_board_is_equal_to_restored_board_{}", i)),
                y,
            )?;
            diff_bits.push(bit);
        }

        let sum_diff_bits = AllocatedNum::sum(cs.namespace(|| "sum_diff_bits"), &diff_bits)?;

        let sixteen = AllocatedNum::alloc(cs.namespace(|| "alloc_sixteen"), || Ok(F::from(16)))?;
        let sixteen_lc = |init: LinearCombination<F>| -> LinearCombination<F> {
            let mut tmp = init.clone() + sixteen.get_variable();
            for _ in 0..16 {
                tmp = tmp - CS::one()
            }

            tmp
        };
        cs.enforce(|| "enforce_sixteen", |lc| lc, |lc| lc, sixteen_lc);

        let sum_sub_sixteen = sum_diff_bits.sub(cs.namespace(|| "sum_sub_sixteen"), &sixteen)?;

        let moveable = sum_sub_sixteen.is_not_equal_to_zero(cs.namespace(|| "moveable"))?;

        Ok(moveable)
    }
}

#[cfg(test)]
mod test {
    use bellpepper_core::{num::AllocatedNum, test_cs::TestConstraintSystem, ConstraintSystem};
    use blstrs::Scalar as Fr;
    use ff::Field;

    use crate::can_move::CanMove;

    #[test]
    fn test_can_move() {
        let zero = Fr::ZERO;
        let one = Fr::ONE;
        let two = Fr::from(2);
        let four = Fr::from(4);

        let mut cs = TestConstraintSystem::<Fr>::new();

        #[rustfmt::skip]
       let board = vec![
           two,   two,   two,   two,
           zero,  zero,  zero,  zero,
           zero,  zero,  zero,  zero,
           zero,  zero,  zero,  zero,
       ];

        let mut board_vars = Vec::new();
        for (i, x) in board.iter().enumerate() {
            board_vars.push(
                AllocatedNum::alloc(cs.namespace(|| format!("input_board_{i}")), || Ok(*x))
                    .unwrap(),
            );
        }

        #[rustfmt::skip]
       let restored_board = vec![
           four,  four,  zero,  zero,
           zero,  zero,  zero,  zero,
           zero,  zero,  zero,  zero,
           zero,  zero,  zero,  zero,
       ];

        let mut restored_board_vars = Vec::new();
        for (i, x) in restored_board.iter().enumerate() {
            restored_board_vars.push(
                AllocatedNum::alloc(cs.namespace(|| format!("restored_board_{i}")), || Ok(*x))
                    .unwrap(),
            );
        }

        let circuit = CanMove::new(&board_vars, &restored_board_vars);
        let moveable = circuit.synthesize(&mut cs).unwrap();
        assert!(cs.is_satisfied());

        assert_eq!(moveable.get_value().unwrap(), one);
    }

    #[test]
    fn test_cannot_move() {
        let zero = Fr::ZERO;
        let two = Fr::from(2);
        let four = Fr::from(4);

        let mut cs = TestConstraintSystem::<Fr>::new();

        #[rustfmt::skip]
       let board = vec![
           two,   two,   four,   four,
           zero,  zero,  zero,  zero,
           zero,  zero,  zero,  zero,
           zero,  zero,  zero,  zero,
       ];

        let mut board_vars = Vec::new();
        for (i, x) in board.iter().enumerate() {
            board_vars.push(
                AllocatedNum::alloc(cs.namespace(|| format!("input_board_{i}")), || Ok(*x))
                    .unwrap(),
            );
        }

        #[rustfmt::skip]
       let restored_board = vec![
           two,   two,   four,  four,
           zero,  zero,  zero,  zero,
           zero,  zero,  zero,  zero,
           zero,  zero,  zero,  zero,
       ];

        let mut restored_board_vars = Vec::new();
        for (i, x) in restored_board.iter().enumerate() {
            restored_board_vars.push(
                AllocatedNum::alloc(cs.namespace(|| format!("restored_board_{i}")), || Ok(*x))
                    .unwrap(),
            );
        }

        let circuit = CanMove::new(&board_vars, &restored_board_vars);
        let moveable = circuit.synthesize(&mut cs).unwrap();
        assert!(cs.is_satisfied());

        assert_eq!(moveable.get_value().unwrap(), zero);
    }
}
