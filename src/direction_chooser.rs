use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;

use crate::NumConstraintSystem;

pub struct DirectionChooser<F: PrimeField> {
    pub board: Vec<AllocatedNum<F>>,

    pub lines: Vec<Vec<AllocatedNum<F>>>,

    pub direction: Vec<AllocatedNum<F>>,
}

impl<F: PrimeField> DirectionChooser<F> {
    pub fn new(board: &[AllocatedNum<F>], direction: &[AllocatedNum<F>]) -> Self {
        assert_eq!(board.len(), 16);
        assert_eq!(direction.len(), 4);

        Self {
            board: board.to_vec(),
            lines: vec![],
            direction: direction.to_vec(),
        }
    }

    pub fn synthesize<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        for (i, x) in self.direction.iter().enumerate() {
            x.apply_bool_constraint(
                cs.namespace(|| format!("apply a boolean constraint on the direction {}", i)),
            );
        }

        let sum_direction =
            AllocatedNum::sum(cs.namespace(|| "sum_of_direction"), &self.direction)?;
        cs.enforce(
            || "enforce `sum_direction` is equal to one",
            |lc| lc,
            |lc| lc,
            |lc| lc + CS::one() - sum_direction.get_variable(),
        );

        let line_0 = vec![
            AllocatedNum::product_sum(
                cs.namespace(|| "0"),
                &[
                    self.board[0].clone(),
                    self.board[12].clone(),
                    self.board[0].clone(),
                    self.board[3].clone(),
                ],
                &self.direction,
            )?,
            AllocatedNum::product_sum(
                cs.namespace(|| "1"),
                &[
                    self.board[4].clone(),
                    self.board[8].clone(),
                    self.board[1].clone(),
                    self.board[2].clone(),
                ],
                &self.direction,
            )?,
            AllocatedNum::product_sum(
                cs.namespace(|| "2"),
                &[
                    self.board[8].clone(),
                    self.board[4].clone(),
                    self.board[2].clone(),
                    self.board[1].clone(),
                ],
                &self.direction,
            )?,
            AllocatedNum::product_sum(
                cs.namespace(|| "3"),
                &[
                    self.board[12].clone(),
                    self.board[0].clone(),
                    self.board[3].clone(),
                    self.board[0].clone(),
                ],
                &self.direction,
            )?,
        ];

        let line_1 = vec![
            AllocatedNum::product_sum(
                cs.namespace(|| "4"),
                &[
                    self.board[1].clone(),
                    self.board[13].clone(),
                    self.board[4].clone(),
                    self.board[7].clone(),
                ],
                &self.direction,
            )?,
            AllocatedNum::product_sum(
                cs.namespace(|| "5"),
                &[
                    self.board[5].clone(),
                    self.board[9].clone(),
                    self.board[5].clone(),
                    self.board[6].clone(),
                ],
                &self.direction,
            )?,
            AllocatedNum::product_sum(
                cs.namespace(|| "6"),
                &[
                    self.board[9].clone(),
                    self.board[5].clone(),
                    self.board[6].clone(),
                    self.board[5].clone(),
                ],
                &self.direction,
            )?,
            AllocatedNum::product_sum(
                cs.namespace(|| "7"),
                &[
                    self.board[13].clone(),
                    self.board[1].clone(),
                    self.board[7].clone(),
                    self.board[4].clone(),
                ],
                &self.direction,
            )?,
        ];

        let line_2 = vec![
            AllocatedNum::product_sum(
                cs.namespace(|| "8"),
                &[
                    self.board[2].clone(),
                    self.board[14].clone(),
                    self.board[8].clone(),
                    self.board[11].clone(),
                ],
                &self.direction,
            )?,
            AllocatedNum::product_sum(
                cs.namespace(|| "9"),
                &[
                    self.board[6].clone(),
                    self.board[10].clone(),
                    self.board[9].clone(),
                    self.board[10].clone(),
                ],
                &self.direction,
            )?,
            AllocatedNum::product_sum(
                cs.namespace(|| "10"),
                &[
                    self.board[10].clone(),
                    self.board[6].clone(),
                    self.board[10].clone(),
                    self.board[9].clone(),
                ],
                &self.direction,
            )?,
            AllocatedNum::product_sum(
                cs.namespace(|| "11"),
                &[
                    self.board[14].clone(),
                    self.board[2].clone(),
                    self.board[11].clone(),
                    self.board[8].clone(),
                ],
                &self.direction,
            )?,
        ];

        let line_3 = vec![
            AllocatedNum::product_sum(
                cs.namespace(|| "12"),
                &[
                    self.board[3].clone(),
                    self.board[15].clone(),
                    self.board[12].clone(),
                    self.board[15].clone(),
                ],
                &self.direction,
            )?,
            AllocatedNum::product_sum(
                cs.namespace(|| "13"),
                &[
                    self.board[7].clone(),
                    self.board[11].clone(),
                    self.board[13].clone(),
                    self.board[14].clone(),
                ],
                &self.direction,
            )?,
            AllocatedNum::product_sum(
                cs.namespace(|| "14"),
                &[
                    self.board[11].clone(),
                    self.board[7].clone(),
                    self.board[14].clone(),
                    self.board[13].clone(),
                ],
                &self.direction,
            )?,
            AllocatedNum::product_sum(
                cs.namespace(|| "15"),
                &[
                    self.board[15].clone(),
                    self.board[3].clone(),
                    self.board[15].clone(),
                    self.board[12].clone(),
                ],
                &self.direction,
            )?,
        ];

        self.lines = vec![line_0, line_1, line_2, line_3];

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use bellpepper_core::{num::AllocatedNum, test_cs::TestConstraintSystem, ConstraintSystem};
    use blstrs::Scalar as Fr;
    use ff::Field;

    use super::DirectionChooser;

    #[test]
    fn test_up() {
        let zero = Fr::ZERO;
        let one = Fr::ONE;
        let two = Fr::from(2);
        let four = Fr::from(4);
        let eight = Fr::from(8);

        let mut cs = TestConstraintSystem::<Fr>::new();

        #[rustfmt::skip]
       let board = vec![
           zero,  zero,  two,   two,
           two,   two,   four,  eight,
           four,  eight, zero,  zero,
           two,   four,  eight, zero,
       ];

        let mut board_vars = Vec::new();
        for (i, x) in board.iter().enumerate() {
            board_vars.push(
                AllocatedNum::alloc(cs.namespace(|| format!("board_{i}")), || Ok(*x)).unwrap(),
            );
        }

        let up = one;
        let down = zero;
        let left = zero;
        let right = zero;

        let up_var = AllocatedNum::alloc(cs.namespace(|| "alloc up"), || Ok(up)).unwrap();
        let down_var = AllocatedNum::alloc(cs.namespace(|| "alloc down"), || Ok(down)).unwrap();
        let left_var = AllocatedNum::alloc(cs.namespace(|| "alloc left"), || Ok(left)).unwrap();
        let right_var = AllocatedNum::alloc(cs.namespace(|| "alloc right"), || Ok(right)).unwrap();

        let direction = vec![up_var, down_var, left_var, right_var];

        let mut circuit = DirectionChooser::new(&board_vars, &direction);
        circuit.synthesize(&mut cs).unwrap();
        assert!(cs.is_satisfied());

        let mut lines = vec![];
        for x in circuit.lines {
            let mut line = Vec::new();
            for y in x {
                line.push(y.get_value().unwrap())
            }
            lines.push(line)
        }

        assert_eq!(lines[0], vec![board[0], board[4], board[8], board[12]]);
        assert_eq!(lines[1], vec![board[1], board[5], board[9], board[13]]);
        assert_eq!(lines[2], vec![board[2], board[6], board[10], board[14]]);
        assert_eq!(lines[3], vec![board[3], board[7], board[11], board[15]]);
    }

    #[test]
    fn test_down() {
        let zero = Fr::ZERO;
        let one = Fr::ONE;
        let two = Fr::from(2);
        let four = Fr::from(4);
        let eight = Fr::from(8);

        let mut cs = TestConstraintSystem::<Fr>::new();

        #[rustfmt::skip]
       let board = vec![
           zero,  zero,  two,   two,
           two,   two,   four,  eight,
           four,  eight, zero,  zero,
           two,   four,  eight, zero,
       ];

        let mut board_vars = Vec::new();
        for (i, x) in board.iter().enumerate() {
            board_vars.push(
                AllocatedNum::alloc(cs.namespace(|| format!("board_{i}")), || Ok(*x)).unwrap(),
            );
        }

        let up = zero;
        let down = one;
        let left = zero;
        let right = zero;

        let up_var = AllocatedNum::alloc(cs.namespace(|| "alloc up"), || Ok(up)).unwrap();
        let down_var = AllocatedNum::alloc(cs.namespace(|| "alloc down"), || Ok(down)).unwrap();
        let left_var = AllocatedNum::alloc(cs.namespace(|| "alloc left"), || Ok(left)).unwrap();
        let right_var = AllocatedNum::alloc(cs.namespace(|| "alloc right"), || Ok(right)).unwrap();

        let direction = vec![up_var, down_var, left_var, right_var];

        let mut circuit = DirectionChooser::new(&board_vars, &direction);
        circuit.synthesize(&mut cs).unwrap();
        assert!(cs.is_satisfied());

        let mut lines = vec![];
        for x in circuit.lines {
            let mut line = Vec::new();
            for y in x {
                line.push(y.get_value().unwrap())
            }
            lines.push(line)
        }

        assert_eq!(lines[0], vec![board[12], board[8], board[4], board[0]]);
        assert_eq!(lines[1], vec![board[13], board[9], board[5], board[1]]);
        assert_eq!(lines[2], vec![board[14], board[10], board[6], board[2]]);
        assert_eq!(lines[3], vec![board[15], board[11], board[7], board[3]]);
    }

    #[test]
    fn test_left() {
        let zero = Fr::ZERO;
        let one = Fr::ONE;
        let two = Fr::from(2);
        let four = Fr::from(4);
        let eight = Fr::from(8);

        let mut cs = TestConstraintSystem::<Fr>::new();

        #[rustfmt::skip]
       let board = vec![
           zero,  zero,  two,   two,
           two,   two,   four,  eight,
           four,  eight, zero,  zero,
           two,   four,  eight, zero,
       ];

        let mut board_vars = Vec::new();
        for (i, x) in board.iter().enumerate() {
            board_vars.push(
                AllocatedNum::alloc(cs.namespace(|| format!("board_{i}")), || Ok(*x)).unwrap(),
            );
        }

        let up = zero;
        let down = zero;
        let left = one;
        let right = zero;

        let up_var = AllocatedNum::alloc(cs.namespace(|| "alloc up"), || Ok(up)).unwrap();
        let down_var = AllocatedNum::alloc(cs.namespace(|| "alloc down"), || Ok(down)).unwrap();
        let left_var = AllocatedNum::alloc(cs.namespace(|| "alloc left"), || Ok(left)).unwrap();
        let right_var = AllocatedNum::alloc(cs.namespace(|| "alloc right"), || Ok(right)).unwrap();

        let direction = vec![up_var, down_var, left_var, right_var];

        let mut circuit = DirectionChooser::new(&board_vars, &direction);
        circuit.synthesize(&mut cs).unwrap();
        assert!(cs.is_satisfied());

        let mut lines = vec![];
        for x in circuit.lines {
            let mut line = Vec::new();
            for y in x {
                line.push(y.get_value().unwrap())
            }
            lines.push(line)
        }

        assert_eq!(lines[0], vec![board[0], board[1], board[2], board[3]]);
        assert_eq!(lines[1], vec![board[4], board[5], board[6], board[7]]);
        assert_eq!(lines[2], vec![board[8], board[9], board[10], board[11]]);
        assert_eq!(lines[3], vec![board[12], board[13], board[14], board[15]]);
    }

    #[test]
    fn test_right() {
        let zero = Fr::ZERO;
        let one = Fr::ONE;
        let two = Fr::from(2);
        let four = Fr::from(4);
        let eight = Fr::from(8);

        let mut cs = TestConstraintSystem::<Fr>::new();

        #[rustfmt::skip]
       let board = vec![
           zero,  zero,  two,   two,
           two,   two,   four,  eight,
           four,  eight, zero,  zero,
           two,   four,  eight, zero,
       ];

        let mut board_vars = Vec::new();
        for (i, x) in board.iter().enumerate() {
            board_vars.push(
                AllocatedNum::alloc(cs.namespace(|| format!("board_{i}")), || Ok(*x)).unwrap(),
            );
        }

        let up = zero;
        let down = zero;
        let left = zero;
        let right = one;

        let up_var = AllocatedNum::alloc(cs.namespace(|| "alloc up"), || Ok(up)).unwrap();
        let down_var = AllocatedNum::alloc(cs.namespace(|| "alloc down"), || Ok(down)).unwrap();
        let left_var = AllocatedNum::alloc(cs.namespace(|| "alloc left"), || Ok(left)).unwrap();
        let right_var = AllocatedNum::alloc(cs.namespace(|| "alloc right"), || Ok(right)).unwrap();

        let direction = vec![up_var, down_var, left_var, right_var];

        let mut circuit = DirectionChooser::new(&board_vars, &direction);
        circuit.synthesize(&mut cs).unwrap();
        assert!(cs.is_satisfied());

        let mut lines = vec![];
        for x in circuit.lines {
            let mut line = Vec::new();
            for y in x {
                line.push(y.get_value().unwrap())
            }
            lines.push(line)
        }

        assert_eq!(lines[0], vec![board[3], board[2], board[1], board[0]]);
        assert_eq!(lines[1], vec![board[7], board[6], board[5], board[4]]);
        assert_eq!(lines[2], vec![board[11], board[10], board[9], board[8]]);
        assert_eq!(lines[3], vec![board[15], board[14], board[13], board[12]]);
    }
}
