use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;

use crate::NumConstraintSystem;

pub struct Restore<F: PrimeField> {
    pub lines: Vec<Vec<AllocatedNum<F>>>,

    pub direction: Vec<AllocatedNum<F>>,

    pub board: Vec<AllocatedNum<F>>,
}

impl<F: PrimeField> Restore<F> {
    pub fn new(lines: &[Vec<AllocatedNum<F>>], direction: &[AllocatedNum<F>]) -> Self {
        assert_eq!(lines.len(), 4);
        assert!(lines.iter().all(|x| x.len() == 4));

        Self {
            lines: lines.to_vec(),
            direction: direction.to_vec(),
            board: vec![],
        }
    }

    pub fn synthesize<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let board_0 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_0"),
            &[
                self.lines[0][0].clone(),
                self.lines[0][3].clone(),
                self.lines[0][0].clone(),
                self.lines[0][3].clone(),
            ],
            &self.direction,
        )?;

        let board_1 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_1"),
            &[
                self.lines[1][0].clone(),
                self.lines[1][3].clone(),
                self.lines[0][1].clone(),
                self.lines[0][2].clone(),
            ],
            &self.direction,
        )?;

        let board_2 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_2"),
            &[
                self.lines[2][0].clone(),
                self.lines[2][3].clone(),
                self.lines[0][2].clone(),
                self.lines[0][1].clone(),
            ],
            &self.direction,
        )?;

        let board_3 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_3"),
            &[
                self.lines[3][0].clone(),
                self.lines[3][3].clone(),
                self.lines[0][3].clone(),
                self.lines[0][0].clone(),
            ],
            &self.direction,
        )?;

        let board_4 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_4"),
            &[
                self.lines[0][1].clone(),
                self.lines[0][2].clone(),
                self.lines[1][0].clone(),
                self.lines[1][3].clone(),
            ],
            &self.direction,
        )?;

        let board_5 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_5"),
            &[
                self.lines[1][1].clone(),
                self.lines[1][2].clone(),
                self.lines[1][1].clone(),
                self.lines[1][2].clone(),
            ],
            &self.direction,
        )?;

        let board_6 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_6"),
            &[
                self.lines[2][1].clone(),
                self.lines[2][2].clone(),
                self.lines[1][2].clone(),
                self.lines[1][1].clone(),
            ],
            &self.direction,
        )?;

        let board_7 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_7"),
            &[
                self.lines[3][1].clone(),
                self.lines[3][2].clone(),
                self.lines[1][3].clone(),
                self.lines[1][0].clone(),
            ],
            &self.direction,
        )?;

        let board_8 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_8"),
            &[
                self.lines[0][2].clone(),
                self.lines[0][1].clone(),
                self.lines[2][0].clone(),
                self.lines[2][3].clone(),
            ],
            &self.direction,
        )?;

        let board_9 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_9"),
            &[
                self.lines[1][2].clone(),
                self.lines[1][1].clone(),
                self.lines[2][1].clone(),
                self.lines[2][2].clone(),
            ],
            &self.direction,
        )?;

        let board_10 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_10"),
            &[
                self.lines[2][2].clone(),
                self.lines[2][1].clone(),
                self.lines[2][2].clone(),
                self.lines[2][1].clone(),
            ],
            &self.direction,
        )?;

        let board_11 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_11"),
            &[
                self.lines[3][2].clone(),
                self.lines[3][1].clone(),
                self.lines[2][3].clone(),
                self.lines[2][0].clone(),
            ],
            &self.direction,
        )?;

        let board_12 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_12"),
            &[
                self.lines[0][3].clone(),
                self.lines[0][0].clone(),
                self.lines[3][0].clone(),
                self.lines[3][3].clone(),
            ],
            &self.direction,
        )?;

        let board_13 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_13"),
            &[
                self.lines[1][3].clone(),
                self.lines[1][0].clone(),
                self.lines[3][1].clone(),
                self.lines[3][2].clone(),
            ],
            &self.direction,
        )?;

        let board_14 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_14"),
            &[
                self.lines[2][3].clone(),
                self.lines[2][0].clone(),
                self.lines[3][2].clone(),
                self.lines[3][1].clone(),
            ],
            &self.direction,
        )?;

        let board_15 = AllocatedNum::product_sum(
            cs.namespace(|| "restore_15"),
            &[
                self.lines[3][3].clone(),
                self.lines[3][0].clone(),
                self.lines[3][3].clone(),
                self.lines[3][0].clone(),
            ],
            &self.direction,
        )?;

        self.board = vec![
            board_0, board_1, board_2, board_3, board_4, board_5, board_6, board_7, board_8,
            board_9, board_10, board_11, board_12, board_13, board_14, board_15,
        ];

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use bellpepper_core::{num::AllocatedNum, test_cs::TestConstraintSystem, ConstraintSystem};
    use blstrs::Scalar as Fr;
    use ff::Field;

    use crate::{direction_chooser::DirectionChooser, merge::Merge, sort::SortByZero};

    use super::Restore;

    #[test]
    fn test_up() {
        let zero = Fr::ZERO;
        let one = Fr::ONE;
        let two = Fr::from(2);
        let four = Fr::from(4);
        let eight = Fr::from(8);
        let f16 = Fr::from(16);

        #[rustfmt::skip]
        let board = vec![
            zero,  eight,  two,  two,
            two,   zero,   two,  two,
            two,   eight,  two,  zero,
            zero,  zero,   two,  two,
        ];

        let mut cs = TestConstraintSystem::<Fr>::new();

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

        let mut step_0 = DirectionChooser::new(&board_vars, &direction);
        step_0.synthesize(&mut cs).unwrap();

        let mut step_1 = SortByZero::new(&step_0.lines, 0);
        step_1.synthesize(&mut cs).unwrap();

        let mut step_2 = Merge::new(&step_1.sorted_lines);
        step_2.synthesize(&mut cs).unwrap();

        let mut step_3 = SortByZero::new(&step_2.merged_lines, step_1.namespace_index);
        step_3.synthesize(&mut cs).unwrap();

        let mut step_4 = Restore::new(&step_3.sorted_lines, &direction);
        step_4.synthesize(&mut cs).unwrap();
        assert!(cs.is_satisfied());

        let mut board: Vec<_> = vec![];
        for x in step_4.board {
            board.push(x.get_value().unwrap())
        }

        assert_eq!(
            board,
            vec![
                four, f16, four, four, zero, zero, four, two, zero, zero, zero, zero, zero, zero,
                zero, zero
            ]
        );
    }

    #[test]
    fn test_down() {
        let zero = Fr::ZERO;
        let one = Fr::ONE;
        let two = Fr::from(2);
        let four = Fr::from(4);
        let eight = Fr::from(8);
        let f16 = Fr::from(16);

        #[rustfmt::skip]
        let board = vec![
            zero,  eight,  two,  two,
            two,   zero,   two,  two,
            two,   eight,  two,  zero,
            zero,  zero,   two,  two,
        ];

        let mut cs = TestConstraintSystem::<Fr>::new();

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

        let mut step_0 = DirectionChooser::new(&board_vars, &direction);
        step_0.synthesize(&mut cs).unwrap();

        let mut step_1 = SortByZero::new(&step_0.lines, 0);
        step_1.synthesize(&mut cs).unwrap();

        let mut step_2 = Merge::new(&step_1.sorted_lines);
        step_2.synthesize(&mut cs).unwrap();

        let mut step_3 = SortByZero::new(&step_2.merged_lines, step_1.namespace_index);
        step_3.synthesize(&mut cs).unwrap();

        let mut step_4 = Restore::new(&step_3.sorted_lines, &direction);
        step_4.synthesize(&mut cs).unwrap();
        assert!(cs.is_satisfied());

        let mut board: Vec<_> = vec![];
        for x in step_4.board {
            board.push(x.get_value().unwrap())
        }

        assert_eq!(
            board,
            vec![
                zero, zero, zero, zero, zero, zero, zero, zero, zero, zero, four, two, four, f16,
                four, four
            ]
        );
    }

    #[test]
    fn test_left() {
        let zero = Fr::ZERO;
        let one = Fr::ONE;
        let two = Fr::from(2);
        let four = Fr::from(4);
        let eight = Fr::from(8);

        #[rustfmt::skip]
        let board = vec![
            zero,  eight,  two,  two,
            two,   zero,   two,  two,
            two,   eight,  two,  zero,
            zero,  zero,   two,  two,
        ];

        let mut cs = TestConstraintSystem::<Fr>::new();

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

        let mut step_0 = DirectionChooser::new(&board_vars, &direction);
        step_0.synthesize(&mut cs).unwrap();

        let mut step_1 = SortByZero::new(&step_0.lines, 0);
        step_1.synthesize(&mut cs).unwrap();

        let mut step_2 = Merge::new(&step_1.sorted_lines);
        step_2.synthesize(&mut cs).unwrap();

        let mut step_3 = SortByZero::new(&step_2.merged_lines, step_1.namespace_index);
        step_3.synthesize(&mut cs).unwrap();

        let mut step_4 = Restore::new(&step_3.sorted_lines, &direction);
        step_4.synthesize(&mut cs).unwrap();
        assert!(cs.is_satisfied());

        let mut board: Vec<_> = vec![];
        for x in step_4.board {
            board.push(x.get_value().unwrap())
        }

        assert_eq!(
            board,
            vec![
                eight, four, zero, zero, four, two, zero, zero, two, eight, two, zero, four, zero,
                zero, zero
            ]
        );
    }

    #[test]
    fn test_right() {
        let zero = Fr::ZERO;
        let one = Fr::ONE;
        let two = Fr::from(2);
        let four = Fr::from(4);
        let eight = Fr::from(8);

        #[rustfmt::skip]
        let board = vec![
            zero,  eight,  two,  two,
            two,   zero,   two,  two,
            two,   eight,  two,  zero,
            zero,  zero,   two,  two,
        ];

        let mut cs = TestConstraintSystem::<Fr>::new();

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

        let mut step_0 = DirectionChooser::new(&board_vars, &direction);
        step_0.synthesize(&mut cs).unwrap();

        let mut step_1 = SortByZero::new(&step_0.lines, 0);
        step_1.synthesize(&mut cs).unwrap();

        let mut step_2 = Merge::new(&step_1.sorted_lines);
        step_2.synthesize(&mut cs).unwrap();

        let mut step_3 = SortByZero::new(&step_2.merged_lines, step_1.namespace_index);
        step_3.synthesize(&mut cs).unwrap();

        let mut step_4 = Restore::new(&step_3.sorted_lines, &direction);
        step_4.synthesize(&mut cs).unwrap();
        assert!(cs.is_satisfied());

        let mut board: Vec<_> = vec![];
        for x in step_4.board {
            board.push(x.get_value().unwrap())
        }

        assert_eq!(
            board,
            vec![
                zero, zero, eight, four, zero, zero, two, four, zero, two, eight, two, zero, zero,
                zero, four
            ]
        );
    }
}
