use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;

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
        let up = self.direction[0].clone();
        let down = self.direction[1].clone();
        let left = self.direction[2].clone();
        let right = self.direction[3].clone();

        let mut namespace_index = 0;

        // The out = wires_in[0] * up +  wires_in[1] * down +  wires_in[2] * left +  wires_in[3] * right.
        let mut chooser =
            |wires_in: &[AllocatedNum<F>; 4]| -> Result<AllocatedNum<F>, SynthesisError> {
                let mul_up = wires_in[0].mul(
                    cs.namespace(|| format!("restore_up_{}", namespace_index)),
                    &up,
                )?;
                let mul_down = wires_in[1].mul(
                    cs.namespace(|| format!("restore_down_{}", namespace_index)),
                    &down,
                )?;
                let mul_left = wires_in[2].mul(
                    cs.namespace(|| format!("restore_left_{}", namespace_index)),
                    &left,
                )?;
                let mul_right = wires_in[3].mul(
                    cs.namespace(|| format!("restore_right_{}", namespace_index)),
                    &right,
                )?;

                let mut sum = mul_up.add(
                    cs.namespace(|| format!("restore_up_add_down_{}", namespace_index)),
                    &mul_down,
                )?;
                sum = sum.add(
                    cs.namespace(|| format!("restore_add_left_{}", namespace_index)),
                    &mul_left,
                )?;
                sum = sum.add(
                    cs.namespace(|| format!("restore_add_right_{}", namespace_index)),
                    &mul_right,
                )?;

                namespace_index += 1;

                Ok(sum)
            };

        let board_0 = chooser(&[
            self.lines[0][0].clone(),
            self.lines[0][3].clone(),
            self.lines[0][0].clone(),
            self.lines[0][3].clone(),
        ])?;

        let board_1 = chooser(&[
            self.lines[1][0].clone(),
            self.lines[1][3].clone(),
            self.lines[0][1].clone(),
            self.lines[0][2].clone(),
        ])?;

        let board_2 = chooser(&[
            self.lines[2][0].clone(),
            self.lines[2][3].clone(),
            self.lines[0][2].clone(),
            self.lines[0][1].clone(),
        ])?;

        let board_3 = chooser(&[
            self.lines[3][0].clone(),
            self.lines[3][3].clone(),
            self.lines[0][3].clone(),
            self.lines[0][0].clone(),
        ])?;

        let board_4 = chooser(&[
            self.lines[0][1].clone(),
            self.lines[0][2].clone(),
            self.lines[1][0].clone(),
            self.lines[1][3].clone(),
        ])?;

        let board_5 = chooser(&[
            self.lines[1][1].clone(),
            self.lines[1][2].clone(),
            self.lines[1][1].clone(),
            self.lines[1][2].clone(),
        ])?;

        let board_6 = chooser(&[
            self.lines[2][1].clone(),
            self.lines[2][2].clone(),
            self.lines[1][2].clone(),
            self.lines[1][1].clone(),
        ])?;

        let board_7 = chooser(&[
            self.lines[3][1].clone(),
            self.lines[3][2].clone(),
            self.lines[1][3].clone(),
            self.lines[1][0].clone(),
        ])?;

        let board_8 = chooser(&[
            self.lines[0][2].clone(),
            self.lines[0][1].clone(),
            self.lines[2][0].clone(),
            self.lines[2][3].clone(),
        ])?;

        let board_9 = chooser(&[
            self.lines[1][2].clone(),
            self.lines[1][1].clone(),
            self.lines[2][1].clone(),
            self.lines[2][2].clone(),
        ])?;

        let board_10 = chooser(&[
            self.lines[2][2].clone(),
            self.lines[2][1].clone(),
            self.lines[2][2].clone(),
            self.lines[2][1].clone(),
        ])?;

        let board_11 = chooser(&[
            self.lines[3][2].clone(),
            self.lines[3][1].clone(),
            self.lines[2][3].clone(),
            self.lines[2][0].clone(),
        ])?;

        let board_12 = chooser(&[
            self.lines[0][3].clone(),
            self.lines[0][0].clone(),
            self.lines[3][0].clone(),
            self.lines[3][3].clone(),
        ])?;

        let board_13 = chooser(&[
            self.lines[1][3].clone(),
            self.lines[1][0].clone(),
            self.lines[3][1].clone(),
            self.lines[3][2].clone(),
        ])?;

        let board_14 = chooser(&[
            self.lines[2][3].clone(),
            self.lines[2][0].clone(),
            self.lines[3][2].clone(),
            self.lines[3][1].clone(),
        ])?;

        let board_15 = chooser(&[
            self.lines[3][3].clone(),
            self.lines[3][0].clone(),
            self.lines[3][3].clone(),
            self.lines[3][0].clone(),
        ])?;

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

        let mut circuit_0 = DirectionChooser::new(&board_vars, &direction);
        circuit_0.synthesize(&mut cs).unwrap();

        let mut circuit_1 = SortByZero::new(&circuit_0.lines, 0);
        circuit_1.synthesize(&mut cs).unwrap();

        let mut circuit_2 = Merge::new(&circuit_1.sorted_lines);
        circuit_2.synthesize(&mut cs).unwrap();

        let mut circuit_3 = SortByZero::new(&circuit_2.merged_lines, circuit_1.namespace_index);
        circuit_3.synthesize(&mut cs).unwrap();

        let mut circuit_4 = Restore::new(&circuit_3.sorted_lines, &direction);
        circuit_4.synthesize(&mut cs).unwrap();

        let mut board: Vec<_> = vec![];
        for x in circuit_4.board {
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

        let mut circuit_0 = DirectionChooser::new(&board_vars, &direction);
        circuit_0.synthesize(&mut cs).unwrap();

        let mut circuit_1 = SortByZero::new(&circuit_0.lines, 0);
        circuit_1.synthesize(&mut cs).unwrap();

        let mut circuit_2 = Merge::new(&circuit_1.sorted_lines);
        circuit_2.synthesize(&mut cs).unwrap();

        let mut circuit_3 = SortByZero::new(&circuit_2.merged_lines, circuit_1.namespace_index);
        circuit_3.synthesize(&mut cs).unwrap();

        let mut circuit_4 = Restore::new(&circuit_3.sorted_lines, &direction);
        circuit_4.synthesize(&mut cs).unwrap();

        let mut board: Vec<_> = vec![];
        for x in circuit_4.board {
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

        let mut circuit_0 = DirectionChooser::new(&board_vars, &direction);
        circuit_0.synthesize(&mut cs).unwrap();

        let mut circuit_1 = SortByZero::new(&circuit_0.lines, 0);
        circuit_1.synthesize(&mut cs).unwrap();

        let mut circuit_2 = Merge::new(&circuit_1.sorted_lines);
        circuit_2.synthesize(&mut cs).unwrap();

        let mut circuit_3 = SortByZero::new(&circuit_2.merged_lines, circuit_1.namespace_index);
        circuit_3.synthesize(&mut cs).unwrap();

        let mut circuit_4 = Restore::new(&circuit_3.sorted_lines, &direction);
        circuit_4.synthesize(&mut cs).unwrap();

        let mut board: Vec<_> = vec![];
        for x in circuit_4.board {
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

        let mut circuit_0 = DirectionChooser::new(&board_vars, &direction);
        circuit_0.synthesize(&mut cs).unwrap();

        let mut circuit_1 = SortByZero::new(&circuit_0.lines, 0);
        circuit_1.synthesize(&mut cs).unwrap();

        let mut circuit_2 = Merge::new(&circuit_1.sorted_lines);
        circuit_2.synthesize(&mut cs).unwrap();

        let mut circuit_3 = SortByZero::new(&circuit_2.merged_lines, circuit_1.namespace_index);
        circuit_3.synthesize(&mut cs).unwrap();

        let mut circuit_4 = Restore::new(&circuit_3.sorted_lines, &direction);
        circuit_4.synthesize(&mut cs).unwrap();

        let mut board: Vec<_> = vec![];
        for x in circuit_4.board {
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
