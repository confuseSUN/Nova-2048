use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;

use crate::NumConstraintSystem;

pub struct Merge<F: PrimeField> {
    pub sorted_lines: Vec<Vec<AllocatedNum<F>>>,

    pub merged_lines: Vec<Vec<AllocatedNum<F>>>,
}

impl<F: PrimeField> Merge<F> {
    pub fn new(sorted_lines: &[Vec<AllocatedNum<F>>]) -> Self {
        assert_eq!(sorted_lines.len(), 4);
        assert!(sorted_lines.iter().all(|x| x.len() == 4));

        Self {
            sorted_lines: sorted_lines.to_vec(),
            merged_lines: vec![],
        }
    }

    pub fn synthesize<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let mut namespace_index = 0;

        // Takes two allocated numbers (a, b) and returns
        // (2 * a, 0) if and only if `a` == `b` , and (a, b)
        // otherwise.
        let mut merge = |a: &AllocatedNum<F>,
                         b: &AllocatedNum<F>|
         -> Result<(AllocatedNum<F>, AllocatedNum<F>), SynthesisError> {
            let bit = a.is_equal(
                cs.namespace(|| format!("a_is_equal_to_b_{}", namespace_index)),
                b,
            )?;

            let (c, d) = if bit.get_value().unwrap().is_zero().into() {
                (a.get_value().unwrap(), b.get_value().unwrap())
            } else {
                (a.get_value().unwrap().double(), F::ZERO)
            };

            let c_var = AllocatedNum::alloc(
                cs.namespace(|| format!("alloc_merge_c_{}", namespace_index)),
                || Ok(c),
            )?;
            let d_var = AllocatedNum::alloc(
                cs.namespace(|| format!("alloc_merge_d_{}", namespace_index)),
                || Ok(d),
            )?;

            cs.enforce(
                || format!("enforce_(a * bit = c - a)_{}", namespace_index),
                |lc| lc + a.get_variable(),
                |lc| lc + bit.get_variable(),
                |lc| lc + c_var.get_variable() - a.get_variable(),
            );
            cs.enforce(
                || format!("enforce_(b * bit = b - d)_{}", namespace_index),
                |lc| lc + b.get_variable(),
                |lc| lc + bit.get_variable(),
                |lc| lc + b.get_variable() - d_var.get_variable(),
            );

            namespace_index += 1;

            Ok((c_var, d_var))
        };

        let mut merged_lines = Vec::new();

        for line_var in self.sorted_lines.iter() {
            let (new_line_0, new_line_1) = merge(&line_var[0], &line_var[1])?;
            let (new_line_1, new_line_2) = merge(&new_line_1, &line_var[2])?;
            let (new_line_2, new_line_3) = merge(&new_line_2, &line_var[3])?;

            merged_lines.push(vec![new_line_0, new_line_1, new_line_2, new_line_3])
        }

        self.merged_lines = merged_lines;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use bellpepper_core::{num::AllocatedNum, test_cs::TestConstraintSystem, ConstraintSystem};
    use blstrs::Scalar as Fr;
    use ff::Field;

    use crate::{direction_chooser::DirectionChooser, sort::SortByZero};

    use super::Merge;

    #[test]
    fn test_up() {
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
        assert!(cs.is_satisfied());

        let mut merged_lines = vec![];
        for x in step_2.merged_lines {
            let mut line = Vec::new();
            for y in x {
                line.push(y.get_value().unwrap())
            }
            merged_lines.push(line)
        }

        assert_eq!(merged_lines[0], vec![four, zero, zero, zero]);
        assert_eq!(merged_lines[1], vec![Fr::from(16), zero, zero, zero]);
        assert_eq!(merged_lines[2], vec![four, zero, four, zero]);
        assert_eq!(merged_lines[3], vec![four, zero, two, zero]);
    }

    #[test]
    fn test_down() {
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
        assert!(cs.is_satisfied());

        let mut merged_lines = vec![];
        for x in step_2.merged_lines {
            let mut line = Vec::new();
            for y in x {
                line.push(y.get_value().unwrap())
            }
            merged_lines.push(line)
        }

        assert_eq!(merged_lines[0], vec![four, zero, zero, zero]);
        assert_eq!(merged_lines[1], vec![Fr::from(16), zero, zero, zero]);
        assert_eq!(merged_lines[2], vec![four, zero, four, zero]);
        assert_eq!(merged_lines[3], vec![four, zero, two, zero]);
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
        assert!(cs.is_satisfied());

        let mut merged_lines = vec![];
        for x in step_2.merged_lines {
            let mut line = Vec::new();
            for y in x {
                line.push(y.get_value().unwrap())
            }
            merged_lines.push(line)
        }

        assert_eq!(merged_lines[0], vec![eight, four, zero, zero]);
        assert_eq!(merged_lines[1], vec![four, zero, two, zero]);
        assert_eq!(merged_lines[2], vec![two, eight, two, zero]);
        assert_eq!(merged_lines[3], vec![four, zero, zero, zero]);
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
        assert!(cs.is_satisfied());

        let mut merged_lines = vec![];
        for x in step_2.merged_lines {
            let mut line = Vec::new();
            for y in x {
                line.push(y.get_value().unwrap())
            }
            merged_lines.push(line)
        }

        assert_eq!(merged_lines[0], vec![four, zero, eight, zero]);
        assert_eq!(merged_lines[1], vec![four, zero, two, zero]);
        assert_eq!(merged_lines[2], vec![two, eight, two, zero]);
        assert_eq!(merged_lines[3], vec![four, zero, zero, zero]);
    }
}
