use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;

use crate::NumConstraintSystem;

pub struct SortByZero<F: PrimeField> {
    pub lines: Vec<Vec<AllocatedNum<F>>>,

    pub sorted_lines: Vec<Vec<AllocatedNum<F>>>,

    pub namespace_index: usize,
}

impl<F: PrimeField> SortByZero<F> {
    pub fn new(lines: &[Vec<AllocatedNum<F>>], namespace_index: usize) -> Self {
        assert_eq!(lines.len(), 4);
        assert!(lines.iter().all(|x| x.len() == 4));

        Self {
            lines: lines.to_vec(),
            sorted_lines: vec![],
            namespace_index,
        }
    }

    pub fn synthesize<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        // Takes two allocated numbers (a, b) and returns
        // (b, a) if and only if `a` == 0 , and (a, b)
        // otherwise.
        let mut swap = |a: &AllocatedNum<F>,
                        b: &AllocatedNum<F>|
         -> Result<(AllocatedNum<F>, AllocatedNum<F>), SynthesisError> {
            let bit = a.is_equal_to_zero_bit(
                cs.namespace(|| format!("a_is_equal_to_zero_bit{}", self.namespace_index)),
            )?;

            let boolean = Boolean::Is(bit);
            let (c, d) = AllocatedNum::conditionally_reverse(
                cs.namespace(|| format!("conditionally_reverse_{}", self.namespace_index)),
                a,
                b,
                &boolean,
            )
            .unwrap();

            self.namespace_index += 1;

            Ok((c, d))
        };

        let mut sorted_lines = Vec::new();

        for line in self.lines.iter() {
            let (new_line_0, new_line_1) = swap(&line[0], &line[1])?;
            let (new_line_0, new_line_2) = swap(&new_line_0, &line[2])?;
            let (new_line_0, new_line_3) = swap(&new_line_0, &line[3])?;
            let (new_line_1, new_line_2) = swap(&new_line_1, &new_line_2)?;
            let (new_line_1, new_line_3) = swap(&new_line_1, &new_line_3)?;
            let (new_line_2, new_line_3) = swap(&new_line_2, &new_line_3)?;

            sorted_lines.push(vec![new_line_0, new_line_1, new_line_2, new_line_3])
        }

        self.sorted_lines = sorted_lines;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use bellpepper_core::{num::AllocatedNum, test_cs::TestConstraintSystem, ConstraintSystem};
    use blstrs::Scalar as Fr;
    use ff::Field;

    use super::SortByZero;

    #[test]
    fn test_clear_zero() {
        let zero = Fr::ZERO;
        let two = Fr::from(2);
        let four = Fr::from(4);

        let line_0 = vec![zero, zero, four, zero];
        let line_1 = vec![zero, two, two, zero];
        let line_2 = vec![zero, two, four, four];
        let line_3 = vec![two, zero, zero, four];

        let mut cs = TestConstraintSystem::<Fr>::new();

        let mut line_0_vars = vec![];
        let mut line_1_vars = vec![];
        let mut line_2_vars = vec![];
        let mut line_3_vars = vec![];

        for (i, x) in line_0.iter().enumerate() {
            line_0_vars.push(
                AllocatedNum::alloc(cs.namespace(|| format!("alloc_line_0_{}", i)), || Ok(*x))
                    .unwrap(),
            )
        }

        for (i, x) in line_1.iter().enumerate() {
            line_1_vars.push(
                AllocatedNum::alloc(cs.namespace(|| format!("alloc_line_1_{}", i)), || Ok(*x))
                    .unwrap(),
            )
        }

        for (i, x) in line_2.iter().enumerate() {
            line_2_vars.push(
                AllocatedNum::alloc(cs.namespace(|| format!("alloc_line_2_{}", i)), || Ok(*x))
                    .unwrap(),
            )
        }

        for (i, x) in line_3.iter().enumerate() {
            line_3_vars.push(
                AllocatedNum::alloc(cs.namespace(|| format!("alloc_line_3_{}", i)), || Ok(*x))
                    .unwrap(),
            )
        }

        let mut circuit = SortByZero::new(&[line_0_vars, line_1_vars, line_2_vars, line_3_vars], 0);
        circuit.synthesize(&mut cs).unwrap();

        let mut sorted_lines = vec![];
        for x in circuit.sorted_lines {
            let mut line = Vec::new();
            for y in x {
                line.push(y.get_value().unwrap())
            }
            sorted_lines.push(line)
        }

        assert_eq!(sorted_lines[0], vec![four, zero, zero, zero]);
        assert_eq!(sorted_lines[1], vec![two, two, zero, zero]);
        assert_eq!(sorted_lines[2], vec![two, four, four, zero]);
        assert_eq!(sorted_lines[3], vec![two, four, zero, zero]);
    }
}
