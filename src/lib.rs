use bellpepper_core::{
    boolean::AllocatedBit, num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError,
};
use ff::PrimeField;

pub mod direction_chooser;
pub mod game;
pub mod gen_next;
pub mod merge;
pub mod restore;
pub mod sort;

pub trait NumConstraintSystem<F: PrimeField> {
    type Output;

    ///  Return the "zero" variable.
    fn zero<CS: ConstraintSystem<F>>(cs: CS) -> Result<Self::Output, SynthesisError>;

    ///  Return a variable that equals 1 if and only if `value` == 0,
    /// otherwise equals 0.
    fn is_equal_to_zero<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
    ) -> Result<Self::Output, SynthesisError>;

    ///  Return a boolean variable that equals 1 if and only if `value` == 0,
    /// otherwise equals 0.
    fn is_equal_to_zero_bit<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
    ) -> Result<AllocatedBit, SynthesisError>;

    /// Subtracts `other` from `self`
    fn sub<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<Self::Output, SynthesisError>;

    ///  Apply a boolean constraint.
    fn apply_bool_constraint<CS: ConstraintSystem<F>>(&self, cs: CS);

    /// Sums up a collection of variables.
    fn sum<CS: ConstraintSystem<F>>(
        cs: CS,
        vars: &[Self::Output],
    ) -> Result<Self::Output, SynthesisError>;

    /// Multiplies two collections of variables and returns their sum.
    fn product_sum<CS: ConstraintSystem<F>>(
        cs: CS,
        a: &[Self::Output],
        b: &[Self::Output],
    ) -> Result<Self::Output, SynthesisError>;
}

impl<F: PrimeField> NumConstraintSystem<F> for AllocatedNum<F> {
    type Output = Self;

    fn zero<CS: ConstraintSystem<F>>(mut cs: CS) -> Result<Self, SynthesisError> {
        let zero = Self::alloc(cs.namespace(|| "alloc"), || Ok(F::ZERO))?;

        cs.enforce(
            || "enforce_zero",
            |lc| lc + zero.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );

        Ok(zero)
    }

    fn is_equal_to_zero<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
    ) -> Result<Self::Output, SynthesisError> {
        let val = self.get_value().unwrap();
        let inv = self.get_value().unwrap().invert().unwrap_or(F::ZERO);
        let inv_var = AllocatedNum::alloc(cs.namespace(|| "alloc_inv"), || Ok(inv))?;

        let bit = if val.is_zero().into() {
            F::ONE
        } else {
            F::ZERO
        };
        let bit_var = AllocatedNum::alloc(cs.namespace(|| "alloc_bit"), || Ok(bit))?;

        cs.enforce(
            || "enforce_(val * inv = 1 - bit)",
            |lc| lc + self.get_variable(),
            |lc| lc + inv_var.get_variable(),
            |lc| lc + CS::one() - bit_var.get_variable(),
        );

        cs.enforce(
            || "enforce_(val * bit = 0)",
            |lc| lc + self.get_variable(),
            |lc| lc + bit_var.get_variable(),
            |lc| lc,
        );

        Ok(bit_var)
    }

    fn is_equal_to_zero_bit<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
    ) -> Result<AllocatedBit, SynthesisError> {
        let val = self.get_value().unwrap();
        let inv = self.get_value().unwrap().invert().unwrap_or(F::ZERO);
        let inv_var = AllocatedNum::alloc(cs.namespace(|| "alloc_inv"), || Ok(inv))?;

        let bit = if val.is_zero().into() { true } else { false };
        let bit_var = AllocatedBit::alloc(cs.namespace(|| "alloc_bit"), Some(bit))?;

        cs.enforce(
            || "enforce_(val * inv = 1 - bit)",
            |lc| lc + self.get_variable(),
            |lc| lc + inv_var.get_variable(),
            |lc| lc + CS::one() - bit_var.get_variable(),
        );

        cs.enforce(
            || "enforce_(val * bit = 0)",
            |lc| lc + self.get_variable(),
            |lc| lc + bit_var.get_variable(),
            |lc| lc,
        );

        Ok(bit_var)
    }

    fn sub<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self::Output, SynthesisError> {
        let result = self.get_value().unwrap().sub(&other.get_value().unwrap());
        let result_var = AllocatedNum::alloc(cs.namespace(|| "alloc_result"), || Ok(result))?;

        cs.enforce(
            || "enfore_sub",
            |lc| lc + self.get_variable() - other.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + result_var.get_variable(),
        );

        Ok(result_var)
    }

    fn apply_bool_constraint<CS: ConstraintSystem<F>>(&self, mut cs: CS) {
        cs.enforce(
            || "apply a boolean constraint",
            |lc| lc + self.get_variable(),
            |lc| lc + CS::one() - self.get_variable(),
            |lc| lc,
        );
    }

    fn sum<CS: ConstraintSystem<F>>(
        mut cs: CS,
        vars: &[Self::Output],
    ) -> Result<Self::Output, SynthesisError> {
        let mut sum = vars[0].get_value().unwrap();
        for x in vars.iter().skip(1) {
            sum += x.get_value().unwrap()
        }

        let sum_var = AllocatedNum::alloc(cs.namespace(|| "alloc_sum"), || Ok(sum))?;

        let linear_combination = |init: LinearCombination<F>| -> LinearCombination<F> {
            let mut sum = init.clone();
            for x in vars.iter() {
                sum = sum + x.get_variable()
            }

            sum
        };

        cs.enforce(
            || "sum",
            linear_combination,
            |lc| lc + CS::one(),
            |lc| lc + sum_var.get_variable(),
        );

        Ok(sum_var)
    }

    fn product_sum<CS: ConstraintSystem<F>>(
        mut cs: CS,
        a: &[Self::Output],
        b: &[Self::Output],
    ) -> Result<Self::Output, SynthesisError> {
        let mut tmp = Vec::new();
        for (i, (x, y)) in a.iter().zip(b.iter()).enumerate() {
            let r = x.mul(cs.namespace(|| format!("product_{}", i)), y)?;
            tmp.push(r);
        }

        let sum = Self::sum(cs.namespace(|| "sum of product"), &tmp)?;

        Ok(sum)
    }
}
