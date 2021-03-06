pub use sapling_crypto::bellman::pairing::bn256::Bn256;
pub use sapling_crypto::bellman::pairing::ff::PrimeField;
pub use sapling_crypto::bellman::Circuit;
pub use sapling_crypto::circuit::test::TestConstraintSystem;
macro_rules! circuit_tests {
    ($($name:ident: $value:expr,)*) => {
        $(
            #[test]
            fn $name() {
                let (circuit, is_sat) = $value;
                let mut cs = TestConstraintSystem::<Bn256>::new();

                circuit.synthesize(&mut cs).expect("synthesis failed");
                println!(concat!("Constraints in {}: {}"), stringify!($name), cs.num_constraints());
                if is_sat && !cs.is_satisfied() {
                    println!("UNSAT: {:#?}", cs.which_is_unsatisfied())
                }
                let unconstrained = cs.find_unconstrained();
                if unconstrained.len() > 0 {
                    println!(concat!("Unconstrained in {}: {}"), stringify!($name), cs.find_unconstrained());
                }

                assert_eq!(cs.is_satisfied(), is_sat);
            }
        )*
    }
}
