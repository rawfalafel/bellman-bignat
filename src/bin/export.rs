extern crate bellman_bignat;
extern crate exitcode;
extern crate memmap;
extern crate num_bigint;
extern crate num_traits;
extern crate rand;
extern crate serde;
extern crate serde_json;
extern crate sapling_crypto;

use bellman_bignat::group::RsaQuotientGroup;
use bellman_bignat::hash::hashes::Poseidon;
use bellman_bignat::mp::bignat::nat_to_limbs;
use bellman_bignat::set::GenSet;
use bellman_bignat::set::int_set::NaiveExpSet;
use bellman_bignat::set::rsa::{SetBench, SetBenchInputs, SetBenchParams};
use num_bigint::BigUint;
use num_traits::Num;
use rand::thread_rng;
use serde::{Deserialize, Serialize};
use sapling_crypto::bellman::{SynthesisError};
use sapling_crypto::bellman::pairing::{CurveAffine,Engine,ff::PrimeField};
use sapling_crypto::bellman::pairing::bn256::Bn256;
use sapling_crypto::bellman::pairing::ff::ScalarEngine;
use sapling_crypto::bellman::groth16::{create_random_proof, generate_random_parameters, Parameters, Proof};

use std::fs::OpenOptions;
use std::io::Write;
use std::ops::DerefMut;
use std::str::FromStr;

#[derive(Serialize, Deserialize)]
struct ProvingKeyJson {
    #[serde(rename = "A")]
    pub a: Vec<Vec<String>>,
    #[serde(rename = "B1")]
    pub b1: Vec<Vec<String>>,
    #[serde(rename = "B2")]
    pub b2: Vec<Vec<Vec<String>>>,
    #[serde(rename = "C")]
    pub c: Vec<Option<Vec<String>>>,
    pub vk_alfa_1: Vec<String>,
    pub vk_beta_1: Vec<String>,
    pub vk_delta_1: Vec<String>,
    pub vk_beta_2: Vec<Vec<String>>,
    pub vk_delta_2: Vec<Vec<String>>,
    #[serde(rename = "hExps")]
    pub h: Vec<Vec<String>>,
}

#[derive(Serialize, Deserialize)]
struct VerifyingKeyJson {
    #[serde(rename = "IC")]
    pub ic: Vec<Vec<String>>,
    pub vk_alfa_1: Vec<String>,
    pub vk_beta_2: Vec<Vec<String>>,
    pub vk_gamma_2: Vec<Vec<String>>,
    pub vk_delta_2: Vec<Vec<String>>,
}

// From https://en.wikipedia.org/wiki/RSA_numbers#RSA-2048
const RSA_2048: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";
const RSA_SIZE: usize = 2048;
const ELEMENT_SIZE: usize = 5;

fn generate_bench_params(group: &RsaQuotientGroup) -> SetBenchParams<Poseidon<Bn256>> {
    let n_swaps = 5;

    SetBenchParams {
        group: group.clone(),
        limb_width: 32,
        n_bits_elem: RSA_SIZE,
        n_bits_challenge: 128,
        n_bits_base: RSA_SIZE,
        item_size: ELEMENT_SIZE,
        n_inserts: n_swaps,
        n_removes: n_swaps,
        hasher: Poseidon::default(),
        verbose: true,
    }
}

fn generate_params(group: &RsaQuotientGroup) -> Parameters<Bn256> {
    let rng = &mut thread_rng();
    
    let c = SetBench::<Poseidon<Bn256>, NaiveExpSet<RsaQuotientGroup>> {
        inputs: None,
        params: generate_bench_params(group),
    };

    let p = generate_random_parameters(c, rng);
    p.unwrap()
}

fn generate_keys(params: &Parameters<Bn256>, vk_filename: &String, pk_filename: &String) -> Result<&'static str, &'static str> {
    let mut proving_key = ProvingKeyJson {
        a: vec![],
        b1: vec![],
        b2: vec![],
        c: vec![],
        vk_alfa_1: vec![],
        vk_beta_1: vec![],
        vk_delta_1: vec![],
        vk_beta_2: vec![],
        vk_delta_2: vec![],
        h: vec![],
    };
    
    let repr_to_big = |r| {
        BigUint::from_str_radix(&format!("{}", r)[2..], 16).unwrap().to_str_radix(10)
    };
    
    let p1_to_vec = |p : &<Bn256 as Engine>::G1Affine| {
        let mut v = vec![];
        //println!("test: {}", p.get_x().into_repr());
        let x = repr_to_big(p.get_x().into_repr());
        v.push(x);
        let y = repr_to_big(p.get_y().into_repr());
        v.push(y);
        if p.is_zero() {
            v.push("0".to_string());
        } else {
            v.push("1".to_string());
        }
        v
    };

    let p2_to_vec = |p : &<Bn256 as Engine>::G2Affine| {
        let mut v = vec![];
        let x = p.get_x();
        let mut x_v = vec![];
        x_v.push(repr_to_big(x.c0.into_repr()));
        x_v.push(repr_to_big(x.c1.into_repr()));
        v.push(x_v);

        let y = p.get_y();
        let mut y_v = vec![];
        y_v.push(repr_to_big(y.c0.into_repr()));
        y_v.push(repr_to_big(y.c1.into_repr()));
        v.push(y_v);

        if p.is_zero() {
            v.push(["0".to_string(), "0".to_string()].to_vec());
        } else {
            v.push(["1".to_string(), "0".to_string()].to_vec());
        }

        v
    };

    let a = params.a.clone();
    for e in a.iter() {
        proving_key.a.push(p1_to_vec(e));
    }
    let b1 = params.b_g1.clone();
    for e in b1.iter() {
        proving_key.b1.push(p1_to_vec(e));
    }
    let b2 = params.b_g2.clone();
    for e in b2.iter() {
        proving_key.b2.push(p2_to_vec(e));
    }
    let c = params.l.clone();
    for _ in 0..params.vk.ic.len() {
        proving_key.c.push(None);
    }
    for e in c.iter() {
        proving_key.c.push(Some(p1_to_vec(e)));
    }

    let vk_alfa_1 = params.vk.alpha_g1.clone();
    proving_key.vk_alfa_1 = p1_to_vec(&vk_alfa_1);

    let vk_beta_1 = params.vk.beta_g1.clone();
    proving_key.vk_beta_1 = p1_to_vec(&vk_beta_1);

    let vk_delta_1 = params.vk.delta_g1.clone();
    proving_key.vk_delta_1 = p1_to_vec(&vk_delta_1);

    let vk_beta_2 = params.vk.beta_g2.clone();
    proving_key.vk_beta_2 = p2_to_vec(&vk_beta_2);

    let vk_delta_2 = params.vk.delta_g2.clone();
    proving_key.vk_delta_2 = p2_to_vec(&vk_delta_2);

    let h = params.h.clone();
    for e in h.iter() {
        proving_key.h.push(p1_to_vec(e));
    }

    let mut verification_key = VerifyingKeyJson {
        ic: vec![],
        vk_alfa_1: vec![],
        vk_beta_2: vec![],
        vk_gamma_2: vec![],
        vk_delta_2: vec![],
    };

    let ic = params.vk.ic.clone();
    for e in ic.iter() {
        verification_key.ic.push(p1_to_vec(e));
    }

    verification_key.vk_alfa_1 = p1_to_vec(&vk_alfa_1);
    verification_key.vk_beta_2 = p2_to_vec(&vk_beta_2);
    let vk_gamma_2 = params.vk.gamma_g2.clone();
    verification_key.vk_gamma_2 = p2_to_vec(&vk_gamma_2);
    verification_key.vk_delta_2 = p2_to_vec(&vk_delta_2);

    let pk_file = OpenOptions::new().read(true).write(true).create_new(true).open(pk_filename).unwrap();
    let pk_json = serde_json::to_string(&proving_key).unwrap();
    pk_file.set_len(pk_json.len() as u64).expect("unable to write pk file");
    let mut mmap = unsafe { memmap::Mmap::map(&pk_file) }.unwrap().make_mut().unwrap();
    mmap.deref_mut().write_all(pk_json.as_bytes()).unwrap();

    let vk_file = OpenOptions::new().read(true).write(true).create_new(true).open(vk_filename).unwrap();
    let vk_json = serde_json::to_string(&verification_key).unwrap();
    vk_file.set_len(vk_json.len() as u64).expect("unable to write vk file");
    let mut mmap = unsafe { memmap::Mmap::map(&vk_file) }.unwrap().make_mut().unwrap();
    mmap.deref_mut().write_all(vk_json.as_bytes()).unwrap();

    println!("Created {} and {}.", pk_filename, vk_filename);

    Ok("complete")
}

fn construct_circuit(group: &RsaQuotientGroup) -> SetBench<Poseidon<Bn256>, NaiveExpSet<RsaQuotientGroup>> {
    let n_swaps = 1;

    // Create a groth16 proof with our parameters.
    SetBench {
        inputs: Some(SetBenchInputs::from_counts(
            0,
            n_swaps,
            n_swaps,
            ELEMENT_SIZE,
            Poseidon::default(),
            RSA_SIZE,
            32,
            RsaQuotientGroup {
                g: BigUint::from(2usize),
                m: BigUint::from_str(RSA_2048).unwrap(),
            },
        )),
        params: generate_bench_params(group),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        println!("Usage: \n<out_vk.json> <out_pk.json>");
        std::process::exit(exitcode::USAGE);
    }

    let vk_filename = &args[1];
    let pk_filename = &args[2];

    let group = RsaQuotientGroup {
        g: BigUint::from(2usize),
        m: BigUint::from_str(RSA_2048).unwrap(),
    };

    let params = generate_params(&group);

    generate_keys(&params, vk_filename, pk_filename).unwrap();

    let circuit = construct_circuit(&group);

    let rng = &mut thread_rng();
    let proof = create_random_proof(circuit, &params, rng).unwrap();

    // Generate witness
    let circuit = construct_circuit(&group);
    let ins = circuit.inputs.as_ref().unwrap();
    let mut initial_set = ins.initial_state.clone();
    let mut final_set = {
        let mut t = initial_set.clone();
        t.swap_all(ins.to_remove.clone(), ins.to_insert.clone());
        t
    };

    let mut inputs: Vec<<Bn256 as ScalarEngine>::Fr> = nat_to_limbs(&group.g, 32, 64).unwrap();
    inputs.extend(nat_to_limbs::<<Bn256 as ScalarEngine>::Fr>(&group.m, 32, 64).unwrap());
    inputs.extend(
        nat_to_limbs::<<Bn256 as ScalarEngine>::Fr>(&initial_set.digest(), 32, 64).unwrap()
    );
    inputs.extend(
        nat_to_limbs::<<Bn256 as ScalarEngine>::Fr>(&final_set.digest(), 32, 64).unwrap()
    );

    // Export proof

    // Export witness

}