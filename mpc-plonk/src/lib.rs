//! Implementation of the PLONK proof system.

//!
//! PLONK is originally described [here](https://eprint.iacr.org/2019/953.pdf).
//!
//! This implementation is based on Dan Boneh's [lecture
//! 17](https://cs251.stanford.edu/lectures/lecture17.pdf) for CS 251 (Spring 20) at Stanford.
//!
//! You should look at those notes for the notation used here.

pub mod data_structures;
pub use data_structures::*;
use std::convert::TryFrom;
use std::{time::{Duration, Instant}};
use ark_ff::BigInteger;
use ark_ff::BigInteger256;
pub mod relations;
use ark_ff::FpParameters;
use ark_ff::FftParameters;
pub use relations::*;
pub mod reveal;
mod util;
use zki_sieve::structs::{relation::Relation, instance::Instance, witness::Witness, gates::Gate};
use log::debug;
use num_bigint::BigUint;
use blake2::Blake2s;
use ark_ff::One;
use ark_ff::PrimeField;
use std::{path::{Path,PathBuf},char};
use ark_ff::{FftField, Field};
use ark_std::char::from_digit;
use crate::structured::PlonkCircuit;
use ark_poly_commit::{LabeledCommitment, LabeledPolynomial, PCRandomness, PolynomialCommitment};
use zki_sieve::cli::*;
use ark_poly::{
    domain::{ EvaluationDomain, MixedRadixEvaluationDomain, Radix2EvaluationDomain },
    univariate::{DenseOrSparsePolynomial, DensePolynomial},
    Polynomial, UVPolynomial,
};

use ark_bls12_377::Fr;
use ark_std::{end_timer, rand::RngCore, start_timer};
use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::iter::once;
use std::marker::PhantomData;
use thiserror::Error;
use crate::flat::CircuitLayout;
use mpc_trait::MpcWire;
pub use util::FiatShamirRng;
use sieve_fields::{Field as SieveField};

fn bigint256_to_biguint(input:&BigInteger256) -> BigUint{
    let bytes_le = input.to_bytes_le();
    BigUint::from_bytes_le(&bytes_le)
}

fn biguint_to_bigint256(input:&BigUint) -> BigInteger256{
    let result_bits_be:Vec<bool> = input.to_radix_be(2).iter().map(|b| if b == &0u8 { false } else { true }).collect();
    BigInteger256::from_bits_be(&result_bits_be[..])
}
#[test]
fn test_biguint_to_bigint(){
    let test =  <SieveField as FftField>::FftParams::GENERATOR;
    let test_biguint = bigint256_to_biguint(&test);
    let test_bigint256 = biguint_to_bigint256(&test_biguint);
    assert_eq!(test,test_bigint256);
}
#[test]
fn test_radix_mixed(){
    let n = 11;
    let gates = Radix2EvaluationDomain::<Fr>::new(n).expect("gate domain");
    let wires = MixedRadixEvaluationDomain::<Fr>::new(3 * n).expect("wire domain");

    assert!(3 * gates.size() == wires.size());    
}

fn sieve_to_plonk<F:FftField + PrimeField>(instance_file:&str,witness_file:&str,relation_file:&str) -> (CircuitLayout::<F>,HashMap::<String,F>,usize) {
    let options = Options{
	tool: "flatten".to_string(),
	paths: vec![PathBuf::from(instance_file),PathBuf::from(witness_file),PathBuf::from(relation_file)],
	field_order: BigUint::from(101 as u32),
incorrect:true,
	gate_set: None,
	modular_reduce: true,
	out: PathBuf::from("output"),
	tmp_wire_start:None,
	resource: "-".to_string()
    };
    let source = stream_messages(&options).ok().unwrap();
    let evaluate = main_evaluate(&source);

    let result = main_ir_flattening_no_out(&options).ok().unwrap();
    let (mut circuit, public) = ir_to_plonk::<F>(result.0,result.1,result.2);
    circuit.pad_to_power_of_2();
    let polys = CircuitLayout::from_circuit(&circuit);
    polys.check(&public);
    return (polys,public,circuit.n_gates());

}
//fill in dummy gates so number of gates is power of 2

fn calc_root_of_unity(){
     /*
    //compute large_subgroup_root_of_unit to put in constant
    

    let gen_biguint =  bigint256_to_biguint(&<SieveField as FftField>::FftParams::GENERATOR);

    let modulus_biguint = bigint256_to_biguint(&<SieveField as FftField>::FftParams::MODULUS);

    let modulus_minus_one_bigint256 = biguint_to_bigint256(&(modulus_biguint - BigUint::from(1u64)));

    let modulus_field = SieveField::from_repr(modulus_minus_one_bigint256).unwrap();
    
    let one = SieveField::from_repr(<SieveField as FftField>::FftParams::GENERATOR).unwrap().pow(modulus_minus_one_bigint256);
    assert_eq!(one,SieveField::one());
    
//    let numerator = gen_biguint^(modulus_biguint - BigUint::from(1u64));
*/    
  /*  
    let two_adicity = <SieveField as FftField>::FftParams::TWO_ADICITY;
    let small_subgroup_base = <SieveField as FftField>::FftParams::SMALL_SUBGROUP_BASE.unwrap();
    let small_subgroup_base_adicity = <SieveField as FftField>::FftParams::SMALL_SUBGROUP_BASE_ADICITY.unwrap();
    let denom = BigUint::from(2u32.pow(two_adicity) * (small_subgroup_base));
    let result = gen_biguint^(modulus_biguint - BigUint::from(1u64)) / denom;
    let result_bits_be:Vec<bool> = result.to_radix_be(2).iter().map(|b| if b == &0u8 { false } else { true }).collect();
    let result_bigint = BigInteger256::from_bits_be(&result_bits_be[..]);
    println!("result {:?}", result_bigint);
     */
}
pub fn ir_to_plonk<F:PrimeField>(instance: Instance, witness: Witness, relation: Relation)->(PlonkCircuit<F>,HashMap::<String,F>){
    let mut instance_queue = instance.common_inputs;
    let mut witness_queue = witness.short_witness;
    let mut circuit = PlonkCircuit::new(true);
    let mut map = HashMap::new();
    let mut public_vars = HashMap::<String,F>::new();
    for gate in relation.gates{
	match gate {
	    Gate::Constant(wireId,v_as_bytes) => {
		let value = F::from_le_bytes_mod_order(&v_as_bytes[..]);
		let new_var = circuit.new_var(|| value);
		map.insert(wireId,new_var); //this should be insert or update
	    },
	    Gate::AssertZero(wireId) => {
		let temp_var = circuit.new_var(|| F::one());
		let new_var = circuit.new_prod_with_output(|| F::zero(), *map.get(&wireId).unwrap(), temp_var);
		//bind to pubilc var with value 0
		let mut var_str = String::from("zero_output");
		var_str.push(char::from_u32(wireId as u32).unwrap());
		circuit.publicize_var(new_var,var_str.clone());
		public_vars.insert(var_str.clone(), F::zero());
	    },
	    Gate::Copy(output,input) => {
		let value = circuit.get_value(*map.get(&input).unwrap());
		let new_var = circuit.new_var(|| value);
		map.insert(output, new_var);
	    },
	    Gate::Add(output,input1,input2) => {
		let sum_var = circuit.new_sum(*map.get(&input1).unwrap(),*map.get(&input2).unwrap());
		map.insert(output,sum_var);
	    },
	    Gate::Mul(output,input1,input2) => {
		let prod_var = circuit.new_prod(*map.get(&input1).unwrap(), *map.get(&input2).unwrap());
		map.insert(output,prod_var);
	    },
	    Gate::AddConstant(output,input,v_as_bytes) => {
		let value = F::from_le_bytes_mod_order(&v_as_bytes[..]);
		let new_var = circuit.new_var(|| value);
		let sum_var = circuit.new_sum(*map.get(&input).unwrap(),new_var);
		map.insert(output,sum_var);
	    },
	    Gate::MulConstant(output,input,v_as_bytes) => {
		let value = F::from_le_bytes_mod_order(&v_as_bytes[..]);		
		let new_var = circuit.new_var(|| value);
		let prod_var = circuit.new_prod(*map.get(&input).unwrap(),new_var);
		map.insert(output,prod_var);		
	    },
	    Gate::And(output, input1, input2) => {
		//mul
		let prod_var = circuit.new_prod(*map.get(&input1).unwrap(), *map.get(&input2).unwrap());
		map.insert(output,prod_var);

	    },
	    Gate::Xor(output,input1, input2) => {
		//mul constant where value = -1, var = input2
		let new_var = circuit.new_var(|| -F::one());
		let prod_var = circuit.new_prod(*map.get(&input2).unwrap(),new_var);
		map.insert(output,prod_var);
		//add prod_var and input1
		let sum_var = circuit.new_sum(*map.get(&input1).unwrap(),*map.get(&input2).unwrap());
		//multiply sum_var by itself
		let prod_var = circuit.new_prod(*map.get(&input1).unwrap(), *map.get(&input2).unwrap());
		map.insert(output,prod_var);
	    },
	    Gate::Not(output,input) => {
		//mul constant where value = -1, var = input
		let new_var = circuit.new_var(|| -F::one());
		let sum_var = circuit.new_prod(*map.get(&input).unwrap(),new_var);
		// AddConstant 1 + sum_var
		let new_var = circuit.new_var(|| F::one());
		let sum_var = circuit.new_sum(sum_var,new_var);
		map.insert(output,sum_var);
	    },
	    Gate::Instance(wireId) => {
		//pop value off instance queue and then Constant
		let v_as_bytes = instance_queue.remove(0);
		let value = F::from_le_bytes_mod_order(&v_as_bytes[..]);				
		let new_var = circuit.new_var(|| value);
		map.insert(wireId,new_var); //this should be insert or update
		let mut var_str = String::from("instance");
		var_str.push(char::from_u32(new_var as u32).unwrap());
		public_vars.insert(var_str.clone(), value);
		circuit.publicize_var(new_var, var_str.clone());
	    },
	    Gate::Witness(wireId) => {
		//pop value off witness queue and then Constant
		let v_as_bytes = witness_queue.remove(0);
		let value = F::from_le_bytes_mod_order(&v_as_bytes[..]);				
		let new_var = circuit.new_var(|| value);
		map.insert(wireId,new_var); //this should be insert or update
	    },
	    Gate::Free(wireId, option) => {
		//what do we have in memory
		//a vector of values -> a vector of labels
		//a map that maps wireId to value
		//if something is freed, then its wireId might be used again
		//

		//to do
	    },
	    Gate::AnonCall(_,_,_,_,_) =>{
		println!("this shouldn't exist in flattened version");
	    },
	    Gate::Call(_,_,_) => {
		println!("this shouldn't exist in flattened version");
	    },
	    Gate::Switch(_,_,_,_) => {
		println!("this shouldn't exist in flattened version");
	    },
	    Gate::For(_,_,_,_,_) => {
		println!("this shouldn't exist in flattened version");
	    }
	}
    }
    (circuit,public_vars)
}
pub fn setup<'r, F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>>(
    srs: &PC::UniversalParams,
    circ: &relations::flat::CircuitLayout<F>,
) -> (
    ProverKey<F, PC::Commitment, PC::CommitterKey>,
    VerifierKey<PC::Commitment, PC::VerifierKey>,
) {
    let (ck, vk) = PC::trim(
        &srs,
        circ.degree_bound(),
        0,
        Some(&[circ.domains.wires.size() - 1]),
    )
    .unwrap();
    let w = LabeledPolynomial::new("w".into(), circ.w.clone(), None, None);
    let (mut cs, rs) = PC::commit(&ck, once(&w), None).unwrap();
    assert_eq!(cs.len(), 1);
    assert_eq!(rs.len(), 1);
    let w_cmt = cs.pop().unwrap();
    let s = LabeledPolynomial::new("s".into(), circ.s.clone(), None, None);
    let (mut cs, rs) = PC::commit(&ck, once(&s), None).unwrap();
    assert_eq!(cs.len(), 1);
    assert_eq!(rs.len(), 1);
    let s_cmt = cs.pop().unwrap();
    (
        ProverKey {
            pc_ck: ck,
            s_cmt: s_cmt.clone(),
            w_cmt: w_cmt.clone(),
            s,
            w,
        },
        VerifierKey {
            pc_vk: vk,
            s_cmt,
            w_cmt,
        },
    )
}

#[allow(dead_code)]
pub struct Prover<'r, F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>> {
    _pc: PhantomData<PC>,
    pk: &'r ProverKey<F, PC::Commitment, PC::CommitterKey>,
    zk_rng: RefCell<&'r mut dyn RngCore>,
    fs_rng: RefCell<FiatShamirRng<Blake2s>>,
}

impl<'r, F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>> Prover<'r, F, PC> {
    pub fn new(
        pk: &'r ProverKey<F, PC::Commitment, PC::CommitterKey>,
        zk_rng: &'r mut dyn RngCore,
    ) -> Self {
        Self {
            _pc: PhantomData::default(),
            pk,
            zk_rng: RefCell::new(zk_rng),
            fs_rng: RefCell::new(FiatShamirRng::from_seed(&0u64)),
        }
    }
}

#[allow(dead_code)]
impl<'r, F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>> Prover<'r, F, PC>
where
    PC::Commitment: mpc_trait::MpcWire,
    PC::Error: 'static,
{
    fn prove_unit_product<D: EvaluationDomain<F>>(
        &self,
        f: &LabeledPolynomial<F, DensePolynomial<F>>,
        f_cmt: &LabeledCommitment<PC::Commitment>,
        f_rand: &PC::Randomness,
        domain: D,
    ) -> ProductProof<PC::Commitment, (F, PC::Proof)> {
        let timer = start_timer!(|| "prove_unit_product");
        let t_evals = {
            let mut t = f.evaluate_over_domain_by_ref(domain);
            F::partial_products_in_place(&mut t.evals);
            t
        };
        // debug_assert!(t_evals.evals[f.coeffs.len() - 1], F::one());
        //        debug_assert_eq!(
        //            t_evals.evals[f.coeffs.len() - 1] * t_evals.evals[0],
        //            t_evals[0]
        //        );
        let t = t_evals.interpolate();
        let (t_cmt, t, t_rand) = self.commit("t", t.clone(), None, None).unwrap();
        let w = domain.element(1);
        // let q = {
        //     let d = &shift(t.clone(), w) - &t.naive_mul(&shift(f.clone(), w));
        //     let (q,r) = d.divide_by_vanishing_poly(domain).unwrap();
        //     assert!(r.is_zero());
        //     q
        // };
        let q_timer = start_timer!(|| "q");
        let q = {
            // get f(wX) over coset
            let mut f_evals = f.coeffs.clone();
            D::distribute_powers(&mut f_evals, w);
            domain.coset_fft_in_place(&mut f_evals);
            // get t(X) over coset
            let mut t_evals = t.coeffs.clone();
            domain.coset_fft_in_place(&mut t_evals);
            // get f(wX)t(X) over coset
            let fwt_evals = domain.mul_polynomials_in_evaluation_domain(&f_evals, &t_evals);
            // get t(wX) over coset
            let mut tw_evals = t.coeffs.clone();
            D::distribute_powers(&mut tw_evals, w);
            domain.coset_fft_in_place(&mut tw_evals);
            // get t(wX) - f(wX)t(X) over coset
            ark_std::cfg_iter_mut!(tw_evals)
                .zip(fwt_evals)
                .for_each(|(a, b)| *a -= b);
            domain.divide_by_vanishing_poly_on_coset_in_place(&mut tw_evals);
            domain.coset_ifft_in_place(&mut tw_evals);
            DensePolynomial::from_coefficients_vec(tw_evals)
        };
        end_timer!(q_timer);
        // assert_eq!(q, qq);
        let (q_cmt, q, q_rand) = self.commit("q", q.clone(), None, None).unwrap();
        let k = domain.size();
        //        debug_assert_eq!(t.evaluate(&domain.element(k - 1)), F::one());
        //        for i in 0..k {
        //            let r = domain.element(i);
        //            debug_assert_eq!(t.evaluate(&(w * r)), t.evaluate(&r) * f.evaluate(&(w * r)));
        //        }
        let r = self.fs_rng.borrow_mut().gen::<F>();
        //        debug_assert_eq!(
        //            t.evaluate(&(w * r)) - t.evaluate(&r) * f.evaluate(&(w * r)),
        //            domain.evaluate_vanishing_polynomial(r) * q.evaluate(&r)
        //        );
        let t_wr_open = self.eval(&t, &t_rand, &t_cmt, w * r).unwrap();
        let t_r_open = self.eval(&t, &t_rand, &t_cmt, r).unwrap();
        let t_wk_open = self
            .eval(&t, &t_rand, &t_cmt, domain.element(k - 1))
            .unwrap();
        let f_wr_open = self.eval(&f, &f_rand, &f_cmt, w * r).unwrap();
        let q_r_open = self.eval(&q, &q_rand, &q_cmt, r).unwrap();
        end_timer!(timer);
        //        debug_assert_eq!(
        //            t_wr_open.0 - t_r_open.0 * f_wr_open.0,
        //            domain.evaluate_vanishing_polynomial(r) * q_r_open.0
        //        );
        //        debug_assert_eq!(t_wk_open.0, F::one());
        ProductProof {
            t_cmt: t_cmt.commitment,
            q_cmt: q_cmt.commitment,
            t_wk_open,
            t_r_open,
            t_wr_open,
            f_wr_open,
            q_r_open,
        }
    }

    /// Prove that p(X) = p(w(X)) on the domain.
    fn prove_wiring<D: EvaluationDomain<F>>(
        &self,
        p: &LabeledPolynomial<F, DensePolynomial<F>>,
        p_cmt: &LabeledCommitment<PC::Commitment>,
        p_rand: &PC::Randomness,
        dom: D,
    ) -> WiringProof<PC::Commitment, (F, PC::Proof)> {
        let timer = start_timer!(|| "prove_wiring");
        let y = self.fs_rng.borrow_mut().gen::<F>();
        let z = self.fs_rng.borrow_mut().gen::<F>();
        let p_evals = p.evaluate_over_domain_by_ref(dom);
        let w_evals = self.pk.w.evaluate_over_domain_by_ref(dom);
        let yx_z_evals =
            DensePolynomial::from_coefficients_vec(vec![z, y]).evaluate_over_domain_by_ref(dom);
        let num_evals = &(&p_evals + &(&w_evals * &y)) + &z;
        let den_evals = &(&p_evals + &yx_z_evals);
        //TODO: batch!
        let l1_evals = &num_evals / &den_evals;
        let l1 = l1_evals.clone().interpolate();
        let (l1_cmt, l1, l1_rand) = self.commit("l1", l1, None, None).unwrap();
        let l1_prod_pf = self.prove_unit_product(&l1, &l1_cmt, &l1_rand, dom);
        let l2_q_coeffs = {
            let mut l1_v = l1.coeffs.clone();
            let mut num_v = num_evals.interpolate().coeffs;
            let mut den_v = den_evals.clone().interpolate().coeffs;
            dom.coset_fft_in_place(&mut l1_v);
            dom.coset_fft_in_place(&mut num_v);
            dom.coset_fft_in_place(&mut den_v);
            let mut l1_den_v = dom.mul_polynomials_in_evaluation_domain(&l1_v, &den_v);
            ark_std::cfg_iter_mut!(l1_den_v)
                .zip(num_v)
                .for_each(|(a, b)| *a -= b);
            dom.divide_by_vanishing_poly_on_coset_in_place(&mut l1_den_v);
            dom.coset_ifft_in_place(&mut l1_den_v);
            l1_den_v
        };
        let l2_q = DensePolynomial::from_coefficients_vec(l2_q_coeffs);
        let (l2_q_cmt, l2_q, l2_q_rand) = self.commit("l2_q", l2_q, None, None).unwrap();
        let x = self.fs_rng.borrow_mut().gen::<F>();
        let l2_q_x_open = self.eval(&l2_q, &l2_q_rand, &l2_q_cmt, x).unwrap();
        let w_x_open = self
            .eval(&self.pk.w, &PC::Randomness::empty(), &self.pk.w_cmt, x)
            .unwrap();
        let l1_x_open = self.eval(&l1, &l1_rand, &l1_cmt, x).unwrap();
        let p_x_open = self.eval(&p, &p_rand, &p_cmt, x).unwrap();
        //        debug_assert_eq!(
        //            (p_x_open.0 + y * x + z) * l1_x_open.0 - (p_x_open.0 + y * w_x_open.0 + z),
        //            l2_q_x_open.0 * dom.evaluate_vanishing_polynomial(x)
        //        );
        end_timer!(timer);
        WiringProof {
            l1_prod_pf,
            l2_q_x_open,
            l1_x_open,
            p_x_open,
            w_x_open,
            l1_cmt: l1_cmt.commitment,
            l2_q_cmt: l2_q_cmt.commitment,
        }
    }

    fn prove_public(
        &self,
        p: &LabeledPolynomial<F, DensePolynomial<F>>,
        p_cmt: &LabeledCommitment<PC::Commitment>,
        p_rand: &PC::Randomness,
        circ: &relations::flat::CircuitLayout<F>,
    ) -> PublicProof<PC::Commitment, (F, PC::Proof)> {
        let timer = start_timer!(|| "prove_public");
        let points: Vec<(F, F)> = circ
            .public_indices
            .iter()
            .map(|(_, i)| {
                let x = circ.domains.wires.element(*i);
                let y = p.evaluate(&x);
                (x, y)
            })
            .collect();
        let v = util::interpolate(&points);
        let z = circ.vanishing_poly_on_inputs();
        let (q, _r) = DenseOrSparsePolynomial::DPolynomial(Cow::Owned(p.polynomial() - &v))
            .divide_with_q_and_r(&DenseOrSparsePolynomial::DPolynomial(Cow::Borrowed(&z)))
            .unwrap();
        let (q_cmt, q, q_rand) = self.commit("pub_q", q, None, None).unwrap();
        let x = self.fs_rng.borrow_mut().gen::<F>();
        let q_open = self.eval(&q, &q_rand, &q_cmt, x).unwrap();
        let p_open = self.eval(&p, &p_rand, &p_cmt, x).unwrap();
        //debug_assert!( p_open.0 - v.evaluate(&x), q_open.0 * z.evaluate(&x));
        end_timer!(timer);
        PublicProof {
            q_open,
            q_cmt: q_cmt.commitment,
            p_open,
        }
    }

    fn prove_gates(
        &self,
        p: &LabeledPolynomial<F, DensePolynomial<F>>,
        p_cmt: &LabeledCommitment<PC::Commitment>,
        p_rand: &PC::Randomness,
        circ: &relations::flat::CircuitLayout<F>,
    ) -> GateProof<PC::Commitment, (F, PC::Proof)> {
        let timer = start_timer!(|| "prove_gates");
        let w = circ.domains.wires.group_gen;
        let pw = util::shift(p.polynomial().clone(), w);
        let pww = util::shift(p.polynomial().clone(), w * w);
        let d = &(&circ.s * &(p.polynomial() + &pw)
            + &(&(&circ.s * &-F::one()) + &F::one()) * &(p.polynomial() * &pw))
            - &pww;
        let (q, _r) = DenseOrSparsePolynomial::DPolynomial(Cow::Owned(d))
            .divide_with_q_and_r(&DenseOrSparsePolynomial::SPolynomial(Cow::Owned(
                circ.domains.gates.vanishing_polynomial(),
            )))
            .unwrap();
        // debug_assert!(r.is_zero());
        let (q_cmt, q, q_rand) = self.commit("gates_q", q, None, None).unwrap();
        let x = self.fs_rng.borrow_mut().gen::<F>();
        let s_open = self
            .eval(&self.pk.s, &PC::Randomness::empty(), &self.pk.s_cmt, x)
            .unwrap();
        let p_open = self.eval(p, p_rand, p_cmt, x).unwrap();
        let q_open = self.eval(&q, &q_rand, &q_cmt, x).unwrap();
        let p_w_open = self.eval(p, p_rand, p_cmt, w * x).unwrap();
        let p_w2_open = self.eval(p, p_rand, p_cmt, w * w * x).unwrap();
        //        debug_assert_eq!(
        //            s_open.0 * (p_open.0 + p_w_open.0) + (F::one() - s_open.0) * p_open.0 * p_w_open.0
        //                - p_w2_open.0,
        //            q_open.0 * circ.domains.gates.evaluate_vanishing_polynomial(x)
        //        );
        end_timer!(timer);
        GateProof {
            q_cmt: q_cmt.commitment,
            s_open,
            p_open,
            q_open,
            p_w_open,
            p_w2_open,
        }
    }

    /// Evaluate polynomial `p` at `x`, producing a proof of the evaluation as well.
    ///
    /// With respect to a commitment `p_c` under randomness `p_r`.
    fn eval(
        &self,
        p: &LabeledPolynomial<F, DensePolynomial<F>>,
        p_r: &PC::Randomness,
        p_c: &LabeledCommitment<PC::Commitment>,
        x: F,
    ) -> Result<(F, PC::Proof), Error<PC::Error>> {
        let timer = start_timer!(|| format!("open: {}", p.label()));
        let pf_p = PC::open(
            &self.pk.pc_ck,
            once(p),
            once(p_c),
            &x,
            F::one(), // acceptable b/c this is just one commitment.
            once(p_r),
            Some(&mut *self.zk_rng.borrow_mut()),
        )?;
        let mut y = p.polynomial().evaluate(&x);
        let p_timer = start_timer!(|| "publicize");
        y.publicize();
        end_timer!(p_timer);
        end_timer!(timer);
        Ok((y, pf_p))
    }

    /// Commit to a polynomial `p`.
    ///
    /// Produces a (commitment, labeled_poly, randomness) triple.
    fn commit(
        &self,
        label: impl ark_std::fmt::Display,
        p: DensePolynomial<F>,
        degree: Option<usize>,
        hiding_bound: Option<usize>,
    ) -> Result<
        (
            LabeledCommitment<PC::Commitment>,
            LabeledPolynomial<F, DensePolynomial<F>>,
            PC::Randomness,
        ),
        Error<PC::Error>,
    > {
        debug!("commit: {}", label);
        let timer = start_timer!(|| format!("commit: {}", label));
        let label_p = LabeledPolynomial::new(format!("{}", label), p, degree, hiding_bound);
        let (mut cs, mut rs) = PC::commit(
            &self.pk.pc_ck,
            once(&label_p),
            Some(&mut *self.zk_rng.borrow_mut()),
        )?;
        assert_eq!(cs.len(), 1);
        assert_eq!(rs.len(), 1);
        let mut c = cs.pop().unwrap();
        c.commitment.publicize();
        self.fs_rng
            .borrow_mut()
            .absorb(&ark_ff::to_bytes![c].expect("failed serialization"));
        end_timer!(timer);
        Ok((c, label_p, rs.pop().unwrap()))
    }

    pub fn prove(
        &self,
        circ: &relations::flat::CircuitLayout<F>,
    ) -> Proof<F, PC::Commitment, PC::Proof> {
        assert!(circ.p.is_some());
        let n_gates = circ.domains.gates.size();
        let n_wires = n_gates * 3;
        let (p_cmt, p, p_rand) = self
            .commit(
                "p".to_owned(),
                circ.p.clone().unwrap(),
                Some(n_wires - 1),
                None,
            )
            .unwrap();
        let public = self.prove_public(&p, &p_cmt, &p_rand, circ);
        let gates = self.prove_gates(&p, &p_cmt, &p_rand, circ);
        let wiring = self.prove_wiring(&p, &p_cmt, &p_rand, circ.domains.wires);
        Proof {
            p_cmt: p_cmt.commitment,
            wiring,
            gates,
            public,
        }
    }
}

pub struct Verifier<'r, F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>> {
    _field: PhantomData<F>,
    _pc: PhantomData<PC>,
    vk: &'r VerifierKey<PC::Commitment, PC::VerifierKey>,
    fs_rng: RefCell<FiatShamirRng<Blake2s>>,
}
#[allow(dead_code)]
impl<'r, F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>> Verifier<'r, F, PC>
where
    PC::Commitment: mpc_trait::MpcWire,
    PC::Error: 'static,
{
    pub fn new(vk: &'r VerifierKey<PC::Commitment, PC::VerifierKey>) -> Self {
        Self {
            _field: PhantomData::default(),
            _pc: PhantomData::default(),
            vk,
            fs_rng: RefCell::new(FiatShamirRng::from_seed(&0u64)),
        }
    }
    fn verify_unit_product<D: EvaluationDomain<F>>(
        &self,
        f_cmt: &LabeledCommitment<PC::Commitment>,
        pf: ProductProof<PC::Commitment, (F, PC::Proof)>,
        domain: D,
    ) {
        let k = domain.size();
        let w = domain.element(1);
        let t_cmt = self.recv_commit("t", pf.t_cmt, None);
        let q_cmt = self.recv_commit("q", pf.q_cmt, None);
        let r = self.fs_rng.borrow_mut().gen::<F>();
        // Check commitments
        let f_wr = self.check(f_cmt, w * r, &pf.f_wr_open);
        let q_r = self.check(&q_cmt, r, &pf.q_r_open);
        let t_r = self.check(&t_cmt, r, &pf.t_r_open);
        let t_wr = self.check(&t_cmt, w * r, &pf.t_wr_open);
        let t_wk = self.check(&t_cmt, domain.element(k - 1), &pf.t_wk_open);
        // Check partial product
        let l = t_wr - t_r * f_wr;
        let r = domain.evaluate_vanishing_polynomial(r) * q_r;
        assert_eq!(l, r, "Partial product failure: \n{}\nnot equal to\n{}", l, r);
        // Check total product is 1
        assert_eq!(t_wk, F::one());
    }
    /// Receive a commitment
    ///
    /// Produces a (commitment, labeled_poly, randomness) triple.
    fn recv_commit(
        &self,
        label: impl ark_std::fmt::Display,
        c: PC::Commitment,
        degree: Option<usize>,
    ) -> LabeledCommitment<PC::Commitment> {
        let label_c = LabeledCommitment::new(format!("{}", label), c, degree);
        self.fs_rng
            .borrow_mut()
            .absorb(&ark_ff::to_bytes![label_c].expect("failed serialization"));
        label_c
    }

    #[track_caller]
    fn check(&self, cmt: &LabeledCommitment<PC::Commitment>, x: F, open: &(F, PC::Proof)) -> F {
        assert!(
            PC::check(
                &self.vk.pc_vk,
                once(cmt),
                &x,
                once(open.0),
                &open.1,
                F::one(), // Okay b/c a single commit
                None,
            )
            .unwrap(),
            "Verification failed: {} at {}",
            cmt.label(),
            x
        );
        open.0
    }

    pub fn verify(
        &self,
        circ: &relations::flat::CircuitLayout<F>,
        pf: Proof<F, PC::Commitment, PC::Proof>,
        public: &HashMap<String, F>,
    ) {
        assert!(circ.p.is_none());
        let n_gates = circ.domains.gates.size();
        let n_wires = n_gates * 3;
        let p = self.recv_commit("p", pf.p_cmt, Some(n_wires - 1));
        self.verify_public(&circ, &p, pf.public, public);
        self.verify_gates(&p, &circ, pf.gates);
        self.verify_wiring(&p, circ.domains.wires, pf.wiring);
    }

    fn verify_public(
        &self,
        circ: &relations::flat::CircuitLayout<F>,
        p_cmt: &LabeledCommitment<PC::Commitment>,
        pf: PublicProof<PC::Commitment, (F, PC::Proof)>,
        public: &HashMap<String, F>,
    ) {
        let q_cmt = self.recv_commit("pub_q", pf.q_cmt, None);
        let x = self.fs_rng.borrow_mut().gen::<F>();
        let p_val = self.check(p_cmt, x, &pf.p_open);
        let q_val = self.check(&q_cmt, x, &pf.q_open);
        let z = circ.vanishing_poly_on_inputs();
        let v = circ.inputs_poly(public);
        assert_eq!(p_val - v.evaluate(&x), q_val * z.evaluate(&x));
    }

    fn verify_gates(
        &self,
        p_cmt: &LabeledCommitment<PC::Commitment>,
        circ: &relations::flat::CircuitLayout<F>,
        pf: GateProof<PC::Commitment, (F, PC::Proof)>,
    ) {
        let q_cmt = self.recv_commit("gates_q", pf.q_cmt, None);
        let x = self.fs_rng.borrow_mut().gen::<F>();
        let w = circ.domains.wires.group_gen;
        let s = self.check(&self.vk.s_cmt, x, &pf.s_open);
        let q = self.check(&q_cmt, x, &pf.q_open);
        let p = self.check(p_cmt, x, &pf.p_open);
        let pw = self.check(p_cmt, x * w, &pf.p_w_open);
        let pww = self.check(p_cmt, x * w * w, &pf.p_w2_open);
        assert_eq!(
            s * (p + pw) + (F::one() - s) * p * pw - pww,
            q * circ.domains.gates.evaluate_vanishing_polynomial(x)
        );
    }
    fn verify_wiring<D: EvaluationDomain<F>>(
        &self,
        p_cmt: &LabeledCommitment<PC::Commitment>,
        dom: D,
        pf: WiringProof<PC::Commitment, (F, PC::Proof)>,
    ) {
        let y = self.fs_rng.borrow_mut().gen::<F>();
        let z = self.fs_rng.borrow_mut().gen::<F>();
        let l1 = self.recv_commit("l1", pf.l1_cmt, None);
        self.verify_unit_product(&l1, pf.l1_prod_pf, dom);
        let l2_q = self.recv_commit("l2_q", pf.l2_q_cmt, None);
        let x = self.fs_rng.borrow_mut().gen::<F>();

        let l2_q_x = self.check(&l2_q, x, &pf.l2_q_x_open);
        let w_x = self.check(&self.vk.w_cmt, x, &pf.w_x_open);
        let l1_x = self.check(&l1, x, &pf.l1_x_open);
        let p_x = self.check(&p_cmt, x, &pf.p_x_open);
        assert_eq!(
            (p_x + y * x + z) * l1_x - (p_x + y * w_x + z),
            l2_q_x * dom.evaluate_vanishing_polynomial(x)
        );
    }
}

#[derive(Error, Debug)]
pub enum Error<PCE: 'static + std::error::Error> {
    #[error("Sub error: {0}")]
    Sub(#[from] PCE),
    #[error("The zero-test failed b/c PC.check failed")]
    ZeroTestPcCheckFailure,
    #[error("Division by vanishing poly on domain failed")]
    DomainDivisionFailed,
    #[error("Eq check for domain division failed")]
    DomainCheckFailed,
}

pub type Result<T, PCE> = std::result::Result<T, PCE>;

pub struct Plonk<F: Field, PC: PolynomialCommitment<F, DensePolynomial<F>>>(PhantomData<(F, PC)>);

impl<F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>> Plonk<F, PC>
where
    PC::Commitment: mpc_trait::MpcWire,
    PC::Error: 'static,
{
    pub fn universal_setup<R: RngCore>(n_gates: usize, setup_rng: &mut R) -> PC::UniversalParams {
        PC::setup(n_gates * 6 - 1, Some(1), setup_rng).unwrap()
    }
    pub fn circuit_setup(
        srs: &PC::UniversalParams,
        circ: &relations::flat::CircuitLayout<F>,
    ) -> (
        ProverKey<F, PC::Commitment, PC::CommitterKey>,
        VerifierKey<PC::Commitment, PC::VerifierKey>,
    ) {
        setup::<F, PC>(srs, circ)
    }
    pub fn prove(
        pk: &ProverKey<F, PC::Commitment, PC::CommitterKey>,
        circ: &relations::flat::CircuitLayout<F>,
        zk_rng: &mut dyn RngCore,
    ) -> Proof<F, PC::Commitment, PC::Proof> {
        let prv = Prover::<F, PC>::new(pk, zk_rng);
        prv.prove(circ)
    }
    pub fn verify(
        vk: &VerifierKey<PC::Commitment, PC::VerifierKey>,
        circ: &relations::flat::CircuitLayout<F>,
        pf: Proof<F, PC::Commitment, PC::Proof>,
        public: &HashMap<String, F>,
    ) {
        let ver = Verifier::<F, PC>::new(vk);
        ver.verify(circ, pf, public)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use vlpa19::vlpa19_marlin::Vlpa19_Marlin;
    type E = ark_bls12_377::Bls12_377;
    type F = ark_bls12_377::Fr;
    type P = DensePolynomial<F>;
    type PC = Vlpa19_Marlin<F>;
    type Pl = Plonk<F, PC>;

    #[test]
    fn plonk_test() {
        use relations::{flat::*, structured::*};
        use std::collections::HashMap;

	let correct_witness   = "../rand_100/arand_witness.sieve";
	let incorrect_witness = "./sum_check1/asum_check1_witness.sieve";
	let (circ,public,n_gates) = sieve_to_plonk::<Fr>("../rand_100/rand_instance.sieve",correct_witness,"../rand_100/rand_relation_flat.sieve");
	println!("num gates {:?}", n_gates);
        let setup_rng = &mut ark_std::test_rng();
        let zk_rng = &mut ark_std::test_rng();

        let v_circ = {
            let mut t = circ.clone();
            t.p = None;
            t
        };

        let srs = Pl::universal_setup( n_gates , setup_rng);
        let (pk, vk) = Pl::circuit_setup(&srs, &v_circ);
	let now = Instant::now();
        let pf = Pl::prove(&pk, &circ, zk_rng);
	println!("proof time {:?}", now.elapsed().as_millis());
        Pl::verify(&vk, &v_circ, pf, &public);
    }
}
