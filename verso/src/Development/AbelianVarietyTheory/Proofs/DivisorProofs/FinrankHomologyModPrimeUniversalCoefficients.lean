import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardQuotPrimeSmulEqCardKerMulPowFinrankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardHomologyOfShortExactMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardZmodTensorEqCardQuotPrimeMultiplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardHomologyRestrictScalarsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMulPrimeZmodTensorComplexStatement
open CategoryTheory Limits

namespace GlobalTheory

/- English proof (translation)
Introduce `C p _ hinj hfin n`. Take `⟨π, hz, hS⟩` from `GlobalTheory.T.shortExact_mul_prime_zmod_tensor_complex C p hinj`. Establish `e` using `GlobalTheory.T.natCard_homology_of_shortExact_mul' p C _ π hz hS n`. Rewrite `e` using `[GlobalTheory.T.natCard_homology_restrictScalars_alt]`. Use `haveI := hfin n`.

Use `haveI := hfin (n + 1)`. Establish `a1` using `GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank (C.homology n) p`. Establish `a2` using `GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank (C.homology (n + 1)) p`. Rewrite `a1`, `a2`, `e` using `[← GlobalTheory.T.card_zmod_tensor_eq_card_quot_prime_multiples]`. Establish `hp : 1 < p` using `(Fact.out : p.Prime).one_lt`.

Establish `hcp : Nat.card (ZMod p) = p` using `by simp`. Establish `c1` using `Module.natCard_eq_pow_finrank (K := ZMod p) (V := TensorProduct ℤ (ZMod p) (C.homology n))`. Establish `c2` using `Module.natCard_eq_pow_finrank (K := ZMod p) (V := TensorProduct ℤ (ZMod p) (C.homology (n + 1)))`. Rewrite `c1`, `c2` using `[hcp]`. Use `set D := (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n`.

Establish `hk : Nat.card (LinearMap.ker ((p : ℤ) • LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1))) ≠ 0`. Introduce `h0; rw [h0, zero_mul, c2] at a2; exact absurd a2 (pow_ne_zero _ (by omega))`. Establish `hD : Nat.card D ≠ 0`. Rewrite using `[e, c1]; exact mul_ne_zero (pow_ne_zero _ (by omega)) hk`. Use `haveI : Finite D := Nat.finite_of_card_ne_zero hD`.

Use `haveI : Module.Finite (ZMod p) D := Module.Finite.of_finite`. Establish `c0` using `Module.natCard_eq_pow_finrank (K := ZMod p) (V := D)`. Rewrite `c0` using `[hcp]`. Establish `key : p ^ (Module.finrank (ZMod p) D + Module.finrank ℤ (C.homology (n + 1))) = p ^ (Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1))))`. Rewrite using `[pow_add, pow_add, ← c0, e, ← c1, ← c2, a2]`.

Expand and normalize the polynomial expressions, which then agree. Use `Nat.pow_right_injective hp key` as an intermediate fact. Use `push_cast`. Use linear arithmetic over natural numbers and integers.
-/
theorem uct_mod_p : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) → (∀ n, Module.Finite ℤ (C.homology n)) → ∀ n : ℕ, (Module.finrank (ZMod p) ((((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1))) - Module.finrank ℤ (C.homology (n + 1)) := by
  intro C p _ hinj hfin n
  obtain ⟨π, hz, hS⟩ := GlobalTheory.T.shortExact_mul_prime_zmod_tensor_complex C p hinj
  have e := GlobalTheory.T.natCard_homology_of_shortExact_mul' p C _ π hz hS n
  rw [GlobalTheory.T.natCard_homology_restrictScalars_alt] at e
  haveI := hfin n
  haveI := hfin (n + 1)
  have a1 := GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank (C.homology n) p
  have a2 := GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank (C.homology (n + 1)) p
  rw [← GlobalTheory.T.card_zmod_tensor_eq_card_quot_prime_multiples] at a1 a2 e
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hcp : Nat.card (ZMod p) = p := by simp
  have c1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := TensorProduct ℤ (ZMod p) (C.homology n))
  have c2 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := TensorProduct ℤ (ZMod p) (C.homology (n + 1)))
  rw [hcp] at c1 c2
  set D := (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n
  have hk : Nat.card (LinearMap.ker ((p : ℤ) • LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1))) ≠ 0 := by
    intro h0; rw [h0, zero_mul, c2] at a2; exact absurd a2 (pow_ne_zero _ (by omega))
  have hD : Nat.card D ≠ 0 := by
    rw [e, c1]; exact mul_ne_zero (pow_ne_zero _ (by omega)) hk
  haveI : Finite D := Nat.finite_of_card_ne_zero hD
  haveI : Module.Finite (ZMod p) D := Module.Finite.of_finite
  have c0 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := D)
  rw [hcp] at c0
  have key : p ^ (Module.finrank (ZMod p) D + Module.finrank ℤ (C.homology (n + 1))) = p ^ (Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1)))) := by
    rw [pow_add, pow_add, ← c0, e, ← c1, ← c2, a2]; ring
  have := Nat.pow_right_injective hp key
  push_cast; omega

end GlobalTheory
