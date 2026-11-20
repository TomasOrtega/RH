import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumEqTorusSumStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveEqPolynomialVonMangoldtConvolutionOneStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassMobiusInverseMonicEqStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSumStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusCharacterOrthogonalityStatement

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Establish `h` using `hs 1 1 monic_one monic_one`. Rewrite `h` using `[mul_one]`. Rewrite using `[pow_zero, Nat.cast_zero, zero_mul]`.

Take the linear combination `-h`. Consider the case `succ m ih`. Rewrite using `[pow_succ, hs _ _ (hf.pow m) hf, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsAdditive.map_pow_monic {F : Type} [Field F] {s : F[X] → ℂ} (hs : IsAdditive s) {f : F[X]}
    (hf : f.Monic) (m : ℕ) : s (f ^ m) = m * s f := by
  induction m with
  | zero =>
    have h := hs 1 1 monic_one monic_one
    rw [mul_one] at h
    rw [pow_zero, Nat.cast_zero, zero_mul]
    linear_combination -h
  | succ m ih =>
    rw [pow_succ, hs _ _ (hf.pow m) hf, ih]
    push_cast
    ring

/- English proof (translation)
Use `set n := Module.finrank F V with hn_def`. Use `set q := Nat.card F with hq_def`. Establish `hq : 1 < q` using `Finite.one_lt_card`. Establish `hN : 0 < q ^ n - 1`. Establish `: 1 < q ^ n` using `Nat.one_lt_pow hn.ne' hq`.

Use linear arithmetic over natural numbers and integers. Take `⟨hadd, -⟩` from `GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k`. Establish `hclass : IsClassFn (psi (rootSum θ k) V)` using `fun e g => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F _ V V e g`. Establish `hprim` using `GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hadd`. Rewrite using `[GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ _ hclass hprim hn l]`.

Establish `hS : {α : AlgebraicClosure F | α ^ (q ^ n - 1) = 1} = ↑((nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset)`. Use extensionality with `α`. Simplify using `[Polynomial.mem_nthRoots hN]`. Rewrite using `[hS, finsum_mem_coe_finset]`. Establish `key : ∀ α ∈ (nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset, ((n / (minpoly F α).natDegree : ℕ) : ℂ) * mass (psi (rootSum θ k) V) (minpoly F α ^ (n / (minpoly F α).natDegree)) * star (θ α ^ l) = glCard F n / ((q : ℂ) ^ n - 1) * ∑ i ∈ Finset.range n, θ α ^ (k * q ^ i) * s …`.

Introduce `α hα`. Establish `hα' : α ∈ {α : AlgebraicClosure F | α ^ (q ^ n - 1) = 1}`. Rewrite using `[hS]`. Conclude with `hα`. Take `⟨hdvd, -, hroot⟩` from `GlobalTheory.T.frobeniusTorus_minpoly_degree_rootPowerSum F θ n hn α hα'`.

Establish `hint : IsIntegral F α` using `Algebra.IsIntegral.isIntegral α`. Establish `hmon : (minpoly F α).Monic` using `minpoly.monic hint`. Establish `hirr : Irreducible (minpoly F α)` using `minpoly.irreducible hint`. Establish `hd : 0 < (minpoly F α).natDegree` using `minpoly.natDegree_pos hint`. Establish `hm : 0 < n / (minpoly F α).natDegree` using `Nat.div_pos (Nat.le_of_dvd hn hdvd) hd`.

Establish `hdeg : (minpoly F α ^ (n / (minpoly F α).natDegree)).natDegree = n`. Rewrite using `[hmon.natDegree_pow]`. Conclude with `Nat.div_mul_cancel hdvd`. Rewrite using `[GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hadd _ (hmon.pow _) hdeg, hdeg, (GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one F _ hadd).2.1 _ _ hmon hirr hm]`. Establish `h1 : ((n / (minpoly F α).natDegree : ℕ) : ℂ) * rootSum θ k (minpoly F α) = ∑ i ∈ Finset.range n, θ α ^ (k * q ^ i)`.

Rewrite using `[← IsAdditive.map_pow_monic hadd hmon, hroot]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, ← pow_mul, Nat.mul_comm]`. Rewrite using `[← Finset.sum_mul, ← h1]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_comm]`. Establish `h2 : ∀ i, ∑ α ∈ (nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset, θ α ^ (k * q ^ i) * star (θ α ^ l) = if k * q ^ i ≡ l [MOD q ^ n - 1] then ((q ^ n - 1 : ℕ) : ℂ) else 0`. Introduce `i`. Rewrite using `[← finsum_mem_coe_finset, ← hS]`. Conclude with `(GlobalTheory.T.frobeniusTorus_character_orthogonality F θ hθ n hn).2 _ _`.

Rewrite using `[Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]`. Establish `hc : ((q ^ n - 1 : ℕ) : ℂ) = (q : ℂ) ^ n - 1`. Rewrite using `[Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]`. Establish `hne : (q : ℂ) ^ n - 1 ≠ 0`. Rewrite using `[← hc]`.

Conclude with `hN.ne'` after adjusting the coercions. Rewrite using `[hc]`. Clear the denominators using the available nonvanishing facts.
-/
theorem ipGL_psi_rootSum (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (hn : 0 < Module.finrank F V)
    (k l : ℕ) :
    ipGL (psi (rootSum θ k) V) (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) =
      glCard F (Module.finrank F V) * (((Finset.range (Module.finrank F V)).filter
        (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)])).card : ℂ) := by
  classical
  set n := Module.finrank F V with hn_def
  set q := Nat.card F with hq_def
  have hq : 1 < q := Finite.one_lt_card
  have hN : 0 < q ^ n - 1 := by
    have : 1 < q ^ n := Nat.one_lt_pow hn.ne' hq
    omega
  obtain ⟨hadd, -⟩ := GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k
  have hclass : IsClassFn (psi (rootSum θ k) V) := fun e g => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F _ V V e g
  have hprim := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hadd
  rw [GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ _ hclass hprim hn l]

  have hS : {α : AlgebraicClosure F | α ^ (q ^ n - 1) = 1} =
      ↑((nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset) := by
    ext α
    simp [Polynomial.mem_nthRoots hN]
  rw [hS, finsum_mem_coe_finset]

  have key : ∀ α ∈ (nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset,
      ((n / (minpoly F α).natDegree : ℕ) : ℂ) *
          mass (psi (rootSum θ k) V) (minpoly F α ^ (n / (minpoly F α).natDegree)) * star (θ α ^ l) =
        glCard F n / ((q : ℂ) ^ n - 1) * ∑ i ∈ Finset.range n, θ α ^ (k * q ^ i) * star (θ α ^ l) := by
    intro α hα
    have hα' : α ∈ {α : AlgebraicClosure F | α ^ (q ^ n - 1) = 1} := by
      rw [hS]; exact hα
    obtain ⟨hdvd, -, hroot⟩ := GlobalTheory.T.frobeniusTorus_minpoly_degree_rootPowerSum F θ n hn α hα'
    have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
    have hmon : (minpoly F α).Monic := minpoly.monic hint
    have hirr : Irreducible (minpoly F α) := minpoly.irreducible hint
    have hd : 0 < (minpoly F α).natDegree := minpoly.natDegree_pos hint
    have hm : 0 < n / (minpoly F α).natDegree := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd
    have hdeg : (minpoly F α ^ (n / (minpoly F α).natDegree)).natDegree = n := by
      rw [hmon.natDegree_pow]
      exact Nat.div_mul_cancel hdvd
    rw [GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hadd _ (hmon.pow _) hdeg, hdeg,
      (GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one F _ hadd).2.1 _ _ hmon hirr hm]
    have h1 : ((n / (minpoly F α).natDegree : ℕ) : ℂ) * rootSum θ k (minpoly F α) =
        ∑ i ∈ Finset.range n, θ α ^ (k * q ^ i) := by
      rw [← IsAdditive.map_pow_monic hadd hmon, hroot]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_pow, ← pow_mul, Nat.mul_comm]
    rw [← Finset.sum_mul, ← h1]
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_comm]

  have h2 : ∀ i, ∑ α ∈ (nthRoots (q ^ n - 1) (1 : AlgebraicClosure F)).toFinset,
      θ α ^ (k * q ^ i) * star (θ α ^ l) =
        if k * q ^ i ≡ l [MOD q ^ n - 1] then ((q ^ n - 1 : ℕ) : ℂ) else 0 := by
    intro i
    rw [← finsum_mem_coe_finset, ← hS]
    exact (GlobalTheory.T.frobeniusTorus_character_orthogonality F θ hθ n hn).2 _ _
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  have hc : ((q ^ n - 1 : ℕ) : ℂ) = (q : ℂ) ^ n - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hne : (q : ℂ) ^ n - 1 ≠ 0 := by
    rw [← hc]
    exact_mod_cast hN.ne'
  rw [hc]
  field_simp

end GlobalTheory.CuspGL
