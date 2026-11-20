import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TildeCharacterOnUnitary

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.SplitWeight

/- English proof (translation)
Set `σ : I ⊕ I → L →+* ℂ` to `Sum.elim φ fun i => (starRingEnd ℂ).comp (φ i)`. Establish `hσ : Function.Injective σ`. Introduce and unpack `(i | i) (j | j) hij`. Conclude with `congrArg _ (h1 hij)`. Conclude with `absurd hij (h2 i j)`.

Conclude with `absurd hij.symm (h2 j i)`. Use `congrArg _ (h1 (RingHom.ext fun x => ?_))` and prove the remaining obligations. Use `congrArg (fun f : L →+* ℂ => starRingEnd ℂ (f x)) hij` as an intermediate fact. Simplify `this` using `[σ]`. Use `GlobalTheory.HalfIntChars.emb_mul_indep σ hσ (Sum.elim c (-c)) (fun k hk => by` as an intermediate fact.

Establish `hne : ∀ i, φ i k ≠ 0` using `fun i => by simpa using hk`. Establish `e3` using `congrArg (· ^ 2) (h k hk)`. Simplify using `only [← Finset.prod_pow, one_pow] at e3`. Rewrite using `[Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← e3]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← zpow_natCast, ← zpow_mul, mul_comm (c i), zpow_mul, zpow_natCast, GlobalTheory.HalfIntChars.unit_sq _ (hne i), div_zpow]`. Simplify using `only [σ, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, RingHom.comp_apply]`. Rewrite using `[div_eq_mul_inv, ← zpow_neg])`. Use function extensionality and compare the values at `i`. Use `congrFun this (Sum.inl i)` as an intermediate fact.

Simplify using `using this`.
-/
theorem exps_eq_zero {L I : Type} [Field L] [NumberField L] [Fintype I] (φ : I → L →+* ℂ)
    (h1 : Function.Injective φ) (h2 : ∀ i j, φ i ≠ (starRingEnd ℂ).comp (φ j)) (c : I → ℤ)
    (h : ∀ k : L, k ≠ 0 → ∏ i, (φ i k / ((‖φ i k‖ : ℝ) : ℂ)) ^ c i = 1) : c = 0 := by
  let σ : I ⊕ I → L →+* ℂ := Sum.elim φ fun i => (starRingEnd ℂ).comp (φ i)
  have hσ : Function.Injective σ := by
    rintro (i | i) (j | j) hij
    · exact congrArg _ (h1 hij)
    · exact absurd hij (h2 i j)
    · exact absurd hij.symm (h2 j i)
    · refine congrArg _ (h1 (RingHom.ext fun x => ?_))
      have := congrArg (fun f : L →+* ℂ => starRingEnd ℂ (f x)) hij
      simpa [σ] using this
  have := GlobalTheory.HalfIntChars.emb_mul_indep σ hσ (Sum.elim c (-c)) (fun k hk => by
    have hne : ∀ i, φ i k ≠ 0 := fun i => by simpa using hk
    have e3 := congrArg (· ^ 2) (h k hk)
    simp only [← Finset.prod_pow, one_pow] at e3
    rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← e3]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm (c i), zpow_mul, zpow_natCast,
      GlobalTheory.HalfIntChars.unit_sq _ (hne i), div_zpow]
    simp only [σ, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, RingHom.comp_apply]
    rw [div_eq_mul_inv, ← zpow_neg])
  funext i
  have := congrFun this (Sum.inl i)
  simpa using this

/- English proof (translation)
Introduce `i j h` and use `D.eTau.injective (GlobalTheory.HalfIntChars.embPsi_inj D.host h)`.
-/
theorem embTau_inj (D : D7) : Function.Injective (Formalism.L2.Host.embTau D) := fun i j h =>
  D.eTau.injective (GlobalTheory.HalfIntChars.embPsi_inj D.host h)

/- English proof (translation)
The claim follows from `GlobalTheory.HalfIntChars.embPsi_ne_conj D.host (D.eTau i) (D.eTau j)`.
-/
theorem embTau_ne_conj (D : D7) (i j : D.what₂.Tau) :
    Formalism.L2.Host.embTau D i ≠ (starRingEnd ℂ).comp (Formalism.L2.Host.embTau D j) :=
  GlobalTheory.HalfIntChars.embPsi_ne_conj D.host (D.eTau i) (D.eTau j)

/- English proof (translation)
Use `set u := Units.mk0 a ha`. Use `set φ := Formalism.L2.Host.embTau D`. Establish `hne : ∀ τ, φ τ a ≠ 0` using `fun τ => by simpa using ha`. Establish `hu : ∀ τ, φ τ a / ((‖φ τ a‖ : ℝ) : ℂ) ≠ 0` using `fun τ => div_ne_zero (hne τ) (by exact_mod_cast norm_ne_zero_iff.2 (hne τ))`. Establish `hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) * ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1` using `χ.aut u`.

Establish `hB` using `χ'.2.2 u`. Rewrite `hB` using `[← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← GlobalTheory.Mem.Col2.SplitChar.finIdl_incU, ← hf]`. Establish `hB' : ((χ'.inf u : ℂˣ) : ℂ) * ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) ^ e = 1`. Use `congrArg Units.val hB` as an intermediate fact. Simplify using `only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_one] at this`.

Conclude with `this`. Rewrite `hB'` using `[hk u]`. Use `set X := ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ)`. Establish `hX : X ≠ 0` using `by simp [X]`. Establish `hX' : X = (∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ))⁻¹` using `eq_inv_of_mul_eq_one_left hA`.

Rewrite `hB'` using `[hX', inv_zpow', ← Finset.prod_zpow]`. Repeatedly rewrite using `[zpow_sub₀ (hu _), Finset.prod_div_distrib, mul_comm e, zpow_mul]`. Rewrite using `[div_eq_one_iff_eq]`. Establish `h2` using `eq_inv_of_mul_eq_one_left hB'`. Establish `hua : (u : D.host.E) = a` using `rfl`.

Rewrite `h2` using `[hua]`. Rewrite using `[h2, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[zpow_neg, inv_inv]`. Conclude with `Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hu τ)`.
-/
theorem prod_eq_one {D : D7} {N : ℕ} (χ : HeckeU D N) (e : ℤ) (χ' : HChar D.host.E) (k : D.what₂.Tau → ℤ)
    (hf : ∀ x, χ.f x ^ e = χ'.1 (finIdl D x)) (hk : χ'.HasInf (Formalism.L2.Host.embTau D) k)
    (a : D.host.E) (ha : a ≠ 0) :
    ∏ τ, (Formalism.L2.Host.embTau D τ a / ((‖Formalism.L2.Host.embTau D τ a‖ : ℝ) : ℂ)) ^ (e * χ.n τ - k τ) = 1 := by
  set u := Units.mk0 a ha
  set φ := Formalism.L2.Host.embTau D
  have hne : ∀ τ, φ τ a ≠ 0 := fun τ => by simpa using ha
  have hu : ∀ τ, φ τ a / ((‖φ τ a‖ : ℝ) : ℂ) ≠ 0 := fun τ =>
    div_ne_zero (hne τ) (by exact_mod_cast norm_ne_zero_iff.2 (hne τ))
  have hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
      ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1 := χ.aut u
  have hB := χ'.2.2 u
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← GlobalTheory.Mem.Col2.SplitChar.finIdl_incU, ← hf] at hB
  have hB' : ((χ'.inf u : ℂˣ) : ℂ) * ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) ^ e = 1 := by
    have := congrArg Units.val hB
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_one] at this
    exact this
  rw [hk u] at hB'
  set X := ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ)
  have hX : X ≠ 0 := by simp [X]
  have hX' : X = (∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ))⁻¹ := eq_inv_of_mul_eq_one_left hA
  rw [hX', inv_zpow', ← Finset.prod_zpow] at hB'
  simp_rw [zpow_sub₀ (hu _), Finset.prod_div_distrib, mul_comm e, zpow_mul]
  rw [div_eq_one_iff_eq]
  · have h2 := eq_inv_of_mul_eq_one_left hB'
    have hua : (u : D.host.E) = a := rfl
    rw [hua] at h2
    rw [h2, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [zpow_neg, inv_inv]
  · exact Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hu τ)

/- English proof (translation)
Introduce `D N χ e χ' k he hf hk τ`. Establish `hc` using `exps_eq_zero (Formalism.L2.Host.embTau D) (embTau_inj D) (embTau_ne_conj D) (fun τ => e * χ.n τ - k τ) (fun a ha => prod_eq_one χ e χ' k hf hk a ha)`. Establish `h` using `congrFun hc τ`. Simplify using `only [Pi.zero_apply, sub_eq_zero] at h`. Rewrite using `[← h]`.

Apply the tactic sequence `rcases he with rfl | rfl <;> simp`.
-/
theorem abs_weight_eq_abs_infType : ∀ {D : D7} {N : ℕ} (χ : HeckeU D N) (e : ℤ) (χ' : HChar D.host.E)
    (k : D.what₂.Tau → ℤ), (e = 1 ∨ e = -1) → (∀ x, χ.f x ^ e = χ'.1 (finIdl D x)) →
    χ'.HasInf (Formalism.L2.Host.embTau D) k → ∀ τ, |χ.n τ| = |k τ| := by
  intro D N χ e χ' k he hf hk τ
  have hc := exps_eq_zero (Formalism.L2.Host.embTau D) (embTau_inj D) (embTau_ne_conj D)
    (fun τ => e * χ.n τ - k τ) (fun a ha => prod_eq_one χ e χ' k hf hk a ha)
  have h := congrFun hc τ
  simp only [Pi.zero_apply, sub_eq_zero] at h
  rw [← h]
  rcases he with rfl | rfl <;> simp

end GlobalTheory.SplitWeight
