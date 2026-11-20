import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffNmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEvaluationSubstCompatibleThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmulSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPowerStatement

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeriodExists

set_option autoImplicit false in
open MvPowerSeries in
/- English proof (translation)
Introduce `α i`. Take `⟨s, hs⟩` from `h i`. Distinguish the cases in `hα : α i = 0`. Conclude with `⟨0, Submodule.mem_top, by simp [hα]⟩`. Take `⟨m, rfl⟩ : ∃ m, α = m + Finsupp.single i 1` from `⟨α - Finsupp.single i 1, by`.

Apply the tactic sequence `ext j; by_cases hj : j = i <;> simp [Finsupp.single_apply, hj] <;> omega⟩`. Use `⟨coeff m s, Submodule.mem_top, ?_⟩` and prove the remaining obligations. Use `congrArg (coeff m) hs` as an intermediate fact. Rewrite `this` using `[coeff_map, coeff_pderiv]`. Rewrite using `[this]`.

Simplify using `[mul_comm]`.
-/
private lemma dIn_univ_of_forall_pderiv_integral {B Q : Type} [CommRing B] [CommRing Q]
    [Algebra B Q] {d : ℕ} (f : MvPowerSeries (Fin d) Q)
    (h : ∀ i, ∃ s : MvPowerSeries (Fin d) B, map (algebraMap B Q) s = pderiv Q i f) :
    _root_.GlobalTheory.QLog.DIn (⊤ : Ideal B) f := by
  intro α i
  obtain ⟨s, hs⟩ := h i
  by_cases hα : α i = 0
  · exact ⟨0, Submodule.mem_top, by simp [hα]⟩
  · obtain ⟨m, rfl⟩ : ∃ m, α = m + Finsupp.single i 1 := ⟨α - Finsupp.single i 1, by
      ext j; by_cases hj : j = i <;> simp [Finsupp.single_apply, hj] <;> omega⟩
    refine ⟨coeff m s, Submodule.mem_top, ?_⟩
    have := congrArg (coeff m) hs
    rw [coeff_map, coeff_pderiv] at this
    rw [this]
    simp [mul_comm]

set_option autoImplicit false in
open MvPowerSeries in
/- English proof (translation)
Apply the tactic sequence `have hE : HasSubst (Sum.elim (X : Fin d → MvPowerSeries (Fin d) R) (0 : Fin d → MvPowerSeries (Fin d) R)) := hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp)`. Establish `hM : HasSubst μ` using `hasSubst_of_constantCoeff_zero hμ`. Establish `hL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R))` using `hasSubst_of_constantCoeff_zero (by simp)`. Establish `hR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))` using `hasSubst_of_constantCoeff_zero (by simp)`. Unfold `_root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR`.

Rewrite using `[map_sub, map_sub, _root_.GlobalTheory.PSChain.pderiv_subst_chain μ hμ, _root_.GlobalTheory.PSChain.pderiv_subst_chain _ (by simp), _root_.GlobalTheory.PSChain.pderiv_subst_chain _ (by simp)]`. Establish `hs1 : ∀ x : Fin d, ((Pi.single (Sum.inr j) (1 : MvPowerSeries (Fin d ⊕ Fin d) R) : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (Sum.inl x)) = 0` using `fun x => by simp [Pi.single_apply]`. Establish `hs2 : ∀ x : Fin d, ((Pi.single (Sum.inr j) (1 : MvPowerSeries (Fin d ⊕ Fin d) R) : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (Sum.inr x)) = if x = j then 1 else 0` using `fun x => by simp [Pi.single_apply]`. Simplify using `only [pderiv_X, hs1, hs2]`. Rewrite using `[← coe_substAlgHom hE]`.

Simplify using `only [map_sub, map_sum, map_mul, map_zero, mul_zero, Finset.sum_const_zero, sub_zero, apply_ite, map_one, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Simplify using `only [coe_substAlgHom]`. Establish `h1 : (fun s => subst (Sum.elim (X : Fin d → MvPowerSeries (Fin d) R) (0 : Fin d → MvPowerSeries (Fin d) R)) (μ s)) = X`. Use function extensionality and compare the values at `hadd`. Establish `h2 : (fun s => subst (Sum.elim (X : Fin d → MvPowerSeries (Fin d) R) (0 : Fin d → MvPowerSeries (Fin d) R)) (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) R)) = 0`.

Use function extensionality and compare the values at `s`. Simplify using `[subst_X hE]`. Simplify using `only [subst_comp_subst_apply hM hE, subst_comp_subst_apply hR hE, h1, h2, subst_self, id_eq, subst_zero_eq_C_constantCoeff]`. Use `congr 1`.
-/
private lemma subst_pderiv_inr_cob1_eq_sum_sub_C {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0)
    (hadd : ∀ k, subst (Sum.elim (X : Fin d → MvPowerSeries (Fin d) R) (0 : Fin d → MvPowerSeries (Fin d) R)) (μ k) = X k)
    (f : MvPowerSeries (Fin d) R) (j : Fin d) :
    subst (Sum.elim (X : Fin d → MvPowerSeries (Fin d) R) (0 : Fin d → MvPowerSeries (Fin d) R))
        (pderiv R (Sum.inr j) (_root_.GlobalTheory.Katz.cob1 μ f)) =
      ∑ k, pderiv R k f * subst (Sum.elim (X : Fin d → MvPowerSeries (Fin d) R) (0 : Fin d → MvPowerSeries (Fin d) R))
        (pderiv R (Sum.inr j) (μ k)) - C (constantCoeff (pderiv R j f)) := by
  have hE : HasSubst (Sum.elim (X : Fin d → MvPowerSeries (Fin d) R) (0 : Fin d → MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp)
  have hM : HasSubst μ := hasSubst_of_constantCoeff_zero hμ
  have hL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have hR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR
  rw [map_sub, map_sub, _root_.GlobalTheory.PSChain.pderiv_subst_chain μ hμ, _root_.GlobalTheory.PSChain.pderiv_subst_chain _ (by simp),
    _root_.GlobalTheory.PSChain.pderiv_subst_chain _ (by simp)]
  have hs1 : ∀ x : Fin d, ((Pi.single (Sum.inr j) (1 : MvPowerSeries (Fin d ⊕ Fin d) R) :
      Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (Sum.inl x)) = 0 := fun x => by simp [Pi.single_apply]
  have hs2 : ∀ x : Fin d, ((Pi.single (Sum.inr j) (1 : MvPowerSeries (Fin d ⊕ Fin d) R) :
      Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (Sum.inr x)) = if x = j then 1 else 0 := fun x => by simp [Pi.single_apply]
  simp only [pderiv_X, hs1, hs2]
  rw [← coe_substAlgHom hE]
  simp only [map_sub, map_sum, map_mul, map_zero, mul_zero, Finset.sum_const_zero, sub_zero,
    apply_ite, map_one, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [coe_substAlgHom]
  have h1 : (fun s => subst (Sum.elim (X : Fin d → MvPowerSeries (Fin d) R) (0 : Fin d → MvPowerSeries (Fin d) R)) (μ s)) = X :=
    funext hadd
  have h2 : (fun s => subst (Sum.elim (X : Fin d → MvPowerSeries (Fin d) R) (0 : Fin d → MvPowerSeries (Fin d) R))
      (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) R)) = 0 := by
    funext s; simp [subst_X hE]
  simp only [subst_comp_subst_apply hM hE, subst_comp_subst_apply hR hE, h1, h2, subst_self,
    id_eq, subst_zero_eq_C_constantCoeff]
  congr 1

set_option autoImplicit false in
open MvPowerSeries in
/- English proof (translation)
Use `choose b hb using hlin`. Use `set EB := Sum.elim (X : Fin d → MvPowerSeries (Fin d) B) (0 : Fin d → MvPowerSeries (Fin d) B)`. Use `set EQ := Sum.elim (X : Fin d → MvPowerSeries (Fin d) Q) (0 : Fin d → MvPowerSeries (Fin d) Q)`. Apply the tactic sequence `have hEB : HasSubst EB := hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp [EB])`. Establish `hEmap : (fun x => map (algebraMap B Q) (EB x)) = EQ`.

Apply the tactic sequence `funext x; rcases x with x | x <;> simp [EB, EQ]`. Establish `hpm : ∀ {σ : Type} (g : MvPowerSeries σ B) (k : σ), pderiv Q k (map (algebraMap B Q) g) = map (algebraMap B Q) (pderiv B k g)`. Introduce `σ g k`. Use extensionality with `n`. Simplify using `[coeff_pderiv]`.

Establish `hsm : ∀ g : MvPowerSeries (Fin d ⊕ Fin d) B,`. Substitute `EQ (map (algebraMap B Q) g) = map (algebraMap B Q) (subst EB g) := by` using the available equality. Introduce `g`. Rewrite using `[map_subst hEB, hEmap]`. Set `M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) B)` to `fun k j => subst EB (pderiv B (Sum.inr j) (μ k))`.

Set `w : Fin d → MvPowerSeries (Fin d) B` to `fun j => subst EB (pderiv B (Sum.inr j) s) + C (b j)`. Establish `hμQ : ∀ k, constantCoeff (_root_.GlobalTheory.QLog.up Q μ k) = 0`. Introduce `k`. Simplify using `[_root_.GlobalTheory.QLog.up, hμ k]`. Establish `haddQ : ∀ k, subst EQ (_root_.GlobalTheory.QLog.up Q μ k) = X k`.

Introduce `k`. Simplify using `only [_root_.GlobalTheory.QLog.up]`. Rewrite using `[hsm, hadd]`. Simplify using the standard rewrite rules. Establish `hrow : ∀ j, ∑ k, pderiv Q k f * map (algebraMap B Q) (M k j) = map (algebraMap B Q) (w j)`.

Introduce `j`. Establish `h` using `subst_pderiv_inr_cob1_eq_sum_sub_C hμQ haddQ f j`. Rewrite `h` using `[← hs, hpm, hsm]`. Establish `hc : (C (constantCoeff (pderiv Q j f)) : MvPowerSeries (Fin d) Q) = map (algebraMap B Q) (C (b j) : MvPowerSeries (Fin d) B)`. Establish `hcc : constantCoeff (pderiv Q j f) = algebraMap B Q (b j)`.

Rewrite using `[← hb j, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]`. Simplify using `[_root_.GlobalTheory.Katz.lin]`. Rewrite using `[hcc, map_C]`. Simplify using `only [M, w, map_add, ← hsm, ← hpm]`. Simplify using `only [_root_.GlobalTheory.QLog.up] at h`.

Rewrite using `[← hc, hpm s, hsm, h, sub_add_cancel]`. Establish `hdet : IsUnit M.det`. Rewrite using `[isUnit_iff_constantCoeff, RingHom.map_det]`. Establish `: (constantCoeff).mapMatrix M = 1`. Use extensionality with `k j`.

Use `show constantCoeff (subst EB (pderiv B (Sum.inr j) (μ k))) = (1 : Matrix (Fin d) (Fin d) B) k j`. Rewrite using `[Matrix.one_apply, ← coeff_zero_eq_constantCoeff_apply, show EB = Sum.elim (fun i => X i) (fun _ => 0) from rfl, (_root_.GlobalTheory.coeff_subst_restrict_sum (pderiv B (Sum.inr j) (μ k))).1 0]`. Simplify using `[coeff_pderiv, hδ]`. Rewrite using `[this, Matrix.det_one]`. Conclude with `isUnit_one`.

Establish `hMN` using `Matrix.mul_nonsing_inv M hdet`. Use `⟨∑ j, w j * M⁻¹ j i, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Conclude with `Finset.sum_comm`.

Use `_ = pderiv Q i f := by`. Rewrite using `[hMN]`. Simplify using `[Matrix.one_apply]`.
-/
private lemma exists_integral_pderiv_of_integral_cob1_lin {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : ∀ i, constantCoeff (μ i) = 0)
    (hadd : ∀ k, subst (Sum.elim (X : Fin d → MvPowerSeries (Fin d) B)
      (0 : Fin d → MvPowerSeries (Fin d) B)) (μ k) = X k)
    (hδ : ∀ k j, coeff (Finsupp.single (Sum.inr j) 1) (μ k) = if k = j then 1 else 0)
    {f : MvPowerSeries (Fin d) Q}
    (hlin : ∀ i, ∃ b, _root_.GlobalTheory.Katz.lin f i = algebraMap B Q b)
    (s : MvPowerSeries (Fin d ⊕ Fin d) B)
    (hs : map (algebraMap B Q) s =
      _root_.GlobalTheory.Katz.cob1 (_root_.GlobalTheory.QLog.up Q μ) f) (i : Fin d) :
    ∃ g, map (algebraMap B Q) g = pderiv Q i f := by
  classical
  choose b hb using hlin
  set EB := Sum.elim (X : Fin d → MvPowerSeries (Fin d) B) (0 : Fin d → MvPowerSeries (Fin d) B)
  set EQ := Sum.elim (X : Fin d → MvPowerSeries (Fin d) Q) (0 : Fin d → MvPowerSeries (Fin d) Q)
  have hEB : HasSubst EB := hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp [EB])
  have hEmap : (fun x => map (algebraMap B Q) (EB x)) = EQ := by
    funext x; rcases x with x | x <;> simp [EB, EQ]
  have hpm : ∀ {σ : Type} (g : MvPowerSeries σ B) (k : σ),
      pderiv Q k (map (algebraMap B Q) g) = map (algebraMap B Q) (pderiv B k g) := by
    intro σ g k; ext n; simp [coeff_pderiv]
  have hsm : ∀ g : MvPowerSeries (Fin d ⊕ Fin d) B,
      subst EQ (map (algebraMap B Q) g) = map (algebraMap B Q) (subst EB g) := by
    intro g; rw [map_subst hEB, hEmap]
  let M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) B) :=
    fun k j => subst EB (pderiv B (Sum.inr j) (μ k))
  let w : Fin d → MvPowerSeries (Fin d) B := fun j => subst EB (pderiv B (Sum.inr j) s) + C (b j)
  have hμQ : ∀ k, constantCoeff (_root_.GlobalTheory.QLog.up Q μ k) = 0 := by
    intro k; simp [_root_.GlobalTheory.QLog.up, hμ k]
  have haddQ : ∀ k, subst EQ (_root_.GlobalTheory.QLog.up Q μ k) = X k := by
    intro k; simp only [_root_.GlobalTheory.QLog.up]; rw [hsm, hadd]; simp
  have hrow : ∀ j, ∑ k, pderiv Q k f * map (algebraMap B Q) (M k j) = map (algebraMap B Q) (w j) := by
    intro j
    have h := subst_pderiv_inr_cob1_eq_sum_sub_C hμQ haddQ f j
    rw [← hs, hpm, hsm] at h
    have hc : (C (constantCoeff (pderiv Q j f)) : MvPowerSeries (Fin d) Q) =
        map (algebraMap B Q) (C (b j) : MvPowerSeries (Fin d) B) := by
      have hcc : constantCoeff (pderiv Q j f) = algebraMap B Q (b j) := by
        rw [← hb j, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
        simp [_root_.GlobalTheory.Katz.lin]
      rw [hcc, map_C]
    simp only [M, w, map_add, ← hsm, ← hpm]
    simp only [_root_.GlobalTheory.QLog.up] at h
    rw [← hc, hpm s, hsm, h, sub_add_cancel]
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_constantCoeff, RingHom.map_det]
    have : (constantCoeff).mapMatrix M = 1 := by
      ext k j
      show constantCoeff (subst EB (pderiv B (Sum.inr j) (μ k))) = (1 : Matrix (Fin d) (Fin d) B) k j
      rw [Matrix.one_apply, ← coeff_zero_eq_constantCoeff_apply,
        show EB = Sum.elim (fun i => X i) (fun _ => 0) from rfl,
        (_root_.GlobalTheory.coeff_subst_restrict_sum (pderiv B (Sum.inr j) (μ k))).1 0]
      simp [coeff_pderiv, hδ]
    rw [this, Matrix.det_one]
    exact isUnit_one
  have hMN := Matrix.mul_nonsing_inv M hdet
  refine ⟨∑ j, w j * M⁻¹ j i, ?_⟩
  calc map (algebraMap B Q) (∑ j, w j * M⁻¹ j i)
      = ∑ j, (∑ k, pderiv Q k f * map (algebraMap B Q) (M k j)) *
          map (algebraMap B Q) (M⁻¹ j i) := by simp [map_sum, hrow]
    _ = ∑ k, pderiv Q k f * map (algebraMap B Q) ((M * M⁻¹) k i) := by
        simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ = pderiv Q i f := by
        rw [hMN]; simp [Matrix.one_apply]

set_option autoImplicit false in
open MvPowerSeries in
/- English proof (translation)
Apply the tactic sequence `have hS : HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) (fun i => X (Sum.inl i))) := hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp)`. Apply the tactic sequence `have hE0 : HasSubst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) (fun i : Fin d => X i)) := hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp)`. Establish `h0 : subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) (fun i : Fin d => X i)) (μ k) = X k`. Rewrite using `[← hsymm k]`. Unfold `_root_.GlobalTheory.Katz.swap _root_.GlobalTheory.Katz.at2`.

Rewrite using `[subst_comp_subst_apply hS hE0]`. Use `hadd k using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Apply the tactic sequence `rcases x with x | x <;> simp [subst_X hE0]`. Establish `h` using `(_root_.GlobalTheory.coeff_subst_restrict_sum (μ k)).2 (Finsupp.single j 1)`.

Rewrite `h` using `[h0, Finsupp.mapDomain_single, coeff_X]`. Rewrite using `[← h]`. Distinguish the cases in `hkj : k = j`. Substitute `hkj` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg, if_neg hkj]`. Introduce `h'`. Conclude with `hkj (Finsupp.single_left_injective one_ne_zero h').symm`.
-/
private lemma coeff_single_inr_eq_ite_of_add_id_of_symm {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hadd : ∀ k, subst (Sum.elim (X : Fin d → MvPowerSeries (Fin d) R)
      (0 : Fin d → MvPowerSeries (Fin d) R)) (μ k) = X k)
    (hsymm : ∀ k, _root_.GlobalTheory.Katz.swap (μ k) = μ k) (k j : Fin d) :
    coeff (Finsupp.single (Sum.inr j) 1) (μ k) = if k = j then 1 else 0 := by
  have hS : HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inl i))) :=
    hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp)
  have hE0 : HasSubst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) (fun i : Fin d => X i)) :=
    hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp)
  have h0 : subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) (fun i : Fin d => X i)) (μ k) =
      X k := by
    rw [← hsymm k]
    unfold _root_.GlobalTheory.Katz.swap _root_.GlobalTheory.Katz.at2
    rw [subst_comp_subst_apply hS hE0]
    convert hadd k using 2
    funext x
    rcases x with x | x <;> simp [subst_X hE0]
  have h := (_root_.GlobalTheory.coeff_subst_restrict_sum (μ k)).2 (Finsupp.single j 1)
  rw [h0, Finsupp.mapDomain_single, coeff_X] at h
  rw [← h]
  by_cases hkj : k = j
  · subst hkj; simp
  · rw [if_neg, if_neg hkj]
    intro h'
    exact hkj (Finsupp.single_left_injective one_ne_zero h').symm

set_option autoImplicit false in
open MvPowerSeries in
/- English proof (translation)
Apply the tactic sequence `have hE : HasSubst (Sum.elim u (X : Fin d → MvPowerSeries (Fin d) R)) := hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp [hu])`. Establish `hM : HasSubst μ` using `hasSubst_of_constantCoeff_zero hμ`. Establish `hL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R))` using `hasSubst_of_constantCoeff_zero (by simp)`. Establish `hR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))` using `hasSubst_of_constantCoeff_zero (by simp)`. Unfold `_root_.GlobalTheory.Katz.at2`.

Rewrite using `[← subst_comp_subst_apply hM hE]`. Unfold `_root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR`. Rewrite using `[subst_sub hE, subst_sub hE, subst_comp_subst_apply hL hE, subst_comp_subst_apply hR hE]`. Simplify using `only [subst_X hE, Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[subst_self]`.

Simplify using the standard rewrite rules.
-/
private lemma subst_at2_eq_subst_add_self_add_subst_cob1 {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → MvPowerSeries (Fin d) R) (hu : ∀ i, constantCoeff (u i) = 0)
    (f : MvPowerSeries (Fin d) R) :
    subst (fun i => _root_.GlobalTheory.Katz.at2 (μ i) u X) f =
      subst u f + f + subst (Sum.elim u X) (_root_.GlobalTheory.Katz.cob1 μ f) := by
  have hE : HasSubst (Sum.elim u (X : Fin d → MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp [hu])
  have hM : HasSubst μ := hasSubst_of_constantCoeff_zero hμ
  have hL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have hR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  unfold _root_.GlobalTheory.Katz.at2
  rw [← subst_comp_subst_apply hM hE]
  unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR
  rw [subst_sub hE, subst_sub hE, subst_comp_subst_apply hL hE, subst_comp_subst_apply hR hE]
  simp only [subst_X hE, Sum.elim_inl, Sum.elim_inr]
  rw [subst_self]
  simp

set_option autoImplicit false in
open MvPowerSeries in
/- English proof (translation)
Take `⟨s, hs⟩` from `(_root_.GlobalTheory.QLog.In.top_iff (B := B)).1 hcob`. Establish `hμQ : ∀ i, constantCoeff (_root_.GlobalTheory.QLog.up Q μ i) = 0`. Introduce `i`. Simplify using `[_root_.GlobalTheory.QLog.up, hμ i]`. Proceed by induction on `k with`.

Consider the case `zero`. Use `⟨0, ?_⟩` and prove the remaining obligations. Use `show _ = ((0 : ℕ) : Q) • f - subst _ f`. Establish `h0 : _root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ 0) = fun _ => 0`. Use function extensionality and compare the values at `i`.

Simplify using `[_root_.GlobalTheory.QLog.up, _root_.GlobalTheory.QLog.nmul]`. Rewrite using `[h0, show (fun _ : Fin d => (0 : MvPowerSeries (Fin d) Q)) = 0 from rfl, subst_zero_eq_C_constantCoeff, hf0]`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Take `⟨a, ha⟩` from `ih`.

Establish `hk : ∀ i, constantCoeff (_root_.GlobalTheory.QLog.nmul μ k i) = 0` using `_root_.GlobalTheory.MapNMul.cc_nmul μ hμ k`. Establish `hkQ : ∀ i, constantCoeff (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ k) i) = 0`. Introduce `i`. Simplify using `[_root_.GlobalTheory.QLog.up, hk i]`. Apply the tactic sequence `have hEB : HasSubst (Sum.elim (_root_.GlobalTheory.QLog.nmul μ k) (X : Fin d → MvPowerSeries (Fin d) B)) := hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp [hk])`.

Use `⟨a - subst (Sum.elim (_root_.GlobalTheory.QLog.nmul μ k) X) s, ?_⟩` and prove the remaining obligations. Establish `hfam : _root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ (k + 1)) = fun i => _root_.GlobalTheory.Katz.at2 (_root_.GlobalTheory.QLog.up Q μ i) (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ k)) X`. Establish `hsucc : _root_.GlobalTheory.QLog.nmul μ (k + 1) = _root_.GlobalTheory.Katz.op μ (_root_.GlobalTheory.QLog.nmul μ k) X`. Simplify using `only [_root_.GlobalTheory.QLog.nmul, Function.iterate_succ_apply']`. Use function extensionality and compare the values at `i`.

Simplify using `only [_root_.GlobalTheory.QLog.up, hsucc, _root_.GlobalTheory.Katz.op, _root_.GlobalTheory.Katz.at2]`. Apply the tactic sequence `rw [map_subst (hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [hk]))]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `rcases j with j | j <;> simp [_root_.GlobalTheory.QLog.up]`.

Use `show _ = (((k + 1 : ℕ)) : Q) • f - subst _ f`. Rewrite using `[hfam, subst_at2_eq_subst_add_self_add_subst_cob1 hμQ _ hkQ, ← hs, map_sub, ha, map_subst hEB]`. Establish `: (fun j => map (algebraMap B Q) (Sum.elim (_root_.GlobalTheory.QLog.nmul μ k) X j)) = Sum.elim (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ k)) X`. Apply the tactic sequence `funext j; rcases j with j | j <;> simp [_root_.GlobalTheory.QLog.up]`. Rewrite using `[this]`.

Use `show ((k : ℕ) : Q) • f - subst _ f - _ = _`. Use `push_cast`. Rewrite using `[add_smul, one_smul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma exists_integral_defect_of_integral_cob1 {B Q : Type} [CommRing B] [CommRing Q]
    [Algebra B Q] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    (hμ : ∀ i, constantCoeff (μ i) = 0) {f : MvPowerSeries (Fin d) Q} (hf0 : constantCoeff f = 0)
    (hcob : _root_.GlobalTheory.QLog.In (⊤ : Ideal B)
      (_root_.GlobalTheory.Katz.cob1 (_root_.GlobalTheory.QLog.up Q μ) f)) (k : ℕ) :
    ∃ a, map (algebraMap B Q) a = _root_.GlobalTheory.QLog.defect μ k f := by
  obtain ⟨s, hs⟩ := (_root_.GlobalTheory.QLog.In.top_iff (B := B)).1 hcob
  have hμQ : ∀ i, constantCoeff (_root_.GlobalTheory.QLog.up Q μ i) = 0 := by
    intro i; simp [_root_.GlobalTheory.QLog.up, hμ i]
  induction k with
  | zero =>
    refine ⟨0, ?_⟩
    show _ = ((0 : ℕ) : Q) • f - subst _ f
    have h0 : _root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ 0) = fun _ => 0 := by
      funext i; simp [_root_.GlobalTheory.QLog.up, _root_.GlobalTheory.QLog.nmul]
    rw [h0, show (fun _ : Fin d => (0 : MvPowerSeries (Fin d) Q)) = 0 from rfl,
      subst_zero_eq_C_constantCoeff, hf0]
    simp
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih
    have hk : ∀ i, constantCoeff (_root_.GlobalTheory.QLog.nmul μ k i) = 0 :=
      _root_.GlobalTheory.MapNMul.cc_nmul μ hμ k
    have hkQ : ∀ i, constantCoeff
        (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ k) i) = 0 := by
      intro i; simp [_root_.GlobalTheory.QLog.up, hk i]
    have hEB : HasSubst (Sum.elim (_root_.GlobalTheory.QLog.nmul μ k)
        (X : Fin d → MvPowerSeries (Fin d) B)) :=
      hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp [hk])
    refine ⟨a - subst (Sum.elim (_root_.GlobalTheory.QLog.nmul μ k) X) s, ?_⟩
    have hfam : _root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ (k + 1)) =
        fun i => _root_.GlobalTheory.Katz.at2 (_root_.GlobalTheory.QLog.up Q μ i)
          (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ k)) X := by
      have hsucc : _root_.GlobalTheory.QLog.nmul μ (k + 1) =
          _root_.GlobalTheory.Katz.op μ (_root_.GlobalTheory.QLog.nmul μ k) X := by
        simp only [_root_.GlobalTheory.QLog.nmul, Function.iterate_succ_apply']
      funext i
      simp only [_root_.GlobalTheory.QLog.up, hsucc, _root_.GlobalTheory.Katz.op,
        _root_.GlobalTheory.Katz.at2]
      rw [map_subst (hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [hk]))]
      congr 1
      funext j
      rcases j with j | j <;> simp [_root_.GlobalTheory.QLog.up]
    show _ = (((k + 1 : ℕ)) : Q) • f - subst _ f
    rw [hfam, subst_at2_eq_subst_add_self_add_subst_cob1 hμQ _ hkQ, ← hs, map_sub, ha, map_subst hEB]
    have : (fun j => map (algebraMap B Q) (Sum.elim (_root_.GlobalTheory.QLog.nmul μ k) X j)) =
        Sum.elim (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ k)) X := by
      funext j; rcases j with j | j <;> simp [_root_.GlobalTheory.QLog.up]
    rw [this]
    show ((k : ℕ) : Q) • f - subst _ f - _ = _
    push_cast
    rw [add_smul, one_smul]
    ring

set_option autoImplicit false in
open MvPowerSeries in
/- English proof (translation)
Establish `hE' : _root_.GlobalTheory.QLog.IsEval p (fun i => θ (z i)) (((t.pt n).comp (c.ev n)) : MvPowerSeries (Fin d) O →ₐ[O] O)`. Use `⟨fun i => ?_, fun m => ?_⟩` and prove the remaining obligations. Simplify using `[hθz, (c.isEval n).1 i]`. Take `⟨N, hN⟩` from `(c.isEval n).2 m`. Use `⟨N, fun g hg => ?_⟩` and prove the remaining obligations.

Use `map_dvd (t.pt n) (hN g hg)` as an intermediate fact. Simplify using `using this`. Conclude with `((_root_.GlobalTheory.CEval.continuous_eval p B B (Fin d) z hz).2 E hE).2.2 O O θ θ _ (fun b => by simp) hE' s`.
-/
private lemma theta_eval_eq_tate_pt_ev_of_isEval {p : ℕ} {O B : Type} [CommRing O] [CommRing B]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsAdicComplete (Ideal.span {(p : B)}) B]
    {G : _root_.GlobalTheory.PDivGroup p O} {d : ℕ} (c : _root_.GlobalTheory.QLog.Chart G d) (θ : B →+* O)
    (t : G.Tate) (n : ℕ) (z : Fin d → B) (hz : ∀ i, ∃ N, (p : B) ∣ z i ^ N)
    (E : MvPowerSeries (Fin d) B →ₐ[B] B) (hE : _root_.GlobalTheory.QLog.IsEval p z E)
    (hθz : ∀ i, θ (z i) = t.pt n (c.x n i)) (s : MvPowerSeries (Fin d) B) :
    θ (E s) = t.pt n (c.ev n (map θ s)) := by
  have hE' : _root_.GlobalTheory.QLog.IsEval p (fun i => θ (z i))
      (((t.pt n).comp (c.ev n)) : MvPowerSeries (Fin d) O →ₐ[O] O) := by
    refine ⟨fun i => ?_, fun m => ?_⟩
    · simp [hθz, (c.isEval n).1 i]
    · obtain ⟨N, hN⟩ := (c.isEval n).2 m
      refine ⟨N, fun g hg => ?_⟩
      have := map_dvd (t.pt n) (hN g hg)
      simpa using this
  exact ((_root_.GlobalTheory.CEval.continuous_eval p B B (Fin d) z hz).2 E hE).2.2
    O O θ θ _ (fun b => by simp) hE' s

set_option autoImplicit false in
open MvPowerSeries in

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hmap f t hf`. Establish `hex : ∃ y, c.HasPeriod F.θ t f y` using `by classical`. Establish `hF` using `F.frame`. Use `haveI : IsAdicComplete (Ideal.span {(p : F.B)}) F.B := hF.complete`. Take `⟨hf0, hlin, hcob⟩` from `hf`.

Establish `hD : _root_.GlobalTheory.QLog.DIn (⊤ : Ideal F.B) f`. Take `⟨s, hs⟩` from `(_root_.GlobalTheory.QLog.In.top_iff (B := F.B)).1 hcob`. Establish `hadd : ∀ k, subst (Sum.elim (X : Fin d → MvPowerSeries (Fin d) F.B) (0 : Fin d → MvPowerSeries (Fin d) F.B)) (μ' k) = X k` using `fun k => congrFun hlift.unit k`. Conclude with `dIn_univ_of_forall_pderiv_integral f (fun i => exists_integral_pderiv_of_integral_cob1_lin hlift.const hadd (coeff_single_inr_eq_ite_of_add_id_of_symm hadd hlift.comm) (fun i => by obtain ⟨b, -, hb⟩ := hlin i; exact ⟨b, hb⟩) s hs i)`. Establish `hμ0` using `hlift.const`.

Take `⟨a, ha⟩` from `exists_integral_defect_of_integral_cob1 hμ0 hf0 hcob p`. Set `IsLift : ℕ → (Fin d → F.B) → Prop` to `fun n z => ∀ i, F.θ (z i) = t.pt n (c.x n i)`. Establish `hnil : ∀ n z, IsLift n z → ∀ i, ∃ N, (p : F.B) ∣ z i ^ N`. Introduce `n z hz i`. Take `⟨N, o, ho⟩` from `c.nil n i`.

Take `⟨b, hb⟩` from `hF.surj (t.pt n o)`. Take `⟨y, -, hy⟩` from `hF.pd (z i ^ N - p * b) (by`. Rewrite using `[map_sub, map_pow, hz i, map_mul, map_natCast, hb, ← map_pow, ho, map_mul, map_natCast, sub_self])`. Use `⟨N * p, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, pow_mul, map_pow]`.

Establish `he : Ideal.Quotient.mk (Ideal.span {(p : F.B)}) (z i ^ N) = Ideal.Quotient.mk _ (z i ^ N - p * b)`. Rewrite using `[Ideal.Quotient.eq]`. Simplify using `[Ideal.mem_span_singleton]`. Rewrite using `[he, ← map_pow, hy, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)`.

Establish `hdiff : ∀ n z z' q q', IsLift n z → IsLift n z' → _root_.GlobalTheory.QLog.HasVal p z f q → _root_.GlobalTheory.QLog.HasVal p z' f q' → ∃ b, q - q' = algebraMap F.B F.Q b`. Introduce `n z z' q q' hz hz' hq hq'`. Take `⟨b, -, b', h⟩` from `_root_.GlobalTheory.HasValCong.hasVal_sub_mem p _ O _ _ hF _ z (hnil n z hz) (RingHom.ker F.θ) (fun x hx => by`. Take `⟨y, hy, hxy⟩` from `hF.pd x hx`. Conclude with `⟨y, hy, hxy⟩) z' f q q' (fun i => by simp [RingHom.mem_ker, hz i, hz' i]) hD hq hq' 0`.

Conclude with `⟨b + (p : F.B) ^ 0 * b', h⟩`. Establish `hdesc : ∀ n z q, IsLift (n + 1) z → _root_.GlobalTheory.QLog.HasVal p z f q → ∃ z', IsLift n z' ∧ ∃ q', _root_.GlobalTheory.QLog.HasVal p z' f q' ∧ ∃ b, (p : F.Q) * q - q' = algebraMap F.B F.Q b`. Introduce `n z q hz hq`. Establish `hzn` using `hnil _ z hz`. Take `⟨E, hE⟩` from `((_root_.GlobalTheory.CEval.continuous_eval p F.B F.B (Fin d) z hzn).1).exists`.

Establish `hk` using `_root_.GlobalTheory.MapNMul.cc_nmul μ' hμ0 p`. Establish `hw : IsLift n (fun i => E (_root_.GlobalTheory.QLog.nmul μ' p i))`. Introduce `i`. Rewrite using `[theta_eval_eq_tate_pt_ev_of_isEval c F.θ t (n + 1) z hzn E hE hz, _root_.GlobalTheory.MapNMul.map_nmul _ _ _ _ _ hμ0]`. Establish `hμc : (fun j => map F.θ (μ' j)) = c.μ` using `funext hmap`.

Rewrite using `[hμc, _root_.GlobalTheory.NMul.ev_nmul p C v O hv G d c, ← G.mulP_res, c.res, _root_.GlobalTheory.PDivGroup.TateOver.pt_mulP]`. Take `⟨q', hq'⟩` from `(_root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p _ O _ _ hF _ _ (hnil n _ hw) f hD).exists`. Use `⟨_, hw, q', hq', E a, ?_⟩` and prove the remaining obligations. Establish `h1` using `_root_.GlobalTheory.QLog.hasVal_subst p _ O _ _ hF _ z hzn E hE _ (_root_.GlobalTheory.QLog.nmul μ' p) f q' hk hD hq'`. Establish `h2` using `_root_.GlobalTheory.hasVal_map_of_isEval p _ O _ _ hF _ z hzn E hE a`.

Establish `h3` using `((_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ _ hF _ z _ _ _ _ h2).1 h1)`. Establish `h4` using `(_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ _ hF _ z f 0 q 0 hq).2.1 (p : F.Q)`. Establish `hser : map (algebraMap F.B F.Q) a +`. Substitute `(_root_.GlobalTheory.QLog.up F.Q (_root_.GlobalTheory.QLog.nmul μ' p)) f = (p : F.Q) • f := by` using the available equality. Rewrite using `[ha]`.

Unfold `_root_.GlobalTheory.QLog.defect`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h3` using `[hser]`. Rewrite using `[_root_.GlobalTheory.QLog.HasVal.unique hF h4 h3]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hint : ∀ n z q, IsLift n z → _root_.GlobalTheory.QLog.HasVal p z f q → ∃ b, (p : F.Q) ^ n * q = algebraMap F.B F.Q b`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `z q hz hq`.

Establish `hx0 : ∀ i, t.pt 0 (c.x 0 i) = 0`. Introduce `i`. Establish `h` using `G.mulBy_pow_self 0 (c.x 0 i)`. Rewrite `h` using `[pow_zero]`. Unfold `_root_.GlobalTheory.PDiv.mulBy at h`.

Simplify using `at h`. Rewrite using `[h, c.aug]`. Simplify using the standard rewrite rules. Establish `h0 : IsLift 0 0` using `fun i => by simp [hx0]`. Establish `hv0 : _root_.GlobalTheory.QLog.HasVal p (0 : Fin d → F.B) f 0`.

Introduce `m`. Use `⟨0, fun N' _ => ⟨0, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [Pi.zero_apply, map_zero, mul_zero, zero_sub, neg_eq_zero]`. Rewrite using `[show (fun _ : Fin d => (0 : F.Q)) = 0 from rfl, MvPolynomial.eval_zero]`. Use `show MvPolynomial.coeff 0 _ = 0`.

Rewrite using `[coeff_trunc']`. Simplify using `[hf0]`. Take `⟨b, hb⟩` from `hdiff 0 z 0 q 0 hz h0 hq hv0`. Conclude with `⟨b, by simpa using hb⟩`. Consider the case `succ n ih`.

Introduce `z q hz hq`. Take `⟨z', hz', q', hq', b, hb⟩` from `hdesc n z q hz hq`. Take `⟨b', hb'⟩` from `ih z' q' hz' hq'`. Use `⟨(p : F.B) ^ n * b + b', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_pow, map_natCast, ← hb, ← hb']`.

Expand and normalize the polynomial expressions, which then agree. Establish `hlift_ex : ∀ n, ∃ z, IsLift n z` using `fun n => ⟨fun i => (hF.surj (t.pt n (c.x n i))).choose, fun i => (hF.surj _).choose_spec⟩`. Use `choose z hz using hlift_ex`. Establish `hq_ex : ∀ n, ∃ q, _root_.GlobalTheory.QLog.HasVal p (z n) f q` using `fun n => (_root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p _ O _ _ hF _ (z n) (hnil n _ (hz n)) f hD).exists`. Use `choose q hq using hq_ex`.

Use `choose r hr using fun n => hint n (z n) (q n) (hz n) (hq n)`. Establish `hstep : ∀ n, (p : F.B) ^ n ∣ r (n + 1) - r n`. Introduce `n`. Take `⟨z', hz', q', hq', b, hb⟩` from `hdesc n (z (n + 1)) (q (n + 1)) (hz _) (hq _)`. Take `⟨b', hb'⟩` from `hdiff n z' (z n) q' (q n) hz' (hz n) hq' (hq n)`.

Use `⟨b + b', hF.inj ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, ← hr, ← hr, map_mul, map_pow, map_natCast, map_add, ← hb, ← hb']`. Expand and normalize the polynomial expressions, which then agree. Establish `hcauchy : ∀ {m n : ℕ}, m ≤ n → r m ≡ r n [SMOD (Ideal.span {(p : F.B)} ^ m • ⊤ : Submodule F.B F.B)]`. Introduce `m n hmn`.

Establish `hdvd : (p : F.B) ^ m ∣ r n - r m`. Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`. Use `(pow_dvd_pow (p : F.B) hmn).trans (hstep n)` as an intermediate fact.

Establish `h` using `dvd_add this ih`. Rewrite `h` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Take `⟨g, hg⟩` from `hdvd`. Rewrite using `[SModEq.sub_mem, _root_.GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists]`. Conclude with `⟨-g, by rw [smul_eq_mul, mul_neg, ← hg]; ring⟩`.

Take `⟨y, hy⟩` from `IsPrecomplete.prec' r hcauchy`. Use `⟨y, (c.hasPeriod_iff hF t f y).2 ?_⟩` and prove the remaining obligations. Introduce `n w hw`. Take `⟨qw, hqw⟩` from `(_root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p _ O _ _ hF _ w (hnil n _ hw) f hD).exists`. Use `⟨qw, hqw, ?_⟩` and prove the remaining obligations.

Take `⟨e, he⟩` from `hdiff n w (z n) qw (q n) hw (hz n) hqw (hq n)`. Take `⟨g, hg⟩` from `_root_.GlobalTheory.CEval.dvd_of_smodEq p n (hy n)`. Use `⟨g + e, ?_⟩` and prove the remaining obligations. Establish `hrn : r n = y + (p : F.B) ^ n * g` using `by rw [← hg]; ring`. Establish `hqw' : qw = q n + algebraMap F.B F.Q e`.

Rewrite using `[← he]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hqw', mul_add, hr n, hrn]`. Simplify using `only [map_add, map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨y, hy⟩` from `hex`. Conclude with `⟨y, hy, fun y' hy' => _root_.GlobalTheory.QLog.Chart.HasPeriod.unique F.frame hy' hy⟩`.
-/
theorem _root_.GlobalTheory.PeriodExists.main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : _root_.GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), ∀ F : _root_.GlobalTheory.QLog.BFrame ε, ∀ (G : _root_.GlobalTheory.PDivGroup p O) (d : ℕ) (c : _root_.GlobalTheory.QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), _root_.GlobalTheory.QLog.IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f : MvPowerSeries (Fin d) F.Q) (t : G.Tate), _root_.GlobalTheory.QLog.QL μ' ⊤ f → ∃! y : F.B, c.HasPeriod F.θ t f y := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hmap f t hf
  have hex : ∃ y, c.HasPeriod F.θ t f y := by
    classical
    have hF := F.frame
    haveI : IsAdicComplete (Ideal.span {(p : F.B)}) F.B :=
      hF.complete
    obtain ⟨hf0, hlin, hcob⟩ := hf
    have hD : _root_.GlobalTheory.QLog.DIn (⊤ : Ideal F.B) f := by
      obtain ⟨s, hs⟩ := (_root_.GlobalTheory.QLog.In.top_iff
        (B := F.B)).1 hcob
      have hadd : ∀ k, subst (Sum.elim (X : Fin d → MvPowerSeries (Fin d) F.B)
          (0 : Fin d → MvPowerSeries (Fin d) F.B)) (μ' k) = X k := fun k =>
        congrFun hlift.unit k
      exact dIn_univ_of_forall_pderiv_integral f (fun i =>
        exists_integral_pderiv_of_integral_cob1_lin hlift.const hadd
          (coeff_single_inr_eq_ite_of_add_id_of_symm hadd hlift.comm)
          (fun i => by obtain ⟨b, -, hb⟩ := hlin i; exact ⟨b, hb⟩) s hs i)
    have hμ0 := hlift.const
    obtain ⟨a, ha⟩ := exists_integral_defect_of_integral_cob1 hμ0 hf0 hcob p
    let IsLift : ℕ → (Fin d → F.B) → Prop := fun n z =>
      ∀ i, F.θ (z i) = t.pt n (c.x n i)
    have hnil : ∀ n z, IsLift n z → ∀ i, ∃ N, (p : F.B) ∣ z i ^ N := by
      intro n z hz i
      obtain ⟨N, o, ho⟩ := c.nil n i
      obtain ⟨b, hb⟩ := hF.surj (t.pt n o)
      obtain ⟨y, -, hy⟩ := hF.pd (z i ^ N - p * b) (by
        rw [map_sub, map_pow, hz i, map_mul, map_natCast, hb, ← map_pow, ho, map_mul,
          map_natCast, sub_self])
      refine ⟨N * p, ?_⟩
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, pow_mul, map_pow]
      have he : Ideal.Quotient.mk (Ideal.span {(p : F.B)}) (z i ^ N) =
          Ideal.Quotient.mk _ (z i ^ N - p * b) := by
        rw [Ideal.Quotient.eq]
        simp [Ideal.mem_span_singleton]
      rw [he, ← map_pow, hy, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    have hdiff : ∀ n z z' q q', IsLift n z → IsLift n z' → _root_.GlobalTheory.QLog.HasVal p z f q →
        _root_.GlobalTheory.QLog.HasVal p z' f q' → ∃ b, q - q' = algebraMap F.B F.Q b := by
      intro n z z' q q' hz hz' hq hq'
      obtain ⟨b, -, b', h⟩ := _root_.GlobalTheory.HasValCong.hasVal_sub_mem p _ O _ _ hF _ z
        (hnil n z hz) (RingHom.ker F.θ) (fun x hx => by
          obtain ⟨y, hy, hxy⟩ := hF.pd x hx
          exact ⟨y, hy, hxy⟩) z' f q q' (fun i => by simp [RingHom.mem_ker, hz i, hz' i]) hD hq hq' 0
      exact ⟨b + (p : F.B) ^ 0 * b', h⟩
    have hdesc : ∀ n z q, IsLift (n + 1) z → _root_.GlobalTheory.QLog.HasVal p z f q →
        ∃ z', IsLift n z' ∧ ∃ q', _root_.GlobalTheory.QLog.HasVal p z' f q' ∧
          ∃ b, (p : F.Q) * q - q' = algebraMap F.B F.Q b := by
      intro n z q hz hq
      have hzn := hnil _ z hz
      obtain ⟨E, hE⟩ := ((_root_.GlobalTheory.CEval.continuous_eval p
        F.B F.B (Fin d) z hzn).1).exists
      have hk := _root_.GlobalTheory.MapNMul.cc_nmul μ' hμ0 p
      have hw : IsLift n (fun i => E (_root_.GlobalTheory.QLog.nmul μ' p i)) := by
        intro i
        rw [theta_eval_eq_tate_pt_ev_of_isEval c F.θ t (n + 1) z hzn E hE hz,
          _root_.GlobalTheory.MapNMul.map_nmul _ _ _ _ _ hμ0]
        have hμc : (fun j => map F.θ (μ' j)) = c.μ := funext hmap
        rw [hμc, _root_.GlobalTheory.NMul.ev_nmul p C v O hv G d c,
          ← G.mulP_res, c.res,
          _root_.GlobalTheory.PDivGroup.TateOver.pt_mulP]
      obtain ⟨q', hq'⟩ := (_root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p _ O _ _ hF _ _
        (hnil n _ hw) f hD).exists
      refine ⟨_, hw, q', hq', E a, ?_⟩
      have h1 := _root_.GlobalTheory.QLog.hasVal_subst p _ O _ _ hF _ z hzn E hE _
        (_root_.GlobalTheory.QLog.nmul μ' p) f q' hk hD hq'
      have h2 := _root_.GlobalTheory.hasVal_map_of_isEval p _ O _ _ hF _ z hzn E hE a
      have h3 := ((_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ _ hF _ z _ _ _ _ h2).1 h1)
      have h4 := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ _ hF _ z f 0 q 0 hq).2.1
        (p : F.Q)
      have hser : map (algebraMap F.B F.Q) a +
          subst (_root_.GlobalTheory.QLog.up F.Q
            (_root_.GlobalTheory.QLog.nmul μ' p)) f = (p : F.Q) • f := by
        rw [ha]; unfold _root_.GlobalTheory.QLog.defect; ring
      rw [hser] at h3
      rw [_root_.GlobalTheory.QLog.HasVal.unique hF h4 h3]
      ring
    have hint : ∀ n z q, IsLift n z → _root_.GlobalTheory.QLog.HasVal p z f q →
        ∃ b, (p : F.Q) ^ n * q = algebraMap F.B F.Q b := by
      intro n
      induction n with
      | zero =>
        intro z q hz hq
        have hx0 : ∀ i, t.pt 0 (c.x 0 i) = 0 := by
          intro i
          have h := G.mulBy_pow_self 0 (c.x 0 i)
          rw [pow_zero] at h
          unfold _root_.GlobalTheory.PDiv.mulBy at h
          simp at h
          rw [h, c.aug]
          simp
        have h0 : IsLift 0 0 := fun i => by simp [hx0]
        have hv0 : _root_.GlobalTheory.QLog.HasVal p (0 : Fin d → F.B) f 0 := by
          intro m
          refine ⟨0, fun N' _ => ⟨0, ?_⟩⟩
          simp only [Pi.zero_apply, map_zero, mul_zero, zero_sub, neg_eq_zero]
          rw [show (fun _ : Fin d => (0 : F.Q)) = 0 from rfl, MvPolynomial.eval_zero]
          show MvPolynomial.coeff 0 _ = 0
          rw [coeff_trunc']
          simp [hf0]
        obtain ⟨b, hb⟩ := hdiff 0 z 0 q 0 hz h0 hq hv0
        exact ⟨b, by simpa using hb⟩
      | succ n ih =>
        intro z q hz hq
        obtain ⟨z', hz', q', hq', b, hb⟩ := hdesc n z q hz hq
        obtain ⟨b', hb'⟩ := ih z' q' hz' hq'
        refine ⟨(p : F.B) ^ n * b + b', ?_⟩
        rw [map_add, map_mul, map_pow, map_natCast, ← hb, ← hb']
        ring
    have hlift_ex : ∀ n, ∃ z, IsLift n z := fun n =>
      ⟨fun i => (hF.surj (t.pt n (c.x n i))).choose,
        fun i => (hF.surj _).choose_spec⟩
    choose z hz using hlift_ex
    have hq_ex : ∀ n, ∃ q, _root_.GlobalTheory.QLog.HasVal p (z n) f q := fun n =>
      (_root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p _ O _ _ hF _ (z n)
        (hnil n _ (hz n)) f hD).exists
    choose q hq using hq_ex
    choose r hr using fun n => hint n (z n) (q n) (hz n) (hq n)
    have hstep : ∀ n, (p : F.B) ^ n ∣ r (n + 1) - r n := by
      intro n
      obtain ⟨z', hz', q', hq', b, hb⟩ := hdesc n (z (n + 1)) (q (n + 1)) (hz _) (hq _)
      obtain ⟨b', hb'⟩ := hdiff n z' (z n) q' (q n) hz' (hz n) hq' (hq n)
      refine ⟨b + b', hF.inj ?_⟩
      rw [map_sub, ← hr, ← hr, map_mul, map_pow, map_natCast, map_add, ← hb, ← hb']
      ring
    have hcauchy : ∀ {m n : ℕ}, m ≤ n → r m ≡ r n
        [SMOD (Ideal.span {(p : F.B)} ^ m • ⊤ : Submodule F.B F.B)] := by
      intro m n hmn
      have hdvd : (p : F.B) ^ m ∣ r n - r m := by
        induction n, hmn using Nat.le_induction with
        | base => simp
        | succ n hmn ih =>
          have := (pow_dvd_pow (p : F.B) hmn).trans (hstep n)
          have h := dvd_add this ih
          rwa [sub_add_sub_cancel] at h
      obtain ⟨g, hg⟩ := hdvd
      rw [SModEq.sub_mem, _root_.GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists]
      exact ⟨-g, by rw [smul_eq_mul, mul_neg, ← hg]; ring⟩
    obtain ⟨y, hy⟩ := IsPrecomplete.prec' r hcauchy
    refine ⟨y, (c.hasPeriod_iff hF t f y).2 ?_⟩
    intro n w hw
    obtain ⟨qw, hqw⟩ := (_root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p _ O _ _ hF _ w
      (hnil n _ hw) f hD).exists
    refine ⟨qw, hqw, ?_⟩
    obtain ⟨e, he⟩ := hdiff n w (z n) qw (q n) hw (hz n) hqw (hq n)
    obtain ⟨g, hg⟩ := _root_.GlobalTheory.CEval.dvd_of_smodEq p n (hy n)
    refine ⟨g + e, ?_⟩
    have hrn : r n = y + (p : F.B) ^ n * g := by rw [← hg]; ring
    have hqw' : qw = q n + algebraMap F.B F.Q e := by
      rw [← he]; ring
    rw [hqw', mul_add, hr n, hrn]
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  obtain ⟨y, hy⟩ := hex
  exact ⟨y, hy, fun y' hy' =>
    _root_.GlobalTheory.QLog.Chart.HasPeriod.unique
      F.frame hy' hy⟩

end GlobalTheory.PeriodExists
