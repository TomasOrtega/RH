import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bridge
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Homothety

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive LinkPer KroneckerLimit DedekindFactor)
open Formalism.MainNotions.TaylorLogMetric (lamConj lamOf embT meanLogOm DataIn tor0 IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice per22 logOmVal)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem g2_smul_lattice (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) : g2 (c • Λ) = (c ^ 4)⁻¹ * g2 Λ := by
  unfold g2; rw [eisG_smul Λ c hc]; ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem g3_smul_lattice (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) : g3 (c • Λ) = (c ^ 6)⁻¹ * g3 Λ := by
  unfold g3; rw [eisG_smul Λ c hc]; ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities.
-/
theorem br_jL_smul (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) : jL (c • Λ) = jL Λ := by
  rw [br_jL_eq, br_jL_eq, g2_smul_lattice Λ c hc, discr_smul Λ c hc]
  have h12 : (c ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hc)
  have : 1728 * ((c ^ 4)⁻¹ * g2 Λ) ^ 3 = (c ^ 12)⁻¹ * (1728 * g2 Λ ^ 3) := by
    rw [mul_pow, inv_pow, ← pow_mul]; ring
  rw [this, mul_div_mul_left _ _ h12]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem br_exists_sq_inv (u : ℂ) (hu : u ≠ 0) : ∃ c : ℂ, c ≠ 0 ∧ (c ^ 2)⁻¹ = u := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (by norm_num : 0 < 2)
  refine ⟨c, ?_, by rw [hc, inv_inv]⟩
  rintro rfl; simp at hc; exact hu hc.symm

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion. Reduce the argument to an intermediate assertion. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem br_exists_scale (Λ₀ : AddSubgroup ℂ) (h0 : discr Λ₀ ≠ 0) (a b : ℂ)
    (hab : a ^ 3 - 27 * b ^ 2 ≠ 0) (hj : 1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2) = jL Λ₀) :
    ∃ c : ℂ, c ≠ 0 ∧ g2 (c • Λ₀) = a ∧ g3 (c • Λ₀) = b := by
  rw [br_jL_eq] at hj
  set G := g2 Λ₀ with hG
  set H := g3 Λ₀ with hH
  have hD : discr Λ₀ = G ^ 3 - 27 * H ^ 2 := rfl
  rw [hD] at hj h0
  have key : a ^ 3 * H ^ 2 = G ^ 3 * b ^ 2 := by
    rw [div_eq_div_iff hab h0] at hj
    linear_combination -hj / 46656

  suffices hu : ∃ u : ℂ, u ≠ 0 ∧ u ^ 2 * G = a ∧ u ^ 3 * H = b by
    obtain ⟨u, hu0, hua, hub⟩ := hu
    obtain ⟨c, hc0, hcu⟩ := br_exists_sq_inv u hu0
    refine ⟨c, hc0, ?_, ?_⟩
    · rw [g2_smul_lattice Λ₀ c hc0, ← hG, ← hua, ← hcu]; ring
    · rw [g3_smul_lattice Λ₀ c hc0, ← hH, ← hub, ← hcu]; ring
  by_cases hG0 : G = 0
  · have hH0 : H ≠ 0 := by rintro hH0; apply h0; rw [hG0, hH0]; ring
    have ha : a = 0 := by
      rw [hG0] at key
      have : a ^ 3 * H ^ 2 = 0 := by rw [key]; ring
      rcases mul_eq_zero.1 this with h | h
      · exact pow_eq_zero_iff (by norm_num) |>.1 h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h) hH0
    have hb : b ≠ 0 := by rintro rfl; apply hab; rw [ha]; ring
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (b / H) (by norm_num : 0 < 3)
    refine ⟨u, ?_, by rw [hG0, ha]; ring, by rw [hu]; field_simp⟩
    rintro rfl; simp at hu; exact (div_ne_zero hb hH0) hu.symm
  by_cases hH0 : H = 0
  · have hb : b = 0 := by
      rw [hH0] at key
      have : G ^ 3 * b ^ 2 = 0 := by rw [← key]; ring
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h) hG0
      · exact pow_eq_zero_iff (by norm_num) |>.1 h
    have ha : a ≠ 0 := by rintro rfl; apply hab; rw [hb]; ring
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (a / G) (by norm_num : 0 < 2)
    refine ⟨u, ?_, by rw [hu]; field_simp, by rw [hH0, hb]; ring⟩
    rintro rfl; simp at hu; exact (div_ne_zero ha hG0) hu.symm
  have ha : a ≠ 0 := by
    rintro rfl
    have : G ^ 3 * b ^ 2 = 0 := by rw [← key]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact hG0 (pow_eq_zero_iff (by norm_num) |>.1 h)
    · apply hab; rw [pow_eq_zero_iff (by norm_num) |>.1 h]; ring
  have hb : b ≠ 0 := by
    rintro rfl
    have : a ^ 3 * H ^ 2 = 0 := by rw [key]; ring
    rcases mul_eq_zero.1 this with h | h
    · apply hab; rw [pow_eq_zero_iff (by norm_num) |>.1 h]; ring
    · exact hH0 (pow_eq_zero_iff (by norm_num) |>.1 h)
  refine ⟨b * G / (a * H), div_ne_zero (mul_ne_zero hb hG0) (mul_ne_zero ha hH0), ?_, ?_⟩
  · rw [div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ (mul_ne_zero ha hH0))]
    linear_combination -key
  · rw [div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ (mul_ne_zero ha hH0))]
    linear_combination (-b * H) * key

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
