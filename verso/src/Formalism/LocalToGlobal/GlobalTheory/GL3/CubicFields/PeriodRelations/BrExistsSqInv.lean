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
Unfold `g2`. Rewrite using `[eisG_smul Λ c hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem g2_smul_lattice (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) : g2 (c • Λ) = (c ^ 4)⁻¹ * g2 Λ := by
  unfold g2; rw [eisG_smul Λ c hc]; ring

/- English proof (translation)
Unfold `g3`. Rewrite using `[eisG_smul Λ c hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem g3_smul_lattice (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) : g3 (c • Λ) = (c ^ 6)⁻¹ * g3 Λ := by
  unfold g3; rw [eisG_smul Λ c hc]; ring

/- English proof (translation)
Rewrite using `[br_jL_eq, br_jL_eq, g2_smul_lattice Λ c hc, discr_smul Λ c hc]`. Establish `h12 : (c ^ 12)⁻¹ ≠ 0` using `inv_ne_zero (pow_ne_zero _ hc)`. Establish `: 1728 * ((c ^ 4)⁻¹ * g2 Λ) ^ 3 = (c ^ 12)⁻¹ * (1728 * g2 Λ ^ 3)`. Rewrite using `[mul_pow, inv_pow, ← pow_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, mul_div_mul_left _ _ h12]`.
-/
theorem br_jL_smul (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) : jL (c • Λ) = jL Λ := by
  rw [br_jL_eq, br_jL_eq, g2_smul_lattice Λ c hc, discr_smul Λ c hc]
  have h12 : (c ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hc)
  have : 1728 * ((c ^ 4)⁻¹ * g2 Λ) ^ 3 = (c ^ 12)⁻¹ * (1728 * g2 Λ ^ 3) := by
    rw [mul_pow, inv_pow, ← pow_mul]; ring
  rw [this, mul_div_mul_left _ _ h12]

/- English proof (translation)
Take `⟨c, hc⟩` from `IsAlgClosed.exists_pow_nat_eq u⁻¹ (by norm_num : 0 < 2)`. Use `⟨c, ?_, by rw [hc, inv_inv]⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at hc`. Conclude with `hu hc.symm`.
-/
theorem br_exists_sq_inv (u : ℂ) (hu : u ≠ 0) : ∃ c : ℂ, c ≠ 0 ∧ (c ^ 2)⁻¹ = u := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (by norm_num : 0 < 2)
  refine ⟨c, ?_, by rw [hc, inv_inv]⟩
  rintro rfl; simp at hc; exact hu hc.symm

/- English proof (translation)
Rewrite `hj` using `[br_jL_eq]`. Use `set G := g2 Λ₀ with hG`. Use `set H := g3 Λ₀ with hH`. Establish `hD : discr Λ₀ = G ^ 3 - 27 * H ^ 2` using `rfl`. Rewrite `hj`, `h0` using `[hD]`.

Establish `key : a ^ 3 * H ^ 2 = G ^ 3 * b ^ 2`. Rewrite `hj` using `[div_eq_div_iff hab h0]`. Take the linear combination `-hj / 46656`. It suffices to establish `hu : ∃ u : ℂ, u ≠ 0 ∧ u ^ 2 * G = a ∧ u ^ 3 * H = b by`. Take `⟨u, hu0, hua, hub⟩` from `hu`.

Take `⟨c, hc0, hcu⟩` from `br_exists_sq_inv u hu0`. Use `⟨c, hc0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[g2_smul_lattice Λ₀ c hc0, ← hG, ← hua, ← hcu]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[g3_smul_lattice Λ₀ c hc0, ← hH, ← hub, ← hcu]`.

Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hG0 : G = 0`. Establish `hH0 : H ≠ 0` using `by rintro hH0; apply h0; rw [hG0, hH0]; ring`. Establish `ha : a = 0`. Rewrite `key` using `[hG0]`.

Establish `: a ^ 3 * H ^ 2 = 0` using `by rw [key]; ring`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `pow_eq_zero_iff (by norm_num) |>.1 h`. Conclude with `absurd (pow_eq_zero_iff (by norm_num) |>.1 h) hH0`. Establish `hb : b ≠ 0` using `by rintro rfl; apply hab; rw [ha]; ring`.

Take `⟨u, hu⟩` from `IsAlgClosed.exists_pow_nat_eq (b / H) (by norm_num : 0 < 3)`. Use `⟨u, ?_, by rw [hG0, ha]; ring, by rw [hu]; field_simp⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at hu`. Conclude with `(div_ne_zero hb hH0) hu.symm`.

Distinguish the cases in `hH0 : H = 0`. Establish `hb : b = 0`. Rewrite `key` using `[hH0]`. Establish `: G ^ 3 * b ^ 2 = 0` using `by rw [← key]; ring`. Break down `mul_eq_zero.1 this with h | h` into its components or cases.

Conclude with `absurd (pow_eq_zero_iff (by norm_num) |>.1 h) hG0`. Conclude with `pow_eq_zero_iff (by norm_num) |>.1 h`. Establish `ha : a ≠ 0` using `by rintro rfl; apply hab; rw [hb]; ring`. Take `⟨u, hu⟩` from `IsAlgClosed.exists_pow_nat_eq (a / G) (by norm_num : 0 < 2)`. Use `⟨u, ?_, by rw [hu]; field_simp, by rw [hH0, hb]; ring⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Simplify using `at hu`. Conclude with `(div_ne_zero ha hG0) hu.symm`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`.

Establish `: G ^ 3 * b ^ 2 = 0` using `by rw [← key]; ring`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `hG0 (pow_eq_zero_iff (by norm_num) |>.1 h)`. Apply `hab; rw [pow_eq_zero_iff (by norm_num) |>.1 h]; ring` to reduce the goal to its premises. Establish `hb : b ≠ 0`.

Introduce and unpack `rfl`. Establish `: a ^ 3 * H ^ 2 = 0` using `by rw [key]; ring`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Apply `hab; rw [pow_eq_zero_iff (by norm_num) |>.1 h]; ring` to reduce the goal to its premises. Conclude with `hH0 (pow_eq_zero_iff (by norm_num) |>.1 h)`.

Use `⟨b * G / (a * H), div_ne_zero (mul_ne_zero hb hG0) (mul_ne_zero ha hH0), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ (mul_ne_zero ha hH0))]`. Take the linear combination `-key`. Rewrite using `[div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ (mul_ne_zero ha hH0))]`. Take the linear combination `(-b * H) * key`.
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
