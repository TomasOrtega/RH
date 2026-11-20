import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.SmoothEnd

/- English proof (translation)
Introduce `O _ bar X _ _ x y hx hy px py b hb h`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Conclude with `not_isPrim_zero (bar := bar) py`. Choose the witnesses or unpack the hypotheses as in `⟨a, c, hac⟩ : ∃ a c, y a c ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hy0 (LinearMap.ext₂ hc)`. Establish `hR : ∀ u v, (x u v : ℝ) = b * (y u v : ℝ)` using `fun u v => by`. Use `LinearMap.congr_fun₂ h u v` as an intermediate fact.

Simplify `this` using `[toReal_apply]`. Establish `hacR : (y a c : ℝ) ≠ 0` using `by exact_mod_cast hac`. Establish `hxac : x a c ≠ 0`. Establish `: (x a c : ℝ) ≠ 0` using `by rw [hR]; exact mul_ne_zero hb.ne' hacR`. Conclude with `this` after adjusting the coercions.

Establish `habs : |(x a c : ℝ)| = b * |(y a c : ℝ)|`. Rewrite using `[hR, abs_mul, abs_of_pos hb]`. Use `eq_of_isPrim hx hy px py (k := (y a c).natAbs) (n := (x a c).natAbs) (Int.natAbs_pos.2 hac) (Int.natAbs_pos.2 hxac) (LinearMap.ext₂ fun u v => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, Int.natCast_natAbs]`. Establish `e : |(y a c : ℝ)| * (x u v : ℝ) = |(x a c : ℝ)| * (y u v : ℝ)`.

Rewrite using `[hR u v, habs]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `e` after adjusting the coercions.
-/
theorem eq_of_isPrim_of_toReal_eq_smul : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (x y : LinearMap.BilinForm ℤ X)
    (hx : x ∈ balForms bar X) (hy : y ∈ balForms bar X), IsPrim bar (⟨x, hx⟩ : balForms bar X) →
    IsPrim bar (⟨y, hy⟩ : balForms bar X) → ∀ b : ℝ, 0 < b → toReal x = b • toReal y → x = y := by
  intro O _ bar X _ _ x y hx hy px py b hb h
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact not_isPrim_zero (bar := bar) py
  obtain ⟨a, c, hac⟩ : ∃ a c, y a c ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy0 (LinearMap.ext₂ hc)
  have hR : ∀ u v, (x u v : ℝ) = b * (y u v : ℝ) := fun u v => by
    have := LinearMap.congr_fun₂ h u v
    simpa [toReal_apply] using this
  have hacR : (y a c : ℝ) ≠ 0 := by exact_mod_cast hac
  have hxac : x a c ≠ 0 := by
    have : (x a c : ℝ) ≠ 0 := by rw [hR]; exact mul_ne_zero hb.ne' hacR
    exact_mod_cast this
  have habs : |(x a c : ℝ)| = b * |(y a c : ℝ)| := by
    rw [hR, abs_mul, abs_of_pos hb]
  refine eq_of_isPrim hx hy px py (k := (y a c).natAbs) (n := (x a c).natAbs)
    (Int.natAbs_pos.2 hac) (Int.natAbs_pos.2 hxac) (LinearMap.ext₂ fun u v => ?_)
  simp only [LinearMap.smul_apply, smul_eq_mul, Int.natCast_natAbs]
  have e : |(y a c : ℝ)| * (x u v : ℝ) = |(x a c : ℝ)| * (y u v : ℝ) := by
    rw [hR u v, habs]; ring
  exact_mod_cast e

end GlobalTheory.PolFan.SmoothEnd
