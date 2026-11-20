import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Establish `mem : ∀ (g : Q →+* C), J.map (g.comp i) ≤ JC → ∀ (n : ℕ) (y : Q), y ∈ (J ^ n).map i → g y ∈ JC ^ n`. Introduce `g hg n y hy`. Establish `h1 : g y ∈ ((J ^ n).map i).map g` using `Ideal.mem_map_of_mem g hy`. Rewrite `h1` using `[Ideal.map_map, Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hg n h1`.

Establish `hJ' : J.map (h'.comp i) ≤ JC` using `by rwa [← he]`. Use extensionality with `x`. Rewrite using `[← sub_eq_zero]`. Apply `hH.haus` to reduce the goal to its premises. Introduce `n`.

Take `⟨a, ha⟩` from `hc.surj x n`. Establish `e1 : h x - h' x = h (x - i a) - h' (x - i a)`. Establish `: h (i a) = h' (i a)` using `RingHom.congr_fun he a`. Simplify using `only [map_sub, this]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[SModEq.zero, e1, smul_eq_mul, Ideal.mul_top]`. Conclude with `Ideal.sub_mem _ (mem h hJ n _ ha) (mem h' hJ' n _ ha)`.
-/
theorem ringHom_eq_of_isCompl (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C]
    (i : L →+* Q) (J : Ideal L) (JC : Ideal C) (hc : IsCompl i J) (hH : IsHausdorff JC C)
    (h h' : Q →+* C) (hJ : J.map (h.comp i) ≤ JC) (he : h.comp i = h'.comp i) : h = h' := by
  have mem : ∀ (g : Q →+* C), J.map (g.comp i) ≤ JC → ∀ (n : ℕ) (y : Q), y ∈ (J ^ n).map i → g y ∈ JC ^ n := by
    intro g hg n y hy
    have h1 : g y ∈ ((J ^ n).map i).map g := Ideal.mem_map_of_mem g hy
    rw [Ideal.map_map, Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hg n h1
  have hJ' : J.map (h'.comp i) ≤ JC := by rwa [← he]
  ext x
  rw [← sub_eq_zero]
  apply hH.haus
  intro n
  obtain ⟨a, ha⟩ := hc.surj x n
  have e1 : h x - h' x = h (x - i a) - h' (x - i a) := by
    have : h (i a) = h' (i a) := RingHom.congr_fun he a
    simp only [map_sub, this]; ring
  rw [SModEq.zero, e1, smul_eq_mul, Ideal.mul_top]
  exact Ideal.sub_mem _ (mem h hJ n _ ha) (mem h' hJ' n _ ha)

/- English proof (translation)
Introduce `L _ Q _ C _ i J JC hc hH h h' hJ he` and use `ringHom_eq_of_isCompl L Q C i J JC hc hH h h' hJ he`.
-/
example : ∀ (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (i : L →+* Q) (J : Ideal L) (JC : Ideal C), IsCompl i J → IsHausdorff JC C → ∀ (h h' : Q →+* C), J.map (h.comp i) ≤ JC → h.comp i = h'.comp i → h = h' :=
  fun L _ Q _ C _ i J JC hc hH h h' hJ he => ringHom_eq_of_isCompl L Q C i J JC hc hH h h' hJ he

end GlobalTheory.BSP
