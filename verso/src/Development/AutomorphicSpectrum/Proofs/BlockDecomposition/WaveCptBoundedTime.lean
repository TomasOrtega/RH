import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

/- English proof (translation)
Establish `hdx : x.det ≠ 0` using `hx`. Establish `hdy : y.det ≠ 0` using `hy`. Establish `hxy : x * y ∈ GLs n`. Express the relevant statement in the definitionally equal form `(x * y).det ≠ 0`. Rewrite using `[Matrix.det_mul]`.

Conclude with `mul_ne_zero hdx hdy`. Establish `hu : IsUnit y.det` using `isUnit_iff_ne_zero.mpr hdy`. Establish `h1` using `(hL n).1 (x * y) hxy y⁻¹ (inv_mem_GLs hy)`. Establish `h2` using `(hL n).2.1 y hy`. Rewrite `h1` using `[Matrix.mul_nonsing_inv_cancel_right _ _ hu, h2]`.

Conclude with `h1`.
-/
theorem lg_le_lg_mul_add (hL : LgFacts) {n : ℕ} {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) :
    lg x ≤ lg (x * y) + lg y := by
  have hdx : x.det ≠ 0 := hx
  have hdy : y.det ≠ 0 := hy
  have hxy : x * y ∈ GLs n := by
    change (x * y).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hdx hdy
  have hu : IsUnit y.det := isUnit_iff_ne_zero.mpr hdy
  have h1 := (hL n).1 (x * y) hxy y⁻¹ (inv_mem_GLs hy)
  have h2 := (hL n).2.1 y hy
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ hu, h2] at h1
  exact h1

/- English proof (translation)
Introduce `hL hS n E u hu hc T`. Take `⟨c, hc'⟩` from `hS n`. Take `⟨R₀, hR₀⟩` from `hc`. Use `⟨R₀ + |c| * (1 + |T|), fun t ht x hx hlg => hc' E u hu t x hx fun y hy hly => ?_⟩` and prove the remaining obligations. Establish `hxy : x * y ∈ GLs n`.

Express the relevant statement in the definitionally equal form `(x * y).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero hx hy`. Use `hR₀ (x * y) hxy ?_` and prove the remaining obligations. Establish `h1` using `lg_le_lg_mul_add hL hx hy`.

Establish `h2 : |t| ≤ |T|` using `ht.trans (le_abs_self T)`. Establish `h3 : c * (1 + |t|) ≤ |c| * (1 + |T|)`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem wave_cpt_bounded_time : LgFacts → WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V),
    IsWave E u → Cpt (u 0) → ∀ T : ℝ, ∃ R : ℝ, ∀ t, |t| ≤ T → ∀ y ∈ GLs n, R < lg y → u t y = 0 := by
  intro hL hS n E u hu hc T
  obtain ⟨c, hc'⟩ := hS n
  obtain ⟨R₀, hR₀⟩ := hc
  refine ⟨R₀ + |c| * (1 + |T|), fun t ht x hx hlg => hc' E u hu t x hx fun y hy hly => ?_⟩
  have hxy : x * y ∈ GLs n := by
    change (x * y).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hx hy
  refine hR₀ (x * y) hxy ?_
  have h1 := lg_le_lg_mul_add hL hx hy
  have h2 : |t| ≤ |T| := ht.trans (le_abs_self T)
  have h3 : c * (1 + |t|) ≤ |c| * (1 + |T|) :=
    calc c * (1 + |t|) ≤ |c| * (1 + |t|) :=
          mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
      _ ≤ |c| * (1 + |T|) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
  linarith

end GlobalTheory.CompanionTheory.WaveMult
