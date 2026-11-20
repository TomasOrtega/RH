import Formalism.UnipotentAdelicQuotients.EllRegCut

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simpa [dw] using h`. Consider the case `cons j w ih => filter_upwards [ih.fderiv (𝕜 := ℝ)] with x hx show fderiv ℝ (dw w f) x (ev j) = fderiv ℝ (dw w f') x (ev j)`. Rewrite using `[hx]`.
-/
lemma dw_eventuallyEq {d : ℕ} (w : List (Fin d)) {f f' : E d → ℂ} {y : E d} (h : f =ᶠ[𝓝 y] f') :
    dw w f =ᶠ[𝓝 y] dw w f' := by
  induction w with
  | nil => simpa [dw] using h
  | cons j w ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with x hx
    show fderiv ℝ (dw w f) x (ev j) = fderiv ℝ (dw w f') x (ev j)
    rw [hx]

/- English proof (translation)
Introduce `d m b b' g φ V hV hg hb`. Use `congr 1`. Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y ∈ V`. Use `congr 1`.

Unfold `trOp`. Use `Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `hev : (fun y => b n w y * φ y) =ᶠ[𝓝 y] (fun y => b' n w y * φ y)` using `by filter_upwards [hV.mem_nhds hy] with z hz`. Rewrite using `[hb n w z hz]`.

Conclude with `(dw_eventuallyEq _ hev).eq_of_nhds`. Establish `hg0 : g y = 0` using `by first`. Consider the case `exact image_eq_zero_of_nmem_tsupport (fun h => hy (hg h))`. Consider the case `exact image_eq_zero_of_notMem_tsupport (fun h => hy (hg h))`. Rewrite using `[hg0, zero_mul, zero_mul]`.
-/
theorem adjointPairingLocal : PairingLocal := by
  intro d m b b' g φ V hV hg hb
  congr 1
  funext y
  by_cases hy : y ∈ V
  · congr 1
    unfold trOp
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
    congr 1

    have hev : (fun y => b n w y * φ y) =ᶠ[𝓝 y] (fun y => b' n w y * φ y) := by
      filter_upwards [hV.mem_nhds hy] with z hz
      rw [hb n w z hz]
    exact (dw_eventuallyEq _ hev).eq_of_nhds
  · have hg0 : g y = 0 := by
      first
        | exact image_eq_zero_of_nmem_tsupport (fun h => hy (hg h))
        | exact image_eq_zero_of_notMem_tsupport (fun h => hy (hg h))
    rw [hg0, zero_mul, zero_mul]

end ZetaZeros.D.EllReg
