import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveCountLower
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveDegreeVert
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertIndex
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveIndexLinear
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxCount
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsIsSheetFinZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

/- English proof (translation)
Introduce `K _ ι _ Ω _ y A II hII hP hB hS hC`. Take `⟨c, hcX, hc⟩` from `exists_chart hP`. Take `⟨R, hRP, hRu, -⟩` from `regularityPointsSum_holds.proof K ι _ hP`. Use `set b : K → ℕ := fun k => (A.a k).natAbs with hb`. Use `set d : K → ℕ := fun k => (A.a k + b k).toNat with hd'`.

Establish `hd : ∀ k, (d k : ℤ) = A.a k + b k` using `fun k => Int.toNat_of_nonneg (by simp only [hb]; omega)`. Establish `h1` using `hD K ι _ A II c R b d hII hP hS hcX hRP hRu hd`. Establish `h2` using `hV K ι Ω y _ d hP (isMultiHomog_curveChartMono c d) (curveChartMono_notMem hc d)`. Establish `h3` using `hV K ι Ω y _ b hP (isMultiHomog_curveChartMono c b) (curveChartMono_notMem hc b)`. Rewrite `h2`, `h3` using `[aeval_curveChartMono]`.

Take `⟨hadd, hpow⟩` from `hL K ι Ω y c hP hc`. Establish `h4` using `hadd A.a (fun k => (b k : ℤ))`. Rewrite `h4` using `[show A.a + (fun k => (b k : ℤ)) = fun k => (d k : ℤ) from funext fun k => (hd k).symm]`. Establish `hI : II K ι (mCoordIdeal y) 1 (fun _ => A) = chartIndexLog y c A.a 1 + ∑ t ∈ R, Real.log (chartRadius A c t)`. Establish `e2 : vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c d) = chartIndexLog y c (fun k => (d k : ℤ)) 1` using `h2`.

Establish `e3 : vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c b) = chartIndexLog y c (fun k => (b k : ℤ)) 1` using `h3`. Rewrite using `[h1, e2, e3, h4]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨C, hCC⟩` from `hN K ι Ω y A c R hP hB hC hc hRP hRu`. Use `⟨C, fun τ hτ => ?_⟩` and prove the remaining obligations.

Establish `h5` using `hCC τ hτ`. Rewrite `h5` using `[hpow A.a τ]`. Rewrite using `[hI]`. Combine the linear relations using `[mul_add (τ : ℝ) (chartIndexLog y c A.a 1) (∑ t ∈ R, Real.log (chartRadius A c t))]`.
-/
theorem CurveCountLower.proof (hD : CurveDegreeVert.Statement) (hV : CurveVertIndex.Statement)
    (hL : CurveIndexLinear.Statement) (hN : CurveBoxCount.Statement) : CurveCountLower.Statement := by
  intro K _ ι _ Ω _ y A II hII hP hB hS hC
  obtain ⟨c, hcX, hc⟩ := exists_chart hP
  obtain ⟨R, hRP, hRu, -⟩ := regularityPointsSum_holds.proof K ι _ hP
  set b : K → ℕ := fun k => (A.a k).natAbs with hb
  set d : K → ℕ := fun k => (A.a k + b k).toNat with hd'
  have hd : ∀ k, (d k : ℤ) = A.a k + b k := fun k =>
    Int.toNat_of_nonneg (by simp only [hb]; omega)
  have h1 := hD K ι _ A II c R b d hII hP hS hcX hRP hRu hd
  have h2 := hV K ι Ω y _ d hP (isMultiHomog_curveChartMono c d) (curveChartMono_notMem hc d)
  have h3 := hV K ι Ω y _ b hP (isMultiHomog_curveChartMono c b) (curveChartMono_notMem hc b)
  rw [aeval_curveChartMono] at h2 h3
  obtain ⟨hadd, hpow⟩ := hL K ι Ω y c hP hc
  have h4 := hadd A.a (fun k => (b k : ℤ))
  rw [show A.a + (fun k => (b k : ℤ)) = fun k => (d k : ℤ) from funext fun k => (hd k).symm] at h4
  have hI : II K ι (mCoordIdeal y) 1 (fun _ => A) =
      chartIndexLog y c A.a 1 + ∑ t ∈ R, Real.log (chartRadius A c t) := by
    have e2 : vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c d) =
        chartIndexLog y c (fun k => (d k : ℤ)) 1 := h2
    have e3 : vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c b) =
        chartIndexLog y c (fun k => (b k : ℤ)) 1 := h3
    rw [h1, e2, e3, h4]
    ring
  obtain ⟨C, hCC⟩ := hN K ι Ω y A c R hP hB hC hc hRP hRu
  refine ⟨C, fun τ hτ => ?_⟩
  have h5 := hCC τ hτ
  rw [hpow A.a τ] at h5
  rw [hI]
  linarith [mul_add (τ : ℝ) (chartIndexLog y c A.a 1) (∑ t ∈ R, Real.log (chartRadius A c t))]

end GroundTheory.Heights₂.Heights.Targets
