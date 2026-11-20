import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnGramSchmidtUpperTriangularFactorStatement
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

/- English proof (translation)
Take `⟨R, hR, hball⟩` from `exists_ball X hx`. Establish `hnhds : {w | cpt X x w ∈ X.dom} ∈ nhds (0 : V (nd X))` using `Filter.mem_of_superset (Metric.ball_mem_nhds 0 hR) fun w hw => hball w hw`. Establish `hB : ∀ τ k b, ContDiffAt ℝ ∞ (fun w => gsB X w τ k b) 0` using `fun τ k b => (GlobalTheory.T.contDiffOn_gramSchmidtUpperTriangularFactor X hx τ k b).contDiffAt hnhds`. Establish `hN : ∀ τ a k, ContDiffAt ℝ ∞ (fun w : V (nd X) => nmat X w τ a k) 0` using `fun τ a k =>`. Establish `h1 : ContDiff ℂ ∞ (fun w : V (nd X) => nmat X w τ a k)`.

Unfold `nmat`. Use `split_ifs`. Conclude with `((EuclideanSpace.proj _ : V (nd X) →L[ℂ] ℂ)).contDiff`. Conclude with `contDiff_const`. Conclude with `contDiff_const`.

Use the proof step `(h1.restrict_scalars ℝ).contDiffAt`. Establish `hY : ContDiffAt ℝ ∞ (yF X) 0`. Rewrite using `[contDiffAt_pi]`. Introduce `τ`. Rewrite using `[contDiffAt_pi]`.

Introduce `a`. Rewrite using `[contDiffAt_pi]`. Introduce `b`. Use `show ContDiffAt ℝ ∞ (fun w => (mat (nmat X w) τ * gsB X w τ) a b) 0`. Simplify using `only [Matrix.mul_apply]`.

Use `ContDiffAt.sum fun k _ => ?_` and prove the remaining obligations. Conclude with `(hN τ a k).mul (hB τ k b)`. Conclude with `hY.hasStrictFDerivAt (by simp)`.
-/
theorem yF_hasStrictFDerivAt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : IsOrth X x) : HasStrictFDerivAt (yF X) (dY X) 0 := by
  obtain ⟨R, hR, hball⟩ := exists_ball X hx
  have hnhds : {w | cpt X x w ∈ X.dom} ∈ nhds (0 : V (nd X)) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hR) fun w hw => hball w hw
  have hB : ∀ τ k b, ContDiffAt ℝ ∞ (fun w => gsB X w τ k b) 0 := fun τ k b =>
    (GlobalTheory.T.contDiffOn_gramSchmidtUpperTriangularFactor X hx τ k b).contDiffAt hnhds
  have hN : ∀ τ a k, ContDiffAt ℝ ∞ (fun w : V (nd X) => nmat X w τ a k) 0 := fun τ a k =>
    have h1 : ContDiff ℂ ∞ (fun w : V (nd X) => nmat X w τ a k) := by
      unfold nmat
      split_ifs
      · exact ((EuclideanSpace.proj _ : V (nd X) →L[ℂ] ℂ)).contDiff
      · exact contDiff_const
      · exact contDiff_const
    (h1.restrict_scalars ℝ).contDiffAt
  have hY : ContDiffAt ℝ ∞ (yF X) 0 := by
    rw [contDiffAt_pi]; intro τ
    rw [contDiffAt_pi]; intro a
    rw [contDiffAt_pi]; intro b
    show ContDiffAt ℝ ∞ (fun w => (mat (nmat X w) τ * gsB X w τ) a b) 0
    simp only [Matrix.mul_apply]
    refine ContDiffAt.sum fun k _ => ?_
    exact (hN τ a k).mul (hB τ k b)
  exact hY.hasStrictFDerivAt (by simp)

end GlobalTheory.SUChartSection
