import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

/- English proof (translation)
Use `Filter.eventually_all.2 fun k => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `hz k`. Conclude with `((continuous_apply (⟨k, i⟩ : Σ k, ι k)).continuousAt.eventually_ne hi).mono fun w hw => ⟨i, hw⟩`.
-/
theorem eventually_blocks_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ᶠ w in 𝓝 z, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := by
  refine Filter.eventually_all.2 fun k => ?_
  obtain ⟨i, hi⟩ := hz k
  exact ((continuous_apply (⟨k, i⟩ : Σ k, ι k)).continuousAt.eventually_ne hi).mono fun w hw => ⟨i, hw⟩

/- English proof (translation)
Establish `h2 : fderiv ℝ (fderiv ℝ φ) z = fderiv ℝ (fderiv ℝ ψ) z`. Establish `h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ` using `h.fderiv.trans (Eventually.of_forall fun x => fderiv_add_const c)`. Conclude with `h1.fderiv_eq`. Unfold `leviForm`. Rewrite using `[h2]`.
-/
theorem leviForm_congr_add_const {N : Type} [Fintype N] {φ ψ : (N → ℂ) → ℝ} {z : N → ℂ} (c : ℝ)
    (h : φ =ᶠ[𝓝 z] fun w => ψ w + c) (w : N → ℂ) : leviForm φ z w = leviForm ψ z w := by
  have h2 : fderiv ℝ (fderiv ℝ φ) z = fderiv ℝ (fderiv ℝ ψ) z := by
    have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ :=
      h.fderiv.trans (Eventually.of_forall fun x => fderiv_add_const c)
    exact h1.fderiv_eq
  unfold leviForm
  rw [h2]

/- English proof (translation)
Introduce `K _ ι _ Ω _ F _ _ _ y D a A P0 II Λ hD hII hvar hbir ha hP0 hsemi hconj hΛ hΛc huniq hmon`. Take `⟨B, hBa, hBs, hBc, hBloc⟩` from `hW K ι Ω F y Λ hΛ hΛc huniq`. Establish `hA' : (A.tensor B).a = fun k => (a k : ℤ)`. Rewrite using `[show (A.tensor B).a = A.a + B.a from rfl, ha, hBa, add_zero]`. Establish `hsemi' : IsSemipositiveRel P0 (mCoordIdeal y) (A.tensor B)`.

Use `⟨hsemi.1.mul hBs, fun z hz w hw => ?_⟩` and prove the remaining obligations. Take `⟨sg, hsg, -⟩` from `huniq z hz`. Establish `hev : (fun x => Real.log ((A.tensor B).h x)) =ᶠ[𝓝 z] fun x => Real.log (A.h x) + Real.log (Λ sg)` using `by filter_upwards [hBloc z hz sg hsg, eventually_blocks_ne_zero hz.1] with x h1 h2`. Rewrite using `[show (A.tensor B).h x = A.h x * B.h x from rfl, h1, Real.log_mul (A.pos x h2).ne' (hΛ sg).ne']`. Rewrite using `[leviForm_congr_add_const _ hev]`.

Conclude with `hsemi.2 z hz w hw`. Establish `hconj' : IsConjInvariantH (A.tensor B)` using `fun z => by show A.h _ * B.h _ = A.h z * B.h z`. Rewrite using `[hconj z, hBc z]`. Establish `hmon' : MonomialsBounded (mCoordIdeal y) (A.tensor B) a`. Introduce `z hz μ hμ`.

Take `⟨sg, hsg, -⟩` from `huniq z hz`. Establish `hb` using `hmon z hz sg hsg μ hμ`. Establish `hBz : B.h z = Λ sg` using `(hBloc z hz sg hsg).eq_of_nhds`. Use `show _ ≤ A.h z * B.h z`. Rewrite using `[hBz, mul_comm]`.

Conclude with `hb`. Establish `h0` using `hG1 K ι Ω y D a (A.tensor B) P0 II hD hII hvar hbir hA' hP0 hsemi' hmon' hconj'`. Rewrite `h0` using `[hT K ι Ω F y D a A B II Λ hD hII hvar hbir ha hsemi.1 hBa hBs hΛ huniq hBloc]`. Then use the resulting hypothesis.
-/
theorem SuccessiveMinimaDual.proof (hG1 : G1.Statement) (hW : EmbeddingWeight.Statement)
    (hT : TwistIntersection.Statement) : SuccessiveMinimaDual.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D a A P0 II Λ hD hII hvar hbir ha hP0 hsemi hconj hΛ hΛc huniq hmon
  obtain ⟨B, hBa, hBs, hBc, hBloc⟩ := hW K ι Ω F y Λ hΛ hΛc huniq
  have hA' : (A.tensor B).a = fun k => (a k : ℤ) := by
    rw [show (A.tensor B).a = A.a + B.a from rfl, ha, hBa, add_zero]
  have hsemi' : IsSemipositiveRel P0 (mCoordIdeal y) (A.tensor B) := by
    refine ⟨hsemi.1.mul hBs, fun z hz w hw => ?_⟩
    obtain ⟨sg, hsg, -⟩ := huniq z hz
    have hev : (fun x => Real.log ((A.tensor B).h x)) =ᶠ[𝓝 z]
        fun x => Real.log (A.h x) + Real.log (Λ sg) := by
      filter_upwards [hBloc z hz sg hsg, eventually_blocks_ne_zero hz.1] with x h1 h2
      rw [show (A.tensor B).h x = A.h x * B.h x from rfl, h1,
        Real.log_mul (A.pos x h2).ne' (hΛ sg).ne']
    rw [leviForm_congr_add_const _ hev]
    exact hsemi.2 z hz w hw
  have hconj' : IsConjInvariantH (A.tensor B) := fun z => by
    show A.h _ * B.h _ = A.h z * B.h z
    rw [hconj z, hBc z]
  have hmon' : MonomialsBounded (mCoordIdeal y) (A.tensor B) a := by
    intro z hz μ hμ
    obtain ⟨sg, hsg, -⟩ := huniq z hz
    have hb := hmon z hz sg hsg μ hμ
    have hBz : B.h z = Λ sg := (hBloc z hz sg hsg).eq_of_nhds
    show _ ≤ A.h z * B.h z
    rw [hBz, mul_comm]
    exact hb
  have h0 := hG1 K ι Ω y D a (A.tensor B) P0 II hD hII hvar hbir hA' hP0 hsemi' hmon' hconj'
  rwa [hT K ι Ω F y D a A B II Λ hD hII hvar hbir ha hsemi.1 hBa hBs hΛ huniq hBloc] at h0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
