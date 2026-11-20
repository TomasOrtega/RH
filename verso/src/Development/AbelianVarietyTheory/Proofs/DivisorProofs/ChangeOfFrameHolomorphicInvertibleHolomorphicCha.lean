import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

/- English proof (translation)
Take `⟨U, hU, a, rfl⟩` from `hg.exists_fnOf`. Establish `hn : e.target ∩ e.symm ⁻¹' ptsIn X.str σ U ∈ 𝓝 (e y)`. Use `Filter.inter_mem (e.open_target.mem_nhds (e.map_source hy)) ?_` and prove the remaining obligations. Conclude with `(e.tendsto_symm hy) ((isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU))`. Conclude with `GlobalTheory.SCV.analyticAt_of_differentiableOn ((he U a).congr fun w hw => ratVal_fnOf hw.2 _ a) hn`.
-/
theorem analyticAt_ratVal_holoChart {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) {y : CxPts X.str σ} (hy : y ∈ e.source)
    {g : X.Fn} (hg : RegAt (under y) g) : AnalyticAt ℂ (fun v => ratVal g (e.symm v)) (e y) := by
  obtain ⟨U, hU, a, rfl⟩ := hg.exists_fnOf
  have hn : e.target ∩ e.symm ⁻¹' ptsIn X.str σ U ∈ 𝓝 (e y) := by
    refine Filter.inter_mem (e.open_target.mem_nhds (e.map_source hy)) ?_
    exact (e.tendsto_symm hy) ((isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU))
  exact GlobalTheory.SCV.analyticAt_of_differentiableOn ((he U a).congr fun w hw => ratVal_fnOf hw.2 _ a) hn

/- English proof (translation)
Introduce `F _ σ X m E e he y hy A A' hA hA'`. Establish `hP : Par 0 ((ratOf X).O (under y)).toSubring (A' * A⁻¹)` using `(Fr.mem_iff hA).1 hA'`. Establish `han (i j : Fin m) : AnalyticAt ℂ (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ i j) (e y)` using `analyticAt_ratVal_holoChart he hy (mem_O_ratOf.1 ((hP ()).1 j i))`. Use `⟨fun i j => ((han i j).contDiffAt (n := 2)).restrict_scalars ℝ, ?_, ?_⟩` and prove the remaining obligations. Take `⟨ψ, hψ⟩` from `exists_ratVal_hom y`.

Rewrite using `[Matrix.det_transpose, e.left_inv hy]`. Conclude with `((hP.map_of (ratVal · y) ψ hψ).det_ne ()).isUnit`. Establish `h : ∀ᶠ x in 𝓝 (e y), ∀ i j : Fin m, AnalyticAt ℂ (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ i j) x` using `eventually_all.2 fun i => eventually_all.2 fun j => (han i j).eventually_analyticAt filter_upwards [h] with x hx η`. Use extensionality with `i j`. Rewrite using `[mdbar_apply, GlobalTheory.dbar_eq_zero (hx i j).differentiableAt]`.

Both sides reduce to the same expression.
-/
theorem changeFrame_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ e.source → ∀ {A A' : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → A' ∈ E.S (under y) → MContDiffAt 2 (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) (e y) ∧ IsUnit (((A' * A⁻¹).map (ratVal · (e.symm (e y))) ())ᵀ).det ∧ ∀ᶠ x in 𝓝 (e y), ∀ η, mdbar (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) x η = 0 := by
  intro F _ σ X m E e he y hy A A' hA hA'
  have hP : Par 0 ((ratOf X).O (under y)).toSubring (A' * A⁻¹) := (Fr.mem_iff hA).1 hA'
  have han (i j : Fin m) : AnalyticAt ℂ (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ i j) (e y) :=
    analyticAt_ratVal_holoChart he hy (mem_O_ratOf.1 ((hP ()).1 j i))
  refine ⟨fun i j => ((han i j).contDiffAt (n := 2)).restrict_scalars ℝ, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
    rw [Matrix.det_transpose, e.left_inv hy]
    exact ((hP.map_of (ratVal · y) ψ hψ).det_ne ()).isUnit
  · have h : ∀ᶠ x in 𝓝 (e y), ∀ i j : Fin m,
        AnalyticAt ℂ (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ i j) x :=
      eventually_all.2 fun i => eventually_all.2 fun j => (han i j).eventually_analyticAt
    filter_upwards [h] with x hx η
    ext i j
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx i j).differentiableAt]
    rfl

end GlobalTheory.GoodTop
