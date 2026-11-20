import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartLieBasisMatrices
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

/- English proof (translation)
Take `⟨N, i, hi, hs⟩` from `Y.proj`. Use `haveI := hi`. Use `haveI : IsProper (PSpace.str O N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N`. Use `haveI : QuasiCompact Y.s := by rw [← hs]; infer_instance`. Conclude with `QuasiCompact.compactSpace_of_compactSpace Y.s`.
-/
private theorem compactSpace_model {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) : CompactSpace Y.X := by
  obtain ⟨N, i, hi, hs⟩ := Y.proj
  haveI := hi
  haveI : IsProper (PSpace.str O N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N
  haveI : QuasiCompact Y.s := by rw [← hs]; infer_instance
  exact QuasiCompact.compactSpace_of_compactSpace Y.s

/- English proof (translation)
Take `⟨U, hU, hxU, hdom, ⟨θ, hθ, hne⟩, n, v₀, ρ, hlie⟩` from `GlobalTheory.ModelChart.exists_chart_lieBasis_matrices E H Dw l Xo c O β Y hP x`. Conclude with `⟨⟨U, hU, hdom, θ, hθ, hne, n, v₀, ρ, hlie⟩, hxU⟩`.
-/
private theorem exists_mChart_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] [IsNoetherianRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (hP : PushInvertible Y.t.G Y.t.PP.L) (x : Y.X) : ∃ M : MChart Y, x ∈ M.U := by
  obtain ⟨U, hU, hxU, hdom, ⟨θ, hθ, hne⟩, n, v₀, ρ, hlie⟩ :=
    GlobalTheory.ModelChart.exists_chart_lieBasis_matrices E H Dw l Xo c O β Y hP x
  exact ⟨⟨U, hU, hdom, θ, hθ, hne, n, v₀, ρ, hlie⟩, hxU⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ _ β Y hP`. Use `haveI := compactSpace_model Y`. Use `choose M hM using exists_mChart_mem Y hP`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun x => ((M x).U : Set Y.X)) (fun x => (M x).U.isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hM x⟩)`. Use `⟨t, inferInstance, fun j => M j.1, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨j, hj, hx⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ x))`. Conclude with `⟨⟨j, hj⟩, hx⟩`.
-/
theorem exists_finite_mchart_cover :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L → ∃ (J : Type) (_ : Finite J) (M : J → MChart Y), ∀ x : Y.X, ∃ j, x ∈ (M j).U := by
  intro E _ _ _ H Dw l Xo c O _ _ β Y hP
  haveI := compactSpace_model Y
  choose M hM using exists_mChart_mem Y hP
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => ((M x).U : Set Y.X))
    (fun x => (M x).U.isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hM x⟩)
  refine ⟨t, inferInstance, fun j => M j.1, fun x => ?_⟩
  obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨⟨j, hj⟩, hx⟩

end GlobalTheory.Reg
