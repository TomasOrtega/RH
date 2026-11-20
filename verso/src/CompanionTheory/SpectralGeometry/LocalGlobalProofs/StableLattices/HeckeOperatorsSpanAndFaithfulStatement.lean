import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeOperatorsSpanAndFaithful
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.HeckeBasis.heckeBasis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FHeckeOperatorsSpanAndFaithful.lean&line=195#L195)
-/
theorem _root_.GlobalTheory.T.hecke_operators_span_and_faithful : ∀ (G : Type) [Group G] (K : Subgroup G), IsHeckePair K → ∃ T : G → Hk K, (∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) → (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = ∑ y ∈ S, Finsupp.single y (1 : ℂ)) ∧ Submodule.span ℂ (Set.range T) = ⊤ ∧ ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBasis.heckeBasis | exact GlobalTheory.CompanionTheory.HeckeBasis.heckeBasis | (intros; apply GlobalTheory.CompanionTheory.HeckeBasis.heckeBasis <;> assumption)
