import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStable

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Express the relevant assertion in an equivalent form by its definition. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lat_stable : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End Ω V), M.IsActOf act.act ρ → ∀ (p : Cpt ξ) (a : O), ∀ e ∈ M.lat p, ρ a e ∈ M.lat p := by
  intro X Ω _ ξ G _ V _ _ M O _ act ρ hact p a e he
  change e ∈ Submodule.span (regAt ξ p) {e | ∃ v, M.Extends p e v} at he
  change ρ a e ∈ Submodule.span (regAt ξ p) {e | ∃ v, M.Extends p e v}
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv⟩ := hx
    unfold LieModel.Extends at hv
    obtain ⟨hv1, hv2⟩ := hv
    refine Submodule.subset_span ⟨v ≫ act.act a, ?_⟩
    unfold LieModel.Extends
    refine ⟨?_, ?_⟩
    · unfold IsTanAt at hv1 ⊢
      haveI := act.hom a
      rw [Over.comp_left, ← Category.assoc, hv1, ← Over.comp_left]
      congr 1
      simp
    · have h := hact a x
      rw [h, Over.comp_left, hv2, Over.comp_left]
      exact Category.assoc _ _ _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Subring.smul_def, map_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ r hx

end GlobalTheory.CompanionTheory.Ar.LieStable
