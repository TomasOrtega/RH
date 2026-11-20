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
Introduce `X Ω _ ξ G _ V _ _ M O _ act ρ hact p a e he`. Express the relevant statement in the definitionally equal form `e ∈ Submodule.span (regAt ξ p) {e | ∃ v, M.Extends p e v} at he`. Express the relevant statement in the definitionally equal form `ρ a e ∈ Submodule.span (regAt ξ p) {e | ∃ v, M.Extends p e v}`. Proceed by induction on `he using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨v, hv⟩` from `hx`. Unfold `LieModel.Extends at hv`. Take `⟨hv1, hv2⟩` from `hv`. Use `Submodule.subset_span ⟨v ≫ act.act a, ?_⟩` and prove the remaining obligations. Unfold `LieModel.Extends`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `IsTanAt at hv1 ⊢ haveI := act.hom a`. Rewrite using `[Over.comp_left, ← Category.assoc, hv1, ← Over.comp_left]`. Use `congr 1`. Simplify using the standard rewrite rules.

Establish `h` using `hact a x`. Rewrite using `[h, Over.comp_left, hv2, Over.comp_left]`. Conclude with `Category.assoc _ _ _`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul r x _ hx`. Rewrite using `[Subring.smul_def, map_smul, ← Subring.smul_def]`. Conclude with `Submodule.smul_mem _ r hx`.
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
