import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusIsAffineHomAndSplitsFinite
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SS

/- English proof (translation)
Introduce `k _ G _ ⟨T⟩`. Use `T.q_hom` as an intermediate fact. Use `T.i_hom` as an intermediate fact. Take `⟨-, k', _, _, hfin, X, _, hfree, hX, e, he⟩` from `GlobalTheory.torus_isAffineHom_and_splits_finite k T.T₀ T.isTorus`. Use `⟨k', inferInstance, inferInstance, hfin, ?_⟩` and prove the remaining obligations.

Set `f : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)` to `Spec.map (CommRingCat.ofHom (algebraMap k k'))`. Establish `hq` using `isPullback_overPullback_map_left f T.q`. Establish `: IsMonHom e.inv` using `inferInstance`. Use `⟨{ X := X B := (Over.pullback f).obj T.B grpB := inferInstance isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian q := (Over.pullback f).map T.q q_hom := inferInstance q_flat := MorphismProperty.of_isPullback (P := @Flat) hq T.q_flat q_surjective := Morphism …` and prove the remaining obligations. Establish `hk` using `T.isKernel.map (Over.pullback f)`.

Use `IsPullback.of_iso hk e (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Conclude with `toUnit_unique _ _`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem exists_finite_torusExtension_of_torusExt : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExt G) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k'), Nonempty (TorusExtension (fieldBaseChange k k' G)) := by
  intro k _ G _ ⟨T⟩
  have := T.q_hom
  have := T.i_hom
  obtain ⟨-, k', _, _, hfin, X, _, hfree, hX, e, he⟩ := GlobalTheory.torus_isAffineHom_and_splits_finite k T.T₀ T.isTorus
  refine ⟨k', inferInstance, inferInstance, hfin, ?_⟩
  let f : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hq := isPullback_overPullback_map_left f T.q
  have : IsMonHom e.inv := inferInstance
  refine ⟨{ X := X
            B := (Over.pullback f).obj T.B
            grpB := inferInstance
            isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
            q := (Over.pullback f).map T.q
            q_hom := inferInstance
            q_flat := MorphismProperty.of_isPullback (P := @Flat) hq T.q_flat
            q_surjective := MorphismProperty.of_isPullback (P := @Surjective) hq T.q_surjective
            q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) hq T.q_quasiCompact
            i := e.inv ≫ (Over.pullback f).map T.i
            i_hom := inferInstance
            isKernel := ?_ }⟩
  have hk := T.isKernel.map (Over.pullback f)
  refine IsPullback.of_iso hk e (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · exact toUnit_unique _ _
  · simp
  · simp

end GlobalTheory.SS
