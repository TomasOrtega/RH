import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

/- English proof (translation)
Take `⟨N, i, hi, hq, rfl⟩` from `h`. Establish `P` using `ProjSpace.isPullback_baseChange N j`. Establish `w : (p ≫ i) ≫ PSpace.str R N = s' ≫ spMap j` using `by rw [Category.assoc]; exact sq.w`. Establish `Q : IsPullback p (P.lift (p ≫ i) s' w) i (ProjSpace.baseChange N j)` using `IsPullback.of_bot (by rw [P.lift_snd]; exact sq) (P.lift_fst _ _ w).symm P`. Conclude with `⟨N, P.lift (p ≫ i) s' w, MorphismProperty.of_isPullback (P := @IsImmersion) Q hi, MorphismProperty.of_isPullback (P := @QuasiCompact) Q hq, P.lift_snd _ _ w⟩`.
-/
theorem isQProjOver_of_isPullback_spMap {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') {Y Y' : Scheme.{0}}
    {s : Y ⟶ Sp R} {p : Y' ⟶ Y} {s' : Y' ⟶ Sp R'} (sq : IsPullback p s' s (spMap j)) (h : IsQProjOver s) :
    IsQProjOver s' := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have P := ProjSpace.isPullback_baseChange N j
  have w : (p ≫ i) ≫ PSpace.str R N = s' ≫ spMap j := by rw [Category.assoc]; exact sq.w
  have Q : IsPullback p (P.lift (p ≫ i) s' w) i (ProjSpace.baseChange N j) :=
    IsPullback.of_bot (by rw [P.lift_snd]; exact sq) (P.lift_fst _ _ w).symm P
  exact ⟨N, P.lift (p ≫ i) s' w, MorphismProperty.of_isPullback (P := @IsImmersion) Q hi,
    MorphismProperty.of_isPullback (P := @QuasiCompact) Q hq, P.lift_snd _ _ w⟩

/- English proof (translation)
Take `⟨N, i, _, _, rfl⟩` from `h`. Use `isProper_str R' N` as an intermediate fact. Establish `: LocallyOfFiniteType (spMap j)` using `HasRingHomProperty.Spec_iff.2 hj`. Conclude with `((isAmple_projective_O_one R' N).pull_of_isImmersion i).isQProjOver _`.
-/
theorem isQProjOver_comp_spMap_of_finiteType {R R' : Type} [CommRing R] [CommRing R'] {j : R →+* R'}
    (hj : j.FiniteType) {Y : Scheme.{0}} {s' : Y ⟶ Sp R'} (h : IsQProjOver s') : IsQProjOver (s' ≫ spMap j) := by
  obtain ⟨N, i, _, _, rfl⟩ := h
  have := isProper_str R' N
  have : LocallyOfFiniteType (spMap j) := HasRingHomProperty.Spec_iff.2 hj
  exact ((isAmple_projective_O_one R' N).pull_of_isImmersion i).isQProjOver _

/- English proof (translation)
Introduce `_ _ _ _ j _ _` and use `⟨fun h => isQProjOver_of_isPullback_spMap j (IsPullback.of_hasPullback _ _) h, fun _ hj h => isQProjOver_comp_spMap_of_finiteType hj.finiteType h⟩`.
-/
theorem isQProjOver_baseChange_and_finite_restrict :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] (j : R →+* R') (Y : Scheme.{0}) (s : Y ⟶ Sp R),
      (IsQProjOver s → IsQProjOver (pullback.snd s (spMap j))) ∧
        ∀ s' : Y ⟶ Sp R', j.Finite → IsQProjOver s' → IsQProjOver (s' ≫ spMap j) :=
  fun _ _ _ _ j _ _ => ⟨fun h => isQProjOver_of_isPullback_spMap j (IsPullback.of_hasPullback _ _) h,
    fun _ hj h => isQProjOver_comp_spMap_of_finiteType hj.finiteType h⟩

end GlobalTheory
