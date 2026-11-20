import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry GroundTheory.Arith.SchemeCoh

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Use `⟨fun y ⟨n, hn⟩ => HomogeneousLocalization.val_injective (𝒜 := 𝒜) (x := S) ?_⟩` and prove the remaining obligations. Rewrite using `[HomogeneousLocalization.val_zero]`. Use `IsReduced.eq_zero _ ⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← HomogeneousLocalization.val_pow, hn, HomogeneousLocalization.val_zero]`.
-/
lemma SectionsLatticeFS.isReduced_homogeneousLocalization {ι R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [AddCommMonoid ι] [DecidableEq ι] {𝒜 : ι → Submodule R A}
    [GradedAlgebra 𝒜] {S : Submonoid A} [IsReduced (Localization S)] :
    IsReduced (HomogeneousLocalization 𝒜 S) := by
  refine ⟨fun y ⟨n, hn⟩ => HomogeneousLocalization.val_injective (𝒜 := 𝒜) (x := S) ?_⟩
  rw [HomogeneousLocalization.val_zero]
  refine IsReduced.eq_zero _ ⟨n, ?_⟩
  rw [← HomogeneousLocalization.val_pow, hn, HomogeneousLocalization.val_zero]

/- English proof (translation)
Introduce `A _ _ N`. Establish `: ∀ x : projectiveSpace A N, _root_.IsReduced ((projectiveSpace A N).presheaf.stalk x)` using `fun x => by`. Use `x.isPrime` as an intermediate fact. Establish `: _root_.IsReduced (CommRingCat.of (HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal))` using `SectionsLatticeFS.isReduced_homogeneousLocalization`. Conclude with `isReduced_of_injective _ (Proj.stalkIso (ProjSpace.grading A N) x).commRingCatIsoToRingEquiv.injective`.

Conclude with `isReduced_of_isReduced_stalk (projectiveSpace A N)`.
-/
theorem SectionsLatticeFS.PNReduced.proof : SectionsLatticeFS.PNReduced.Statement.{u} := by
  intro A _ _ N
  have : ∀ x : projectiveSpace A N,
      _root_.IsReduced ((projectiveSpace A N).presheaf.stalk x) := fun x => by
    have := x.isPrime
    have : _root_.IsReduced (CommRingCat.of
        (HomogeneousLocalization.AtPrime (ProjSpace.grading A N)
          x.asHomogeneousIdeal.toIdeal)) :=
      SectionsLatticeFS.isReduced_homogeneousLocalization
    exact isReduced_of_injective _
      (Proj.stalkIso (ProjSpace.grading A N) x).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk (projectiveSpace A N)

end GroundTheory.Heights₂.Heights
