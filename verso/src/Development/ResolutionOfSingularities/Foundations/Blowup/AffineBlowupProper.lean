import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.ReesGrading
open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.Blowup

universe u

variable {R : Type u} [CommRing R]

/- English proof (authored)
The algebra structure over the degree-zero part uses its inclusion in the Rees algebra, so its structure map sends an element to that same element in the full algebra.
-/
private theorem algebraMap_degreeZero_apply (I : Ideal R) (x : ↥(reesGrading I 0)) :
    algebraMap ↥(reesGrading I 0) ↥(reesAlgebra I) x = (x : ↥(reesAlgebra I)) := rfl

/- English proof (authored)
Both maps send the original ring element to its constant polynomial representative in the Rees algebra. The degree-zero equivalence uses this same representative.
-/
private theorem algebraMap_reesAlgebra_eq_algebraMap_degreeZero (I : Ideal R) (r : R) :
    algebraMap R ↥(reesAlgebra I) r =
      algebraMap ↥(reesGrading I 0) ↥(reesAlgebra I) (reesDegreeZeroEquiv I r) := by
  apply Subtype.ext
  rw [algebraMap_degreeZero_apply, reesDegreeZeroEquiv_coe_coe]
  rfl

private noncomputable def adjoinOverDegreeZero (I : Ideal R) (s : Set ↥(reesAlgebra I)) :
    Subalgebra R ↥(reesAlgebra I) where
  toSubsemiring := (Algebra.adjoin ↥(reesGrading I 0) s).toSubsemiring
  algebraMap_mem' := fun r => by
    rw [algebraMap_reesAlgebra_eq_algebraMap_degreeZero]
    exact Subalgebra.algebraMap_mem (Algebra.adjoin ↥(reesGrading I 0) s) _

/- English proof (authored)
Restricting scalars of a subalgebra keeps its underlying set. Hence membership in this restricted subalgebra is membership in the original degree-zero generated subalgebra.
-/
private theorem mem_adjoin_degreeZero_of_mem_restrictScalars (I : Ideal R) (s : Set ↥(reesAlgebra I))
    (x : ↥(reesAlgebra I)) (hx : x ∈ adjoinOverDegreeZero I s) :
    x ∈ Algebra.adjoin ↥(reesGrading I 0) s := hx

/- English proof (authored)
The subalgebra with restricted scalars has the same elements as the degree-zero generated subalgebra. The given membership transfers directly.
-/
private theorem mem_restrictScalars_of_mem_adjoin_degreeZero (I : Ideal R) (s : Set ↥(reesAlgebra I))
    (x : ↥(reesAlgebra I)) (hx : x ∈ Algebra.adjoin ↥(reesGrading I 0) s) :
    x ∈ adjoinOverDegreeZero I s := hx

/- English proof (authored)
The algebra generated over the degree-zero part contains each generator. Viewed as an algebra over the original ring, it therefore contains the algebra generated over the original ring by those elements.
-/
private theorem adjoin_le_adjoin_degreeZero (I : Ideal R) (s : Set ↥(reesAlgebra I)) :
    Algebra.adjoin R s ≤ adjoinOverDegreeZero I s := by
  refine Algebra.adjoin_le ?_
  intro y hy
  rw [SetLike.mem_coe]
  exact mem_restrictScalars_of_mem_adjoin_degreeZero I s y (Algebra.subset_adjoin hy)

/- English proof (authored)
Every element belongs to the original-ring generated algebra by hypothesis. The comparison includes this algebra in the degree-zero generated algebra, so the latter contains every element.
-/
private theorem adjoin_degreeZero_eq_top_of_adjoin_eq_top (I : Ideal R) (s : Set ↥(reesAlgebra I))
    (hs : Algebra.adjoin R s = ⊤) : Algebra.adjoin ↥(reesGrading I 0) s = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Algebra.adjoin R s := by
    rw [hs]
    exact Algebra.mem_top
  exact mem_adjoin_degreeZero_of_mem_restrictScalars I s x (adjoin_le_adjoin_degreeZero I s hx)

/- English proof (authored)
The Rees algebra of an ideal in a Noetherian ring is generated over the original ring by finitely many elements, using finite generation of the ideal. The same set generates over the degree-zero ring by the comparison of generated subalgebras.
-/
theorem finiteType_reesAlgebra_degreeZero (I : Ideal R) [IsNoetherianRing R] :
    Algebra.FiniteType ↥(reesGrading I 0) ↥(reesAlgebra I) := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R ↥(reesAlgebra I)).out
  exact ⟨⟨s, adjoin_degreeZero_eq_top_of_adjoin_eq_top I (↑s : Set ↥(reesAlgebra I)) hs⟩⟩

instance instFiniteTypeReesAlgebraOverDegZero (I : Ideal R) [IsNoetherianRing R] :
    Algebra.FiniteType ↥(reesGrading I 0) ↥(reesAlgebra I) :=
  finiteType_reesAlgebra_degreeZero I

/- English proof (authored)
An isomorphism is proper, and the composition of proper morphisms is proper.
-/
private theorem isProper_comp_of_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : AlgebraicGeometry.IsProper f) (hg : IsIso g) :
    AlgebraicGeometry.IsProper (f ≫ g) := by
  have := hf
  have := hg
  infer_instance

/- English proof (authored)
The Rees algebra is of finite type over its degree-zero part, so the projective spectrum projection to that spectrum is proper. The blowup projection follows it by the isomorphism identifying the degree-zero spectrum with the original spectrum. The composite is proper.
-/
theorem isProper_affineBlowup_toSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.IsProper (AffineBlowup.toSpec I) := by
  have hft : Algebra.FiniteType ↥(reesGrading I 0) ↥(reesAlgebra I) :=
    finiteType_reesAlgebra_degreeZero I
  have h1 : AlgebraicGeometry.IsProper (AlgebraicGeometry.Proj.toSpecZero (reesGrading I)) :=
    inferInstance
  rw [AffineBlowup.toSpec_eq_toSpecZero_comp]
  exact isProper_comp_of_isIso _ _ h1 (isIso_SpecMap_iff.mpr (reesDegreeZeroEquiv I).bijective)

instance instIsProperAffineBlowupToSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.IsProper (AffineBlowup.toSpec I) :=
  isProper_affineBlowup_toSpec I

/- English proof (authored)
The affine blowup projection is proper. Local finite type is part of properness.
-/
theorem locallyOfFiniteType_affineBlowup_toSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.LocallyOfFiniteType (AffineBlowup.toSpec I) := by
  have := isProper_affineBlowup_toSpec I
  infer_instance

instance instLocallyOfFiniteTypeAffineBlowupToSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.LocallyOfFiniteType (AffineBlowup.toSpec I) :=
  locallyOfFiniteType_affineBlowup_toSpec I

/- English proof (authored)
The affine blowup projection is proper and therefore universally closed.
-/
theorem universallyClosed_affineBlowup_toSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.UniversallyClosed (AffineBlowup.toSpec I) := by
  have := isProper_affineBlowup_toSpec I
  infer_instance

instance instUniversallyClosedAffineBlowupToSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.UniversallyClosed (AffineBlowup.toSpec I) :=
  universallyClosed_affineBlowup_toSpec I

/- English proof (authored)
A proper morphism is quasi-compact. Apply this to the affine blowup projection.
-/
theorem quasiCompact_affineBlowup_toSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.QuasiCompact (AffineBlowup.toSpec I) := by
  have := isProper_affineBlowup_toSpec I
  infer_instance

instance instQuasiCompactAffineBlowupToSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.QuasiCompact (AffineBlowup.toSpec I) :=
  quasiCompact_affineBlowup_toSpec I

end FunctorialResolution.Blowup
