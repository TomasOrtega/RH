import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InstFintypeHodgeBidegree
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
open CategoryTheory AlgebraicGeometry Module ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeFin

open GlobalTheory.CechDR GlobalTheory.QCoh

variable {k : Type} [Field k] {X : Scheme.{0}} (s : X ⟶ Sp k)

/- English proof (translation)
Establish `h1` using `LocallyOfFiniteType.finiteType_of_affine_subset s (isAffineOpen_top (Sp k)) hU (by simp)`. Establish `h2 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType` using `RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective`. Conclude with `h1.comp h2`.
-/
theorem finiteType_sec [LocallyOfFiniteType s] {U : X.Opens} (hU : IsAffineOpen U) :
    Algebra.FiniteType k (Sec s U) := by
  have h1 := LocallyOfFiniteType.finiteType_of_affine_subset s (isAffineOpen_top (Sp k)) hU
    (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact h1.comp h2

end GlobalTheory.HodgeFin
