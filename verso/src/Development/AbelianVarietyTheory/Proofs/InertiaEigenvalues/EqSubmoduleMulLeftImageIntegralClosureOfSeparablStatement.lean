import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FEqSubmoduleMulLeftImageIntegralClosureOfSeparabl.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.eq_submoduleMulLeftImage_integralClosure_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ N : Submodule O A, IsLat O E N → (∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N) → ∃ t : Aˣ, N = mulLat O (t : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  first | exact @GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable | exact GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable | (intros; apply GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable <;> assumption)
