import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerClassCohomologousAlongEndomorphism
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FKodairaSpencerClassCohomologousAlongEndomorphism.lean&line=424#L424)
-/
theorem _root_.GlobalTheory.T.kodairaSpencerClass_cohomologous_along_endomorphism : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D : R → K) d θ (f : X ⟶ X) (f₀ : A₀ ⟶ A₀) (F : Matrix (Fin g) (Fin g) K), KSCoc A₀.hom p m D W dd d θ → IsMonHom f₀ → f ≫ p = p → f₀.left ≫ m = m ≫ f → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → ∀ x, Cohom f₀.left _ (lc A₀.hom (F x) θ) (θ x) := by
  first | exact @GlobalTheory.KS.cohom_ksCoc_of_endomorphism | exact GlobalTheory.KS.cohom_ksCoc_of_endomorphism | (intros; apply GlobalTheory.KS.cohom_ksCoc_of_endomorphism <;> assumption)
