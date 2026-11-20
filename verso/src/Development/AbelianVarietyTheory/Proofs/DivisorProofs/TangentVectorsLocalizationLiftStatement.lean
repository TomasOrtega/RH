import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsLocalizationLift
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushRProdPtsResP

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_tangent_isLieBasis_atPrime` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTangentVectorsLocalizationLift.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.tangent_vectors_localization_lift : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → ∀ (p : Ideal R) [p.IsPrime],
    ∃ (n : ℕ) (w : Fin n → (epsR R ⟶ G)), (∀ i, IsTangent (w i)) ∧
      (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i) (v i)) → IsLieBasis v) := by
  first | exact @GlobalTheory.exists_tangent_isLieBasis_atPrime | exact GlobalTheory.exists_tangent_isLieBasis_atPrime | (intros; apply GlobalTheory.exists_tangent_isLieBasis_atPrime <;> assumption)
