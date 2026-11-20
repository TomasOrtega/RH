import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLiftIdempotentForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentPlaceChartFiniteAdeles
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdeleCMMemIntegralOfIdempotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsThetaLiftIdempotentForm.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.exists_theta_lift_idempotent_form : ∀ {D : D7} (V : HSp D), V.gram = 1 → ∀ (e : AE D), e * e = e → e * cA D e = 0 →
    ∀ (P Q : Matrix (Fin V.rank) (Fin V.rank) (AE D)), e • (P * Q) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
      e • (Q * P) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
    ∃ g : GA D V,
      Formalism.L2.Theta.mt V g = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • P + cA D e • (Q.map (cA D)).transpose ∧
      Formalism.L2.Theta.mt V g⁻¹ = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • Q + cA D e • (P.map (cA D)).transpose := by
  first | exact @GlobalTheory.UnitaryMove.exists_blockUnit | exact GlobalTheory.UnitaryMove.exists_blockUnit | (intros; apply GlobalTheory.UnitaryMove.exists_blockUnit <;> assumption)
