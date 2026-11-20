import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.EllipticCharpolyLocalRealisation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalTwistContinuousInvolutionIntegralProperties
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FAutomorphicKernels%2FIsobaricBaseChange%2FIntegralCoefficientBaseChange%2FUnitaryBaseChangeCharacters%2FUnitaryBaseChangeLinks%2FEllipticCharpolyLocalRealisation.lean&line=138#L138)
-/
theorem _root_.GlobalTheory.T.elliptic_charpoly_local_realisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P ∈ Ell E n → (∀ᶠ w in (cofinite : Filter (Pl E)), ∃ y : UL n w, y ∈ KL n w ∧ y.1.val.charpoly = atPl w P) ∧ ∀ w : Pl E, IsSplitAt w → ∃ y : UL n w, y.1.val.charpoly = atPl w P := by
  first | exact @GlobalTheory.IntUnitaryPoly.main | exact GlobalTheory.IntUnitaryPoly.main | (intros; apply GlobalTheory.IntUnitaryPoly.main <;> assumption)
