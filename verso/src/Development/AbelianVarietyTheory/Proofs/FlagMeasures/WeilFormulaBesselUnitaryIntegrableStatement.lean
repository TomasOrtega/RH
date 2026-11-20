import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrable
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FWeilFormulaBesselUnitaryIntegrable.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.weil_formula_besselUnitary_integrable : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r)), IsClosedSub k r S → IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → IsQuotMeas μG μS ν → SigmaFinite ν ∧ ν {x | Matrix.of x ∉ GG k r} = 0 ∧ μG = (ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) ∧ (∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] (f : Mt k r → B), Integrable f μG → Integrable (fun x => ∫ s, f (lmulM (Matrix.of s) x) ∂μS) ν ∧ ∫ x, f x ∂μG = ∫ x, (∫ s, f (lmulM (Matrix.of s) x) ∂μS) ∂ν) ∧ (∀ F : Mt k r → ENNReal, Measurable F → (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) → ∀ y ∈ GG k r, ∫⁻ x, F (rmulM y x) ∂ν = ∫⁻ x, F x ∂ν) := by
  first | exact @GlobalTheory.SgInf.weil_integrable | exact GlobalTheory.SgInf.weil_integrable | (intros; apply GlobalTheory.SgInf.weil_integrable <;> assumption)
