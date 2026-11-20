import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliOperatorsCommute
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CTFin.CapComm.capR_capS_commute` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCapelliOperatorsCommute.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.capelli_operators_commute : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u v : ℂ), Commute (capR r s τ u) (capR r s τ v) ∧ Commute (capR r s τ u) (capS r s τ v) ∧ Commute (capS r s τ u) (capS r s τ v) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.CapComm.capR_capS_commute | exact GlobalTheory.CompanionTheory.CTFin.CapComm.capR_capS_commute | (intros; apply GlobalTheory.CompanionTheory.CTFin.CapComm.capR_capS_commute <;> assumption)
