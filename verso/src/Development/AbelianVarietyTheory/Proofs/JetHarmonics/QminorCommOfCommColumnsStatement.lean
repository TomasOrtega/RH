import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorCommOfCommColumns
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FQminorCommOfCommColumns.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.qminor_commute_of_commute_columns : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (x : A) (a b : Fin t → Fin n) (u : ℂ), (∀ (c : Fin n) (i : Fin t), E c (b i) * x = x * E c (b i)) → qminor E a b u * x = x * qminor E a b u := by
  first | exact @GlobalTheory.qminor_comm_of_comm_columns | exact GlobalTheory.qminor_comm_of_comm_columns | (intros; apply GlobalTheory.qminor_comm_of_comm_columns <;> assumption)
