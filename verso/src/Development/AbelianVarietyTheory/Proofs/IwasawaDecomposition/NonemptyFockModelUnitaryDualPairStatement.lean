import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyFockModelUnitaryDualPair
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.nonempty_fockData_pair` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNonemptyFockModelUnitaryDualPair.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.nonempty_fockModel_unitary_dual_pair : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s), Nonempty (FockData T0 T1 T2) := by
  first | exact @GlobalTheory.nonempty_fockData_pair | exact GlobalTheory.nonempty_fockData_pair | (intros; apply GlobalTheory.nonempty_fockData_pair <;> assumption)
