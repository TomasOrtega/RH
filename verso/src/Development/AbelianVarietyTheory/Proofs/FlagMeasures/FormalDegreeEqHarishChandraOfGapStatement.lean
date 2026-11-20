import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeEqHarishChandraOfGap
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.dsig_eq_fdegHC_of_gap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FFormalDegreeEqHarishChandraOfGap.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.formalDegree_eq_harishChandra_of_gap : ∀ (D : D7), Ties D → ∀ (τ : D.what₂.Tau) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam (lamSH D.R (D.hc τ)) → Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc τ)) h → Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < h → D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := by
  first | exact @GlobalTheory.dsig_eq_fdegHC_of_gap | exact GlobalTheory.dsig_eq_fdegHC_of_gap | (intros; apply GlobalTheory.dsig_eq_fdegHC_of_gap <;> assumption)
