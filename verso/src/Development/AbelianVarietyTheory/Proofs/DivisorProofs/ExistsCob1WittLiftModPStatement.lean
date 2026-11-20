import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCob1WittLiftModP
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WittStart.start` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCob1WittLiftModP.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.exists_cob1_witt_lift_mod_p : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c → ∀ w : Fin d → k, ∃ f ∈ intBy p k (Fin d) 1, RedV p (lin f) w ∧ ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < 2 → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w) := by
  first | exact @GlobalTheory.WittStart.start | exact GlobalTheory.WittStart.start | (intros; apply GlobalTheory.WittStart.start <;> assumption)
