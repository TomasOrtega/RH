import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemIntegralDifferentialSubmodule
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSubstMemIntegralDifferentialSubmodule.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.subst_mem_integralDifferentialSubmodule : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (f : MvPowerSeries (σ) (Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, u i ∈ intBy p k τ 1) → f ∈ quasiInt p k σ → subst u f ∈ quasiInt p k τ := by
  first | exact @GlobalTheory.Katz.subst_mem_quasiInt | exact GlobalTheory.Katz.subst_mem_quasiInt | (intros; apply GlobalTheory.Katz.subst_mem_quasiInt <;> assumption)
