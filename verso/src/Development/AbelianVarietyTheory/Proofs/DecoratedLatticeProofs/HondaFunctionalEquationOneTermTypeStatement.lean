import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFunctionalEquationOneTermType
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HondaFunEq.honda_funEq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FHondaFunctionalEquationOneTermType.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.honda_functional_equation_one_term_type : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), Formalism.L2.Th1.C.IsLogPair f e → ∀ c ε : K, ‖ε‖ = 1 → ε = c * (σ ^ 2) ε → CoefLe ‖(l : K)‖ (C (l : K) * f - C c * frobOp (σ ^ 2) (l ^ 2) 1 f) → CoefLe 1 (e.subst (C ε * ltLog K l)) := by
  first | exact @GlobalTheory.HondaFunEq.honda_funEq | exact GlobalTheory.HondaFunEq.honda_funEq | (intros; apply GlobalTheory.HondaFunEq.honda_funEq <;> assumption)
