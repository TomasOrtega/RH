import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightTwoFormalGroupUnramifiedMultiplier
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Honda.heightTwo_unitTwist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FHeightTwoFormalGroupUnramifiedMultiplier.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.heightTwo_formalGroup_unramified_multiplier : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (l : ℕ) (σ : K →+* K), Unr K l σ → ResAlg K → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → σ (σ w) = w → ‖σ w - w‖ = 1 → (∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy f e (l : K))‖ = 1) → ∃ ε : K, ‖ε‖ = 1 ∧ CoefLe 1 (e.subst (C ε * ltLog K l)) := by
  first | exact @GlobalTheory.Honda.heightTwo_unitTwist | exact GlobalTheory.Honda.heightTwo_unitTwist | (intros; apply GlobalTheory.Honda.heightTwo_unitTwist <;> assumption)
