import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTorusWeightOfPolyRepCompSwap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isWt_comp_swap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsTorusWeightOfPolyRepCompSwap.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.isTorusWeightOfPolyRep_comp_swap : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ μ : Fin n → ℤ, IsWt Φ μ → ∀ i j : Fin n, IsWt Φ (μ ∘ Equiv.swap i j) := by
  first | exact @GlobalTheory.isWt_comp_swap | exact GlobalTheory.isWt_comp_swap | (intros; apply GlobalTheory.isWt_comp_swap <;> assumption)
