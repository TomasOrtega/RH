import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundProjectionDualTensorStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundEmbeddedComponentStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlgTensWtNear
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `M _ _ n ε E N _ _ F io pr μ j w hE hF hT hw s c d`. Take `⟨hc, hwt⟩` from `hw`. Establish `hn : (1 : ℝ) ≤ n`. Establish `: 0 < n` using `Fin.pos s`. Conclude with `this` after adjusting the coercions.

Establish `hsq : Real.sqrt n ≤ n`. Rewrite using `[Real.sqrt_le_left (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hs0 : 0 ≤ Real.sqrt (n : ℝ)` using `Real.sqrt_nonneg _`. Establish `h0 : 0 ≤ Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * (j : ℝ)` using `by positivity`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `GlobalTheory.T.compactCasimirBound_projection_dualTensor M n ε E N F io pr _ w hE hF hT h0 hc s c`. Establish `h2` using `GlobalTheory.T.compactCasimirBound_embedded_component M n ε E N F io pr _ s _ hE hF hT (by linarith) h1 d`. Take `⟨S, hS1, hS2, hS3, hS4⟩` from `h2`. Use `⟨S, hS1, hS2, hS3, fun x hx => (hS4 x hx).trans ?_⟩` and prove the remaining obligations.

Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Apply `pow_le_pow_left₀ (by linarith)` to reduce the goal to its premises. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Establish `h1` using `(GlobalTheory.algTens_wtNear M n ε E N F io pr (lowK ε μ) j hT).1 w hwt s c`.

Establish `h2` using `(GlobalTheory.algTens_wtNear M n ε E N F io pr (lowK ε μ) (j + 1) hT).2 s _ h1 d`. Establish `e : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 1 + 1` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `h2`.
-/
theorem lev_io_pr_single : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (j : ℕ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → Lev ε E μ j w → ∀ s c d, Lev ε E μ (j + 2) (io s (pr s (Pi.single c w)) d) := by
  intro M _ _ n ε E N _ _ F io pr μ j w hE hF hT hw s c d
  obtain ⟨hc, hwt⟩ := hw
  have hn : (1 : ℝ) ≤ n := by
    have : 0 < n := Fin.pos s
    exact_mod_cast this
  have hsq : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have h0 : 0 ≤ Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * (j : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · have h1 := GlobalTheory.T.compactCasimirBound_projection_dualTensor M n ε E N F io pr _ w hE hF hT h0 hc s c
    have h2 := GlobalTheory.T.compactCasimirBound_embedded_component M n ε E N F io pr _ s _ hE hF hT (by linarith) h1 d
    obtain ⟨S, hS1, hS2, hS3, hS4⟩ := h2
    refine ⟨S, hS1, hS2, hS3, fun x hx => (hS4 x hx).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply pow_le_pow_left₀ (by linarith)
    push_cast
    nlinarith
  · have h1 := (GlobalTheory.algTens_wtNear M n ε E N F io pr (lowK ε μ) j hT).1 w hwt s c
    have h2 := (GlobalTheory.algTens_wtNear M n ε E N F io pr (lowK ε μ) (j + 1) hT).2 s _ h1 d
    have e : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 1 + 1 := by push_cast; ring
    rw [e]
    exact h2

end GlobalTheory
