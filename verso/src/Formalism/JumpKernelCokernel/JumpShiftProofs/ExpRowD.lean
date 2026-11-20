import Formalism.JumpKernelCokernel.Statement
import Formalism.JumpKernelCokernel.JumpShiftProofs.RowDegreeBound
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ExpBound

namespace Formalism.KernelCokernelLengths

/- English proof (translation)
Introduce `ℓ hℓ h η S b a s₁ E e₂ hη hb ha hs hE he`. Establish `key` using `Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.expBound_statement ℓ hℓ h η S b a s₁ E e₂ hb ha hs hE he`. Establish `hℓ0 : (0 : ℝ) < (ℓ : ℝ)` using `by exact_mod_cast (by omega : 0 < ℓ)`. Establish `hℓ2 : (0 : ℝ) < (ℓ : ℝ) ^ 2` using `by positivity`. Establish `hη' : (2 * (η : ℝ)) ≤ h` using `by exact_mod_cast hη`.

Establish `hc : 32 * ((h + η : ℕ) : ℝ) / (ℓ : ℝ) ^ 2 ≤ 50 * (h : ℝ) / (ℓ : ℝ) ^ 2`. Apply `div_le_div_of_nonneg_right _ hℓ2.le` to reduce the goal to its premises. Use `push_cast`. Use polynomial arithmetic with `[(Nat.cast_nonneg η : (0 : ℝ) ≤ η)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem row_degree_exponent : ExpRowD := by
  intro ℓ hℓ h η S b a s₁ E e₂ hη hb ha hs hE he
  have key := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.expBound_statement ℓ hℓ h η S b a s₁ E e₂ hb ha hs hE he
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ2 : (0 : ℝ) < (ℓ : ℝ) ^ 2 := by positivity
  have hη' : (2 * (η : ℝ)) ≤ h := by exact_mod_cast hη
  have hc : 32 * ((h + η : ℕ) : ℝ) / (ℓ : ℝ) ^ 2 ≤ 50 * (h : ℝ) / (ℓ : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_right _ hℓ2.le
    push_cast
    nlinarith [(Nat.cast_nonneg η : (0 : ℝ) ≤ η)]
  linarith

end Formalism.KernelCokernelLengths
