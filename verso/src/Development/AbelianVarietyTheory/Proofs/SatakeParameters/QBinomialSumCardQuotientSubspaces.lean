import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussBinomMulProd

namespace GlobalTheory

/- English proof (translation)
Introduce `k V _ _ _ _ _ X`. Simplify using `only [GlobalTheory.GaussCount.card_codim]`. Conclude with `GlobalTheory.GaussCount.gauss_formula (Nat.card k) ℂ X (Module.finrank k V)`.
-/
theorem qBinomial_subspaces : ∀ (k V : Type) [Field k] [Finite k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (X : ℂ),
    ∑ j ∈ Finset.range (Module.finrank k V + 1),
        (-1 : ℂ) ^ j * (Nat.card k : ℂ) ^ (j * (j - 1) / 2) *
          (Nat.card {W : Submodule k V // Module.finrank k (V ⧸ W) = j} : ℂ) * X ^ j =
      ∏ i ∈ Finset.range (Module.finrank k V), (1 - (Nat.card k : ℂ) ^ i * X) := by
  intro k V _ _ _ _ _ X
  simp only [GlobalTheory.GaussCount.card_codim]
  exact GlobalTheory.GaussCount.gauss_formula (Nat.card k) ℂ X (Module.finrank k V)

end GlobalTheory
