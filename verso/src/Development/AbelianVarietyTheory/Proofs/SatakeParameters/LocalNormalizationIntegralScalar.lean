import Mathlib
import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm

namespace GlobalTheory

open Formalism.L2.AlgTh

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [Formalism.L2.Th1.H.tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem tensorFourthPower_smul {n : Type} [Fintype n] [DecidableEq n] (c : ℂ) (θ : (n → ℂ) → ℂ) :
    Formalism.L2.Th1.H.tens4 (c • θ) = c ^ 4 • Formalism.L2.Th1.H.tens4 θ := by
  funext z
  simp only [Formalism.L2.Th1.H.tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Introduce `a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι c hc hLN`. Take `⟨g₁, ε, hiso, hp, hidx, hε, heq⟩` from `hLN`. Use `⟨g₁, c ^ 4 * ε, hiso, hp, hidx, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, norm_mul, norm_pow]`. Establish `h0 : 0 ≤ ‖ι c‖` using `norm_nonneg _`.

Establish `h4 : ‖ι c‖ ^ 4 ≤ 1` using `pow_le_one₀ h0 hc`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[tensorFourthPower_smul, heq, smul_smul]`.
-/
theorem locNormScale : LocNormScale := by
  intro a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι c hc hLN
  obtain ⟨g₁, ε, hiso, hp, hidx, hε, heq⟩ := hLN
  refine ⟨g₁, c ^ 4 * ε, hiso, hp, hidx, ?_, ?_⟩
  · rw [map_mul, map_pow, norm_mul, norm_pow]
    have h0 : 0 ≤ ‖ι c‖ := norm_nonneg _
    have h4 : ‖ι c‖ ^ 4 ≤ 1 := pow_le_one₀ h0 hc
    calc ‖ι c‖ ^ 4 * ‖ι ε‖ ≤ 1 * 1 := mul_le_mul h4 hε (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [tensorFourthPower_smul, heq, smul_smul]

end GlobalTheory
