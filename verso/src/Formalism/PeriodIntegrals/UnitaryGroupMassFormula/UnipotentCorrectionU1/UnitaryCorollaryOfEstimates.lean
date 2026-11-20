import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `k j ρ Wp Wq _ _ _ _ _ o κ Θ χ hΘ hχ Q mm₀ A₀ hQ`. Take `⟨hcd, Cφ, hWB⟩` from `hD k j ρ χ (Q + o) hχ`. Take `⟨C, hCf⟩` from `hC k j ρ Wp Wq o κ 0 Θ χ (fun g => χ (DjU k j ρ g)) hΘ hχ Q mm₀ A₀ hQ hcd (fun g hg => image_eq_zero_of_notMem_tsupport hg) ⟨Cφ, by simpa using hWB⟩`. Use `⟨C, fun f c hf => ?_⟩` and prove the remaining obligations.

Use `hCf f c hf` as an intermediate fact. Simplify using `only [Nat.cast_zero, zero_mul, sub_zero] at this`. Conclude with `this`. Introduce `k j ρ Wp Wq _ _ _ _ _ z z' o κ Θ χ χε ε hΘ hχ hε Q mm₀ A₀ hQ`. Take `⟨hcd, C1, h1⟩` from `hD k j ρ χ (Q + o) hχ`.

Take `⟨hcg, C2, h2⟩` from `hG k (j + ρ) z z' χε ε (Q + o) hε`. Take `⟨C3, h3⟩` from `hM k (j + ρ) _ _ _ _ (Q + o) C1 C2 0 0 hcd hcg h1 h2`. Rewrite `h3` using `[zero_add]`. Take `⟨C, hCf⟩` from `hC k j ρ Wp Wq o κ (2 * (j + ρ + 1)) Θ χ (fun g => χ (DjU k j ρ g) * ((χε (Gf k (j + ρ) z z' g) : ℝ) : ℂ)) hΘ hχ Q mm₀ A₀ hQ (hcd.mul hcg) (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg]) ⟨C3, h3⟩`. Use `⟨C, fun f c hf => ?_⟩` and prove the remaining obligations.

Use `hCf f c hf` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unitary_corollary_of_estimates (hC : CoreStar) (hD : DjWB) (hG : GfWB) (hM : WBmul) :
    Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator ∧ Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator := by
  constructor
  · intro k j ρ Wp Wq _ _ _ _ _ o κ Θ χ hΘ hχ Q mm₀ A₀ hQ
    obtain ⟨hcd, Cφ, hWB⟩ := hD k j ρ χ (Q + o) hχ
    obtain ⟨C, hCf⟩ := hC k j ρ Wp Wq o κ 0 Θ χ (fun g => χ (DjU k j ρ g)) hΘ hχ Q mm₀ A₀ hQ hcd
      (fun g hg => image_eq_zero_of_notMem_tsupport hg) ⟨Cφ, by simpa using hWB⟩
    refine ⟨C, fun f c hf => ?_⟩
    have := hCf f c hf
    simp only [Nat.cast_zero, zero_mul, sub_zero] at this
    exact this
  · intro k j ρ Wp Wq _ _ _ _ _ z z' o κ Θ χ χε ε hΘ hχ hε Q mm₀ A₀ hQ
    obtain ⟨hcd, C1, h1⟩ := hD k j ρ χ (Q + o) hχ
    obtain ⟨hcg, C2, h2⟩ := hG k (j + ρ) z z' χε ε (Q + o) hε
    obtain ⟨C3, h3⟩ := hM k (j + ρ) _ _ _ _ (Q + o) C1 C2 0 0 hcd hcg h1 h2
    rw [zero_add] at h3
    obtain ⟨C, hCf⟩ := hC k j ρ Wp Wq o κ (2 * (j + ρ + 1)) Θ χ
      (fun g => χ (DjU k j ρ g) * ((χε (Gf k (j + ρ) z z' g) : ℝ) : ℂ)) hΘ hχ Q mm₀ A₀ hQ (hcd.mul hcg)
      (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg]) ⟨C3, h3⟩
    refine ⟨C, fun f c hf => ?_⟩
    have := hCf f c hf
    convert this using 2
    · rfl
    · push_cast; ring

end PI.UnitaryCorollaryDerivatives
