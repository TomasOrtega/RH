import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.RightSub
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

open Formalism.BasicNotions UpperTheory.TP.RP

/- English proof (translation)
Unfold `ofTall`. Use `MvPolynomial.rename_injective _ fun a b hab => ?_` and prove the remaining obligations. Simplify using `only [Prod.mk.injEq, Sum.inl.injEq] at hab`. Conclude with `Prod.ext hab.2 hab.1`.
-/
private theorem ofTall_injective {n d : ℕ} :
    Function.Injective (ofTall (n := n) (d := d)) := by
  unfold ofTall
  refine MvPolynomial.rename_injective _ fun a b hab => ?_
  simp only [Prod.mk.injEq, Sum.inl.injEq] at hab
  exact Prod.ext hab.2 hab.1

/- English proof (translation)
Introduce `n d h μ _ h0`. Use `Formalism.GradedWeylDivisibility.hwNe ℂ d n h μ (ofTall_injective ?_)` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `h0`.
-/
theorem UpperTheory.TP.RP.jointNe :
    ∀ {n d : ℕ} (h : n ≤ d) (μ : Fin n → ℕ), Antitone μ → joint h μ ≠ 0 := by
  intro n d h μ _ h0
  refine Formalism.GradedWeylDivisibility.hwNe ℂ d n h μ (ofTall_injective ?_)
  rw [map_zero]
  exact h0
