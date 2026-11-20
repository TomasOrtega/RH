import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial GroundTheory.Heights₂.Heights

/- English proof (translation)
Introduce `Ψ _ _ N j R hR h`. Use `⟨(mem_homogeneousSubmodule _ _).2 hR, ?_⟩` and prove the remaining obligations. Introduce and unpack `σ ⟨τ, a, b, hab, hblock, rfl⟩`. Use `MvPolynomial.funext fun lam => ?_` and prove the remaining obligations. Rewrite using `[eval_rename, map_neg]`.

Conclude with `eq_neg_of_add_eq_zero_right (h τ a b hab hblock lam)`.
-/
theorem mem_antisymSpace_of_pointwise :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (R : MvPolynomial (Ψ × Fin N) ℝ),
      R.IsHomogeneous (antisymDegree Ψ N + 1) →
      (∀ (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) →
        ∀ lam : Ψ × Fin N → ℝ, eval lam R + eval (lam ∘ Equiv.swap (τ, a) (τ, b)) R = 0) →
      R ∈ antisymSpace Ψ N j := by
  intro Ψ _ _ N j R hR h
  refine ⟨(mem_homogeneousSubmodule _ _).2 hR, ?_⟩
  rintro σ ⟨τ, a, b, hab, hblock, rfl⟩
  refine MvPolynomial.funext fun lam => ?_
  rw [eval_rename, map_neg]
  exact eq_neg_of_add_eq_zero_right (h τ a b hab hblock lam)

end GlobalTheory.CompanionTheory.Ar.PB
