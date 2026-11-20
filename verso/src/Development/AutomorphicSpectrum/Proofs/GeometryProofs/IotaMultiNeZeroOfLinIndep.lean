import Mathlib

namespace GlobalTheory.CompanionTheory.Exterior

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem ιMulti_ne_zero_of_linearIndependent :
    ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V),
      LinearIndependent Ω e → exteriorPower.ιMulti Ω n e ≠ 0 := by
  intro Ω V _ _ _ n e he h
  let f : (Fin n → Ω) →ₗ[Ω] V := Fintype.linearCombination Ω e
  have hf : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot.2 he.fintypeLinearCombination_injective
  obtain ⟨π, hπ⟩ := f.exists_leftInverse_of_injective hf
  have hπe : ∀ j, π (e j) = Pi.single j 1 := by
    intro j
    have h2 := LinearMap.congr_fun hπ (Pi.single j 1)
    simpa [f, Fintype.linearCombination_apply_single] using h2
  let D : V [⋀^Fin n]→ₗ[Ω] Ω :=
    (Matrix.detRowAlternating (n := Fin n) (R := Ω)).compLinearMap π
  have h1 := exteriorPower.alternatingMapLinearEquiv_apply_ιMulti D e
  rw [h, map_zero] at h1
  have h3 : D e = 1 := by
    have h4 : (fun i => π (e i)) = (1 : Matrix (Fin n) (Fin n) Ω) := by
      ext i j
      simp [hπe, Matrix.one_apply, Pi.single_apply, eq_comm]
    change Matrix.det (fun i => π (e i)) = 1
    rw [h4, Matrix.det_one]
  rw [h3] at h1
  exact zero_ne_one h1

end GlobalTheory.CompanionTheory.Exterior
