import Mathlib

namespace GlobalTheory.CompanionTheory.Exterior

/- English proof (translation)
Introduce `Ω V _ _ _ n e he h`. Set `f : (Fin n → Ω) →ₗ[Ω] V` to `Fintype.linearCombination Ω e`. Establish `hf : LinearMap.ker f = ⊥` using `LinearMap.ker_eq_bot.2 he.fintypeLinearCombination_injective`. Take `⟨π, hπ⟩` from `f.exists_leftInverse_of_injective hf`. Establish `hπe : ∀ j, π (e j) = Pi.single j 1`.

Introduce `j`. Establish `h2` using `LinearMap.congr_fun hπ (Pi.single j 1)`. Simplify `h2` using `[f, Fintype.linearCombination_apply_single]`. Set `D : V [⋀^Fin n]→ₗ[Ω] Ω` to `(Matrix.detRowAlternating (n := Fin n) (R := Ω)).compLinearMap π`. Establish `h1` using `exteriorPower.alternatingMapLinearEquiv_apply_ιMulti D e`.

Rewrite `h1` using `[h, map_zero]`. Establish `h3 : D e = 1`. Establish `h4 : (fun i => π (e i)) = (1 : Matrix (Fin n) (Fin n) Ω)`. Use extensionality with `i j`. Simplify using `[hπe, Matrix.one_apply, Pi.single_apply, eq_comm]`.

Express the relevant statement in the definitionally equal form `Matrix.det (fun i => π (e i)) = 1`. Rewrite using `[h4, Matrix.det_one]`. Rewrite `h1` using `[h3]`. Conclude with `zero_ne_one h1`.
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
