import Mathlib

namespace Bl.general_b_fact_right_version

/- English proof (translation)
Introduce `E Ω _ _ _ σ y hy`. Establish `hmem : ∀ k : ℕ, (σ ^ k) y ∈ (minpoly E y).rootSet Ω`. Introduce `k`. Rewrite using `[Polynomial.mem_rootSet]`. Use `⟨minpoly.ne_zero hy, ?_⟩` and prove the remaining obligations.

Establish `h` using `Polynomial.aeval_algHom_apply ((σ ^ k : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) y (minpoly E y)`. Rewrite `h` using `[minpoly.aeval, map_zero]`. Simplify using `using h`. Take `⟨a, b, hab, he⟩` from `Set.Finite.exists_lt_map_eq_of_forall_mem (f := fun k : ℕ => (σ ^ k) y) hmem (Polynomial.rootSet_finite _ _)`. Use `⟨b - a, by omega, ?_⟩` and prove the remaining obligations.

Establish `hb : b = a + (b - a)` using `by omega`. Rewrite `he` using `[hb, pow_add, AlgEquiv.mul_apply]`. Conclude with `((σ ^ a).injective he).symm`.
-/
theorem goal1 :
  ∀ {E Ω : Type} [inst : Field.{0} E] [inst_1 : Field.{0} Ω] [inst_2 : Algebra.{0, 0} E Ω] (σ : AlgEquiv.{0, 0, 0} E Ω Ω)
  (y : Ω),
  IsIntegral.{0, 0} E y →
    Exists.{1} fun (n : Nat) ↦ And (Ne.{1} n 0) (Eq.{1} (DFunLike.coe.{1, 1, 1} (HPow.hPow.{0, 0, 0} σ n) y) y) := by
  intro E Ω _ _ _ σ y hy
  have hmem : ∀ k : ℕ, (σ ^ k) y ∈ (minpoly E y).rootSet Ω := by
    intro k
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hy, ?_⟩
    have h := Polynomial.aeval_algHom_apply ((σ ^ k : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) y (minpoly E y)
    rw [minpoly.aeval, map_zero] at h
    simpa using h
  obtain ⟨a, b, hab, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun k : ℕ => (σ ^ k) y) hmem (Polynomial.rootSet_finite _ _)
  refine ⟨b - a, by omega, ?_⟩
  have hb : b = a + (b - a) := by omega
  rw [hb, pow_add, AlgEquiv.mul_apply] at he
  exact ((σ ^ a).injective he).symm

end Bl.general_b_fact_right_version
