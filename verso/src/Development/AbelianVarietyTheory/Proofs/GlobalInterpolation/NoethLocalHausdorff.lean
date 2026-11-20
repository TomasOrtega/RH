import Mathlib

namespace GlobalTheory.NoetherianLocalHausdorff

/- English proof (translation)
Introduce `B _ _ _`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Establish `h : x ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal B) ^ n`. Rewrite using `[Ideal.mem_iInf]`. Introduce `n`.

Use `hx n` as an intermediate fact. Rewrite `this` using `[SModEq.zero, smul_eq_mul, Ideal.mul_top]`. Conclude with `this`. Rewrite `h` using `[Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal B).ne_top]`. Conclude with `(Submodule.mem_bot B).1 h`.
-/
theorem noeth_local_hausdorff : ∀ (B : Type) [inst : CommRing B] [inst_1 : IsLocalRing B] [IsNoetherianRing B],
    IsHausdorff (IsLocalRing.maximalIdeal B) B := by
  intro B _ _ _
  refine ⟨fun x hx => ?_⟩
  have h : x ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal B) ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    have := hx n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this
    exact this
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal B).ne_top] at h
  exact (Submodule.mem_bot B).1 h

end GlobalTheory.NoetherianLocalHausdorff
