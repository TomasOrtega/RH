import Mathlib

namespace GlobalTheory.ClosingLemmaSecond

/- English proof (translation)
Introduce `R _ _ _ I q hq`. Take `⟨k, hk⟩` from `Ideal.exists_pow_inf_eq_pow_smul I (Ideal.span {q} : Submodule R R)`. Use `⟨k, fun n a ha => ?_⟩` and prove the remaining obligations. Establish `hmem : q * a ∈ I ^ (n + k) • (⊤ : Submodule R R) ⊓ Ideal.span {q}`. Use `Submodule.mem_inf.2 ⟨?_, Ideal.mem_span_singleton.2 ⟨a, rfl⟩⟩` and prove the remaining obligations.

Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top]`. Conclude with `ha`. Rewrite `hmem` using `[hk (n + k) (by omega), Nat.add_sub_cancel]`. Establish `hle : I ^ n • (I ^ k • (⊤ : Submodule R R) ⊓ Ideal.span {q}) ≤ I ^ n • Ideal.span {q}` using `Submodule.smul_le.2 fun r hr x hx => Submodule.smul_mem_smul hr (Submodule.mem_inf.1 hx).2`. Establish `h2` using `hle hmem`.

Rewrite `h2` using `[Ideal.smul_eq_mul, mul_comm, Ideal.mem_span_singleton_mul]`. Take `⟨z, hz, hzq⟩` from `h2`. Rewrite using `[← mul_left_cancel₀ hq hzq]` and apply the resulting hypothesis.
-/
theorem main : ∀ {R : Type} [inst : CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) {q : R}, q ≠ (0 : R) → ∃ (c : ℕ), ∀ (n : ℕ) (a : R), q * a ∈ I ^ (n + c) → a ∈ I ^ n := by
  intro R _ _ _ I q hq
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (Ideal.span {q} : Submodule R R)
  refine ⟨k, fun n a ha => ?_⟩
  have hmem : q * a ∈ I ^ (n + k) • (⊤ : Submodule R R) ⊓ Ideal.span {q} := by
    refine Submodule.mem_inf.2 ⟨?_, Ideal.mem_span_singleton.2 ⟨a, rfl⟩⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact ha
  rw [hk (n + k) (by omega), Nat.add_sub_cancel] at hmem
  have hle : I ^ n • (I ^ k • (⊤ : Submodule R R) ⊓ Ideal.span {q}) ≤ I ^ n • Ideal.span {q} :=
    Submodule.smul_le.2 fun r hr x hx => Submodule.smul_mem_smul hr (Submodule.mem_inf.1 hx).2
  have h2 := hle hmem
  rw [Ideal.smul_eq_mul, mul_comm, Ideal.mem_span_singleton_mul] at h2
  obtain ⟨z, hz, hzq⟩ := h2
  rwa [← mul_left_cancel₀ hq hzq]

end GlobalTheory.ClosingLemmaSecond
