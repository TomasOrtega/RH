import Mathlib

noncomputable section

namespace Formalism.MainNotions.N.Ln34.AdicCompletionMax

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible (mt Ideal.span_singleton_eq_bot.mp hp0) hϖ`. Use `⟨n, Nat.one_le_iff_ne_zero.mpr ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hn` using `[pow_zero, Ideal.span_singleton_one, Ideal.span_singleton_eq_top]`.

Conclude with `absurd hn ((IsLocalRing.mem_maximalIdeal _).1 hpm)`. Rewrite using `[hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]`.
-/
theorem span_eq_max_pow {p : O} (hp0 : p ≠ 0) (hpm : p ∈ IsLocalRing.maximalIdeal O) :
    ∃ k : ℕ, 1 ≤ k ∧ Ideal.span {p} = IsLocalRing.maximalIdeal O ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (mt Ideal.span_singleton_eq_bot.mp hp0) hϖ
  refine ⟨n, Nat.one_le_iff_ne_zero.mpr ?_, ?_⟩
  · rintro rfl
    rw [pow_zero, Ideal.span_singleton_one, Ideal.span_singleton_eq_top] at hn
    exact absurd hn ((IsLocalRing.mem_maximalIdeal _).1 hpm)
  · rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

/- English proof (translation)
Establish `key : ∀ n : ℕ, (J ^ k) ^ n = J ^ (k * n)` using `fun n => (pow_mul J k n).symm`. Establish `hkn : ∀ n : ℕ, n ≤ k * n` using `fun n => by simpa using Nat.mul_le_mul hk (le_refl n)`. Establish `hle : ∀ {a b : ℕ}, a ≤ b → J ^ b • (⊤ : Submodule O O) ≤ J ^ a • ⊤` using `fun hab => Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)`. Use `{ toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun f hf => ?_⟩ }` and prove the remaining obligations. Use `IsHausdorff.haus h.toIsHausdorff x fun n => ?_` and prove the remaining obligations.

Rewrite using `[key]`. Conclude with `hx (k * n)`. Take `⟨L, hL⟩` from `IsPrecomplete.prec h.toIsPrecomplete (f := fun n => f (k * n)) (fun {a b} hab => by`. Rewrite using `[key]`. Conclude with `hf (Nat.mul_le_mul (le_refl k) hab))`.

Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Establish `h1 : f n ≡ f (k * n) [SMOD (J ^ n • ⊤ : Submodule O O)]` using `hf (hkn n)`. Establish `h2 : f (k * n) ≡ L [SMOD (J ^ n • ⊤ : Submodule O O)]`. Establish `h3` using `hL n`. Rewrite `h3` using `[key]`.

Conclude with `SModEq.mono (hle (hkn n)) h3`. Conclude with `h1.trans h2`.
-/
private theorem isAdicComplete_of_isAdicComplete_pow {J : Ideal O} {k : ℕ} (hk : 1 ≤ k)
    (h : IsAdicComplete (J ^ k) O) : IsAdicComplete J O := by
  have key : ∀ n : ℕ, (J ^ k) ^ n = J ^ (k * n) := fun n => (pow_mul J k n).symm
  have hkn : ∀ n : ℕ, n ≤ k * n := fun n => by simpa using Nat.mul_le_mul hk (le_refl n)
  have hle : ∀ {a b : ℕ}, a ≤ b → J ^ b • (⊤ : Submodule O O) ≤ J ^ a • ⊤ :=
    fun hab => Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  · refine IsHausdorff.haus h.toIsHausdorff x fun n => ?_
    rw [key]
    exact hx (k * n)
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := fun n => f (k * n))
      (fun {a b} hab => by
        rw [key]
        exact hf (Nat.mul_le_mul (le_refl k) hab))
    refine ⟨L, fun n => ?_⟩
    have h1 : f n ≡ f (k * n) [SMOD (J ^ n • ⊤ : Submodule O O)] := hf (hkn n)
    have h2 : f (k * n) ≡ L [SMOD (J ^ n • ⊤ : Submodule O O)] := by
      have h3 := hL n
      rw [key] at h3
      exact SModEq.mono (hle (hkn n)) h3
    exact h1.trans h2

/- English proof (translation)
Take `⟨k, hk, hkeq⟩` from `span_eq_max_pow hp0 hpm`. Rewrite `h` using `[hkeq]`. Conclude with `isAdicComplete_of_isAdicComplete_pow hk h`.
-/
theorem isAdicComplete_max {p : O} (hp0 : p ≠ 0) (hpm : p ∈ IsLocalRing.maximalIdeal O)
    [h : IsAdicComplete (Ideal.span {p}) O] : IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  obtain ⟨k, hk, hkeq⟩ := span_eq_max_pow hp0 hpm
  rw [hkeq] at h
  exact isAdicComplete_of_isAdicComplete_pow hk h

end Formalism.MainNotions.N.Ln34.AdicCompletionMax
