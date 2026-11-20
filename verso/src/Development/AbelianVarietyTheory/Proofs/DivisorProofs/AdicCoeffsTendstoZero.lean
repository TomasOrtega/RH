import Mathlib
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ _ _ M _ _ r s hs X z hz`. Use `set m := maximalIdeal R`. Establish `coef : ∀ (x : M) (k : ℕ), x ∈ (m ^ k • ⊤ : Submodule R M) → ∃ a : Fin r → R, x = ∑ j, a j • s j ∧ ∀ j, a j ∈ m ^ k`. Introduce `x k hx`. Rewrite `hx` using `[← hs, Submodule.mem_ideal_smul_span_iff_exists_sum]`.

Take `⟨a, ha, hsum⟩` from `hx`. Use `⟨a, ?_, ha⟩` and prove the remaining obligations. Rewrite using `[← hsum, Finsupp.sum_fintype]`. Introduce `j`. Simplify using the standard rewrite rules.

Use `haveI : Module.Finite R M := ⟨by rw [← hs]; exact Submodule.fg_span (Set.finite_range s)⟩`. Establish `krull : (⨅ i : ℕ, m ^ i • ⊤ : Submodule R M) = ⊥` using `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top`. Establish `anti : ∀ {a b : ℕ}, a ≤ b → (m ^ b • ⊤ : Submodule R M) ≤ m ^ a • ⊤` using `fun h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)`. Establish `choiceχ : ∀ χ, ∃ a : Fin r → R, z χ = ∑ j, a j • s j ∧ ∀ n, (¬ ∀ j, a j ∈ m ^ n) → z χ ∉ (m ^ n • ⊤ : Submodule R M)`. Introduce `χ`.

Distinguish the cases in `h : ∃ n, z χ ∉ (m ^ n • ⊤ : Submodule R M)`. Use `set N := Nat.find h with hN`. Establish `hN0 : N ≠ 0`. Introduce `h0`. Use `Nat.find_spec h` as an intermediate fact.

Rewrite `this` using `[← hN, h0, pow_zero, Ideal.one_eq_top, Submodule.top_smul]`. Conclude with `this Submodule.mem_top`. Establish `hmem : z χ ∈ (m ^ (N - 1) • ⊤ : Submodule R M)`. Assume the negation of the conclusion as `hc`. Use `Nat.find_min' h hc` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Take `⟨a, ha, hm⟩` from `coef _ _ hmem`. Use `⟨a, ha, fun n hn hzn => hn fun j => ?_⟩` and prove the remaining obligations. Establish `hlt : n < N`. Assume the negation of the conclusion as `hle`.

Use `push_neg at hle`. Conclude with `(Nat.find_spec h) (anti hle hzn)`. Conclude with `Ideal.pow_le_pow_right (by omega) (hm j)`. Use `push_neg at h`. Establish `hz0 : z χ = 0`.

Establish `: z χ ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R M)` using `Submodule.mem_iInf _ |>.mpr h`. Rewrite `this` using `[krull]`. Conclude with `(Submodule.mem_bot R).mp this`. Use `⟨0, by simp [hz0], fun n hn _ => hn fun j => ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Use `choose c hc hbad using choiceχ`. Use `⟨c, hc, fun n => (hz n).subset ?_⟩` and prove the remaining obligations. Introduce `χ hχ`. Conclude with `hbad χ n hχ`.
-/
theorem adic_coeffs_tendsto_zero :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) = ⊤ → ∀ (X : Type) (z : X → M), (∀ n : ℕ, {χ | z χ ∉ (maximalIdeal R ^ n • ⊤ : Submodule R M)}.Finite) → ∃ c : X → Fin r → R, (∀ χ, z χ = ∑ j, c χ j • s j) ∧ ∀ n : ℕ, {χ | ¬ ∀ j, c χ j ∈ maximalIdeal R ^ n}.Finite := by
  intro R _ _ _ M _ _ r s hs X z hz
  classical
  set m := maximalIdeal R

  have coef : ∀ (x : M) (k : ℕ), x ∈ (m ^ k • ⊤ : Submodule R M) →
      ∃ a : Fin r → R, x = ∑ j, a j • s j ∧ ∀ j, a j ∈ m ^ k := by
    intro x k hx
    rw [← hs, Submodule.mem_ideal_smul_span_iff_exists_sum] at hx
    obtain ⟨a, ha, hsum⟩ := hx
    refine ⟨a, ?_, ha⟩
    rw [← hsum, Finsupp.sum_fintype]
    intro j; simp
  haveI : Module.Finite R M := ⟨by rw [← hs]; exact Submodule.fg_span (Set.finite_range s)⟩
  have krull : (⨅ i : ℕ, m ^ i • ⊤ : Submodule R M) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  have anti : ∀ {a b : ℕ}, a ≤ b → (m ^ b • ⊤ : Submodule R M) ≤ m ^ a • ⊤ :=
    fun h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  have choiceχ : ∀ χ, ∃ a : Fin r → R, z χ = ∑ j, a j • s j ∧
      ∀ n, (¬ ∀ j, a j ∈ m ^ n) → z χ ∉ (m ^ n • ⊤ : Submodule R M) := by
    intro χ
    by_cases h : ∃ n, z χ ∉ (m ^ n • ⊤ : Submodule R M)
    · set N := Nat.find h with hN
      have hN0 : N ≠ 0 := by
        intro h0
        have := Nat.find_spec h
        rw [← hN, h0, pow_zero, Ideal.one_eq_top, Submodule.top_smul] at this
        exact this Submodule.mem_top
      have hmem : z χ ∈ (m ^ (N - 1) • ⊤ : Submodule R M) := by
        by_contra hc
        have := Nat.find_min' h hc
        omega
      obtain ⟨a, ha, hm⟩ := coef _ _ hmem
      refine ⟨a, ha, fun n hn hzn => hn fun j => ?_⟩
      have hlt : n < N := by
        by_contra hle
        push_neg at hle
        exact (Nat.find_spec h) (anti hle hzn)
      exact Ideal.pow_le_pow_right (by omega) (hm j)
    · push_neg at h
      have hz0 : z χ = 0 := by
        have : z χ ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R M) := Submodule.mem_iInf _ |>.mpr h
        rw [krull] at this
        exact (Submodule.mem_bot R).mp this
      refine ⟨0, by simp [hz0], fun n hn _ => hn fun j => ?_⟩
      simp
  choose c hc hbad using choiceχ
  refine ⟨c, hc, fun n => (hz n).subset ?_⟩
  intro χ hχ
  exact hbad χ n hχ

end GlobalTheory
