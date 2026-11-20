import Mathlib

namespace GroundTheory.Variant₂.N1

/- English proof (translation)
Establish `hmem : ∀ n : ℕ, (σ ^ n) x ∈ p.rootSet Ω` using `fun n => by`. Rewrite using `[Polynomial.mem_rootSet_of_ne hp, Polynomial.aeval_algHom_apply, hx, map_zero]`. Establish `: Finite (p.rootSet Ω)` using `(Polynomial.rootSet_finite p Ω).to_subtype`. Set `f : ℕ → p.rootSet Ω` to `fun n => ⟨(σ ^ n) x, hmem n⟩`. Take `⟨i, j, hne, hij⟩` from `Finite.exists_ne_map_eq_of_infinite f`.

Establish `key : (σ ^ i) x = (σ ^ j) x` using `congrArg Subtype.val hij`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Use `⟨j - i, Nat.sub_pos_of_lt h, ?_⟩` and prove the remaining obligations. Apply `(σ ^ i).injective` to reduce the goal to its premises. Rewrite using `[← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le, key]`.

Use `⟨i - j, Nat.sub_pos_of_lt h, ?_⟩` and prove the remaining obligations. Apply `(σ ^ j).injective` to reduce the goal to its premises. Rewrite using `[← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le, key]`.
-/
theorem exists_pow_apply_eq_self_of_aeval_eq_zero {K : Type*} [Field K] {Ω : Type*} [Field Ω]
    [Algebra K Ω] (σ : Gal(Ω/K)) {p : Polynomial K} (hp : p ≠ 0) {x : Ω}
    (hx : Polynomial.aeval x p = 0) : ∃ N : ℕ, 0 < N ∧ (σ ^ N) x = x := by
  have hmem : ∀ n : ℕ, (σ ^ n) x ∈ p.rootSet Ω := fun n => by
    rw [Polynomial.mem_rootSet_of_ne hp, Polynomial.aeval_algHom_apply, hx, map_zero]
  have : Finite (p.rootSet Ω) := (Polynomial.rootSet_finite p Ω).to_subtype
  let f : ℕ → p.rootSet Ω := fun n => ⟨(σ ^ n) x, hmem n⟩
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : (σ ^ i) x = (σ ^ j) x := congrArg Subtype.val hij
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨j - i, Nat.sub_pos_of_lt h, ?_⟩
    apply (σ ^ i).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le, key]
  · refine ⟨i - j, Nat.sub_pos_of_lt h, ?_⟩
    apply (σ ^ j).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le, key]

end GroundTheory.Variant₂.N1
