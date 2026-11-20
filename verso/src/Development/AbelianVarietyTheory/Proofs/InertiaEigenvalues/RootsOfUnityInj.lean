import Mathlib

namespace GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues

/- English proof (translation)
Establish `key : ∀ z : O, z ^ M = 1 → f z = 1 → z = 1`. Introduce `z hz hfz`. Establish `h` using `geom_sum_mul z M`. Rewrite `h` using `[hz, sub_self]`. Break down `mul_eq_zero.mp h with h1 | h1` into its components or cases.

It suffices to derive a contradiction. Apply `hM` to reduce the goal to its premises. Establish `h2` using `congrArg f h1`. Simplify `h2` using `[map_sum, map_pow, hfz]`. Conclude with `sub_eq_zero.mp h1`.

Establish `hM0 : M ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hM`. Establish `hsub : M - 1 + 1 = M` using `Nat.sub_add_cancel (Nat.pos_of_ne_zero hM0)`. Establish `hyM : y ^ (M - 1) * y = 1` using `by rw [← pow_succ, hsub, hy]`.

Establish `hz : (x * y ^ (M - 1)) ^ M = 1`. Rewrite using `[mul_pow, hx, ← pow_mul, mul_comm (M - 1) M, pow_mul, hy, one_pow, one_mul]`. Establish `hfz : f (x * y ^ (M - 1)) = 1`. Rewrite using `[map_mul, map_pow, hf, ← pow_succ', hsub, ← map_pow, hy, map_one]`. Establish `h1` using `key _ hz hfz`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem rootsOfUnity_inj {O k : Type} [CommRing O] [IsDomain O] [Field k] (f : O →+* k) {M : ℕ}
    (hM : (M : k) ≠ 0) {x y : O} (hx : x ^ M = 1) (hy : y ^ M = 1) (hf : f x = f y) : x = y := by
  have key : ∀ z : O, z ^ M = 1 → f z = 1 → z = 1 := by
    intro z hz hfz
    have h := geom_sum_mul z M
    rw [hz, sub_self] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exfalso
      apply hM
      have h2 := congrArg f h1
      simpa [map_sum, map_pow, hfz] using h2
    · exact sub_eq_zero.mp h1
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp at hM
  have hsub : M - 1 + 1 = M := Nat.sub_add_cancel (Nat.pos_of_ne_zero hM0)
  have hyM : y ^ (M - 1) * y = 1 := by rw [← pow_succ, hsub, hy]
  have hz : (x * y ^ (M - 1)) ^ M = 1 := by
    rw [mul_pow, hx, ← pow_mul, mul_comm (M - 1) M, pow_mul, hy, one_pow, one_mul]
  have hfz : f (x * y ^ (M - 1)) = 1 := by
    rw [map_mul, map_pow, hf, ← pow_succ', hsub, ← map_pow, hy, map_one]
  have h1 := key _ hz hfz
  calc x = x * (y ^ (M - 1) * y) := by rw [hyM, mul_one]
    _ = (x * y ^ (M - 1)) * y := by ring
    _ = y := by rw [h1, one_mul]

/- English proof (translation)
Introduce `f _ hM _ _ hx hy hf` and use `rootsOfUnity_inj f hM hx hy hf`.
-/
theorem main : ∀ {O k : Type} [inst : CommRing O] [IsDomain O] [inst_2 : Field k] (f : O →+* k) {M : ℕ},
    (↑M : k) ≠ (0 : k) → ∀ {x y : O}, x ^ M = (1 : O) → y ^ M = (1 : O) →
      (f : O → k) x = (f : O → k) y → x = y :=
  fun f _ hM _ _ hx hy hf => rootsOfUnity_inj f hM hx hy hf

end GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues
