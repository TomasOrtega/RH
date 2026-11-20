import Mathlib

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Establish `hn : ∀ n : ℕ, z = (3 : ℤ) ^ n • (z * w ^ n)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_mul_assoc, smul_smul, pow_succ', pow_succ, mul_assoc]`. Set `b` to `Module.Free.chooseBasis ℤ R`. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`.

Establish `hd : ∀ n : ℕ, (3 : ℤ) ^ n ∣ b.repr z i`. Introduce `n`. Use `⟨b.repr (z * w ^ n) i, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [hn n]`. Rewrite using `[map_zsmul]`.

Simplify using the standard rewrite rules. Simplify using `only [map_zero, Finsupp.coe_zero, Pi.zero_apply]`. Assume the negation of the conclusion as `hne`. Establish `h1` using `Int.natAbs_le_of_dvd_ne_zero (hd (b.repr z i).natAbs) hne`. Rewrite `h1` using `[Int.natAbs_pow]`.

Establish `h2 : (b.repr z i).natAbs < 3 ^ (b.repr z i).natAbs` using `Nat.lt_pow_self (by norm_num)`. Establish `h3 : (3 : ℤ).natAbs = 3` using `rfl`. Rewrite `h1` using `[h3]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem UpperTheory.V.KT.torsfree_sep {R : Type} [Ring R] [Module.Free ℤ R]
    (z w : R) (h : z = (3 : ℤ) • (z * w)) : z = 0 := by
  have hn : ∀ n : ℕ, z = (3 : ℤ) ^ n • (z * w ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc z = (3 : ℤ) • (z * w) := h
        _ = (3 : ℤ) • (((3 : ℤ) ^ n • (z * w ^ n)) * w) := by rw [← ih]
        _ = (3 : ℤ) ^ (n + 1) • (z * w ^ (n + 1)) := by
          rw [smul_mul_assoc, smul_smul, pow_succ', pow_succ, mul_assoc]
  let b := Module.Free.chooseBasis ℤ R
  apply b.repr.injective
  ext i
  have hd : ∀ n : ℕ, (3 : ℤ) ^ n ∣ b.repr z i := by
    intro n
    refine ⟨b.repr (z * w ^ n) i, ?_⟩
    conv_lhs => rw [hn n]
    rw [map_zsmul]
    simp
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_contra hne
  have h1 := Int.natAbs_le_of_dvd_ne_zero (hd (b.repr z i).natAbs) hne
  rw [Int.natAbs_pow] at h1
  have h2 : (b.repr z i).natAbs < 3 ^ (b.repr z i).natAbs := Nat.lt_pow_self (by norm_num)
  have h3 : (3 : ℤ).natAbs = 3 := rfl
  rw [h3] at h1
  omega

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ k ih`. Take `⟨w, hw⟩` from `ih`. Use `⟨(k : ℤ) • 1 + w * (1 + z), ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ, hw]`. Use `push_cast`. Simplify using `only [add_smul, one_smul, mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
private theorem UpperTheory.V.KT.torsfree_binom {R : Type} [Ring R] (z : R) (k : ℕ) :
    ∃ w : R, (1 + z) ^ k = 1 + (k : ℤ) • z + z * z * w := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨(k : ℤ) • 1 + w * (1 + z), ?_⟩
    rw [pow_succ, hw]
    push_cast
    simp only [add_smul, one_smul, mul_add, add_mul, mul_one, one_mul, smul_mul_assoc,
      mul_smul_comm, mul_assoc]
    abel

/- English proof (translation)
Introduce `R _ _ _ u x k`. Establish `h3 : ∀ y : R, 3 * y = (3 : ℤ) • y`. Introduce `y`. Rewrite using `[zsmul_eq_mul]`. Evaluate the numerical expressions.

Proceed by induction on `k using Nat.strong_induction_on generalizing u x with`. Consider the case `_ k ih`. Introduce `hk hu hpow`. Rewrite `hu` using `[h3]`. Distinguish the cases in `hdiv : 3 ∣ k`.

Take `⟨m, rfl⟩` from `hdiv`. Establish `hm : 0 < m` using `by omega`. Take `⟨w, hw⟩` from `UpperTheory.V.KT.torsfree_binom ((3 : ℤ) • x) m`. Rewrite `hw` using `[← hu]`. Use `set y : R := (m : ℤ) • x + x * ((3 : ℤ) • x) * w with hy`.

Establish `hv : u ^ m = 1 + (3 : ℤ) • y`. Rewrite using `[hw, hy, smul_add, smul_comm (3 : ℤ) (m : ℤ), add_assoc, smul_mul_assoc (3 : ℤ) x, smul_mul_assoc (3 : ℤ)]`. Establish `hv3 : (1 + (3 : ℤ) • y) ^ 3 = 1`. Rewrite using `[← hv, ← pow_mul, mul_comm, hpow]`. Establish `hz : (3 : ℤ) • y = 0`.

Apply `UpperTheory.V.KT.torsfree_sep _ (-y - y * y)` to reduce the goal to its premises. Establish `hinj : Function.Injective (fun t : R => (3 : ℤ) • t)` using `smul_right_injective R (by norm_num)`. Apply `hinj` to reduce the goal to its premises. Establish `e : (3 : ℤ) • ((3 : ℤ) • y) - (3 : ℤ) • ((3 : ℤ) • (((3 : ℤ) • y) * (-y - y * y))) = (1 + (3 : ℤ) • y) ^ 3 - 1`. Simplify using `only [pow_succ, pow_zero, mul_add, add_mul, mul_sub, mul_neg, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]`.

Use `module`. Rewrite `e` using `[hv3, sub_self, sub_eq_zero]`. Conclude with `e`. Rewrite `hv` using `[hz, add_zero]`. Conclude with `ih m (by omega) u x hm (by rw [h3]; exact hu) hv`.

Take `⟨w, hw⟩` from `UpperTheory.V.KT.torsfree_binom ((3 : ℤ) • x) k`. Rewrite `hw` using `[← hu, hpow, add_assoc, left_eq_add]`. Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab⟩ : ∃ a b : ℤ, a * k + 3 * b = 1 := by`. Establish `: (k : ℤ) % 3 = 1 ∨ (k : ℤ) % 3 = 2` using `by omega`. Break down `this with h | h` into its components or cases.

Conclude with `⟨1, -((k : ℤ) / 3), by omega⟩`. Conclude with `⟨-1, (k : ℤ) / 3 + 1, by omega⟩`. Establish `hz : (3 : ℤ) • x = 0`. Apply `UpperTheory.V.KT.torsfree_sep _ (b • 1 - a • (x * w))` to reduce the goal to its premises. Establish `e : (3 : ℤ) • (((3 : ℤ) • x) * (b • 1 - a • (x * w))) = (a * k + 3 * b) • ((3 : ℤ) • x) - a • ((k : ℤ) • ((3 : ℤ) • x) + (3 : ℤ) • x * (3 : ℤ) • x * w)`.

Simplify using `only [mul_sub, mul_one, smul_mul_assoc, mul_smul_comm, mul_assoc]`. Use `module`. Rewrite using `[e, hw, hab, smul_zero, sub_zero, one_smul]`. Rewrite using `[hu, hz, add_zero]`.
-/
theorem UpperTheory.V.KT.torsfree :
    ∀ (R : Type) [Ring R] [Module.Free ℤ R] [Module.Finite ℤ R] (u x : R) (k : ℕ), 0 < k →
    u = 1 + 3 * x → u ^ k = 1 → u = 1 := by
  intro R _ _ _ u x k
  have h3 : ∀ y : R, 3 * y = (3 : ℤ) • y := by
    intro y
    rw [zsmul_eq_mul]; norm_num
  induction k using Nat.strong_induction_on generalizing u x with
  | _ k ih =>
    intro hk hu hpow
    rw [h3] at hu
    by_cases hdiv : 3 ∣ k
    · obtain ⟨m, rfl⟩ := hdiv
      have hm : 0 < m := by omega
      obtain ⟨w, hw⟩ := UpperTheory.V.KT.torsfree_binom ((3 : ℤ) • x) m
      rw [← hu] at hw
      set y : R := (m : ℤ) • x + x * ((3 : ℤ) • x) * w with hy
      have hv : u ^ m = 1 + (3 : ℤ) • y := by
        rw [hw, hy, smul_add, smul_comm (3 : ℤ) (m : ℤ), add_assoc, smul_mul_assoc (3 : ℤ) x,
          smul_mul_assoc (3 : ℤ)]
      have hv3 : (1 + (3 : ℤ) • y) ^ 3 = 1 := by
        rw [← hv, ← pow_mul, mul_comm, hpow]
      have hz : (3 : ℤ) • y = 0 := by
        apply UpperTheory.V.KT.torsfree_sep _ (-y - y * y)
        have hinj : Function.Injective (fun t : R => (3 : ℤ) • t) :=
          smul_right_injective R (by norm_num)
        apply hinj
        have e : (3 : ℤ) • ((3 : ℤ) • y) - (3 : ℤ) • ((3 : ℤ) • (((3 : ℤ) • y) * (-y - y * y)))
            = (1 + (3 : ℤ) • y) ^ 3 - 1 := by
          simp only [pow_succ, pow_zero, mul_add, add_mul, mul_sub, mul_neg, mul_one, one_mul,
            smul_mul_assoc, mul_smul_comm, mul_assoc]
          module
        rw [hv3, sub_self, sub_eq_zero] at e
        exact e
      rw [hz, add_zero] at hv
      exact ih m (by omega) u x hm (by rw [h3]; exact hu) hv
    · obtain ⟨w, hw⟩ := UpperTheory.V.KT.torsfree_binom ((3 : ℤ) • x) k
      rw [← hu, hpow, add_assoc, left_eq_add] at hw
      obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * k + 3 * b = 1 := by
        have : (k : ℤ) % 3 = 1 ∨ (k : ℤ) % 3 = 2 := by omega
        rcases this with h | h
        · exact ⟨1, -((k : ℤ) / 3), by omega⟩
        · exact ⟨-1, (k : ℤ) / 3 + 1, by omega⟩
      have hz : (3 : ℤ) • x = 0 := by
        apply UpperTheory.V.KT.torsfree_sep _ (b • 1 - a • (x * w))
        have e : (3 : ℤ) • (((3 : ℤ) • x) * (b • 1 - a • (x * w)))
            = (a * k + 3 * b) • ((3 : ℤ) • x)
              - a • ((k : ℤ) • ((3 : ℤ) • x) + (3 : ℤ) • x * (3 : ℤ) • x * w) := by
          simp only [mul_sub, mul_one, smul_mul_assoc, mul_smul_comm, mul_assoc]
          module
        rw [e, hw, hab, smul_zero, sub_zero, one_smul]
      rw [hu, hz, add_zero]
