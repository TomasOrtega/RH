import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.RegNorm

/- English proof (translation)
Establish `h1 : 1 ≤ q ^ m` using `Nat.one_le_pow _ _ hq`. Establish `h2 : 1 ≤ (q ^ l) ^ m` using `Nat.one_le_pow _ _ (pow_pos hq _)`. Establish `hZ : (((q ^ m : ℕ) : ℤ) - 1) * ∑ i ∈ Finset.range l, ((q ^ m : ℕ) : ℤ) ^ i = ((q ^ m : ℕ) : ℤ) ^ l - 1` using `mul_geom_sum _ _`. Establish `: (((q ^ m - 1) * ∑ i ∈ Finset.range l, q ^ (m * i) : ℕ) : ℤ) = (((q ^ l) ^ m - 1 : ℕ) : ℤ)`. Move the coercions through the operations in `[Nat.cast_sub h1, Nat.cast_sub h2]`.

Simplify using `only [pow_mul] at *`. Move the coercions through the operations in `at hZ`. Rewrite using `[hZ, ← pow_mul, ← pow_mul, mul_comm m l]`. Conclude with `this` after adjusting the coercions.
-/
theorem geom_mul (q m l : ℕ) (hq : 0 < q) :
    (q ^ m - 1) * ∑ i ∈ Finset.range l, q ^ (m * i) = (q ^ l) ^ m - 1 := by
  have h1 : 1 ≤ q ^ m := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ (q ^ l) ^ m := Nat.one_le_pow _ _ (pow_pos hq _)
  have hZ : (((q ^ m : ℕ) : ℤ) - 1) * ∑ i ∈ Finset.range l, ((q ^ m : ℕ) : ℤ) ^ i
      = ((q ^ m : ℕ) : ℤ) ^ l - 1 := mul_geom_sum _ _
  have : (((q ^ m - 1) * ∑ i ∈ Finset.range l, q ^ (m * i) : ℕ) : ℤ) = (((q ^ l) ^ m - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    simp only [pow_mul] at *
    push_cast at hZ
    rw [hZ, ← pow_mul, ← pow_mul, mul_comm m l]
  exact_mod_cast this

/- English proof (translation)
Establish `h1 : 1 ≤ q ^ m` using `Nat.one_le_pow _ _ hq`. Establish `hm : q ^ m ≡ 1 [MOD q ^ m - 1]` using `Nat.modEq_sub h1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_mul, ← pow_add, Nat.div_add_mod]`. Use `_ ≡ 1 ^ (x / m) * q ^ (x % m) [MOD q ^ m - 1] := (hm.pow _).mul_right _`.

Use `_ = q ^ (x % m) := by simp`.
-/
theorem pow_modEq_pow_mod (q m x : ℕ) (hq : 1 ≤ q) :
    q ^ x ≡ q ^ (x % m) [MOD q ^ m - 1] := by
  have h1 : 1 ≤ q ^ m := Nat.one_le_pow _ _ hq
  have hm : q ^ m ≡ 1 [MOD q ^ m - 1] := Nat.modEq_sub h1
  calc q ^ x = (q ^ m) ^ (x / m) * q ^ (x % m) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≡ 1 ^ (x / m) * q ^ (x % m) [MOD q ^ m - 1] := (hm.pow _).mul_right _
    _ = q ^ (x % m) := by simp

end GlobalTheory.Shin.RegNorm

namespace GlobalTheory.Shin.RegNorm

/- English proof (translation)
Use `set S := ∑ i ∈ Finset.range l, q ^ (m * i) with hSdef`. Establish `hS : S ≠ 0`. Establish `: 0 < S` using `Finset.sum_pos (fun i _ => pow_pos hq _) ⟨0, by simp [hl]⟩`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← geom_mul q m l hq, ← hSdef]`.

Establish `e1 : k * S * x = k * x * S` using `by ring`. Establish `e2 : k * S * y = k * y * S` using `by ring`. Rewrite using `[e1, e2]`. Conclude with `⟨Nat.ModEq.mul_right_cancel' hS, Nat.ModEq.mul_right' S⟩`.
-/
theorem lift_iff (q m l k x y : ℕ) (hq : 0 < q) (hl : 0 < l) :
    (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * x ≡ (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * y
      [MOD (q ^ l) ^ m - 1] ↔ k * x ≡ k * y [MOD q ^ m - 1] := by
  set S := ∑ i ∈ Finset.range l, q ^ (m * i) with hSdef
  have hS : S ≠ 0 := by
    have : 0 < S := Finset.sum_pos (fun i _ => pow_pos hq _) ⟨0, by simp [hl]⟩
    omega
  rw [← geom_mul q m l hq, ← hSdef]
  have e1 : k * S * x = k * x * S := by ring
  have e2 : k * S * y = k * y * S := by ring
  rw [e1, e2]
  exact ⟨Nat.ModEq.mul_right_cancel' hS, Nat.ModEq.mul_right' S⟩

end GlobalTheory.Shin.RegNorm

namespace GlobalTheory.Shin

/- English proof (translation)
Introduce `q l m k hq hl hm hlm hreg`. Establish `hq0 : 0 < q` using `by omega`. Establish `hq1 : 1 ≤ q` using `by omega`. Establish `hcop : Nat.Coprime l m` using `(Nat.Prime.coprime_iff_not_dvd hl).2 hlm`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `i hi0 him h`. Establish `h' : (k * ∑ j ∈ Finset.range l, q ^ (m * j)) * (q ^ l) ^ i ≡ (k * ∑ j ∈ Finset.range l, q ^ (m * j)) * 1 [MOD (q ^ l) ^ m - 1]`. Simplify using `using h`. Establish `h2` using `(RegNorm.lift_iff q m l k _ _ hq0 hl.pos).1 h'`. Rewrite `h2` using `[← pow_mul, mul_one]`.

Establish `h3 : k * q ^ (l * i % m) ≡ k [MOD q ^ m - 1]` using `((RegNorm.pow_modEq_pow_mod q m (l * i) hq1).mul_left k).symm.trans h2`. Use `hreg (l * i % m) ?_ (Nat.mod_lt _ hm) h3` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos (l * i % m) with h0 | h0` into its components or cases. It suffices to derive a contradiction. Establish `hd : m ∣ l * i` using `Nat.dvd_of_mod_eq_zero h0`.

Establish `: m ∣ i` using `hcop.symm.dvd_of_dvd_mul_left hd`. Conclude with `absurd (Nat.le_of_dvd hi0 this) (by omega)`. Conclude with `h0`. Establish `ha : ∃ a, l * a % m = 1 % m`. Break down `Nat.lt_or_ge 1 m with h1 | h1` into its components or cases.

Take `⟨a, -, ha⟩` from `Nat.exists_mul_mod_eq_one_of_coprime hcop h1`. Conclude with `⟨a, by rw [ha, Nat.mod_eq_of_lt h1]⟩`. Establish `: m = 1` using `by omega`. Substitute `this` using the available equality. Conclude with `⟨0, by simp⟩`.

Take `⟨a, ha⟩` from `ha`. Use `⟨a, (RegNorm.lift_iff q m l k _ _ hq0 hl.pos).2 ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_mul]`. Establish `e1 : q ^ 1 ≡ q ^ (1 % m) [MOD q ^ m - 1]` using `RegNorm.pow_modEq_pow_mod q m 1 hq1`. Establish `e2 : q ^ (l * a) ≡ q ^ (l * a % m) [MOD q ^ m - 1]` using `RegNorm.pow_modEq_pow_mod q m (l * a) hq1`.

Rewrite `e2` using `[ha]`. Rewrite `e1` using `[pow_one]`. Conclude with `(e1.trans e2.symm).mul_left k`.
-/
theorem reg_norm_frob : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k →
    Reg (q ^ l) m (k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∧
      ∃ a, (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * q ≡
        (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ l) ^ a [MOD (q ^ l) ^ m - 1] := by
  intro q l m k hq hl hm hlm hreg
  have hq0 : 0 < q := by omega
  have hq1 : 1 ≤ q := by omega
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hlm
  refine ⟨?_, ?_⟩
  · intro i hi0 him h
    have h' : (k * ∑ j ∈ Finset.range l, q ^ (m * j)) * (q ^ l) ^ i ≡
        (k * ∑ j ∈ Finset.range l, q ^ (m * j)) * 1 [MOD (q ^ l) ^ m - 1] := by
      simpa using h
    have h2 := (RegNorm.lift_iff q m l k _ _ hq0 hl.pos).1 h'
    rw [← pow_mul, mul_one] at h2
    have h3 : k * q ^ (l * i % m) ≡ k [MOD q ^ m - 1] :=
      ((RegNorm.pow_modEq_pow_mod q m (l * i) hq1).mul_left k).symm.trans h2
    refine hreg (l * i % m) ?_ (Nat.mod_lt _ hm) h3
    rcases Nat.eq_zero_or_pos (l * i % m) with h0 | h0
    · exfalso
      have hd : m ∣ l * i := Nat.dvd_of_mod_eq_zero h0
      have : m ∣ i := hcop.symm.dvd_of_dvd_mul_left hd
      exact absurd (Nat.le_of_dvd hi0 this) (by omega)
    · exact h0
  · have ha : ∃ a, l * a % m = 1 % m := by
      rcases Nat.lt_or_ge 1 m with h1 | h1
      · obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
        exact ⟨a, by rw [ha, Nat.mod_eq_of_lt h1]⟩
      · have : m = 1 := by omega
        subst this
        exact ⟨0, by simp⟩
    obtain ⟨a, ha⟩ := ha
    refine ⟨a, (RegNorm.lift_iff q m l k _ _ hq0 hl.pos).2 ?_⟩
    rw [← pow_mul]
    have e1 : q ^ 1 ≡ q ^ (1 % m) [MOD q ^ m - 1] := RegNorm.pow_modEq_pow_mod q m 1 hq1
    have e2 : q ^ (l * a) ≡ q ^ (l * a % m) [MOD q ^ m - 1] := RegNorm.pow_modEq_pow_mod q m (l * a) hq1
    rw [ha] at e2
    rw [pow_one] at e1
    exact (e1.trans e2.symm).mul_left k

end GlobalTheory.Shin
