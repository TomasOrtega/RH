import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

/- English proof (translation)
Use `haveI : NeZero M := ⟨hM0⟩`. Establish `hf : χ.FactorsThrough M`. Rewrite using `[DirichletCharacter.factorsThrough_iff_ker_unitsMap hM]`. Introduce `u hu`. Rewrite `hu`, the goal using `[MonoidHom.mem_ker]`.

Take `⟨a, ha⟩` from `ZMod.intCast_surjective (u : ZMod N)`. Establish `h1 : ((a : ℤ) : ZMod M) = ((1 : ℤ) : ZMod M)`. Establish `h` using `congrArg (fun x : (ZMod M)ˣ => (x : ZMod M)) hu`. Simplify using `only [ZMod.unitsMap_val, Units.val_one] at h`. Rewrite `h` using `[← ha, ZMod.cast_intCast hM]`.

Simplify using `using h`. Rewrite `h1` using `[ZMod.intCast_eq_intCast_iff_dvd_sub]`. Take `⟨t, ht⟩` from `h1`. Take `⟨v, hv⟩` from `hsq (-t)`. Establish `ha' : a = 1 + (M : ℤ) * (-t)` using `by linarith`.

Establish `huv : (u : ZMod N) = v ^ 2`. Rewrite using `[hv, ← ha, ha']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hvu : IsUnit v`.

Establish `: IsUnit (v ^ 2)` using `huv ▸ u.isUnit`. Conclude with `(isUnit_pow_iff two_ne_zero).mp this`. Use `ext`. Rewrite using `[MulChar.coe_toUnitHom, huv, map_pow, ← MulChar.pow_apply' χ two_ne_zero, h2, MulChar.one_apply hvu, Units.val_one]`. Establish `hle : χ.conductor ≤ M` using `Nat.sInf_le hf`.

Rewrite `hp` using `[DirichletCharacter.isPrimitive_def]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem conductor_le_of_quadratic_squares {N M : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) (hM : M ∣ N) (hM0 : M ≠ 0)
    (hsq : ∀ t : ℤ, ∃ v : ZMod N, v ^ 2 = 1 + (M : ZMod N) * (t : ZMod N)) : N ≤ M := by
  haveI : NeZero M := ⟨hM0⟩
  have hf : χ.FactorsThrough M := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hM]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (u : ZMod N)
    have h1 : ((a : ℤ) : ZMod M) = ((1 : ℤ) : ZMod M) := by
      have h := congrArg (fun x : (ZMod M)ˣ => (x : ZMod M)) hu
      simp only [ZMod.unitsMap_val, Units.val_one] at h
      rw [← ha, ZMod.cast_intCast hM] at h
      simpa using h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    obtain ⟨t, ht⟩ := h1
    obtain ⟨v, hv⟩ := hsq (-t)
    have ha' : a = 1 + (M : ℤ) * (-t) := by linarith
    have huv : (u : ZMod N) = v ^ 2 := by
      rw [hv, ← ha, ha']; push_cast; ring
    have hvu : IsUnit v := by
      have : IsUnit (v ^ 2) := huv ▸ u.isUnit
      exact (isUnit_pow_iff two_ne_zero).mp this
    ext
    rw [MulChar.coe_toUnitHom, huv, map_pow, ← MulChar.pow_apply' χ two_ne_zero, h2,
      MulChar.one_apply hvu, Units.val_one]
  have hle : χ.conductor ≤ M := Nat.sInf_le hf
  rw [DirichletCharacter.isPrimitive_def] at hp
  omega

/- English proof (translation)
Introduce and unpack `⟨k, hk⟩`. Establish `hN : N ≠ 0` using `NeZero.ne N`. Establish `hk0 : k ≠ 0` using `by rintro rfl; simp at hk; exact hN hk`. Take `⟨r, hr⟩` from `hpp.odd_of_ne_two hodd`. Establish `hle : N ≤ p * k`.

Use `conductor_le_of_quadratic_squares χ hp h2 ⟨p, by rw [hk]; ring⟩ (mul_ne_zero hpp.ne_zero hk0) fun t => ?_` and prove the remaining obligations. Use `⟨1 + (p : ZMod N) * k * t * (r + 1), ?_⟩` and prove the remaining obligations. Establish `h0 : (p : ZMod N) ^ 2 * k = 0`. Establish `h` using `congrArg (Nat.cast : ℕ → ZMod N) hk`. Rewrite `h` using `[ZMod.natCast_self]`.

Move the coercions through the operations in `at h`. Take the linear combination `-h`. Establish `hr' : (p : ZMod N) = 2 * r + 1` using `by rw [hr]; push_cast; ring`. Use `push_cast`. Take the linear combination `(t + k * t ^ 2 * (r + 1) ^ 2) * h0 - (p : ZMod N) * k * t * hr'`.

Establish `h1` using `hpp.one_lt`. Establish `: 0 < p * k` using `Nat.pos_of_ne_zero (mul_ne_zero hpp.ne_zero hk0)`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem real_cond_odd {N p : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) (hpp : p.Prime) (hodd : p ≠ 2) : ¬ p ^ 2 ∣ N := by
  rintro ⟨k, hk⟩
  have hN : N ≠ 0 := NeZero.ne N
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hN hk
  obtain ⟨r, hr⟩ := hpp.odd_of_ne_two hodd
  have hle : N ≤ p * k := by
    refine conductor_le_of_quadratic_squares χ hp h2 ⟨p, by rw [hk]; ring⟩ (mul_ne_zero hpp.ne_zero hk0) fun t => ?_
    refine ⟨1 + (p : ZMod N) * k * t * (r + 1), ?_⟩
    have h0 : (p : ZMod N) ^ 2 * k = 0 := by
      have h := congrArg (Nat.cast : ℕ → ZMod N) hk
      rw [ZMod.natCast_self] at h
      push_cast at h
      linear_combination -h
    have hr' : (p : ZMod N) = 2 * r + 1 := by rw [hr]; push_cast; ring
    push_cast
    linear_combination (t + k * t ^ 2 * (r + 1) ^ 2) * h0 - (p : ZMod N) * k * t * hr'
  have h1 := hpp.one_lt
  have : 0 < p * k := Nat.pos_of_ne_zero (mul_ne_zero hpp.ne_zero hk0)
  nlinarith

/- English proof (translation)
Introduce and unpack `⟨k, hk⟩`. Establish `hN : N ≠ 0` using `NeZero.ne N`. Establish `hk0 : k ≠ 0` using `by rintro rfl; simp at hk; exact hN hk`. Establish `hle : N ≤ 8 * k`. Use `conductor_le_of_quadratic_squares χ hp h2 ⟨2, by rw [hk]; ring⟩ (mul_ne_zero (by norm_num) hk0) fun t => ?_` and prove the remaining obligations.

Use `⟨1 + 4 * (k : ZMod N) * t, ?_⟩` and prove the remaining obligations. Establish `h0 : (16 : ZMod N) * k = 0`. Establish `h` using `congrArg (Nat.cast : ℕ → ZMod N) hk`. Rewrite `h` using `[ZMod.natCast_self]`. Move the coercions through the operations in `at h`.

Take the linear combination `-h`. Use `push_cast`. Take the linear combination `(k * t ^ 2) * h0`. Use linear arithmetic over natural numbers and integers.
-/
private theorem real_cond_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) : ¬ 2 ^ 4 ∣ N := by
  rintro ⟨k, hk⟩
  have hN : N ≠ 0 := NeZero.ne N
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hN hk
  have hle : N ≤ 8 * k := by
    refine conductor_le_of_quadratic_squares χ hp h2 ⟨2, by rw [hk]; ring⟩ (mul_ne_zero (by norm_num) hk0) fun t => ?_
    refine ⟨1 + 4 * (k : ZMod N) * t, ?_⟩
    have h0 : (16 : ZMod N) * k = 0 := by
      have h := congrArg (Nat.cast : ℕ → ZMod N) hk
      rw [ZMod.natCast_self] at h
      push_cast at h
      linear_combination -h
    push_cast
    linear_combination (k * t ^ 2) * h0
  omega

/- English proof (translation)
Introduce `N₀ q d N _ χ hp h2 h8 hq hd hall`. Rewrite using `[Nat.dvd_iff_prime_pow_dvd_dvd]`. Introduce `p k hpp hk`. Distinguish the cases in `hp2 : p = 2`. Substitute `hp2` using the available equality.

Establish `hk3 : k ≤ 3`. Assume the negation of the conclusion as `hc`. Conclude with `real_cond_two χ hp h2 ((pow_dvd_pow 2 (by omega)).trans hk)`. Establish `: 2 ^ k ∣ 8` using `pow_dvd_pow 2 hk3`. Conclude with `((this.trans h8).mul_right q).mul_right d`.

Establish `hk1 : k ≤ 1`. Assume the negation of the conclusion as `hc`. Conclude with `real_cond_odd χ hp h2 hpp hp2 ((pow_dvd_pow p (by omega)).trans hk)`. Use `interval_cases k`. Simplify using the standard rewrite rules.

Rewrite `hk`, the goal using `[pow_one]`. Break down `hall p hpp hk with h | rfl | rfl` into its components or cases. Conclude with `(h.mul_right q).mul_right d`. Conclude with `(Dvd.intro_left N₀ rfl).mul_right d`. Conclude with `Dvd.intro_left _ rfl`.
-/
theorem real_cond :
    ∀ (N₀ q d : ℕ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ^ 2 = 1 → 8 ∣ N₀ → q.Prime → d.Prime →
      (∀ p : ℕ, p.Prime → p ∣ N → p ∣ N₀ ∨ p = q ∨ p = d) → N ∣ N₀ * q * d := by
  intro N₀ q d N _ χ hp h2 h8 hq hd hall
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hpp hk
  by_cases hp2 : p = 2
  · subst hp2
    have hk3 : k ≤ 3 := by
      by_contra hc
      exact real_cond_two χ hp h2 ((pow_dvd_pow 2 (by omega)).trans hk)
    have : 2 ^ k ∣ 8 := pow_dvd_pow 2 hk3
    exact ((this.trans h8).mul_right q).mul_right d
  · have hk1 : k ≤ 1 := by
      by_contra hc
      exact real_cond_odd χ hp h2 hpp hp2 ((pow_dvd_pow p (by omega)).trans hk)
    interval_cases k
    · simp
    · rw [pow_one] at hk ⊢
      rcases hall p hpp hk with h | rfl | rfl
      · exact (h.mul_right q).mul_right d
      · exact (Dvd.intro_left N₀ rfl).mul_right d
      · exact Dvd.intro_left _ rfl

end QH
