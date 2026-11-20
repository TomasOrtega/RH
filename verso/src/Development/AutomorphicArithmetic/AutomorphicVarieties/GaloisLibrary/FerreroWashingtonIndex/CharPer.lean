import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Introduce `l hl f n _ k _ _ χ s hf hn`. Use `set M : ZMod (f * l ^ n) := ((f * l : ℕ) : ZMod (f * l ^ n)) with hM`. Establish `hnil : IsNilpotent M`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[hM, ← Nat.cast_pow, CharP.cast_eq_zero_iff (ZMod (f * l ^ n)) (f * l ^ n), mul_pow]`.

Conclude with `Nat.mul_dvd_mul_right (dvd_pow_self f (by omega)) _`. Distinguish the cases in `hs : IsUnit s`. Use `swap`. Establish `hs' : ¬ IsUnit (s + M)`. Introduce `h`.

Apply `hs` to reduce the goal to its premises. Simplify using `using hnil.neg.isUnit_add_right_of_commute h (Commute.all _ _)`. Rewrite using `[MulChar.map_nonunit _ hs, MulChar.map_nonunit _ hs']`. Take `⟨u, rfl⟩` from `hs`. Use `set t : ℤ := ((((u⁻¹ : (ZMod (f * l ^ n))ˣ) : ZMod (f * l ^ n)).val : ℕ) : ℤ) with ht`.

Use `set w : ZMod (f * l ^ n) := 1 + M * ((u⁻¹ : (ZMod (f * l ^ n))ˣ) : ZMod (f * l ^ n)) with hw`. Establish `hsplit : (u : ZMod (f * l ^ n)) + M = u * w`. Rewrite using `[hw, mul_add, mul_one, mul_left_comm, Units.mul_inv, mul_one]`. Establish `hwint : w = ((1 + (f : ℤ) * l * t : ℤ) : ZMod (f * l ^ n))`. Rewrite using `[hw, hM, ht]`.

Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val]`. Establish `hdvd : ((f * l ^ n : ℕ) : ℤ) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1`. Establish `h1 : ((l : ℕ) : ℤ) ^ (n - 1 + 1) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1 ^ (l ^ (n - 1))` using `dvd_sub_pow_of_dvd_sub (by simp only [add_sub_cancel_left]; exact ⟨f * t, by ring⟩) _`. Rewrite `h1` using `[Nat.sub_add_cancel hn, one_pow]`.

Establish `h2 : (f : ℤ) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1`. Use `sub_dvd_pow_sub_pow (1 + (f : ℤ) * l * t) 1 (l ^ (n - 1))` as an intermediate fact. Rewrite `this` using `[one_pow]`. Conclude with `dvd_trans ⟨l * t, by ring⟩ this`. Establish `hcop : IsCoprime (f : ℤ) ((l : ℤ) ^ n)`.

Use `Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right n hf)` as an intermediate fact. Simplify using `using this`. Use `push_cast`. Conclude with `hcop.mul_dvd h2 h1`. Establish `hwpow : w ^ (l ^ (n - 1)) = 1`.

Establish `h0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd`. Rewrite using `[hwint]`. Move the coercions through the operations in `at h0 ⊢`. Take the linear combination `h0`. Establish `hcw : MulChar.ofUnitHom χ w = 1`.

Establish `hp : (MulChar.ofUnitHom χ w) ^ (l ^ (n - 1)) = 1`. Rewrite using `[← map_pow, hwpow, map_one]`. Establish `: (MulChar.ofUnitHom χ w - 1) ^ (l ^ (n - 1)) = 0`. Rewrite using `[sub_pow_char_pow, hp, one_pow, sub_self]`. Conclude with `sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ hl.out.ne_zero)).mp this)`.

Rewrite using `[hsplit, map_mul, hcw, mul_one]`.
-/
theorem UpperTheory.V.FW.charPer :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ) [NeZero (f * l ^ n)] (k : Type) [Field k] [CharP k l] (χ : (ZMod (f * l ^ n))ˣ →* kˣ) (s : ZMod (f * l ^ n)), f.Coprime l → 1 ≤ n → MulChar.ofUnitHom χ (s + ((f * l : ℕ) : ZMod (f * l ^ n))) = MulChar.ofUnitHom χ s := by
  intro l hl f n _ k _ _ χ s hf hn
  set M : ZMod (f * l ^ n) := ((f * l : ℕ) : ZMod (f * l ^ n)) with hM
  have hnil : IsNilpotent M := by
    refine ⟨n, ?_⟩
    rw [hM, ← Nat.cast_pow, CharP.cast_eq_zero_iff (ZMod (f * l ^ n)) (f * l ^ n), mul_pow]
    exact Nat.mul_dvd_mul_right (dvd_pow_self f (by omega)) _
  by_cases hs : IsUnit s
  swap
  · have hs' : ¬ IsUnit (s + M) := by
      intro h
      apply hs
      simpa using hnil.neg.isUnit_add_right_of_commute h (Commute.all _ _)
    rw [MulChar.map_nonunit _ hs, MulChar.map_nonunit _ hs']
  obtain ⟨u, rfl⟩ := hs
  set t : ℤ := ((((u⁻¹ : (ZMod (f * l ^ n))ˣ) : ZMod (f * l ^ n)).val : ℕ) : ℤ) with ht
  set w : ZMod (f * l ^ n) := 1 + M * ((u⁻¹ : (ZMod (f * l ^ n))ˣ) : ZMod (f * l ^ n)) with hw
  have hsplit : (u : ZMod (f * l ^ n)) + M = u * w := by
    rw [hw, mul_add, mul_one, mul_left_comm, Units.mul_inv, mul_one]
  have hwint : w = ((1 + (f : ℤ) * l * t : ℤ) : ZMod (f * l ^ n)) := by
    rw [hw, hM, ht]
    push_cast
    rw [ZMod.natCast_zmod_val]
  have hdvd : ((f * l ^ n : ℕ) : ℤ) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1 := by
    have h1 : ((l : ℕ) : ℤ) ^ (n - 1 + 1) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1 ^ (l ^ (n - 1)) :=
      dvd_sub_pow_of_dvd_sub (by simp only [add_sub_cancel_left]; exact ⟨f * t, by ring⟩) _
    rw [Nat.sub_add_cancel hn, one_pow] at h1
    have h2 : (f : ℤ) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1 := by
      have := sub_dvd_pow_sub_pow (1 + (f : ℤ) * l * t) 1 (l ^ (n - 1))
      rw [one_pow] at this
      exact dvd_trans ⟨l * t, by ring⟩ this
    have hcop : IsCoprime (f : ℤ) ((l : ℤ) ^ n) := by
      have := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right n hf)
      simpa using this
    push_cast
    exact hcop.mul_dvd h2 h1
  have hwpow : w ^ (l ^ (n - 1)) = 1 := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
    rw [hwint]
    push_cast at h0 ⊢
    linear_combination h0
  have hcw : MulChar.ofUnitHom χ w = 1 := by
    have hp : (MulChar.ofUnitHom χ w) ^ (l ^ (n - 1)) = 1 := by
      rw [← map_pow, hwpow, map_one]
    have : (MulChar.ofUnitHom χ w - 1) ^ (l ^ (n - 1)) = 0 := by
      rw [sub_pow_char_pow, hp, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ hl.out.ne_zero)).mp this)
  rw [hsplit, map_mul, hcw, mul_one]
