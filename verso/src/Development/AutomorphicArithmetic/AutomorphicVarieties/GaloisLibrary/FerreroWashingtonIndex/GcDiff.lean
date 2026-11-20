import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero => simp`. Consider the case `succ c ih`. Establish `e : a + (c + 1) = (a + c) + 1` using `by omega`. Establish `h1 : ∀ j : ℕ, (((j + 1 : ℕ) : ZMod M) = (((a + c + 1 : ℕ)) : ZMod M)) ↔ ((j : ZMod M) = ((a + c : ℕ) : ZMod M))`.

Introduce `j`. Use `push_cast`. Conclude with `add_left_inj 1`. Establish `h2 : ((0 : ℕ) : ZMod M) = ((a + c + 1 : ℕ) : ZMod M) ↔ M ∣ a + c + 1`. Rewrite using `[Nat.cast_zero, eq_comm]`.

Conclude with `CharP.cast_eq_zero_iff (ZMod M) M _`. Rewrite using `[e, Nat.succ_div, Finset.sum_range_succ']`. Simplify using `only [h1, h2]`. Rewrite using `[Nat.cast_add, ih]`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.
-/
private theorem norm_index_count_bound (M a c : ℕ) :
    (((a + c) / M : ℕ) : ℤ) = ((a / M : ℕ) : ℤ) +
      ∑ j ∈ Finset.range c, if (j : ZMod M) = ((a + c : ℕ) : ZMod M) then 1 else 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    have e : a + (c + 1) = (a + c) + 1 := by omega
    have h1 : ∀ j : ℕ, (((j + 1 : ℕ) : ZMod M) = (((a + c + 1 : ℕ)) : ZMod M)) ↔
        ((j : ZMod M) = ((a + c : ℕ) : ZMod M)) := by
      intro j
      push_cast
      exact add_left_inj 1
    have h2 : ((0 : ℕ) : ZMod M) = ((a + c + 1 : ℕ) : ZMod M) ↔ M ∣ a + c + 1 := by
      rw [Nat.cast_zero, eq_comm]
      exact CharP.cast_eq_zero_iff (ZMod M) M _
    rw [e, Nat.succ_div, Finset.sum_range_succ']
    simp only [h1, h2]
    rw [Nat.cast_add, ih]
    split_ifs <;> push_cast <;> ring

/- English proof (translation)
Introduce `M c _ s hc`. Establish `hM : 0 < M` using `Nat.pos_of_ne_zero (NeZero.ne M)`. Establish `hinv : (c : ZMod M)⁻¹ * (c : ZMod M) = 1`. Rewrite using `[mul_comm]`. Conclude with `ZMod.coe_mul_inv_eq_one c hc`.

Establish `hts : (c : ZMod M)⁻¹ * (s - c) = (c : ZMod M)⁻¹ * s - 1`. Rewrite using `[mul_sub, hinv]`. Unfold `UpperTheory.V.FW.gc`. Rewrite using `[hts]`. Use `set t : ZMod M := (c : ZMod M)⁻¹ * s with ht`.

Establish `hs : s = (c : ZMod M) * t`. Rewrite using `[ht, ← mul_assoc, ZMod.coe_mul_inv_eq_one c hc, one_mul]`. Use `set w := (t - 1).val with hw`. Establish `htw : t = ((w + 1 : ℕ) : ZMod M)`. Rewrite using `[Nat.cast_add, Nat.cast_one, hw, ZMod.natCast_zmod_val]`.

Expand and normalize the polynomial expressions, which then agree. Establish `key` using `norm_index_count_bound M (c * w) c`. Establish `hcast : ((c * w + c : ℕ) : ZMod M) = s`. Rewrite using `[hs, htw]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[hcast]`. Break down `Nat.lt_or_ge (w + 1) M with h | h` into its components or cases. Establish `hvt : t.val = w + 1`. Rewrite using `[htw, ZMod.val_natCast, Nat.mod_eq_of_lt h]`.

Establish `hs0 : s ≠ 0`. Introduce `h0`. Establish `t0 : t = 0` using `by rw [ht, h0, mul_zero]`. Rewrite `hvt` using `[t0, ZMod.val_zero]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hvt, if_neg hs0, sub_zero]`. Establish `e : c * (w + 1) = c * w + c` using `by ring`. Rewrite using `[e, key]`. Expand and normalize the polynomial expressions, which then agree. Establish `hwe : w + 1 = M`.

Use `ZMod.val_lt (t - 1)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `ht0 : t = 0` using `by rw [htw, hwe, ZMod.natCast_self]`. Establish `hs0 : s = 0` using `by rw [hs, ht0, mul_zero]`. Rewrite using `[ht0, ZMod.val_zero, if_pos hs0]`.

Establish `e : c * w + c = c * M` using `by rw [← hwe]; ring`. Rewrite `key` using `[e, Nat.mul_div_cancel _ hM]`. Simplify using `only [mul_zero, Nat.zero_div, Nat.cast_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.FW.gcDiff :
    ∀ (M c : ℕ) [NeZero M] (s : ZMod M), c.Coprime M → gc M c s - gc M c (s - c) = (∑ j ∈ Finset.range c, if (j : ZMod M) = s then 1 else 0) - if s = 0 then (c : ℤ) else 0 := by
  intro M c _ s hc
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hinv : (c : ZMod M)⁻¹ * (c : ZMod M) = 1 := by
    rw [mul_comm]
    exact ZMod.coe_mul_inv_eq_one c hc
  have hts : (c : ZMod M)⁻¹ * (s - c) = (c : ZMod M)⁻¹ * s - 1 := by
    rw [mul_sub, hinv]
  unfold UpperTheory.V.FW.gc
  rw [hts]
  set t : ZMod M := (c : ZMod M)⁻¹ * s with ht
  have hs : s = (c : ZMod M) * t := by
    rw [ht, ← mul_assoc, ZMod.coe_mul_inv_eq_one c hc, one_mul]
  set w := (t - 1).val with hw
  have htw : t = ((w + 1 : ℕ) : ZMod M) := by
    rw [Nat.cast_add, Nat.cast_one, hw, ZMod.natCast_zmod_val]
    ring
  have key := norm_index_count_bound M (c * w) c
  have hcast : ((c * w + c : ℕ) : ZMod M) = s := by
    rw [hs, htw]
    push_cast
    ring
  rw [hcast] at key
  rcases Nat.lt_or_ge (w + 1) M with h | h
  · have hvt : t.val = w + 1 := by
      rw [htw, ZMod.val_natCast, Nat.mod_eq_of_lt h]
    have hs0 : s ≠ 0 := by
      intro h0
      have t0 : t = 0 := by rw [ht, h0, mul_zero]
      rw [t0, ZMod.val_zero] at hvt
      omega
    rw [hvt, if_neg hs0, sub_zero]
    have e : c * (w + 1) = c * w + c := by ring
    rw [e, key]
    ring
  · have hwe : w + 1 = M := by
      have := ZMod.val_lt (t - 1)
      omega
    have ht0 : t = 0 := by rw [htw, hwe, ZMod.natCast_self]
    have hs0 : s = 0 := by rw [hs, ht0, mul_zero]
    rw [ht0, ZMod.val_zero, if_pos hs0]
    have e : c * w + c = c * M := by rw [← hwe]; ring
    rw [e, Nat.mul_div_cancel _ hM] at key
    simp only [mul_zero, Nat.zero_div, Nat.cast_zero]
    linarith
