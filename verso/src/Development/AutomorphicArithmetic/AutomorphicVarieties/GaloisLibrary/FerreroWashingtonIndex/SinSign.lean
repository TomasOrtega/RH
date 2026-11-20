import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Introduce `x hx hne`. Use `set n := ⌊x⌋₊ with hn`. Establish `h0 : (0 : ℝ) ≤ x - n` using `sub_nonneg.mpr (Nat.floor_le hx)`. Establish `h1 : x - n ≤ 1`. Use `Nat.lt_floor_add_one x` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs : 0 ≤ Real.sin (Real.pi * (x - n))` using `Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le h0) (mul_le_of_le_one_right Real.pi_pos.le h1)`. Establish `he : Real.sin (Real.pi * x) = (-1) ^ n * Real.sin (Real.pi * (x - n))`. Rewrite using `[← Real.sin_add_nat_mul_pi]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hne`, the goal using `[he]`. Establish `hpos : 0 < Real.sin (Real.pi * (x - n))` using `lt_of_le_of_ne hs (fun h => hne (by rw [← h, mul_zero]))`. Break down `Nat.even_or_odd n with h | h` into its components or cases. Rewrite using `[h.neg_one_pow, one_mul]`.

Conclude with `⟨fun hlt => absurd hlt (not_lt.mpr hpos.le), fun ho => absurd ho (Nat.not_odd_iff_even.mpr h)⟩`. Rewrite using `[h.neg_one_pow]`. Conclude with `⟨fun _ => h, fun _ => by linarith⟩`.
-/
theorem UpperTheory.V.FW.sinSign :
    ∀ x : ℝ, 0 ≤ x → Real.sin (Real.pi * x) ≠ 0 → (Real.sin (Real.pi * x) < 0 ↔ Odd ⌊x⌋₊) := by
  intro x hx hne
  set n := ⌊x⌋₊ with hn
  have h0 : (0 : ℝ) ≤ x - n := sub_nonneg.mpr (Nat.floor_le hx)
  have h1 : x - n ≤ 1 := by
    have := Nat.lt_floor_add_one x
    linarith
  have hs : 0 ≤ Real.sin (Real.pi * (x - n)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le h0)
      (mul_le_of_le_one_right Real.pi_pos.le h1)
  have he : Real.sin (Real.pi * x) = (-1) ^ n * Real.sin (Real.pi * (x - n)) := by
    rw [← Real.sin_add_nat_mul_pi]
    congr 1
    ring
  rw [he] at hne ⊢
  have hpos : 0 < Real.sin (Real.pi * (x - n)) :=
    lt_of_le_of_ne hs (fun h => hne (by rw [← h, mul_zero]))
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, one_mul]
    exact ⟨fun hlt => absurd hlt (not_lt.mpr hpos.le), fun ho => absurd ho (Nat.not_odd_iff_even.mpr h)⟩
  · rw [h.neg_one_pow]
    exact ⟨fun _ => h, fun _ => by linarith⟩
