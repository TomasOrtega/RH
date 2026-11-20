import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

noncomputable section

namespace UpperTheory.KStar.Words

open Formalism.HC Formalism.FrobeniusOrbits

variable {φ : Frame}

/- English proof (translation)
Use `show ((c0, (1 : φ.MA)) : G0 × φ.MA) * (c0, 1) = 1`. Simplify using `[c0]`.
-/
theorem cc_mul_cc : φ.cc * φ.cc = 1 := by
  show ((c0, (1 : φ.MA)) : G0 × φ.MA) * (c0, 1) = 1
  simp [c0]

/- English proof (translation)
Introduce `h`. Use `congrArg (fun g : φ.GG => g.1.2) h` as an intermediate fact. Simplify using `[Frame.cc, c0] at this`.
-/
theorem cc_ne_one : φ.cc ≠ 1 := by
  intro h
  have := congrArg (fun g : φ.GG => g.1.2) h
  simp [Frame.cc, c0] at this

/- English proof (translation)
The claim follows from `orderOf_eq_prime (by rw [pow_two, cc_mul_cc]) cc_ne_one`.
-/
theorem orderOf_cc : orderOf φ.cc = 2 := orderOf_eq_prime (by rw [pow_two, cc_mul_cc]) cc_ne_one

/- English proof (translation)
Establish `h1 : orderOf g.1 = 2`. Rewrite using `[Prod.orderOf, h]`. Establish `ha : orderOf g.1.1 ∣ 2` using `orderOf_dvd_of_pow_eq_one (Int.units_sq g.1.1)`. Establish `hn : orderOf (-1 : ℤˣ) = 2` using `orderOf_eq_prime (by decide) (by decide)`. Rewrite using `[hn]`.

Conclude with `Nat.lcm_eq_right ha`. Rewrite using `[Prod.orderOf, h1]`.
-/
theorem orderOf_moving (g : φ.GG) (h : g.1.2 = -1) : orderOf g = Nat.lcm 2 (orderOf g.2) := by
  have h1 : orderOf g.1 = 2 := by
    rw [Prod.orderOf, h]
    have ha : orderOf g.1.1 ∣ 2 := orderOf_dvd_of_pow_eq_one (Int.units_sq g.1.1)
    have hn : orderOf (-1 : ℤˣ) = 2 := orderOf_eq_prime (by decide) (by decide)
    rw [hn]
    exact Nat.lcm_eq_right ha
  rw [Prod.orderOf, h1]

/- English proof (translation)
Establish `hc : (φ.cc * g).1.2 = -g.1.2` using `by show (((c0, (1 : φ.MA)) : G0 × φ.MA) * g).1.2 = -g.1.2`. Simplify using `[c0]`. Unfold `Frame.placeOf`. Break down `Int.units_eq_one_or g.1.2 with h | h` into its components or cases. Rewrite using `[if_neg (by rw [hc, h]; decide), if_pos h, ← mul_assoc, cc_mul_cc, one_mul]`.

Rewrite using `[if_pos (by rw [hc, h]; decide), if_neg (by rw [h]; decide)]`.
-/
theorem placeOf_cc_mul (g : φ.GG) : Frame.placeOf (φ.cc * g) = Frame.placeOf g := by
  have hc : (φ.cc * g).1.2 = -g.1.2 := by
    show (((c0, (1 : φ.MA)) : G0 × φ.MA) * g).1.2 = -g.1.2
    simp [c0]
  unfold Frame.placeOf
  rcases Int.units_eq_one_or g.1.2 with h | h
  · rw [if_neg (by rw [hc, h]; decide), if_pos h, ← mul_assoc, cc_mul_cc, one_mul]
  · rw [if_pos (by rw [hc, h]; decide), if_neg (by rw [h]; decide)]

/- English proof (translation)
Unfold `Frame.placeOf`. Use `split_ifs`. Both sides reduce to the same expression. Use `show (((c0, (1 : φ.MA)) : G0 × φ.MA) * g).2 = g.2`. Simplify using the standard rewrite rules.
-/
theorem placeOf_snd (g : φ.GG) : (Frame.placeOf g).2 = g.2 := by
  unfold Frame.placeOf
  split_ifs
  · rfl
  · show (((c0, (1 : φ.MA)) : G0 × φ.MA) * g).2 = g.2
    simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hxy`. Unfold `Frame.placeOf at hxy`. Use `split_ifs at hxy with hx hy hy`. Conclude with `Or.inl hxy`.

Conclude with `Or.inr hxy`. Use `right`. Rewrite using `[← hxy, ← mul_assoc, cc_mul_cc, one_mul]`. Conclude with `Or.inl (mul_left_cancel hxy)`. Introduce and unpack `(rfl | rfl)`.

Both sides reduce to the same expression. Conclude with `placeOf_cc_mul y`.
-/
theorem placeOf_eq_iff (x y : φ.GG) : Frame.placeOf x = Frame.placeOf y ↔ x = y ∨ x = φ.cc * y := by
  constructor
  · intro hxy
    unfold Frame.placeOf at hxy
    split_ifs at hxy with hx hy hy
    · exact Or.inl hxy
    · exact Or.inr hxy
    · right
      rw [← hxy, ← mul_assoc, cc_mul_cc, one_mul]
    · exact Or.inl (mul_left_cancel hxy)
  · rintro (rfl | rfl)
    · rfl
    · exact placeOf_cc_mul y

/- English proof (translation)
Rewrite using `[placeOf_eq_iff, mul_left_comm φ.cc τ, mul_left_cancel_iff, mul_left_cancel_iff]`.
-/
theorem placeOf_letter_eq_iff (τ g : φ.GG) (a b : ℕ) :
    Frame.placeOf (τ * g ^ a) = Frame.placeOf (τ * g ^ b) ↔ g ^ a = g ^ b ∨ g ^ a = φ.cc * g ^ b := by
  rw [placeOf_eq_iff, mul_left_comm φ.cc τ, mul_left_cancel_iff, mul_left_cancel_iff]

/- English proof (translation)
Use `haveI : NeZero (orderOf g) := ⟨(orderOf_pos g).ne'⟩`. Rewrite using `[ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, pow_mod_orderOf]`.
-/
theorem pow_val_add (g : φ.GG) (i : ZMod (orderOf g)) (k : ℕ) :
    g ^ (i + (k : ZMod (orderOf g))).val = g ^ (i.val + k) := by
  haveI : NeZero (orderOf g) := ⟨(orderOf_pos g).ne'⟩
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, pow_mod_orderOf]

/- English proof (translation)
Introduce `heq`. Establish `hv` using `pow_val_add g i 1`. Rewrite `hv` using `[Nat.cast_one]`. Rewrite `heq` using `[placeOf_letter_eq_iff, hv, pow_succ]`. Break down `heq with h | h` into its components or cases.

Conclude with `h1 (by simpa using h)`. Apply `hc` to reduce the goal to its premises. Rewrite `h` using `[mul_comm φ.cc]`. Conclude with `mul_left_cancel h`.
-/
theorem placeOf_letter_succ_ne (τ g : φ.GG) (h1 : g ≠ 1) (hc : g ≠ φ.cc) (i : ZMod (orderOf g)) :
    Frame.placeOf (τ * g ^ (i + 1).val) ≠ Frame.placeOf (τ * g ^ i.val) := by
  intro heq
  have hv := pow_val_add g i 1
  rw [Nat.cast_one] at hv
  rw [placeOf_letter_eq_iff, hv, pow_succ] at heq
  rcases heq with h | h
  · exact h1 (by simpa using h)
  · apply hc
    rw [mul_comm φ.cc] at h
    exact mul_left_cancel h

/- English proof (translation)
Take `⟨s, hs, hsa⟩` from `ha`. Take `⟨s', hs', hsb⟩` from `hb`. Establish `mem : ∀ (n s : ℕ), s ∈ T → φ.tau2 (φ.dig s + u₀) = Frame.placeOf (τ * g ^ n) → φ.dig s + u₀ ∈ {y | (∃ i : ℤ, y = φ.iotaInv τ.2 + i • φ.iotaInv g.2) ∧ φ.InTranslate T u₀ y}`. Introduce `n s hsT hsn`. Use `⟨⟨(n : ℤ), ?_⟩, s, hsT, rfl⟩` and prove the remaining obligations.

Establish `h2` using `congrArg Prod.snd hsn`. Rewrite `h2` using `[placeOf_snd]`. Establish `h3 : φ.iota (φ.dig s + u₀) = τ.2 * g.2 ^ n`. Rewrite using `[← Prod.pow_snd, ← Prod.snd_mul]`. Conclude with `h2`.

Rewrite using `[← φ.iotaInv_iota (φ.dig s + u₀), h3, natCast_zsmul]`. Unfold `Frame.iotaInv`. Rewrite using `[toAdd_mul, toAdd_pow]`. Establish `hord' : addOrderOf (φ.h (φ.iotaInv g.2)) ≤ 4 * L`. Rewrite using `[← φ.orderOf_hH_iota, φ.iota_iotaInv]`.

Conclude with `hord`. Establish `hle` using `φ.thick_part_two T hT u₀ (φ.iotaInv τ.2) (φ.iotaInv g.2) hord'`. Establish `heq` using `(Set.ncard_le_one).1 hle _ (mem a s hs hsa) _ (mem b s' hs' hsb)`. Rewrite using `[← hsa, ← hsb, heq]`.
-/
theorem thick_one_place {L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < φ.n0) (u₀ : φ.A) (τ g : φ.GG)
    (hord : orderOf (φ.hH g.2) ≤ 4 * L) (a b : ℕ)
    (ha : ∃ s ∈ T, φ.tau2 (φ.dig s + u₀) = Frame.placeOf (τ * g ^ a))
    (hb : ∃ s ∈ T, φ.tau2 (φ.dig s + u₀) = Frame.placeOf (τ * g ^ b)) :
    Frame.placeOf (τ * g ^ a) = Frame.placeOf (τ * g ^ b) := by
  obtain ⟨s, hs, hsa⟩ := ha
  obtain ⟨s', hs', hsb⟩ := hb
  have mem : ∀ (n s : ℕ), s ∈ T → φ.tau2 (φ.dig s + u₀) = Frame.placeOf (τ * g ^ n) →
      φ.dig s + u₀ ∈ {y | (∃ i : ℤ, y = φ.iotaInv τ.2 + i • φ.iotaInv g.2) ∧ φ.InTranslate T u₀ y} := by
    intro n s hsT hsn
    refine ⟨⟨(n : ℤ), ?_⟩, s, hsT, rfl⟩
    have h2 := congrArg Prod.snd hsn
    rw [placeOf_snd] at h2
    have h3 : φ.iota (φ.dig s + u₀) = τ.2 * g.2 ^ n := by
      rw [← Prod.pow_snd, ← Prod.snd_mul]
      exact h2
    rw [← φ.iotaInv_iota (φ.dig s + u₀), h3, natCast_zsmul]
    unfold Frame.iotaInv
    rw [toAdd_mul, toAdd_pow]
  have hord' : addOrderOf (φ.h (φ.iotaInv g.2)) ≤ 4 * L := by
    rw [← φ.orderOf_hH_iota, φ.iota_iotaInv]
    exact hord
  have hle := φ.thick_part_two T hT u₀ (φ.iotaInv τ.2) (φ.iotaInv g.2) hord'
  have heq := (Set.ncard_le_one).1 hle _ (mem a s hs hsa) _ (mem b s' hs' hsb)
  rw [← hsa, ← hsb, heq]

end UpperTheory.KStar.Words

end
