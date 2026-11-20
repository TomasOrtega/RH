import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

noncomputable section

namespace UpperTheory.KStar.Words

open Formalism.HC Formalism.FrobeniusOrbits

variable {φ : Frame}

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cc_mul_cc : φ.cc * φ.cc = 1 := by
  show ((c0, (1 : φ.MA)) : G0 × φ.MA) * (c0, 1) = 1
  simp [c0]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem cc_ne_one : φ.cc ≠ 1 := by
  intro h
  have := congrArg (fun g : φ.GG => g.1.2) h
  simp [Frame.cc, c0] at this

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem orderOf_cc : orderOf φ.cc = 2 := orderOf_eq_prime (by rw [pow_two, cc_mul_cc]) cc_ne_one

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Establish an intermediate fact. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities.
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
Replace the relevant objects with their definitions. Both sides reduce to the same expression. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem placeOf_snd (g : φ.GG) : (Frame.placeOf g).2 = g.2 := by
  unfold Frame.placeOf
  split_ifs
  · rfl
  · show (((c0, (1 : φ.MA)) : G0 × φ.MA) * g).2 = g.2
    simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Prove the first alternative. Prove the second alternative.

Rewrite the conclusion using the stated equalities. Prove the first alternative. Assume the hypotheses and unpack their components. Both sides reduce to the same expression. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities.
-/
theorem placeOf_letter_eq_iff (τ g : φ.GG) (a b : ℕ) :
    Frame.placeOf (τ * g ^ a) = Frame.placeOf (τ * g ^ b) ↔ g ^ a = g ^ b ∨ g ^ a = φ.cc * g ^ b := by
  rw [placeOf_eq_iff, mul_left_comm φ.cc τ, mul_left_cancel_iff, mul_left_cancel_iff]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pow_val_add (g : φ.GG) (i : ZMod (orderOf g)) (k : ℕ) :
    g ^ (i + (k : ZMod (orderOf g))).val = g ^ (i.val + k) := by
  haveI : NeZero (orderOf g) := ⟨(orderOf_pos g).ne'⟩
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, pow_mod_orderOf]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Reduce the claim to the hypotheses of an applicable result. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
