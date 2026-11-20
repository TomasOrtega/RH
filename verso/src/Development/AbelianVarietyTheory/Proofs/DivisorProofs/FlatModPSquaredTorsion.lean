import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory

/- English proof (translation)
Establish `h0 : ((p * a.val : ℕ) : ZMod (p ^ 2)) = 0`. Rewrite using `[Nat.cast_mul, ZMod.natCast_zmod_val]`. Conclude with `ha`. Rewrite `h0` using `[ZMod.natCast_eq_zero_iff]`. Take `⟨k, hk⟩` from `h0`.

Establish `h1 : a.val = p * k`. Apply `Nat.eq_of_mul_eq_mul_left hp.out.pos` to reduce the goal to its premises. Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(k : ZMod (p ^ 2)), ?_⟩` and prove the remaining obligations.

Rewrite using `[← ZMod.natCast_zmod_val a, h1, Nat.cast_mul]`.
-/
theorem zmod_sq_dvd_of_mul_eq_zero (p : ℕ) [hp : Fact p.Prime] (a : ZMod (p ^ 2))
    (ha : (p : ZMod (p ^ 2)) * a = 0) : ∃ c : ZMod (p ^ 2), a = (p : ZMod (p ^ 2)) * c := by
  have h0 : ((p * a.val : ℕ) : ZMod (p ^ 2)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact ha
  rw [ZMod.natCast_eq_zero_iff] at h0
  obtain ⟨k, hk⟩ := h0
  have h1 : a.val = p * k := by
    apply Nat.eq_of_mul_eq_mul_left hp.out.pos
    rw [hk]; ring
  refine ⟨(k : ZMod (p ^ 2)), ?_⟩
  rw [← ZMod.natCast_zmod_val a, h1, Nat.cast_mul]

/- English proof (translation)
Introduce `p hp B _ φ hφ w`. Use `letI : Algebra (ZMod (p ^ 2)) B := φ.toAlgebra`. Establish `hflat : Module.Flat (ZMod (p ^ 2)) B` using `hφ`. Establish `hsmul : ∀ (r : ZMod (p ^ 2)) (b : B), r • b = φ r * b` using `fun r b => by`. Rewrite using `[Algebra.smul_def]`.

Both sides reduce to the same expression. Establish `hpB : φ (p : ZMod (p ^ 2)) = (p : B)` using `map_natCast φ p`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Establish `hsum : ∑ i : Unit, (fun _ => (p : ZMod (p ^ 2))) i • (fun _ => w) i = 0`.

Simplify using `only [Finset.univ_unique, Finset.sum_singleton]`. Rewrite using `[hsmul, hpB, hw]`. Establish `htr` using `@Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (ZMod (p ^ 2)) B _ _ _ hflat Unit _ _ _ hsum`. Take `⟨k, a, y, hy, ha⟩` from `htr`. Establish `ha' : ∀ j, (p : ZMod (p ^ 2)) * a () j = 0` using `fun j => by`.

Simplify `ha j` using `only [Finset.univ_unique, Finset.sum_singleton]`. Use `choose c hc using fun j => zmod_sq_dvd_of_mul_eq_zero p (a () j) (ha' j)`. Use `⟨∑ j, φ (c j) * y j, ?_⟩` and prove the remaining obligations. Establish `hw : w = ∑ j, a () j • y j` using `hy ()`. Rewrite using `[hw, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hsmul, hc j, map_mul, hpB, mul_assoc]`. Introduce and unpack `⟨v, rfl⟩`. Establish `h2 : (((p ^ 2 : ℕ) : ZMod (p ^ 2))) = 0` using `ZMod.natCast_self _`. Establish `: ((p ^ 2 : ℕ) : B) = 0`.

Rewrite using `[← map_natCast φ, h2, map_zero]`. Rewrite using `[← mul_assoc, ← Nat.cast_mul, ← pow_two, this, zero_mul]`.
-/
theorem flat_zmod_sq_mul_p_eq_zero_iff : ∀ (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (φ : ZMod (p ^ 2) →+* B), φ.Flat → ∀ w : B, (p : B) * w = 0 ↔ ∃ v, w = p * v := by
  intro p hp B _ φ hφ w
  letI : Algebra (ZMod (p ^ 2)) B := φ.toAlgebra
  have hflat : Module.Flat (ZMod (p ^ 2)) B := hφ
  have hsmul : ∀ (r : ZMod (p ^ 2)) (b : B), r • b = φ r * b := fun r b => by
    rw [Algebra.smul_def]; rfl
  have hpB : φ (p : ZMod (p ^ 2)) = (p : B) := map_natCast φ p
  constructor
  · intro hw
    have hsum : ∑ i : Unit, (fun _ => (p : ZMod (p ^ 2))) i • (fun _ => w) i = 0 := by
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [hsmul, hpB, hw]
    have htr := @Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (ZMod (p ^ 2)) B _ _ _ hflat Unit _ _ _ hsum
    obtain ⟨k, a, y, hy, ha⟩ := htr
    have ha' : ∀ j, (p : ZMod (p ^ 2)) * a () j = 0 := fun j => by
      simpa only [Finset.univ_unique, Finset.sum_singleton] using ha j
    choose c hc using fun j => zmod_sq_dvd_of_mul_eq_zero p (a () j) (ha' j)
    refine ⟨∑ j, φ (c j) * y j, ?_⟩
    have hw : w = ∑ j, a () j • y j := hy ()
    rw [hw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsmul, hc j, map_mul, hpB, mul_assoc]
  · rintro ⟨v, rfl⟩
    have h2 : (((p ^ 2 : ℕ) : ZMod (p ^ 2))) = 0 := ZMod.natCast_self _
    have : ((p ^ 2 : ℕ) : B) = 0 := by
      rw [← map_natCast φ, h2, map_zero]
    rw [← mul_assoc, ← Nat.cast_mul, ← pow_two, this, zero_mul]

end GlobalTheory
