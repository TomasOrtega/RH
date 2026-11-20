import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.LSq

def cInt (l : ℕ) (n : ℕ) : ℤ := ((n : ℤ) - (n : ℤ) ^ l) / l

/- English proof (translation)
Unfold `cInt`. Apply `Int.mul_ediv_cancel'` to reduce the goal to its premises. Establish `h : (((n : ℤ) - (n : ℤ) ^ l : ℤ) : ZMod l) = 0` using `by push_cast; rw [ZMod.pow_card, sub_self]`. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h`.
-/
theorem l_mul_cInt (l : ℕ) [hl : Fact l.Prime] (n : ℕ) : (l : ℤ) * cInt l n = (n : ℤ) - (n : ℤ) ^ l := by
  unfold cInt
  apply Int.mul_ediv_cancel'
  have h : (((n : ℤ) - (n : ℤ) ^ l : ℤ) : ZMod l) = 0 := by
    push_cast; rw [ZMod.pow_card, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `: cInt l 0 = 0`. Unfold `cInt`. Simplify using `[zero_pow hl.out.ne_zero]`.

Simplify using `[this, Delta.δ_zero]`. Consider the case `succ n ih`. Establish `h` using `D.δ_add (n : A) 1`. Rewrite `h` using `[D.δ_one, ih]`. Use `push_cast`.

Rewrite using `[h]`. Establish `key : cInt l (n + 1) = cInt l n - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : ℤ) * (n : ℤ) ^ k`. Establish `h0 : (l : ℤ) ≠ 0` using `by exact_mod_cast hl.out.ne_zero`. Apply `mul_left_cancel₀ h0` to reduce the goal to its premises. Establish `e1` using `l_mul_cInt l (n + 1)`.

Establish `e2` using `l_mul_cInt l n`. Establish `h5 : ((n : ℤ) + 1) ^ l = (n : ℤ) ^ l + 1 ^ l + (l : ℤ) * ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : ℤ) * (n : ℤ) ^ k * (1 : ℤ) ^ (l - k)`. Rewrite using `[add_pow_prime_eq' hl.out]`. Use `congr 2`. Use `Finset.sum_congr rfl fun k _ => by ring` and prove the remaining obligations.

Simplify using `only [one_pow, mul_one] at h5`. Move the coercions through the operations in `at e1`. Rewrite using `[mul_sub, e1, e2, h5]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, Int.cast_sub, Int.cast_sum]`.

Simplify using `only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, one_pow, mul_one, add_zero]`.
-/
theorem δ_natCast (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) (n : ℕ) :
    D.δ (n : A) = ((cInt l n : ℤ) : A) := by
  induction n with
  | zero =>
    have : cInt l 0 = 0 := by
      unfold cInt; simp [zero_pow hl.out.ne_zero]
    simp [this, Delta.δ_zero]
  | succ n ih =>
    have h := D.δ_add (n : A) 1
    rw [D.δ_one, ih] at h
    push_cast
    rw [h]
    have key : cInt l (n + 1) = cInt l n - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : ℤ) * (n : ℤ) ^ k := by
      have h0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
      apply mul_left_cancel₀ h0
      have e1 := l_mul_cInt l (n + 1)
      have e2 := l_mul_cInt l n
      have h5 : ((n : ℤ) + 1) ^ l = (n : ℤ) ^ l + 1 ^ l + (l : ℤ) *
          ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : ℤ) * (n : ℤ) ^ k * (1 : ℤ) ^ (l - k) := by
        rw [add_pow_prime_eq' hl.out]
        congr 2
        refine Finset.sum_congr rfl fun k _ => by ring
      simp only [one_pow, mul_one] at h5
      push_cast at e1
      rw [mul_sub, e1, e2, h5]; ring
    rw [key, Int.cast_sub, Int.cast_sum]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, one_pow, mul_one, add_zero]

/- English proof (translation)
Establish `h0 : (l : ℤ) ≠ 0` using `by exact_mod_cast hl.out.ne_zero`. Apply `mul_left_cancel₀ h0` to reduce the goal to its premises. Rewrite using `[l_mul_cInt, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hl.out.one_le]`.
-/
theorem cInt_self (l : ℕ) [hl : Fact l.Prime] : cInt l l = 1 - (l : ℤ) ^ (l - 1) := by
  have h0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  apply mul_left_cancel₀ h0
  rw [l_mul_cInt, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hl.out.one_le]

/- English proof (translation)
Rewrite using `[δ_natCast, cInt_self]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem δ_l (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) :
    D.δ (l : A) = 1 - (l : A) ^ (l - 1) := by
  rw [δ_natCast, cInt_self]; push_cast; ring

/- English proof (translation)
Rewrite `hx` using `[sq]`. Establish `hl0` using `hl.out.ne_zero`. It suffices to establish `x ∈ m ∧ D.δ x ∈ m from this.2`. Use `Submodule.mul_induction_on hx (fun a ha b hb => ⟨m.mul_mem_right b ha, ?_⟩) ?_` and prove the remaining obligations. Rewrite using `[D.δ_mul]`.

Use `m.add_mem (m.add_mem (m.mul_mem_right _ (m.pow_mem_of_mem ha _ (Nat.pos_of_ne_zero hl0))) (m.mul_mem_right _ (m.pow_mem_of_mem hb _ (Nat.pos_of_ne_zero hl0)))) ?_` and prove the remaining obligations. Conclude with `m.mul_mem_right _ (m.mul_mem_right _ hlm)`. Introduce and unpack `x y ⟨hx, hδx⟩ ⟨hy, hδy⟩`. Use `⟨m.add_mem hx hy, ?_⟩` and prove the remaining obligations. Rewrite using `[D.δ_add]`.

Use `m.sub_mem (m.add_mem hδx hδy) (m.sum_mem fun k hk => ?_)` and prove the remaining obligations. Take `⟨hk0, hkl⟩` from `Finset.mem_Ioo.1 hk`. Conclude with `m.mul_mem_left _ (m.pow_mem_of_mem hy _ (Nat.sub_pos_of_lt hkl))`.
-/
theorem δ_mem_of_mem_sq (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) (m : Ideal A)
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m ^ 2) : D.δ x ∈ m := by
  rw [sq] at hx
  have hl0 := hl.out.ne_zero
  suffices x ∈ m ∧ D.δ x ∈ m from this.2
  refine Submodule.mul_induction_on hx (fun a ha b hb => ⟨m.mul_mem_right b ha, ?_⟩) ?_
  · rw [D.δ_mul]
    refine m.add_mem (m.add_mem (m.mul_mem_right _ (m.pow_mem_of_mem ha _ (Nat.pos_of_ne_zero hl0)))
      (m.mul_mem_right _ (m.pow_mem_of_mem hb _ (Nat.pos_of_ne_zero hl0)))) ?_
    exact m.mul_mem_right _ (m.mul_mem_right _ hlm)
  · rintro x y ⟨hx, hδx⟩ ⟨hy, hδy⟩
    refine ⟨m.add_mem hx hy, ?_⟩
    rw [D.δ_add]
    refine m.sub_mem (m.add_mem hδx hδy) (m.sum_mem fun k hk => ?_)
    obtain ⟨hk0, hkl⟩ := Finset.mem_Ioo.1 hk
    exact m.mul_mem_left _ (m.pow_mem_of_mem hy _ (Nat.sub_pos_of_lt hkl))

/- English proof (translation)
Introduce `l hl A _ D m hm hlm`. Establish `hδ : D.δ (l : A) ∉ m`. Introduce `h`. Rewrite `h` using `[δ_l]`. Establish `h2 : (l : A) ^ (l - 1) ∈ m` using `m.pow_mem_of_mem hlm _ (Nat.sub_pos_of_lt hl.out.one_lt)`.

Conclude with `hm ((Ideal.eq_top_iff_one _).2 (by simpa using m.add_mem h h2))`. Conclude with `⟨fun h => hδ (δ_mem_of_mem_sq l D m hlm h), hδ⟩`.
-/
theorem l_not_mem_sq : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (m : Ideal A),
    m ≠ ⊤ → (l : A) ∈ m → (l : A) ∉ m ^ 2 ∧ D.δ (l : A) ∉ m := by
  intro l hl A _ D m hm hlm
  have hδ : D.δ (l : A) ∉ m := by
    intro h
    rw [δ_l] at h
    have h2 : (l : A) ^ (l - 1) ∈ m :=
      m.pow_mem_of_mem hlm _ (Nat.sub_pos_of_lt hl.out.one_lt)
    exact hm ((Ideal.eq_top_iff_one _).2 (by simpa using m.add_mem h h2))
  exact ⟨fun h => hδ (δ_mem_of_mem_sq l D m hlm h), hδ⟩

end GlobalTheory.BSP.LSq
