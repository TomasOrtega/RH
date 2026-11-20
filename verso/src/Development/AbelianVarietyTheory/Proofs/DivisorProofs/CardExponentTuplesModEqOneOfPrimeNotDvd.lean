import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.ExpCount

/- English proof (translation)
Use `set S : ℕ := ∑ i ∈ Finset.range l, q ^ (m * i) with hS`. Establish `hSpos : 0 < S` using `Finset.sum_pos (fun i _ => by positivity) ⟨0, Finset.mem_range.2 hl.pos⟩`. Establish `hgeom : ((q ^ (l * m) - 1 : ℕ) : ℤ) = ((q : ℤ) ^ m - 1) * (S : ℤ)`. Rewrite using `[Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), hS]`. Use `push_cast`.

Establish `e : ∑ i ∈ Finset.range l, (q : ℤ) ^ (m * i) = ∑ i ∈ Finset.range l, ((q : ℤ) ^ m) ^ i` using `Finset.sum_congr rfl fun i _ => by rw [pow_mul]`. Rewrite using `[e, mul_comm ((q : ℤ) ^ m - 1), geom_sum_mul, ← pow_mul, mul_comm m l]`. Establish `h1` using `Nat.modEq_iff_dvd.1 h`. Rewrite `h1` using `[hgeom]`. Move the coercions through the operations in `at h1`.

Establish `h2 : ((q : ℤ) ^ m - 1) ∣ (k : ℤ) - k * (q : ℤ) ^ c`. Establish `h1' : ((q : ℤ) ^ m - 1) * S ∣ ((k : ℤ) - k * (q : ℤ) ^ c) * S`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Conclude with `(mul_dvd_mul_iff_right (by exact_mod_cast hSpos.ne')).1 h1'`.

Establish `h3 : ((q : ℤ) ^ m - 1) ∣ (k : ℤ) - k * (q : ℤ) ^ (c % m)`. Establish `hc' : (q : ℤ) ^ c = ((q : ℤ) ^ m) ^ (c / m) * (q : ℤ) ^ (c % m)`. Rewrite using `[← pow_mul, ← pow_add, Nat.div_add_mod]`. Establish `e : (k : ℤ) - k * (q : ℤ) ^ (c % m) = ((k : ℤ) - k * (q : ℤ) ^ c) + k * (q : ℤ) ^ (c % m) * (((q : ℤ) ^ m) ^ (c / m) - 1 ^ (c / m))`. Rewrite using `[hc']`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_add h2 (Dvd.dvd.mul_left (sub_dvd_pow_sub_pow _ _ _) _)`. Establish `hmc : m ∣ c`. Assume the negation of the conclusion as `hne`.

Establish `hd : 0 < c % m` using `Nat.pos_of_ne_zero (fun h0 => hne (Nat.dvd_of_mod_eq_zero h0))`. Apply `hreg (c % m) hd (Nat.mod_lt c hm)` to reduce the goal to its premises. Apply `Nat.modEq_iff_dvd.2` to reduce the goal to its premises. Rewrite using `[Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]`. Use `push_cast`.

Conclude with `h3`. Establish `hcop : Nat.Coprime l m` using `(Nat.Prime.coprime_iff_not_dvd hl).2 hlm`. Conclude with `Nat.eq_zero_of_dvd_of_lt (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hlc hmc) hc`.
-/
theorem eq_zero_of_modEq (q l m k c : ℕ) (hq : 2 ≤ q) (hl : l.Prime) (hm : 0 < m) (hlm : ¬ l ∣ m)
    (hreg : Reg q m k) (hc : c < l * m) (hlc : l ∣ c)
    (h : k * (∑ i ∈ Finset.range l, q ^ (m * i)) * q ^ c ≡ k * ∑ i ∈ Finset.range l, q ^ (m * i)
      [MOD q ^ (l * m) - 1]) : c = 0 := by
  set S : ℕ := ∑ i ∈ Finset.range l, q ^ (m * i) with hS
  have hSpos : 0 < S := Finset.sum_pos (fun i _ => by positivity) ⟨0, Finset.mem_range.2 hl.pos⟩
  have hgeom : ((q ^ (l * m) - 1 : ℕ) : ℤ) = ((q : ℤ) ^ m - 1) * (S : ℤ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), hS]
    push_cast
    have e : ∑ i ∈ Finset.range l, (q : ℤ) ^ (m * i) = ∑ i ∈ Finset.range l, ((q : ℤ) ^ m) ^ i :=
      Finset.sum_congr rfl fun i _ => by rw [pow_mul]
    rw [e, mul_comm ((q : ℤ) ^ m - 1), geom_sum_mul, ← pow_mul, mul_comm m l]
  have h1 := Nat.modEq_iff_dvd.1 h
  rw [hgeom] at h1
  push_cast at h1
  have h2 : ((q : ℤ) ^ m - 1) ∣ (k : ℤ) - k * (q : ℤ) ^ c := by
    have h1' : ((q : ℤ) ^ m - 1) * S ∣ ((k : ℤ) - k * (q : ℤ) ^ c) * S := by
      convert h1 using 1; ring
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hSpos.ne')).1 h1'
  have h3 : ((q : ℤ) ^ m - 1) ∣ (k : ℤ) - k * (q : ℤ) ^ (c % m) := by
    have hc' : (q : ℤ) ^ c = ((q : ℤ) ^ m) ^ (c / m) * (q : ℤ) ^ (c % m) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have e : (k : ℤ) - k * (q : ℤ) ^ (c % m) = ((k : ℤ) - k * (q : ℤ) ^ c)
        + k * (q : ℤ) ^ (c % m) * (((q : ℤ) ^ m) ^ (c / m) - 1 ^ (c / m)) := by
      rw [hc']; ring
    rw [e]
    exact dvd_add h2 (Dvd.dvd.mul_left (sub_dvd_pow_sub_pow _ _ _) _)
  have hmc : m ∣ c := by
    by_contra hne
    have hd : 0 < c % m := Nat.pos_of_ne_zero (fun h0 => hne (Nat.dvd_of_mod_eq_zero h0))
    apply hreg (c % m) hd (Nat.mod_lt c hm)
    apply Nat.modEq_iff_dvd.2
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
    push_cast
    exact h3
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hlm
  exact Nat.eq_zero_of_dvd_of_lt (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hlc hmc) hc

/- English proof (translation)
Rewrite using `[ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, ← pow_add]`. Use `conv_rhs => rw [← Nat.mod_add_div (x.val + n) N, pow_add, pow_mul, hQ, one_pow, mul_one]`.
-/
theorem pow_val_add_natCast {M N : ℕ} [NeZero N] (Q : ZMod M) (hQ : Q ^ N = 1) (x : ZMod N) (n : ℕ) :
    Q ^ (x + (n : ZMod N)).val = Q ^ x.val * Q ^ n := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + n) N, pow_add, pow_mul, hQ, one_pow, mul_one]

/- English proof (translation)
Use `haveI : Fact (l' + 1).Prime := ⟨hl⟩`. Establish `hm0 : (m : ZMod (l' + 1)) ≠ 0` using `fun h0 => hlm ((ZMod.natCast_eq_zero_iff _ _).1 h0)`. Establish `hind : ∀ n : ℕ, h ((n : ZMod (l' + 1)) * m) = h 0 + ((n * m : ℕ) : ZMod ((l' + 1) * m))`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `hf` using `hfix (((n + 1 : ℕ) : ZMod (l' + 1)) * m)`. Rewrite using `[← hf]`. Establish `e : ((n + 1 : ℕ) : ZMod (l' + 1)) * m - m = (n : ZMod (l' + 1)) * m` using `by push_cast; ring`.

Rewrite using `[e, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hr : r = (((r * (m : ZMod (l' + 1))⁻¹).val : ℕ) : ZMod (l' + 1)) * m`. Rewrite using `[ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hm0, mul_one]`.

Use `conv_lhs => rw [hr]`. Conclude with `hind _`.
-/
theorem fixed_eq (l' m : ℕ) (hl : (l' + 1).Prime) (hlm : ¬ (l' + 1) ∣ m)
    (h : ZMod (l' + 1) → ZMod ((l' + 1) * m)) (hfix : ∀ r, h (r - m) + m = h r) (r : ZMod (l' + 1)) :
    h r = h 0 + (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m)) := by
  haveI : Fact (l' + 1).Prime := ⟨hl⟩
  have hm0 : (m : ZMod (l' + 1)) ≠ 0 := fun h0 => hlm ((ZMod.natCast_eq_zero_iff _ _).1 h0)
  have hind : ∀ n : ℕ, h ((n : ZMod (l' + 1)) * m) = h 0 + ((n * m : ℕ) : ZMod ((l' + 1) * m)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hf := hfix (((n + 1 : ℕ) : ZMod (l' + 1)) * m)
      rw [← hf]
      have e : ((n + 1 : ℕ) : ZMod (l' + 1)) * m - m = (n : ZMod (l' + 1)) * m := by push_cast; ring
      rw [e, ih]; push_cast; ring
  have hr : r = (((r * (m : ZMod (l' + 1))⁻¹).val : ℕ) : ZMod (l' + 1)) * m := by
    rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hm0, mul_one]
  conv_lhs => rw [hr]
  exact hind _

/- English proof (translation)
Use `haveI : Fact (l' + 1).Prime := ⟨hl⟩`. Use `haveI : NeZero ((l' + 1) * m) := ⟨by positivity⟩`. Establish `hm0 : (m : ZMod (l' + 1)) ≠ 0` using `fun h0 => hlm ((ZMod.natCast_eq_zero_iff _ _).1 h0)`. Rewrite using `[Finset.sum_congr rfl (fun r _ => by rw [fixed_eq l' m hl hlm h hfix r, pow_val_add_natCast Q hQ]), ← Finset.mul_sum]`. Use `congr 1`.

Establish `e1 : ∑ r : ZMod (l' + 1), Q ^ ((r * (m : ZMod (l' + 1))⁻¹).val * m) = ∑ s : ZMod (l' + 1), Q ^ (s.val * m)` using `Equiv.sum_comp (Equiv.mulRight₀ ((m : ZMod (l' + 1))⁻¹) (inv_ne_zero hm0)) (fun s : ZMod (l' + 1) => Q ^ (s.val * m))`. Rewrite using `[e1, ← Fin.sum_univ_eq_sum_range (fun i => Q ^ (m * i)) (l' + 1)]`. Conclude with `Finset.sum_congr rfl fun s _ => by rw [mul_comm]; rfl`.
-/
theorem fixed_sum (M l' m : ℕ) (Q : ZMod M) (hl : (l' + 1).Prime) (hlm : ¬ (l' + 1) ∣ m) (hm : 0 < m)
    (hQ : Q ^ ((l' + 1) * m) = 1)
    (h : ZMod (l' + 1) → ZMod ((l' + 1) * m)) (hfix : ∀ r, h (r - m) + m = h r) :
    ∑ r, Q ^ (h r).val = Q ^ (h 0).val * ∑ i ∈ Finset.range (l' + 1), Q ^ (m * i) := by
  haveI : Fact (l' + 1).Prime := ⟨hl⟩
  haveI : NeZero ((l' + 1) * m) := ⟨by positivity⟩
  have hm0 : (m : ZMod (l' + 1)) ≠ 0 := fun h0 => hlm ((ZMod.natCast_eq_zero_iff _ _).1 h0)
  rw [Finset.sum_congr rfl (fun r _ => by rw [fixed_eq l' m hl hlm h hfix r, pow_val_add_natCast Q hQ]),
    ← Finset.mul_sum]
  congr 1
  have e1 : ∑ r : ZMod (l' + 1), Q ^ ((r * (m : ZMod (l' + 1))⁻¹).val * m)
      = ∑ s : ZMod (l' + 1), Q ^ (s.val * m) :=
    Equiv.sum_comp (Equiv.mulRight₀ ((m : ZMod (l' + 1))⁻¹) (inv_ne_zero hm0)) (fun s : ZMod (l' + 1) => Q ^ (s.val * m))
  rw [e1, ← Fin.sum_univ_eq_sum_range (fun i => Q ^ (m * i)) (l' + 1)]
  exact Finset.sum_congr rfl fun s _ => by rw [mul_comm]; rfl

end GlobalTheory.ExpCount

namespace GlobalTheory.ExpCount

/- English proof (translation)
Use `haveI : NeZero ((l' + 1) * m) := ⟨by positivity⟩`. Rewrite using `[← Fintype.card_subtype, ← Nat.card_eq_fintype_card]`. Set `ef : Fin (l' + 1) ≃ ZMod (l' + 1)` to `Equiv.refl _`. Establish `hef : ∀ r : ZMod (l' + 1), ((ef.symm r : Fin (l' + 1)) : ℕ) = r.val` using `fun r => rfl`. Establish `hef' : ∀ j : Fin (l' + 1), (ef j).val = (j : ℕ)` using `fun j => rfl`.

Establish `hb : ∀ (j : ℕ) (x : ℕ), j < l' + 1 → x < m → j + (l' + 1) * x < (l' + 1) * m`. Introduce `j x hj hx`. Combine the equalities or inequalities in the displayed calculation. Establish `hkey : ∀ (g : ZMod (l' + 1) → ZMod ((l' + 1) * m)), (∀ r, ZMod.castHom (dvd_mul_right (l' + 1) m) (ZMod (l' + 1)) (g r) = r) → ∀ r : ZMod (l' + 1), r.val + (l' + 1) * ((g r).val / (l' + 1)) = (g r).val`. Introduce `g hg r`.

Establish `h` using `hg r`. Rewrite `h` using `[ZMod.castHom_apply, ← ZMod.natCast_val]`. Establish `h2` using `congrArg ZMod.val h`. Rewrite `h2` using `[ZMod.val_natCast]`. Rewrite using `[← h2, Nat.mod_add_div]`.

Establish `hmod : (q ^ (l' + 1)) ^ m - 1 = q ^ ((l' + 1) * m) - 1` using `by rw [← pow_mul]`. Use `Nat.card_congr { toFun := fun a => ⟨fun r => ((r.val + (l' + 1) * (a.1 (ef.symm r)).val : ℕ) : ZMod ((l' + 1) * m)), ?_, ?_⟩ invFun := fun g => ⟨fun j => ⟨(g.1 (ef j)).val / (l' + 1), (Nat.div_lt_iff_lt_mul (Nat.succ_pos l')).2 (lt_of_lt_of_eq (ZMod.val_lt _) (mul_comm _ _))⟩, ?_ …` and prove the remaining obligations. Introduce `r`. Rewrite using `[map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]`. Break down `a with ⟨a, ha⟩` into its components or cases.

Rewrite `ha` using `[hmod]`. Establish `h` using `(ZMod.natCast_eq_natCast_iff _ _ _).2 ha`. Establish `hv : ∀ r : ZMod (l' + 1), (((r.val + (l' + 1) * (a (ef.symm r)).val : ℕ) : ZMod ((l' + 1) * m))).val = r.val + (l' + 1) * (a (ef.symm r)).val` using `fun r => ZMod.val_cast_of_lt (hb _ _ (ZMod.val_lt r) (a (ef.symm r)).isLt)`. Simplify using `only [hv]`. Rewrite using `[h]`.

Use `push_cast`. Rewrite using `[← Equiv.sum_comp ef.symm (fun j : Fin (l' + 1) => (k : ZMod (q ^ ((l' + 1) * m) - 1)) * (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (j : ℕ) * ((q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (l' + 1)) ^ (a j : ℕ))]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[pow_add (q : ZMod (q ^ ((l' + 1) * m) - 1)) r.val, hef, mul_assoc, ← pow_mul]`. Break down `g with ⟨g, hg1, hg2⟩` into its components or cases.

Apply `(ZMod.natCast_eq_natCast_iff _ _ _).1` to reduce the goal to its premises. Use `show ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod ((q ^ (l' + 1)) ^ m - 1)) = ((∑ j : Fin (l' + 1), k * q ^ (j : ℕ) * (q ^ (l' + 1)) ^ ((g (ef j)).val / (l' + 1)) : ℕ) : ZMod ((q ^ (l' + 1)) ^ m - 1))`. Rewrite using `[hmod, hg2]`. Use `push_cast`. Rewrite using `[← Equiv.sum_comp ef (fun r : ZMod (l' + 1) => (k : ZMod (q ^ ((l' + 1) * m) - 1)) * (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (g r).val)]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_assoc, ← pow_add, ← hef' j, hkey g hg1 (ef j)]`. Introduce `a`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `j`.

Apply `Fin.ext` to reduce the goal to its premises. Use `show ((((ef j).val + (l' + 1) * (a.1 (ef.symm (ef j))).val : ℕ) : ZMod ((l' + 1) * m))).val / (l' + 1) = (a.1 j).val`. Rewrite using `[Equiv.symm_apply_apply, ZMod.val_cast_of_lt (hb _ _ (ZMod.val_lt _) (a.1 j).isLt), Nat.add_mul_div_left _ _ (Nat.succ_pos l'), Nat.div_eq_of_lt (ZMod.val_lt _), zero_add]`. Introduce `g`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `r`. Use `show ((r.val + (l' + 1) * ((g.1 (ef (ef.symm r))).val / (l' + 1)) : ℕ) : ZMod ((l' + 1) * m)) = g.1 r`. Rewrite using `[Equiv.apply_symm_apply, hkey g.1 g.2.1 r, ZMod.natCast_zmod_val]`.
-/
theorem card_eq (q l' m k : ℕ) (hm : 0 < m) :
    (Finset.univ.filter fun a : Fin (l' + 1) → Fin m => k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) ≡
      ∑ j : Fin (l' + 1), k * q ^ (j : ℕ) * (q ^ (l' + 1)) ^ (a j : ℕ) [MOD (q ^ (l' + 1)) ^ m - 1]).card =
    Nat.card {g : ZMod (l' + 1) → ZMod ((l' + 1) * m) //
      (∀ r, ZMod.castHom (dvd_mul_right (l' + 1) m) (ZMod (l' + 1)) (g r) = r) ∧
      ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod (q ^ ((l' + 1) * m) - 1)) =
        ∑ r, (k : ZMod (q ^ ((l' + 1) * m) - 1)) * (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (g r).val} := by
  haveI : NeZero ((l' + 1) * m) := ⟨by positivity⟩
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  let ef : Fin (l' + 1) ≃ ZMod (l' + 1) := Equiv.refl _
  have hef : ∀ r : ZMod (l' + 1), ((ef.symm r : Fin (l' + 1)) : ℕ) = r.val := fun r => rfl
  have hef' : ∀ j : Fin (l' + 1), (ef j).val = (j : ℕ) := fun j => rfl
  have hb : ∀ (j : ℕ) (x : ℕ), j < l' + 1 → x < m → j + (l' + 1) * x < (l' + 1) * m := by
    intro j x hj hx
    calc j + (l' + 1) * x < (l' + 1) + (l' + 1) * x := by omega
      _ = (l' + 1) * (x + 1) := by ring
      _ ≤ (l' + 1) * m := Nat.mul_le_mul_left _ hx
  have hkey : ∀ (g : ZMod (l' + 1) → ZMod ((l' + 1) * m)),
      (∀ r, ZMod.castHom (dvd_mul_right (l' + 1) m) (ZMod (l' + 1)) (g r) = r) →
      ∀ r : ZMod (l' + 1), r.val + (l' + 1) * ((g r).val / (l' + 1)) = (g r).val := by
    intro g hg r
    have h := hg r
    rw [ZMod.castHom_apply, ← ZMod.natCast_val] at h
    have h2 := congrArg ZMod.val h
    rw [ZMod.val_natCast] at h2
    rw [← h2, Nat.mod_add_div]
  have hmod : (q ^ (l' + 1)) ^ m - 1 = q ^ ((l' + 1) * m) - 1 := by rw [← pow_mul]
  refine Nat.card_congr
    { toFun := fun a => ⟨fun r => ((r.val + (l' + 1) * (a.1 (ef.symm r)).val : ℕ) : ZMod ((l' + 1) * m)), ?_, ?_⟩
      invFun := fun g => ⟨fun j => ⟨(g.1 (ef j)).val / (l' + 1),
        (Nat.div_lt_iff_lt_mul (Nat.succ_pos l')).2 (lt_of_lt_of_eq (ZMod.val_lt _) (mul_comm _ _))⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro r
    rw [map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]
  · rcases a with ⟨a, ha⟩
    rw [hmod] at ha
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).2 ha
    have hv : ∀ r : ZMod (l' + 1), (((r.val + (l' + 1) * (a (ef.symm r)).val : ℕ) : ZMod ((l' + 1) * m))).val
        = r.val + (l' + 1) * (a (ef.symm r)).val := fun r =>
      ZMod.val_cast_of_lt (hb _ _ (ZMod.val_lt r) (a (ef.symm r)).isLt)
    simp only [hv]
    rw [h]; push_cast
    rw [← Equiv.sum_comp ef.symm (fun j : Fin (l' + 1) => (k : ZMod (q ^ ((l' + 1) * m) - 1)) *
      (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (j : ℕ) * ((q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (l' + 1)) ^ (a j : ℕ))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pow_add (q : ZMod (q ^ ((l' + 1) * m) - 1)) r.val, hef, mul_assoc, ← pow_mul]
  · rcases g with ⟨g, hg1, hg2⟩
    apply (ZMod.natCast_eq_natCast_iff _ _ _).1
    show ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod ((q ^ (l' + 1)) ^ m - 1)) =
      ((∑ j : Fin (l' + 1), k * q ^ (j : ℕ) * (q ^ (l' + 1)) ^ ((g (ef j)).val / (l' + 1)) : ℕ) : ZMod ((q ^ (l' + 1)) ^ m - 1))
    rw [hmod, hg2]; push_cast
    rw [← Equiv.sum_comp ef (fun r : ZMod (l' + 1) => (k : ZMod (q ^ ((l' + 1) * m) - 1)) *
      (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (g r).val)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, mul_assoc, ← pow_add, ← hef' j, hkey g hg1 (ef j)]
  · intro a
    apply Subtype.ext; funext j; apply Fin.ext
    show ((((ef j).val + (l' + 1) * (a.1 (ef.symm (ef j))).val : ℕ) : ZMod ((l' + 1) * m))).val / (l' + 1)
      = (a.1 j).val
    rw [Equiv.symm_apply_apply, ZMod.val_cast_of_lt (hb _ _ (ZMod.val_lt _) (a.1 j).isLt),
      Nat.add_mul_div_left _ _ (Nat.succ_pos l'), Nat.div_eq_of_lt (ZMod.val_lt _), zero_add]
  · intro g
    apply Subtype.ext; funext r
    show ((r.val + (l' + 1) * ((g.1 (ef (ef.symm r))).val / (l' + 1)) : ℕ) : ZMod ((l' + 1) * m)) = g.1 r
    rw [Equiv.apply_symm_apply, hkey g.1 g.2.1 r, ZMod.natCast_zmod_val]

end GlobalTheory.ExpCount

namespace GlobalTheory.ExpCount

/- English proof (translation)
Introduce `q l m k hq hl hm hlm hreg`. Take `⟨l', rfl⟩ : ∃ l', l = l' + 1` from `⟨l - 1, by have := hl.one_lt; omega⟩`. Rewrite using `[card_eq q l' m k hm]`. Use `haveI : Fact (l' + 1).Prime := ⟨hl⟩`. Use `haveI : NeZero ((l' + 1) * m) := ⟨by positivity⟩`.

Establish `hm0 : (m : ZMod (l' + 1)) ≠ 0` using `fun h0 => hlm ((ZMod.natCast_eq_zero_iff _ _).1 h0)`. Establish `hQ : (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ ((l' + 1) * m) = 1`. Establish `h0 : ((q ^ ((l' + 1) * m) - 1 : ℕ) : ZMod (q ^ ((l' + 1) * m) - 1)) = 0` using `ZMod.natCast_self _`. Rewrite `h0` using `[Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]`. Move the coercions through the operations in `at h0`.

Conclude with `sub_eq_zero.1 h0`. Generalize the expression as in `hMdef : q ^ ((l' + 1) * m) - 1 = M at hQ ⊢`. Establish `hSQ : (q : ZMod M) ^ m * ∑ i ∈ Finset.range (l' + 1), (q : ZMod M) ^ (m * i) = ∑ i ∈ Finset.range (l' + 1), (q : ZMod M) ^ (m * i)`. Establish `h1` using `Finset.sum_range_succ' (fun i => (q : ZMod M) ^ (m * i)) (l' + 1)`. Establish `h2` using `Finset.sum_range_succ (fun i => (q : ZMod M) ^ (m * i)) (l' + 1)`.

Use `beta_reduce at h1 h2`. Establish `h3 : (q : ZMod M) ^ (m * (l' + 1)) = (q : ZMod M) ^ (m * 0)`. Rewrite using `[mul_comm m, hQ, mul_zero, pow_zero]`. Rewrite `h2` using `[h3]`. Rewrite using `[Finset.mul_sum]`.

Establish `h4 : ∀ i ∈ Finset.range (l' + 1), (q : ZMod M) ^ m * (q : ZMod M) ^ (m * i) = (q : ZMod M) ^ (m * (i + 1))` using `fun i _ => by`. Rewrite using `[← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl h4]`.

Conclude with `add_right_cancel (h1.symm.trans h2)`. Set `P : (ZMod (l' + 1) → ZMod ((l' + 1) * m)) → Prop` to `fun g => (∀ r, ZMod.castHom (dvd_mul_right (l' + 1) m) (ZMod (l' + 1)) (g r) = r) ∧ ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod M) = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g r).val`. Establish `hpres : ∀ g, P g → P (fun r => g (r - m) + m)`. Introduce `g hg`. Use `⟨fun r => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, hg.1, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `e : ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g (r - m) + m).val = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g r + m).val` using `Equiv.sum_comp (Equiv.subRight (m : ZMod (l' + 1))) (fun r => (k : ZMod M) * (q : ZMod M) ^ (g r + m).val) show _ = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g (r - m) + m).val`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[pow_val_add_natCast _ hQ]`. Expand and normalize the polynomial expressions, which then agree. Set `X` to `{g : ZMod (l' + 1) → ZMod ((l' + 1) * m) // P g}`.

Set `σ : Function.End X` to `fun g => ⟨fun r => g.1 (r - m) + m, hpres g.1 g.2⟩`. Establish `hpow : ∀ n : ℕ, ∀ g : X, ((σ ^ n) g).1 = fun r => g.1 (r - (n : ZMod (l' + 1)) * m) + ((n * m : ℕ) : ZMod ((l' + 1) * m))`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro g`.

Use function extensionality and compare the values at `r`. Rewrite using `[pow_zero]`. Use `show g.1 r = _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Introduce `g`. Use function extensionality and compare the values at `r`. Rewrite using `[pow_succ]`. Use `show ((σ ^ n) (σ g)).1 r = _`. Rewrite using `[ih]`.

Use `show g.1 (r - (n : ZMod (l' + 1)) * m - m) + m + ((n * m : ℕ) : ZMod ((l' + 1) * m)) = _`. Rewrite using `[add_assoc]`. Use `congr 1`. Use `congr 1`. Use `push_cast`.

Put the polynomial expressions in normal form. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hσ : σ ^ (l' + 1) ^ 1 = 1`. Rewrite using `[pow_one]`.

Use `funext fun g => Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[hpow]`. Use function extensionality and compare the values at `r`. Use `show _ = g.1 r`. Rewrite using `[ZMod.natCast_self, ZMod.natCast_self, zero_mul, sub_zero, add_zero]`.

Establish `hcard` using `Equiv.Perm.card_fixedPoints_modEq (p := l' + 1) (n := 1) hσ`. Set `gs : ZMod (l' + 1) → ZMod ((l' + 1) * m)` to `fun r => (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m))`. Establish `hgs_fix : ∀ r, gs (r - m) + m = gs r`. Introduce `r`. Use `show ((((r - m) * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m)) + m = (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m))`.

Establish `e : (r - m) * (m : ZMod (l' + 1))⁻¹ = r * (m : ZMod (l' + 1))⁻¹ - 1`. Rewrite using `[sub_mul, mul_inv_cancel₀ hm0]`. Rewrite using `[e]`. Establish `h1 : (r * (m : ZMod (l' + 1))⁻¹ - 1).val + 1 ≡ (r * (m : ZMod (l' + 1))⁻¹).val [MOD l' + 1]`. Rewrite using `[← ZMod.natCast_eq_natCast_iff]`.

Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `(ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.ModEq.mul_right' m h1)`. Rewrite using `[← h2]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hgs0 : gs 0 = 0` using `by simp [gs]`. Establish `hgsP : P gs`. Use `⟨fun r => ?_, ?_⟩` and prove the remaining obligations.

Use `show ZMod.castHom _ (ZMod (l' + 1)) (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m)) = r`. Rewrite using `[map_natCast]`. Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hm0, mul_one]`. Use `show _ = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (gs r).val`.

Rewrite using `[← Finset.mul_sum, fixed_sum M l' m _ hl hlm hm hQ gs hgs_fix, hgs0, ZMod.val_zero, pow_zero, one_mul]`. Use `push_cast`. Both sides reduce to the same expression. Establish `huniq : ∀ g, P g → (∀ r, g (r - m) + m = g r) → g = gs`. Introduce `g hg hfix`.

Establish `hs` using `fixed_sum M l' m (q : ZMod M) hl hlm hm hQ g hfix`. Establish `hlc : l' + 1 ∣ (g 0).val`. Establish `h` using `hg.1 0`. Rewrite `h` using `[ZMod.castHom_apply, ← ZMod.natCast_val]`. Conclude with `(ZMod.natCast_eq_zero_iff _ _).1 h`.

Establish `hmodeq : k * (∑ i ∈ Finset.range (l' + 1), q ^ (m * i)) * q ^ (g 0).val ≡ k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) [MOD q ^ ((l' + 1) * m) - 1]`. Rewrite using `[hMdef, ← ZMod.natCast_eq_natCast_iff]`. Establish `h2` using `hg.2`. Rewrite `h2` using `[← Finset.mul_sum, hs]`. Move the coercions through the operations in `at h2 ⊢`.

Take the linear combination `h2.symm`. Establish `hc` using `eq_zero_of_modEq q (l' + 1) m k (g 0).val hq hl hm hlm hreg (ZMod.val_lt _) hlc hmodeq`. Establish `h0 : g 0 = 0` using `(ZMod.val_eq_zero _).1 hc`. Use function extensionality and compare the values at `r`. Rewrite using `[fixed_eq l' m hl hlm g hfix r, h0, zero_add]`.

Establish `hfp : Fintype.card (Function.fixedPoints σ) = 1`. Rewrite using `[Fintype.card_eq_one_iff]`. Use `⟨⟨⟨gs, hgsP⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show σ ⟨gs, hgsP⟩ = ⟨gs, hgsP⟩`. Conclude with `Subtype.ext (funext hgs_fix)`.

Introduce and unpack `⟨⟨g, hg⟩, hfx⟩`. Establish `hfx' : σ ⟨g, hg⟩ = ⟨g, hg⟩` using `hfx`. Establish `hfix : ∀ r, g (r - m) + m = g r` using `fun r => congrFun (congrArg Subtype.val hfx') r`. Conclude with `Subtype.ext (Subtype.ext (huniq g hg hfix))`. Express the relevant statement in the definitionally equal form `Nat.card X ≡ 1 [MOD l' + 1]`.

Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `hcard.trans (by rw [hfp])`.
-/
theorem count_one_mod : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k →
    (Finset.univ.filter fun a : Fin l → Fin m => k * ∑ i ∈ Finset.range l, q ^ (m * i) ≡
      ∑ j : Fin l, k * q ^ (j : ℕ) * (q ^ l) ^ (a j : ℕ) [MOD (q ^ l) ^ m - 1]).card ≡ 1 [MOD l] := by
  intro q l m k hq hl hm hlm hreg
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by have := hl.one_lt; omega⟩
  rw [card_eq q l' m k hm]
  haveI : Fact (l' + 1).Prime := ⟨hl⟩
  haveI : NeZero ((l' + 1) * m) := ⟨by positivity⟩
  have hm0 : (m : ZMod (l' + 1)) ≠ 0 := fun h0 => hlm ((ZMod.natCast_eq_zero_iff _ _).1 h0)
  have hQ : (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ ((l' + 1) * m) = 1 := by
    have h0 : ((q ^ ((l' + 1) * m) - 1 : ℕ) : ZMod (q ^ ((l' + 1) * m) - 1)) = 0 := ZMod.natCast_self _
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))] at h0
    push_cast at h0
    exact sub_eq_zero.1 h0
  generalize hMdef : q ^ ((l' + 1) * m) - 1 = M at hQ ⊢
  have hSQ : (q : ZMod M) ^ m * ∑ i ∈ Finset.range (l' + 1), (q : ZMod M) ^ (m * i)
      = ∑ i ∈ Finset.range (l' + 1), (q : ZMod M) ^ (m * i) := by
    have h1 := Finset.sum_range_succ' (fun i => (q : ZMod M) ^ (m * i)) (l' + 1)
    have h2 := Finset.sum_range_succ (fun i => (q : ZMod M) ^ (m * i)) (l' + 1)
    beta_reduce at h1 h2
    have h3 : (q : ZMod M) ^ (m * (l' + 1)) = (q : ZMod M) ^ (m * 0) := by
      rw [mul_comm m, hQ, mul_zero, pow_zero]
    rw [h3] at h2
    rw [Finset.mul_sum]
    have h4 : ∀ i ∈ Finset.range (l' + 1),
        (q : ZMod M) ^ m * (q : ZMod M) ^ (m * i) = (q : ZMod M) ^ (m * (i + 1)) := fun i _ => by
      rw [← pow_add]; congr 1; ring
    rw [Finset.sum_congr rfl h4]
    exact add_right_cancel (h1.symm.trans h2)
  let P : (ZMod (l' + 1) → ZMod ((l' + 1) * m)) → Prop := fun g =>
    (∀ r, ZMod.castHom (dvd_mul_right (l' + 1) m) (ZMod (l' + 1)) (g r) = r) ∧
      ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod M) = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g r).val
  have hpres : ∀ g, P g → P (fun r => g (r - m) + m) := by
    intro g hg
    refine ⟨fun r => ?_, ?_⟩
    · rw [map_add, hg.1, map_natCast]; ring
    · have e : ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g (r - m) + m).val
          = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g r + m).val :=
        Equiv.sum_comp (Equiv.subRight (m : ZMod (l' + 1))) (fun r => (k : ZMod M) * (q : ZMod M) ^ (g r + m).val)
      show _ = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g (r - m) + m).val
      rw [e]
      calc ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod M)
          = (q : ZMod M) ^ m * ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod M) := by
            push_cast; rw [mul_left_comm, hSQ]
        _ = (q : ZMod M) ^ m * ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g r).val := by rw [hg.2]
        _ = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g r + m).val := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [pow_val_add_natCast _ hQ]; ring
  let X := {g : ZMod (l' + 1) → ZMod ((l' + 1) * m) // P g}
  let σ : Function.End X := fun g => ⟨fun r => g.1 (r - m) + m, hpres g.1 g.2⟩
  have hpow : ∀ n : ℕ, ∀ g : X, ((σ ^ n) g).1 =
      fun r => g.1 (r - (n : ZMod (l' + 1)) * m) + ((n * m : ℕ) : ZMod ((l' + 1) * m)) := by
    intro n
    induction n with
    | zero => intro g; funext r; rw [pow_zero]; show g.1 r = _; simp
    | succ n ih =>
      intro g; funext r
      rw [pow_succ]
      show ((σ ^ n) (σ g)).1 r = _
      rw [ih]
      show g.1 (r - (n : ZMod (l' + 1)) * m - m) + m + ((n * m : ℕ) : ZMod ((l' + 1) * m)) = _
      rw [add_assoc]
      congr 1
      · congr 1; push_cast; ring_nf
      · push_cast; ring
  have hσ : σ ^ (l' + 1) ^ 1 = 1 := by
    rw [pow_one]
    refine funext fun g => Subtype.ext ?_
    rw [hpow]
    funext r
    show _ = g.1 r
    rw [ZMod.natCast_self, ZMod.natCast_self, zero_mul, sub_zero, add_zero]
  have hcard := Equiv.Perm.card_fixedPoints_modEq (p := l' + 1) (n := 1) hσ
  let gs : ZMod (l' + 1) → ZMod ((l' + 1) * m) :=
    fun r => (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m))
  have hgs_fix : ∀ r, gs (r - m) + m = gs r := by
    intro r
    show ((((r - m) * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m)) + m
      = (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m))
    have e : (r - m) * (m : ZMod (l' + 1))⁻¹ = r * (m : ZMod (l' + 1))⁻¹ - 1 := by
      rw [sub_mul, mul_inv_cancel₀ hm0]
    rw [e]
    have h1 : (r * (m : ZMod (l' + 1))⁻¹ - 1).val + 1 ≡ (r * (m : ZMod (l' + 1))⁻¹).val [MOD l' + 1] := by
      rw [← ZMod.natCast_eq_natCast_iff]; push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; ring
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.ModEq.mul_right' m h1)
    rw [← h2]; push_cast; ring
  have hgs0 : gs 0 = 0 := by simp [gs]
  have hgsP : P gs := by
    refine ⟨fun r => ?_, ?_⟩
    · show ZMod.castHom _ (ZMod (l' + 1)) (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m)) = r
      rw [map_natCast]; push_cast
      rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hm0, mul_one]
    · show _ = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (gs r).val
      rw [← Finset.mul_sum, fixed_sum M l' m _ hl hlm hm hQ gs hgs_fix, hgs0, ZMod.val_zero, pow_zero, one_mul]
      push_cast; rfl
  have huniq : ∀ g, P g → (∀ r, g (r - m) + m = g r) → g = gs := by
    intro g hg hfix
    have hs := fixed_sum M l' m (q : ZMod M) hl hlm hm hQ g hfix
    have hlc : l' + 1 ∣ (g 0).val := by
      have h := hg.1 0
      rw [ZMod.castHom_apply, ← ZMod.natCast_val] at h
      exact (ZMod.natCast_eq_zero_iff _ _).1 h
    have hmodeq : k * (∑ i ∈ Finset.range (l' + 1), q ^ (m * i)) * q ^ (g 0).val
        ≡ k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) [MOD q ^ ((l' + 1) * m) - 1] := by
      rw [hMdef, ← ZMod.natCast_eq_natCast_iff]
      have h2 := hg.2
      rw [← Finset.mul_sum, hs] at h2
      push_cast at h2 ⊢
      linear_combination h2.symm
    have hc := eq_zero_of_modEq q (l' + 1) m k (g 0).val hq hl hm hlm hreg (ZMod.val_lt _) hlc hmodeq
    have h0 : g 0 = 0 := (ZMod.val_eq_zero _).1 hc
    funext r
    rw [fixed_eq l' m hl hlm g hfix r, h0, zero_add]
  have hfp : Fintype.card (Function.fixedPoints σ) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨gs, hgsP⟩, ?_⟩, ?_⟩
    · show σ ⟨gs, hgsP⟩ = ⟨gs, hgsP⟩
      exact Subtype.ext (funext hgs_fix)
    · rintro ⟨⟨g, hg⟩, hfx⟩
      have hfx' : σ ⟨g, hg⟩ = ⟨g, hg⟩ := hfx
      have hfix : ∀ r, g (r - m) + m = g r := fun r => congrFun (congrArg Subtype.val hfx') r
      exact Subtype.ext (Subtype.ext (huniq g hg hfix))
  change Nat.card X ≡ 1 [MOD l' + 1]
  rw [Nat.card_eq_fintype_card]
  exact hcard.trans (by rw [hfp])

end GlobalTheory.ExpCount
