import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Finset

namespace GlobalTheory.CompanionTheory.SquareRootCount

def rootCount (n : ℤ) (e : ℕ) : ℕ :=
  ((range e).filter fun x : ℕ => (e : ℤ) ∣ (x : ℤ) ^ 2 - n).card

noncomputable def addCharAt (d : ℕ) (t : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) / (d : ℂ))

noncomputable def rootSum (n : ℤ) (d : ℕ) : ℂ :=
  ∑ x ∈ range d, ∑ r ∈ (range d).filter (fun r : ℕ => Nat.Coprime r d),
    addCharAt d ((r : ℤ) * ((x : ℤ) ^ 2 - n))

/- English proof (translation)
Establish `he0 : (e : ℂ) ≠ 0` using `by exact_mod_cast he.ne'`. Establish `hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (e : ℂ))) e` using `Complex.isPrimitiveRoot_exp e he.ne'`. Use `set ζ := Complex.exp (2 * Real.pi * Complex.I / (e : ℂ)) with hζ`. Establish `hterm : ∀ r : ℕ, addCharAt e ((r : ℤ) * m) = (ζ ^ m) ^ r`. Introduce `r`.

Rewrite using `[← zpow_natCast, ← zpow_mul, hζ, ← Complex.exp_int_mul]`. Unfold `addCharAt`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[hterm]`. Use `split_ifs with h`. Rewrite using `[(hprim.zpow_eq_one_iff_dvd m).2 h]`. Simplify using the standard rewrite rules. Establish `h1 : ζ ^ m ≠ 1` using `fun h' => h ((hprim.zpow_eq_one_iff_dvd m).1 h')`.

Rewrite using `[geom_sum_eq h1]`. Establish `: (ζ ^ m) ^ e = 1`. Rewrite using `[← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hprim.pow_eq_one, one_zpow]`. Simplify using `[this]`.
-/
theorem geom_addChar {e : ℕ} (he : 0 < e) (m : ℤ) :
    ∑ r ∈ range e, addCharAt e ((r : ℤ) * m) = if (e : ℤ) ∣ m then (e : ℂ) else 0 := by
  have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (e : ℂ))) e :=
    Complex.isPrimitiveRoot_exp e he.ne'
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (e : ℂ)) with hζ
  have hterm : ∀ r : ℕ, addCharAt e ((r : ℤ) * m) = (ζ ^ m) ^ r := by
    intro r
    rw [← zpow_natCast, ← zpow_mul, hζ, ← Complex.exp_int_mul]
    unfold addCharAt
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  split_ifs with h
  · rw [(hprim.zpow_eq_one_iff_dvd m).2 h]
    simp
  · have h1 : ζ ^ m ≠ 1 := fun h' => h ((hprim.zpow_eq_one_iff_dvd m).1 h')
    rw [geom_sum_eq h1]
    have : (ζ ^ m) ^ e = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hprim.pow_eq_one, one_zpow]
    simp [this]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `hs : ∀ s : Finset ℕ, (s.filter fun x : ℕ => (e : ℤ) ∣ (x : ℤ) ^ 2 - n).card = ∑ x ∈ s, if (e : ℤ) ∣ (x : ℤ) ^ 2 - n then 1 else 0` using `fun s => by`. Rewrite using `[card_filter]`.

Rewrite `ih`, the goal using `[hs]`. Rewrite using `[Nat.mul_succ, sum_range_add, ih, Nat.succ_mul]`. Use `congr 1`. Unfold `rootCount`. Rewrite using `[hs]`.

Use `sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Establish `: (e : ℤ) ∣ (((e * k + x : ℕ) : ℤ)) ^ 2 - n ↔ (e : ℤ) ∣ (x : ℤ) ^ 2 - n`. Establish `hd : (e : ℤ) ∣ (((e * k + x : ℕ) : ℤ)) ^ 2 - (x : ℤ) ^ 2` using `⟨k * (e * k + 2 * x), by push_cast; ring⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `dvd_sub h hd` as an intermediate fact. Simplify using `using this`. Introduce `h`. Use `dvd_add h hd` as an intermediate fact. Simplify using `using this`.

Simplify using `only [this]`.
-/
theorem count_periodic (n : ℤ) (e k : ℕ) :
    ((range (e * k)).filter fun x : ℕ => (e : ℤ) ∣ (x : ℤ) ^ 2 - n).card = k * rootCount n e := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs : ∀ s : Finset ℕ, (s.filter fun x : ℕ => (e : ℤ) ∣ (x : ℤ) ^ 2 - n).card
        = ∑ x ∈ s, if (e : ℤ) ∣ (x : ℤ) ^ 2 - n then 1 else 0 := fun s => by
      rw [card_filter]
    rw [hs] at ih ⊢
    rw [Nat.mul_succ, sum_range_add, ih, Nat.succ_mul]
    congr 1
    unfold rootCount
    rw [hs]
    refine sum_congr rfl fun x _ => ?_
    have : (e : ℤ) ∣ (((e * k + x : ℕ) : ℤ)) ^ 2 - n ↔ (e : ℤ) ∣ (x : ℤ) ^ 2 - n := by
      have hd : (e : ℤ) ∣ (((e * k + x : ℕ) : ℤ)) ^ 2 - (x : ℤ) ^ 2 :=
        ⟨k * (e * k + 2 * x), by push_cast; ring⟩
      constructor
      · intro h
        have := dvd_sub h hd
        simpa using this
      · intro h
        have := dvd_add h hd
        simpa using this
    simp only [this]

/- English proof (translation)
Establish `h` using `congrArg (fun f : ArithmeticFunction ℤ => f m) ArithmeticFunction.moebius_mul_coe_zeta`. Simplify using `only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h`. Conclude with `h`.
-/
theorem sum_moebius_divisors {m : ℕ} (hm : m ≠ 0) :
    ∑ g ∈ m.divisors, ArithmeticFunction.moebius g = if m = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

/- English proof (translation)
Establish `hind : ∀ r : ℕ, (if Nat.Coprime r d then f r else 0) = ∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) * f r else 0`. Introduce `r`. Establish `hg : Nat.gcd r d ≠ 0` using `Nat.gcd_ne_zero_right hd.ne'`. Establish `hdiv : (Nat.gcd r d).divisors = d.divisors.filter (· ∣ r)`. Use extensionality with `g`.

Simplify using `only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, -⟩`. Conclude with `⟨⟨h2, hd.ne'⟩, h1⟩`. Introduce and unpack `⟨⟨h2, -⟩, h1⟩`.

Conclude with `⟨⟨h1, h2⟩, hg⟩`. Establish `h` using `sum_moebius_divisors hg`. Rewrite `h` using `[hdiv, sum_filter]`. Establish `h' : (∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) else 0) = if Nat.Coprime r d then 1 else 0`. Use `congrArg (fun z : ℤ => (z : ℂ)) h` as an intermediate fact.

Simplify using `only [Int.cast_sum] at this`. Simplify using `only [apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero, Int.cast_one] at this`. Conclude with `this`. Establish `h'' : (∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) * f r else 0) = (∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) else 0) * f r`. Rewrite using `[sum_mul]`.

Use `sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[h'', h']`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[sum_filter]`.

Repeatedly rewrite using `[hind]`. Rewrite using `[sum_comm]`. Use `sum_congr rfl fun g hg => ?_` and prove the remaining obligations. Establish `hgd : g ∣ d` using `Nat.dvd_of_mem_divisors hg`. Establish `hg0 : 0 < g` using `Nat.pos_of_mem_divisors hg`.

Rewrite using `[← sum_filter, ← mul_sum]`. Use `congr 1`. Establish `himg : (range d).filter (fun r => g ∣ r) = (range (d / g)).image (fun r => g * r)`. Use extensionality with `r`. Simplify using `only [mem_filter, mem_range, mem_image]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hr, k, rfl⟩`. Use `⟨k, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Nat.lt_div_iff_mul_lt' hgd]`. Conclude with `hr`.

Introduce and unpack `⟨k, hk, rfl⟩`. Use `⟨?_, dvd_mul_right _ _⟩` and prove the remaining obligations. Rewrite `hk` using `[Nat.lt_div_iff_mul_lt' hgd]`. Then use the resulting hypothesis. Rewrite using `[himg, sum_image]`. Introduce `a _ b _ hab`.

Conclude with `Nat.eq_of_mul_eq_mul_left hg0 hab`.
-/
theorem sum_coprime_eq {d : ℕ} (hd : 0 < d) (f : ℕ → ℂ) :
    ∑ r ∈ (range d).filter (fun r : ℕ => Nat.Coprime r d), f r
      = ∑ g ∈ d.divisors, (ArithmeticFunction.moebius g : ℂ) * ∑ r ∈ range (d / g), f (g * r) := by
  have hind : ∀ r : ℕ, (if Nat.Coprime r d then f r else 0)
      = ∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) * f r else 0 := by
    intro r
    have hg : Nat.gcd r d ≠ 0 := Nat.gcd_ne_zero_right hd.ne'
    have hdiv : (Nat.gcd r d).divisors = d.divisors.filter (· ∣ r) := by
      ext g
      simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩
        exact ⟨⟨h2, hd.ne'⟩, h1⟩
      · rintro ⟨⟨h2, -⟩, h1⟩
        exact ⟨⟨h1, h2⟩, hg⟩
    have h := sum_moebius_divisors hg
    rw [hdiv, sum_filter] at h
    have h' : (∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) else 0)
        = if Nat.Coprime r d then 1 else 0 := by
      have := congrArg (fun z : ℤ => (z : ℂ)) h
      simp only [Int.cast_sum] at this
      simp only [apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero, Int.cast_one] at this
      exact this
    have h'' : (∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) * f r else 0)
        = (∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) else 0) * f r := by
      rw [sum_mul]
      refine sum_congr rfl fun g _ => ?_
      split_ifs <;> simp
    rw [h'', h']
    split_ifs <;> simp
  rw [sum_filter]
  simp_rw [hind]
  rw [sum_comm]
  refine sum_congr rfl fun g hg => ?_
  have hgd : g ∣ d := Nat.dvd_of_mem_divisors hg
  have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
  rw [← sum_filter, ← mul_sum]
  congr 1
  have himg : (range d).filter (fun r => g ∣ r) = (range (d / g)).image (fun r => g * r) := by
    ext r
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hr, k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      rw [Nat.lt_div_iff_mul_lt' hgd]
      exact hr
    · rintro ⟨k, hk, rfl⟩
      refine ⟨?_, dvd_mul_right _ _⟩
      rwa [Nat.lt_div_iff_mul_lt' hgd] at hk
  rw [himg, sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hg0 hab

/- English proof (translation)
Unfold `addCharAt`. Use `congr 1`. Establish `h1 : (g : ℂ) ≠ 0` using `by exact_mod_cast hg.ne'`. Establish `h2 : (e : ℂ) ≠ 0` using `by exact_mod_cast he.ne'`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem addCharAt_mul {g e : ℕ} (hg : 0 < g) (he : 0 < e) (t : ℤ) :
    addCharAt (g * e) ((g : ℤ) * t) = addCharAt e t := by
  unfold addCharAt
  congr 1
  have h1 : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have h2 : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  push_cast
  field_simp

/- English proof (translation)
Establish `hinner : ∀ x : ℕ, ∑ r ∈ (range d).filter (fun r : ℕ => Nat.Coprime r d), addCharAt d ((r : ℤ) * ((x : ℤ) ^ 2 - n)) = ∑ g ∈ d.divisors, (ArithmeticFunction.moebius g : ℂ) * (if ((d / g : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - n then ((d / g : ℕ) : ℂ) else 0)`. Introduce `x`. Rewrite using `[sum_coprime_eq hd]`. Use `sum_congr rfl fun g hg => ?_` and prove the remaining obligations. Establish `hgd : g ∣ d` using `Nat.dvd_of_mem_divisors hg`.

Establish `hg0 : 0 < g` using `Nat.pos_of_mem_divisors hg`. Establish `he : 0 < d / g` using `Nat.div_pos (Nat.le_of_dvd hd hgd) hg0`. Use `congr 1`. Rewrite using `[← geom_addChar he]`. Use `sum_congr rfl fun r _ => ?_` and prove the remaining obligations.

Use `conv_lhs => rw [← Nat.mul_div_cancel' hgd]`. Rewrite using `[← addCharAt_mul hg0 he]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Unfold `rootSum`. Repeatedly rewrite using `[hinner]`. Rewrite using `[sum_comm]`. Rewrite using `[← Nat.sum_div_divisors d (fun e => (ArithmeticFunction.moebius (d / e) : ℂ) * (rootCount n e : ℂ)), mul_sum]`. Use `sum_congr rfl fun g hg => ?_` and prove the remaining obligations.

Establish `hgd : g ∣ d` using `Nat.dvd_of_mem_divisors hg`. Establish `hg0 : 0 < g` using `Nat.pos_of_mem_divisors hg`. Establish `he : 0 < d / g` using `Nat.div_pos (Nat.le_of_dvd hd hgd) hg0`. Rewrite using `[← mul_sum, Nat.div_div_self hgd hd.ne']`. Establish `hcount : ∑ x ∈ range d, (if ((d / g : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - n then ((d / g : ℕ) : ℂ) else 0) = ((d / g : ℕ) : ℂ) * ((g : ℂ) * (rootCount n (d / g) : ℂ))`.

Establish `hc` using `count_periodic n (d / g) g`. Rewrite `hc` using `[Nat.div_mul_cancel hgd]`. Rewrite using `[← sum_filter, sum_const, nsmul_eq_mul, hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hcount]`. Establish `hdc : (d : ℂ) = ((d / g : ℕ) : ℂ) * (g : ℂ)`. Conclude with `(Nat.div_mul_cancel hgd).symm` after adjusting the coercions. Rewrite using `[hdc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rootSum_eq (n : ℤ) {d : ℕ} (hd : 0 < d) :
    rootSum n d
      = (d : ℂ) * ∑ e ∈ d.divisors, (ArithmeticFunction.moebius (d / e) : ℂ) * (rootCount n e : ℂ) := by
  have hinner : ∀ x : ℕ, ∑ r ∈ (range d).filter (fun r : ℕ => Nat.Coprime r d),
      addCharAt d ((r : ℤ) * ((x : ℤ) ^ 2 - n))
      = ∑ g ∈ d.divisors, (ArithmeticFunction.moebius g : ℂ) *
          (if ((d / g : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - n then ((d / g : ℕ) : ℂ) else 0) := by
    intro x
    rw [sum_coprime_eq hd]
    refine sum_congr rfl fun g hg => ?_
    have hgd : g ∣ d := Nat.dvd_of_mem_divisors hg
    have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
    have he : 0 < d / g := Nat.div_pos (Nat.le_of_dvd hd hgd) hg0
    congr 1
    rw [← geom_addChar he]
    refine sum_congr rfl fun r _ => ?_
    conv_lhs => rw [← Nat.mul_div_cancel' hgd]
    rw [← addCharAt_mul hg0 he]
    congr 1
    push_cast
    ring
  unfold rootSum
  simp_rw [hinner]
  rw [sum_comm]
  rw [← Nat.sum_div_divisors d (fun e => (ArithmeticFunction.moebius (d / e) : ℂ) * (rootCount n e : ℂ)), mul_sum]
  refine sum_congr rfl fun g hg => ?_
  have hgd : g ∣ d := Nat.dvd_of_mem_divisors hg
  have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
  have he : 0 < d / g := Nat.div_pos (Nat.le_of_dvd hd hgd) hg0
  rw [← mul_sum, Nat.div_div_self hgd hd.ne']
  have hcount : ∑ x ∈ range d, (if ((d / g : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - n then ((d / g : ℕ) : ℂ) else 0)
      = ((d / g : ℕ) : ℂ) * ((g : ℂ) * (rootCount n (d / g) : ℂ)) := by
    have hc := count_periodic n (d / g) g
    rw [Nat.div_mul_cancel hgd] at hc
    rw [← sum_filter, sum_const, nsmul_eq_mul, hc]
    push_cast
    ring
  rw [hcount]
  have hdc : (d : ℂ) = ((d / g : ℕ) : ℂ) * (g : ℂ) := by
    exact_mod_cast (Nat.div_mul_cancel hgd).symm
  rw [hdc]
  ring

/- English proof (translation)
Establish `key : ∀ x : ℕ, (e : ℤ) ∣ (x : ℤ) ^ 2 - n ↔ ((x : ZMod e)) ^ 2 = (n : ZMod e)`. Introduce `x`. Rewrite using `[← CharP.intCast_eq_zero_iff (ZMod e) e]`. Use `push_cast`. Conclude with `sub_eq_zero`.

Unfold `rootCount`. Use `card_bij (fun x _ => (x : ZMod e)) ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [mem_filter, mem_univ, true_and]`. Conclude with `(key x).1 (mem_filter.1 hx).2`.

Introduce `a ha b hb hab`. Establish `ha'` using `mem_range.1 (mem_filter.1 ha).1`. Establish `hb'` using `mem_range.1 (mem_filter.1 hb).1`. Use `(ZMod.natCast_eq_natCast_iff' a b e).1 hab` as an intermediate fact. Rewrite `this` using `[Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb']`. Then use the resulting hypothesis.

Introduce `y hy`. Use `⟨y.val, ?_, by simp⟩` and prove the remaining obligations. Use `mem_filter.2 ⟨mem_range.2 (ZMod.val_lt y), (key _).2 ?_⟩` and prove the remaining obligations. Simplify using `using (mem_filter.1 hy).2`.
-/
theorem rootCount_eq_card_zmod (n : ℤ) (e : ℕ) [NeZero e] :
    rootCount n e = (univ.filter fun x : ZMod e => x ^ 2 = (n : ZMod e)).card := by
  have key : ∀ x : ℕ, (e : ℤ) ∣ (x : ℤ) ^ 2 - n ↔ ((x : ZMod e)) ^ 2 = (n : ZMod e) := by
    intro x
    rw [← CharP.intCast_eq_zero_iff (ZMod e) e]
    push_cast
    exact sub_eq_zero
  unfold rootCount
  refine card_bij (fun x _ => (x : ZMod e)) ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and]
    exact (key x).1 (mem_filter.1 hx).2
  · intro a ha b hb hab
    have ha' := mem_range.1 (mem_filter.1 ha).1
    have hb' := mem_range.1 (mem_filter.1 hb).1
    have := (ZMod.natCast_eq_natCast_iff' a b e).1 hab
    rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
  · intro y hy
    refine ⟨y.val, ?_, by simp⟩
    refine mem_filter.2 ⟨mem_range.2 (ZMod.val_lt y), (key _).2 ?_⟩
    simpa using (mem_filter.1 hy).2

/- English proof (translation)
Unfold `Ad3.S.RR rootSum Ad3.S.GS`. Repeatedly rewrite using `[sum_mul]`. Rewrite using `[sum_comm]`. Use `sum_congr rfl fun x _ => sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Unfold `Ad3.S.ee addCharAt`.

Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rr_eq_rootSum (n : ℤ) (d : ℕ) : Ad3.S.RR n d = rootSum n d := by
  unfold Ad3.S.RR rootSum Ad3.S.GS
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun r _ => ?_
  unfold Ad3.S.ee addCharAt
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Introduce `n d hd` and use `by rw [rr_eq_rootSum] exact rootSum_eq n hd`.
-/
theorem rr_eq : Ad3.S.N1 := fun n d hd => by
  rw [rr_eq_rootSum]
  exact rootSum_eq n hd

end GlobalTheory.CompanionTheory.SquareRootCount
