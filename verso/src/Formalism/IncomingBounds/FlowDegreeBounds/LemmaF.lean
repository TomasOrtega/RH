import Formalism.IncomingBounds.IncomingBound
import Formalism.IncomingBounds.LevelTail

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

section Helpers

variable {l d : ℕ} [NeZero d]

/- English proof (translation)
Unfold `oddLevels at hi`. Establish `h` using `(Finset.mem_filter.1 hi).2.pos`. Use linear arithmetic over natural numbers and integers.
-/
private lemma oddLevels_one_le {d i : ℕ} (hi : i ∈ oddLevels d) : 1 ≤ i := by
  unfold oddLevels at hi
  have h := (Finset.mem_filter.1 hi).2.pos
  omega

/- English proof (translation)
Unfold `oddLevels`. Conclude with `Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), odd_one⟩`.
-/
private lemma one_mem_oddLevels {d : ℕ} (hd : 2 ≤ d) : 1 ∈ oddLevels d := by
  unfold oddLevels
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), odd_one⟩

/- English proof (translation)
Establish `h2 : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `h1 : (l : ℝ) ^ 2 - 1 ≠ 0` using `(by nlinarith : (0 : ℝ) < (l : ℝ) ^ 2 - 1).ne'`. Establish `h3 : (l : ℝ) + 1 ≠ 0` using `(by linarith : (0 : ℝ) < (l : ℝ) + 1).ne'`. Unfold `gam rho`. Rewrite using `[div_sub_div _ _ h1 h3, div_eq_div_iff (mul_ne_zero h1 h3) h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma gam_sub_inv (hl : 2 ≤ l) : gam l - 1 / ((l : ℝ) + 1) = rho l := by
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (l : ℝ) ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < (l : ℝ) ^ 2 - 1).ne'
  have h3 : (l : ℝ) + 1 ≠ 0 := (by linarith : (0 : ℝ) < (l : ℝ) + 1).ne'
  unfold gam rho
  rw [div_sub_div _ _ h1 h3, div_eq_div_iff (mul_ne_zero h1 h3) h1]
  ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem one_le_pow_of_one_le_real {a : ℝ} (ha : 1 ≤ a) (n : ℕ) : 1 ≤ a ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ]; nlinarith

/- English proof (translation)
Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le h`. Rewrite using `[pow_add]`. Establish `h1` using `one_le_pow_of_one_le_real ha k`. Establish `h2 : 0 ≤ a ^ m` using `pow_nonneg (by linarith) m`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem pow_le_pow_right_of_one_le_real {a : ℝ} (ha : 1 ≤ a) {m n : ℕ} (h : m ≤ n) : a ^ m ≤ a ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  have h1 := one_le_pow_of_one_le_real ha k
  have h2 : 0 ≤ a ^ m := pow_nonneg (by linarith) m
  nlinarith

/- English proof (translation)
Establish `h` using `pow_le_pow_right_of_one_le_real ha hn`. Rewrite `h` using `[pow_one]`. Then use the resulting hypothesis.
-/
private theorem self_le_pow_of_one_le_of_one_le_exp {a : ℝ} (ha : 1 ≤ a) {n : ℕ} (hn : 1 ≤ n) : a ≤ a ^ n := by
  have h := pow_le_pow_right_of_one_le_real ha hn
  rwa [pow_one] at h

/- English proof (translation)
Establish `hl1 : (1 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hpos : (0 : ℝ) < (l : ℝ) + 1` using `by linarith`. Establish `hc : ((l : ℝ) + 1) * (1 / ((l : ℝ) + 1)) = 1` using `mul_one_div_cancel hpos.ne'`. Establish `hc0 : 0 ≤ 1 / ((l : ℝ) + 1)` using `by positivity`. Use `⟨fun s => ⟨hc0, ?_⟩, fun s i hi => ?_⟩` and prove the remaining obligations.

Use `show 1 / ((l : ℝ) + 1) ≤ 1`. Use the polynomial consequences of the given equalities and inequalities. Use `show 1 ≤ (l : ℝ) ^ i * (1 / ((l : ℝ) + 1)) + 1 / ((l : ℝ) + 1)`. Establish `hli` using `self_le_pow_of_one_le_of_one_le_exp hl1 (oddLevels_one_le hi)`. Establish `hm` using `mul_le_mul_of_nonneg_right hli hc0`.

Use the polynomial consequences of the given equalities and inequalities.
-/
private lemma isDual_const (hl : 1 ≤ l) : IsDual l d (fun _ => 1 / ((l : ℝ) + 1)) := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hpos : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have hc : ((l : ℝ) + 1) * (1 / ((l : ℝ) + 1)) = 1 := mul_one_div_cancel hpos.ne'
  have hc0 : 0 ≤ 1 / ((l : ℝ) + 1) := by positivity
  refine ⟨fun s => ⟨hc0, ?_⟩, fun s i hi => ?_⟩
  · show 1 / ((l : ℝ) + 1) ≤ 1
    nlinarith
  · show 1 ≤ (l : ℝ) ^ i * (1 / ((l : ℝ) + 1)) + 1 / ((l : ℝ) + 1)
    have hli := self_le_pow_of_one_le_of_one_le_exp hl1 (oddLevels_one_le hi)
    have hm := mul_le_mul_of_nonneg_right hli hc0
    nlinarith

/- English proof (translation)
Establish `h` using `hx.2 s`. Establish `h0 : 0 ≤ ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i` using `Finset.sum_nonneg fun i _ => hx.1 _ _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma flow_out_le {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) (s : ZMod d) :
    ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i ≤ D s := by
  have h := hx.2 s
  have h0 : 0 ≤ ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i :=
    Finset.sum_nonneg fun i _ => hx.1 _ _
  linarith

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
private lemma sum_incoming (x : ZMod d → ℕ → ℝ) :
    ∑ s : ZMod d, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i =
      ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := by
  calc ∑ s : ZMod d, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i
      = ∑ i ∈ oddLevels d, ∑ s : ZMod d, x (s - (i : ZMod d)) i := Finset.sum_comm
    _ = ∑ i ∈ oddLevels d, ∑ s : ZMod d, x s i :=
        Finset.sum_congr rfl fun i _ =>
          Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ (fun s => rfl)
    _ = ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := Finset.sum_comm

/- English proof (translation)
Establish `hl1 : (1 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `h1 : ∑ s : ZMod d, ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) + (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i)) ≤ ∑ s, D s` using `Finset.sum_le_sum fun s _ => hx.2 s`. Rewrite `h1` using `[Finset.sum_add_distrib, sum_incoming x]`. Establish `h2 : (l : ℝ) * flowVal d x ≤ ∑ s : ZMod d, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i`. Unfold `flowVal`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (self_le_pow_of_one_le_of_one_le_exp hl1 (oddLevels_one_le hi)) (hx.1 s i)`. Establish `h3 : flowVal d x = ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i` using `rfl`.

Rewrite using `[add_mul, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma flowVal_mul_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    ((l : ℝ) + 1) * flowVal d x ≤ ∑ s, D s := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : ∑ s : ZMod d, ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
      (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i)) ≤ ∑ s, D s :=
    Finset.sum_le_sum fun s _ => hx.2 s
  rw [Finset.sum_add_distrib, sum_incoming x] at h1
  have h2 : (l : ℝ) * flowVal d x ≤ ∑ s : ZMod d, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i := by
    unfold flowVal
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (self_le_pow_of_one_le_of_one_le_exp hl1 (oddLevels_one_le hi)) (hx.1 s i)
  have h3 : flowVal d x = ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := rfl
  rw [add_mul, one_mul]
  linarith

/- English proof (translation)
Establish `h2` using `mul_le_mul_of_nonneg_right h (inv_nonneg.2 hc.le)`. Rewrite `h2` using `[mul_inv_cancel_right₀ hc.ne', ← div_eq_mul_inv]`. Then use the resulting hypothesis.
-/
private theorem le_div_of_mul_le_of_pos_flow_degree_bounds {a b c : ℝ} (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by
  have h2 := mul_le_mul_of_nonneg_right h (inv_nonneg.2 hc.le)
  rwa [mul_inv_cancel_right₀ hc.ne', ← div_eq_mul_inv] at h2

/- English proof (translation)
Establish `hpos : (0 : ℝ) < (l : ℝ) + 1` using `by positivity`. Unfold `maxFlow`. Apply `Real.sSup_le` to reduce the goal to its premises. Introduce and unpack `t ⟨x, hx, rfl⟩`. Conclude with `le_div_of_mul_le_of_pos_flow_degree_bounds hpos (by rw [mul_comm]; exact flowVal_mul_le hl hx)`.

Conclude with `div_nonneg (Finset.sum_nonneg fun s _ => hD s) hpos.le`.
-/
private lemma maxFlow_le (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : 0 ≤ D) :
    maxFlow l d D ≤ (∑ s, D s) / ((l : ℝ) + 1) := by
  have hpos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  unfold maxFlow
  apply Real.sSup_le
  · rintro t ⟨x, hx, rfl⟩
    exact le_div_of_mul_le_of_pos_flow_degree_bounds hpos (by rw [mul_comm]; exact flowVal_mul_le hl hx)
  · exact div_nonneg (Finset.sum_nonneg fun s _ => hD s) hpos.le

/- English proof (translation)
Establish `hpos : (0 : ℝ) < (l : ℝ) + 1` using `by positivity`. Unfold `maxFlow`. Use `le_csSup ⟨(∑ s, D s) / ((l : ℝ) + 1), ?_⟩ ⟨x, hx, rfl⟩` and prove the remaining obligations. Introduce and unpack `t ⟨y, hy, rfl⟩`. Conclude with `le_div_of_mul_le_of_pos_flow_degree_bounds hpos (by rw [mul_comm]; exact flowVal_mul_le hl hy)`.
-/
private lemma le_maxFlow (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ maxFlow l d D := by
  have hpos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  unfold maxFlow
  refine le_csSup ⟨(∑ s, D s) / ((l : ℝ) + 1), ?_⟩ ⟨x, hx, rfl⟩
  rintro t ⟨y, hy, rfl⟩
  exact le_div_of_mul_le_of_pos_flow_degree_bounds hpos (by rw [mul_comm]; exact flowVal_mul_le hl hy)

private def altNum (l d : ℕ) (D : ZMod d → ℝ) (s : ZMod d) : ℝ :=
  ∑ r ∈ Finset.range d, (-1 : ℝ) ^ r * ((l : ℝ) ^ (r + 1))⁻¹ * D (s - (r : ZMod d))

/- English proof (translation)
Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast (show 0 < l by omega)`. Establish `hinv : (l : ℝ) * (l : ℝ)⁻¹ = 1` using `mul_inv_cancel₀ hl0.ne'`. Take `⟨f, hf⟩ : ∃ f : ℕ → ℝ, ∀ r, f r = (-1 : ℝ) ^ r * ((l : ℝ) ^ r)⁻¹ * D (s - (r : ZMod d))` from `⟨_, fun _ => rfl⟩`. Establish `h1 : (l : ℝ) * altNum l d D s = ∑ r ∈ Finset.range d, f r`. Unfold `altNum`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[hf, pow_succ, mul_inv]`. Take the linear combination `((-1 : ℝ) ^ r * ((l : ℝ) ^ r)⁻¹ * D (s - (r : ZMod d))) * hinv`. Establish `h2 : altNum l d D (s - 1) = ∑ r ∈ Finset.range d, -f (r + 1)`.

Unfold `altNum`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[hf]`. Establish `e : s - 1 - (r : ZMod d) = s - ((r + 1 : ℕ) : ZMod d)` using `by push_cast; ring`. Rewrite using `[e]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e0 : ((0 : ℕ) : ZMod d) = 0` using `Nat.cast_zero`. Establish `ed : ((d : ℕ) : ZMod d) = 0` using `ZMod.natCast_self d`. Establish `eneg : ((-1 : ℝ)) ^ d = 1` using `hev.neg_one_pow`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h1, h2, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun r _ => (sub_eq_add_neg _ _).symm`. Use `_ = f 0 - f d := Finset.sum_range_sub' f d`. Use `_ = (1 - ((l : ℝ) ^ d)⁻¹) * D s := by`. Rewrite using `[hf, hf, e0, ed, sub_zero, eneg]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma altNum_rec (hl : 1 ≤ l) (hev : Even d) (D : ZMod d → ℝ) (s : ZMod d) :
    (l : ℝ) * altNum l d D s + altNum l d D (s - 1) = (1 - ((l : ℝ) ^ d)⁻¹) * D s := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hinv : (l : ℝ) * (l : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hl0.ne'
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, ∀ r, f r = (-1 : ℝ) ^ r * ((l : ℝ) ^ r)⁻¹ * D (s - (r : ZMod d)) :=
    ⟨_, fun _ => rfl⟩
  have h1 : (l : ℝ) * altNum l d D s = ∑ r ∈ Finset.range d, f r := by
    unfold altNum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hf, pow_succ, mul_inv]
    linear_combination ((-1 : ℝ) ^ r * ((l : ℝ) ^ r)⁻¹ * D (s - (r : ZMod d))) * hinv
  have h2 : altNum l d D (s - 1) = ∑ r ∈ Finset.range d, -f (r + 1) := by
    unfold altNum
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hf]
    have e : s - 1 - (r : ZMod d) = s - ((r + 1 : ℕ) : ZMod d) := by push_cast; ring
    rw [e]
    ring
  have e0 : ((0 : ℕ) : ZMod d) = 0 := Nat.cast_zero
  have ed : ((d : ℕ) : ZMod d) = 0 := ZMod.natCast_self d
  have eneg : ((-1 : ℝ)) ^ d = 1 := hev.neg_one_pow
  calc (l : ℝ) * altNum l d D s + altNum l d D (s - 1)
      = ∑ r ∈ Finset.range d, (f r - f (r + 1)) := by
        rw [h1, h2, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun r _ => (sub_eq_add_neg _ _).symm
    _ = f 0 - f d := Finset.sum_range_sub' f d
    _ = (1 - ((l : ℝ) ^ d)⁻¹) * D s := by
        rw [hf, hf, e0, ed, sub_zero, eneg]
        ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[show 2 * (m + 1) = 2 * m + 1 + 1 by ring]`. Simplify using `only [Finset.sum_range_succ, ih]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma sum_range_two_mul (f : ℕ → ℝ) (m : ℕ) :
    ∑ r ∈ Finset.range (2 * m), f r = ∑ u ∈ Finset.range m, (f (2 * u) + f (2 * u + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    simp only [Finset.sum_range_succ, ih]
    ring

/- English proof (translation)
Establish `h` using `(hA l d hl hd hev D hD).2`. Conclude with `h.2 ⟨sig, hsig, rfl⟩`.
-/
private theorem sum_deficit_le_Fnum_of_isDual (hA : LemmaFa) (hl : 3 ≤ l) (hd : 2 ≤ d) (hev : Even d)
    {D sig : ZMod d → ℝ} (hD : 0 ≤ D) (hsig : IsDual l d sig) :
    ∑ s, D s * (gam l - sig s) ≤ Fnum l d D := by
  have h := (hA l d hl hd hev D hD).2
  exact h.2 ⟨sig, hsig, rfl⟩

/- English proof (translation)
The claim follows from `(hA l d hl hd hev D hD).2.1`.
-/
private theorem exists_isDual_Fnum_eq_sum_deficit (hA : LemmaFa) (hl : 3 ≤ l) (hd : 2 ≤ d) (hev : Even d)
    {D : ZMod d → ℝ} (hD : 0 ≤ D) :
    ∃ sig, IsDual l d sig ∧ Fnum l d D = ∑ s, D s * (gam l - sig s) :=
  (hA l d hl hd hev D hD).2.1

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, mul_assoc]`.
-/
private theorem sum_smul_apply_mul (c : ℝ) (D f : ZMod d → ℝ) :
    ∑ s, (c • D) s * f s = c * ∑ s, D s * f s := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

/- English proof (translation)
Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.add_apply, add_mul]`.
-/
private theorem sum_add_apply_mul (D E f : ZMod d → ℝ) :
    ∑ s, (D + E) s * f s = ∑ s, D s * f s + ∑ s, E s * f s := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Pi.add_apply, add_mul]

/- English proof (translation)
Take `⟨m, hm⟩` from `hev`. Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast (show 0 < l by omega)`. Establish `hli : (0 : ℝ) < (l : ℝ)⁻¹` using `inv_pos.2 hl0`. Establish `hinv : (l : ℝ) * (l : ℝ)⁻¹ = 1` using `mul_inv_cancel₀ hl0.ne'`. Establish `hrange : Finset.range d = Finset.range (2 * m)` using `congrArg Finset.range (by omega)`.

Unfold `altNum`. Rewrite using `[hrange, sum_range_two_mul]`. Use `Finset.sum_nonneg fun u _ => ?_` and prove the remaining obligations. Establish `e1 : ((-1 : ℝ)) ^ (2 * u) = 1` using `Even.neg_one_pow ⟨u, two_mul u⟩`. Establish `e2 : ((-1 : ℝ)) ^ (2 * u + 1) = -1` using `Odd.neg_one_pow ⟨u, rfl⟩`.

Establish `e3 : ((l : ℝ) ^ (2 * u + 1 + 1))⁻¹ = ((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹`. Rewrite using `[pow_succ (l : ℝ) (2 * u + 1), mul_inv]`. Establish `hp : (0 : ℝ) < ((l : ℝ) ^ (2 * u + 1))⁻¹` using `inv_pos.2 (pow_pos hl0 _)`. Establish `hab` using `hr (s - ((2 * u : ℕ) : ZMod d)) (s - ((2 * u + 1 : ℕ) : ZMod d))`. Establish `hint_r` using `mul_nonneg (mul_nonneg hp.le hli.le) (sub_nonneg.2 hab)`.

Establish `key : (1 : ℝ) * ((l : ℝ) ^ (2 * u + 1))⁻¹ * D (s - ((2 * u : ℕ) : ZMod d)) + -1 * (((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹) * D (s - ((2 * u + 1 : ℕ) : ZMod d)) = ((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹ * ((l : ℝ) * D (s - ((2 * u : ℕ) : ZMod d)) - D (s - ((2 * u + 1 : ℕ) : ZMod d)))`. Take the linear combination `(-(((l : ℝ) ^ (2 * u + 1))⁻¹ * D (s - ((2 * u : ℕ) : ZMod d)))) * hinv`. Simplify using `only [e1, e2, e3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma altNum_nonneg (hl : 1 ≤ l) (hev : Even d) {D : ZMod d → ℝ}
    (hr : ∀ s s' : ZMod d, D s' ≤ (l : ℝ) * D s) (s : ZMod d) : 0 ≤ altNum l d D s := by
  obtain ⟨m, hm⟩ := hev
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hli : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 hl0
  have hinv : (l : ℝ) * (l : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hl0.ne'
  have hrange : Finset.range d = Finset.range (2 * m) := congrArg Finset.range (by omega)
  unfold altNum
  rw [hrange, sum_range_two_mul]
  refine Finset.sum_nonneg fun u _ => ?_
  have e1 : ((-1 : ℝ)) ^ (2 * u) = 1 := Even.neg_one_pow ⟨u, two_mul u⟩
  have e2 : ((-1 : ℝ)) ^ (2 * u + 1) = -1 := Odd.neg_one_pow ⟨u, rfl⟩
  have e3 : ((l : ℝ) ^ (2 * u + 1 + 1))⁻¹ = ((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹ := by
    rw [pow_succ (l : ℝ) (2 * u + 1), mul_inv]
  have hp : (0 : ℝ) < ((l : ℝ) ^ (2 * u + 1))⁻¹ := inv_pos.2 (pow_pos hl0 _)
  have hab := hr (s - ((2 * u : ℕ) : ZMod d)) (s - ((2 * u + 1 : ℕ) : ZMod d))
  have hint_r := mul_nonneg (mul_nonneg hp.le hli.le) (sub_nonneg.2 hab)
  have key : (1 : ℝ) * ((l : ℝ) ^ (2 * u + 1))⁻¹ * D (s - ((2 * u : ℕ) : ZMod d)) +
      -1 * (((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹) * D (s - ((2 * u + 1 : ℕ) : ZMod d)) =
      ((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹ *
        ((l : ℝ) * D (s - ((2 * u : ℕ) : ZMod d)) - D (s - ((2 * u + 1 : ℕ) : ZMod d))) := by
    linear_combination (-(((l : ℝ) ^ (2 * u + 1))⁻¹ * D (s - ((2 * u : ℕ) : ZMod d)))) * hinv
  simp only [e1, e2, e3]
  linarith

end Helpers

/- English proof (translation)
Introduce `l d _ hl hd hev`. Use `⟨fun c D hc hD => ?_, ⟨convex_Ici 0, fun D hD E hE a b ha hb hab => ?_⟩, fun D hD => ?_⟩` and prove the remaining obligations. Establish `hcD : 0 ≤ c • D` using `fun s => by`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_nonneg hc (hD s)`.

Take `⟨s1, hs1, e1⟩` from `exists_isDual_Fnum_eq_sum_deficit hA hl hd hev hcD`. Take `⟨s0, hs0, e0⟩` from `exists_isDual_Fnum_eq_sum_deficit hA hl hd hev hD`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[e1, sum_smul_apply_mul]`. Conclude with `mul_le_mul_of_nonneg_left (sum_deficit_le_Fnum_of_isDual hA hl hd hev hD hs1) hc`.

Establish `h` using `sum_deficit_le_Fnum_of_isDual hA hl hd hev hcD hs0`. Rewrite `h` using `[sum_smul_apply_mul, ← e0]`. Conclude with `h`. Establish `hD' : 0 ≤ D` using `hD`. Establish `hE' : 0 ≤ E` using `hE`.

Establish `hF0 : 0 ≤ a • D + b • E` using `fun s => by`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `add_nonneg (mul_nonneg ha (hD' s)) (mul_nonneg hb (hE' s))`. Take `⟨sg, hsg, e⟩` from `exists_isDual_Fnum_eq_sum_deficit hA hl hd hev hF0`. Rewrite using `[e, sum_add_apply_mul, sum_smul_apply_mul, sum_smul_apply_mul, smul_eq_mul, smul_eq_mul]`.

Conclude with `add_le_add (mul_le_mul_of_nonneg_left (sum_deficit_le_Fnum_of_isDual hA hl hd hev hD' hsg) ha) (mul_le_mul_of_nonneg_left (sum_deficit_le_Fnum_of_isDual hA hl hd hev hE' hsg) hb)`. Establish `h` using `sum_deficit_le_Fnum_of_isDual hA hl hd hev hD (isDual_const (d := d) (by omega : 1 ≤ l))`. Rewrite `h` using `[gam_sub_inv (by omega : 2 ≤ l), ← Finset.sum_mul]`. Rewrite using `[mul_comm]`. Conclude with `h`.
-/
theorem lemmaFb_of (hF : FlowAttained) (hA : LemmaFa) : LemmaFb := by
  intro l d _ hl hd hev
  refine ⟨fun c D hc hD => ?_, ⟨convex_Ici 0, fun D hD E hE a b ha hb hab => ?_⟩, fun D hD => ?_⟩
  · have hcD : 0 ≤ c • D := fun s => by
      rw [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg hc (hD s)
    obtain ⟨s1, hs1, e1⟩ := exists_isDual_Fnum_eq_sum_deficit hA hl hd hev hcD
    obtain ⟨s0, hs0, e0⟩ := exists_isDual_Fnum_eq_sum_deficit hA hl hd hev hD
    apply le_antisymm
    · rw [e1, sum_smul_apply_mul]
      exact mul_le_mul_of_nonneg_left (sum_deficit_le_Fnum_of_isDual hA hl hd hev hD hs1) hc
    · have h := sum_deficit_le_Fnum_of_isDual hA hl hd hev hcD hs0
      rw [sum_smul_apply_mul, ← e0] at h
      exact h
  · have hD' : 0 ≤ D := hD
    have hE' : 0 ≤ E := hE
    have hF0 : 0 ≤ a • D + b • E := fun s => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hD' s)) (mul_nonneg hb (hE' s))
    obtain ⟨sg, hsg, e⟩ := exists_isDual_Fnum_eq_sum_deficit hA hl hd hev hF0
    rw [e, sum_add_apply_mul, sum_smul_apply_mul, sum_smul_apply_mul, smul_eq_mul, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (sum_deficit_le_Fnum_of_isDual hA hl hd hev hD' hsg) ha)
      (mul_le_mul_of_nonneg_left (sum_deficit_le_Fnum_of_isDual hA hl hd hev hE' hsg) hb)
  · have h := sum_deficit_le_Fnum_of_isDual hA hl hd hev hD (isDual_const (d := d) (by omega : 1 ≤ l))
    rw [gam_sub_inv (by omega : 2 ≤ l), ← Finset.sum_mul] at h
    rw [mul_comm]
    exact h

/- English proof (translation)
Introduce `l d _ hl hd hev D E sig hD hE hopt`. Establish `hDE : 0 ≤ D + E` using `add_nonneg hD hE`. Take `⟨hsig, hdef⟩` from `hopt`. Prove the components needed by the constructor for the conclusion. Establish `h1` using `sum_deficit_le_Fnum_of_isDual hA hl hd hev hDE hsig`.

Rewrite `h1` using `[sum_add_apply_mul, ← hdef]`. Establish `h2 : -(∑ s, E s * max (sig s - gam l) 0) ≤ ∑ s, E s * (gam l - sig s)`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_le_sum fun s _ => ?_` and prove the remaining obligations. Establish `hEs : 0 ≤ E s` using `hE s`.

Establish `hm` using `le_max_left (sig s - gam l) 0`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨sg, hsg, e⟩` from `exists_isDual_Fnum_eq_sum_deficit hA hl hd hev hDE`. Establish `h3` using `sum_deficit_le_Fnum_of_isDual hA hl hd hev hD hsg`.

Establish `h4 : ∑ s, E s * (gam l - sg s) ≤ gam l * ∑ s, E s`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun s _ => ?_` and prove the remaining obligations. Establish `hEs : 0 ≤ E s` using `hE s`. Establish `hs0 : 0 ≤ sg s` using `(hsg.1 s).1`.

Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[e, sum_add_apply_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lemmaFc_of (hF : FlowAttained) (hA : LemmaFa) : LemmaFc := by
  intro l d _ hl hd hev D E sig hD hE hopt
  have hDE : 0 ≤ D + E := add_nonneg hD hE
  obtain ⟨hsig, hdef⟩ := hopt
  constructor
  · have h1 := sum_deficit_le_Fnum_of_isDual hA hl hd hev hDE hsig
    rw [sum_add_apply_mul, ← hdef] at h1
    have h2 : -(∑ s, E s * max (sig s - gam l) 0) ≤ ∑ s, E s * (gam l - sig s) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun s _ => ?_
      have hEs : 0 ≤ E s := hE s
      have hm := le_max_left (sig s - gam l) 0
      nlinarith
    linarith
  · obtain ⟨sg, hsg, e⟩ := exists_isDual_Fnum_eq_sum_deficit hA hl hd hev hDE
    have h3 := sum_deficit_le_Fnum_of_isDual hA hl hd hev hD hsg
    have h4 : ∑ s, E s * (gam l - sg s) ≤ gam l * ∑ s, E s := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      have hEs : 0 ≤ E s := hE s
      have hs0 : 0 ≤ sg s := (hsg.1 s).1
      nlinarith
    rw [e, sum_add_apply_mul]
    linarith

/- English proof (translation)
Introduce `l d _ hl hd hev D hD hr`. Establish `hl1 : 1 ≤ l` using `by omega`. Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast (show 0 < l by omega)`. Establish `hpos : (0 : ℝ) < (l : ℝ) + 1` using `by linarith`. Take `⟨q, hq_eq⟩ : ∃ q : ℝ, q = 1 - ((l : ℝ) ^ d)⁻¹` from `⟨_, rfl⟩`.

Establish `hq : 0 < q`. Establish `hL : (3 : ℝ) ≤ (l : ℝ) ^ d` using `le_trans (by exact_mod_cast hl) (self_le_pow_of_one_le_of_one_le_exp (by exact_mod_cast hl1) (by omega))`. Establish `hLpos : (0 : ℝ) < (l : ℝ) ^ d` using `by linarith`. Establish `hu` using `inv_mul_cancel₀ hLpos.ne'`. Establish `hupos` using `inv_pos.2 hLpos`.

Rewrite using `[hq_eq]`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨y, hy⟩ : ∃ y : ZMod d → ℝ, ∀ s, y s = altNum l d D s / q` from `⟨_, fun _ => rfl⟩`. Establish `hy0 : ∀ s, 0 ≤ y s` using `fun s => by`. Rewrite using `[hy]`.

Conclude with `div_nonneg (altNum_nonneg hl1 hev hr s) hq.le`. Establish `hrec : ∀ s, (l : ℝ) * y s + y (s - 1) = D s`. Introduce `s`. Establish `h` using `altNum_rec hl1 hev D s`. Rewrite `h` using `[← hq_eq]`.

Establish `e : (l : ℝ) * (altNum l d D s / q) + altNum l d D (s - 1) / q = ((l : ℝ) * altNum l d D s + altNum l d D (s - 1)) / q` using `by ring`. Rewrite using `[hy, hy, e, h, mul_div_cancel_left₀ _ hq.ne']`. Establish `h1mem` using `one_mem_oddLevels hd`. Take `⟨x, hx⟩ : ∃ x : ZMod d → ℕ → ℝ, ∀ s i, x s i = if i = 1 then y s else 0` from `⟨fun s i => if i = 1 then y s else 0, fun _ _ => rfl⟩`. Establish `hout : ∀ s, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i = (l : ℝ) * y s`.

Introduce `s`. Rewrite using `[Finset.sum_eq_single_of_mem 1 h1mem (fun i _ hi => by rw [hx, if_neg hi, mul_zero]), hx, if_pos rfl, pow_one]`. Establish `hin : ∀ s, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i = y (s - 1)`. Introduce `s`. Rewrite using `[Finset.sum_eq_single_of_mem 1 h1mem (fun i _ hi => by rw [hx, if_neg hi]), hx, if_pos rfl, Nat.cast_one]`.

Establish `hsel : ∀ s, ∑ i ∈ oddLevels d, x s i = y s`. Introduce `s`. Rewrite using `[Finset.sum_eq_single_of_mem 1 h1mem (fun i _ hi => by rw [hx, if_neg hi]), hx, if_pos rfl]`. Establish `hflow : IsFlow l d D x`. Use `⟨fun s i => ?_, fun s => le_of_eq ?_⟩` and prove the remaining obligations.

Rewrite using `[hx] split_ifs exacts [hy0 s, le_refl 0]`. Rewrite using `[hout, hin, hrec]`. Establish `hval : flowVal d x = ∑ s, y s`. Unfold `flowVal`. Conclude with `Finset.sum_congr rfl fun s _ => hsel s`.

Establish `hshift : ∑ s, y (s - 1) = ∑ s, y s` using `Fintype.sum_equiv (Equiv.subRight (1 : ZMod d)) _ _ (fun s => rfl)`. Establish `htot : ((l : ℝ) + 1) * ∑ s, y s = ∑ s, D s`. Establish `h : ∑ s, ((l : ℝ) * y s + y (s - 1)) = ∑ s, D s` using `Finset.sum_congr rfl fun s _ => hrec s`. Rewrite `h` using `[Finset.sum_add_distrib, ← Finset.mul_sum, hshift]`. Rewrite using `[add_mul, one_mul]`.

Conclude with `h`. Establish `hsum : ∑ s, y s = (∑ s, D s) / ((l : ℝ) + 1)`. Rewrite using `[eq_div_iff hpos.ne', mul_comm]`. Conclude with `htot`. Establish `hmax : maxFlow l d D = (∑ s, D s) / ((l : ℝ) + 1)` using `le_antisymm (maxFlow_le hl1 hD) (by rw [← hsum, ← hval]; exact le_maxFlow hl1 hflow)`.

Unfold `Fnum`. Rewrite using `[hmax, ← gam_sub_inv (l := l) (by omega)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deficitOfBoundedRatio : LemmaFe := by
  intro l d _ hl hd hev D hD hr
  have hl1 : 1 ≤ l := by omega
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hpos : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  obtain ⟨q, hq_eq⟩ : ∃ q : ℝ, q = 1 - ((l : ℝ) ^ d)⁻¹ := ⟨_, rfl⟩
  have hq : 0 < q := by
    have hL : (3 : ℝ) ≤ (l : ℝ) ^ d :=
      le_trans (by exact_mod_cast hl) (self_le_pow_of_one_le_of_one_le_exp (by exact_mod_cast hl1) (by omega))
    have hLpos : (0 : ℝ) < (l : ℝ) ^ d := by linarith
    have hu := inv_mul_cancel₀ hLpos.ne'
    have hupos := inv_pos.2 hLpos
    rw [hq_eq]
    nlinarith
  obtain ⟨y, hy⟩ : ∃ y : ZMod d → ℝ, ∀ s, y s = altNum l d D s / q := ⟨_, fun _ => rfl⟩
  have hy0 : ∀ s, 0 ≤ y s := fun s => by
    rw [hy]
    exact div_nonneg (altNum_nonneg hl1 hev hr s) hq.le
  have hrec : ∀ s, (l : ℝ) * y s + y (s - 1) = D s := by
    intro s
    have h := altNum_rec hl1 hev D s
    rw [← hq_eq] at h
    have e : (l : ℝ) * (altNum l d D s / q) + altNum l d D (s - 1) / q =
        ((l : ℝ) * altNum l d D s + altNum l d D (s - 1)) / q := by ring
    rw [hy, hy, e, h, mul_div_cancel_left₀ _ hq.ne']
  have h1mem := one_mem_oddLevels hd
  obtain ⟨x, hx⟩ : ∃ x : ZMod d → ℕ → ℝ, ∀ s i, x s i = if i = 1 then y s else 0 :=
    ⟨fun s i => if i = 1 then y s else 0, fun _ _ => rfl⟩
  have hout : ∀ s, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i = (l : ℝ) * y s := by
    intro s
    rw [Finset.sum_eq_single_of_mem 1 h1mem (fun i _ hi => by rw [hx, if_neg hi, mul_zero]),
      hx, if_pos rfl, pow_one]
  have hin : ∀ s, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i = y (s - 1) := by
    intro s
    rw [Finset.sum_eq_single_of_mem 1 h1mem (fun i _ hi => by rw [hx, if_neg hi]),
      hx, if_pos rfl, Nat.cast_one]
  have hsel : ∀ s, ∑ i ∈ oddLevels d, x s i = y s := by
    intro s
    rw [Finset.sum_eq_single_of_mem 1 h1mem (fun i _ hi => by rw [hx, if_neg hi]), hx, if_pos rfl]
  have hflow : IsFlow l d D x := by
    refine ⟨fun s i => ?_, fun s => le_of_eq ?_⟩
    · rw [hx]
      split_ifs
      exacts [hy0 s, le_refl 0]
    · rw [hout, hin, hrec]
  have hval : flowVal d x = ∑ s, y s := by
    unfold flowVal
    exact Finset.sum_congr rfl fun s _ => hsel s
  have hshift : ∑ s, y (s - 1) = ∑ s, y s :=
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod d)) _ _ (fun s => rfl)
  have htot : ((l : ℝ) + 1) * ∑ s, y s = ∑ s, D s := by
    have h : ∑ s, ((l : ℝ) * y s + y (s - 1)) = ∑ s, D s := Finset.sum_congr rfl fun s _ => hrec s
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hshift] at h
    rw [add_mul, one_mul]
    exact h
  have hsum : ∑ s, y s = (∑ s, D s) / ((l : ℝ) + 1) := by
    rw [eq_div_iff hpos.ne', mul_comm]
    exact htot
  have hmax : maxFlow l d D = (∑ s, D s) / ((l : ℝ) + 1) :=
    le_antisymm (maxFlow_le hl1 hD) (by rw [← hsum, ← hval]; exact le_maxFlow hl1 hflow)
  unfold Fnum
  rw [hmax, ← gam_sub_inv (l := l) (by omega)]
  ring

/- English proof (translation)
Introduce `l d _ hl D x hx i0`. Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast (show 0 < l by omega)`. Establish `hl1 : (1 : ℝ) ≤ l` using `by exact_mod_cast (show 1 ≤ l by omega)`. Establish `hpos : (0 : ℝ) < (l : ℝ) ^ i0` using `pow_pos hl0 i0`. Apply `le_div_of_mul_le_of_pos_flow_degree_bounds hpos` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.

Use `_ ≤ ∑ a : ZMod d, ∑ i ∈ (oddLevels d).filter (fun i => i0 ≤ i), (l : ℝ) ^ i * x a i := Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (pow_le_pow_right_of_one_le_real hl1 (Finset.mem_filter.1 hi).2) (hx.1 a i)`. Use `_ ≤ ∑ a : ZMod d, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i := Finset.sum_le_sum fun a _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => mul_nonneg (pow_nonneg hl0.le i) (hx.1 a i))`. Use `_ ≤ ∑ a : ZMod d, D a := Finset.sum_le_sum fun a _ => flow_out_le hx a`.
-/
theorem highLevelTail : LevelTail := by
  intro l d _ hl D x hx i0
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
  have hpos : (0 : ℝ) < (l : ℝ) ^ i0 := pow_pos hl0 i0
  apply le_div_of_mul_le_of_pos_flow_degree_bounds hpos
  calc (∑ a : ZMod d, ∑ i ∈ (oddLevels d).filter (fun i => i0 ≤ i), x a i) * (l : ℝ) ^ i0
      = ∑ a : ZMod d, ∑ i ∈ (oddLevels d).filter (fun i => i0 ≤ i), (l : ℝ) ^ i0 * x a i := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ ≤ ∑ a : ZMod d, ∑ i ∈ (oddLevels d).filter (fun i => i0 ≤ i), (l : ℝ) ^ i * x a i :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (pow_le_pow_right_of_one_le_real hl1 (Finset.mem_filter.1 hi).2) (hx.1 a i)
    _ ≤ ∑ a : ZMod d, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => mul_nonneg (pow_nonneg hl0.le i) (hx.1 a i))
    _ ≤ ∑ a : ZMod d, D a := Finset.sum_le_sum fun a _ => flow_out_le hx a

end Formalism.IncomingBounds
