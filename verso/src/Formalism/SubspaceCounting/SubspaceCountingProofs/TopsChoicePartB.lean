import Formalism.SubspaceCounting.TopsChoiceSecondBound

noncomputable section
open scoped BigOperators

namespace Formalism.G0.TopsWeightFunctionBounds

inductive St where
  | bad
  | good
  | run (K j d : ℕ) (al ev : Bool)
  deriving DecidableEq

def okG (L₂ j d : ℕ) (ev : Bool) : Bool :=
  if j = 0 then !ev else (decide ((d + 1) % 2 = 0) && decide (L₂ < 2 * (d + 1)))

def step (R L₂ : ℕ) : St → Bool → St
  | .bad, _ => .bad
  | .good, _ => .good
  | .run K j d al ev, false => .run K j (d + 1) al (!ev)
  | .run K j d al ev, true =>
      if j + 1 = R then
        (if (al && okG L₂ j d ev) = true then .good
         else if K ≤ 1 then .bad else .run (K - 1) 0 0 true (!ev))
      else .run K (j + 1) 0 (al && okG L₂ j d ev) (!ev)

def runS (R L₂ : ℕ) (s : St) (bs : List Bool) : St := bs.foldl (step R L₂) s

def Wt (R L₂ : ℕ) (δ : ℝ) : ℕ → St → ℝ
  | 0, s => if s = .bad then 1 else 0
  | m + 1, s => δ * Wt R L₂ δ m (step R L₂ s true) + (1 - δ) * Wt R L₂ δ m (step R L₂ s false)

def WF (R : ℕ) : St → Prop
  | .run _ j _ _ _ => j < R
  | _ => True

def aF (L₂ : ℕ) (δ : ℝ) : ℝ := 1 / 2 * (1 - L₂ * δ)

def eF (δ : ℝ) (d : ℕ) : ℝ := if d % 2 = 0 then (1 - δ) / (2 - δ) else 1 / (2 - δ)

def gF (L₂ : ℕ) (δ : ℝ) (j d : ℕ) (ev : Bool) : ℝ :=
  if j = 0 then (if ev = true then (1 - δ) / (2 - δ) else 1 / (2 - δ))
  else (1 - δ) ^ (L₂ / 2 - d) * eF δ (max d (L₂ / 2))

def GF (R L₂ : ℕ) (δ : ℝ) (j d : ℕ) (al ev : Bool) : ℝ :=
  if al = true then aF L₂ δ ^ (R - 1 - j) * gF L₂ δ j d ev else 0

def Phi (R L₂ : ℕ) (δ : ℝ) : St → ℝ
  | .bad => 1
  | .good => 0
  | .run K j d al ev => (1 - aF L₂ δ ^ R) ^ (K - 1) * (1 - GF R L₂ δ j d al ev)

section arith
variable {L₂ : ℕ} {δ : ℝ}

/- English proof (translation)
Establish `: (1 : ℝ) ≤ L₂` using `by exact_mod_cast hL`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma d_le_one (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) : δ ≤ 1 := by
  have : (1 : ℝ) ≤ L₂ := by exact_mod_cast hL
  nlinarith

/- English proof (translation)
Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma two_sub_pos (h1 : δ ≤ 1) : 0 < 2 - δ := by linarith

/- English proof (translation)
Unfold `aF`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma aF_nonneg (hLδ : (L₂ : ℝ) * δ ≤ 1) : 0 ≤ aF L₂ δ := by
  unfold aF; nlinarith

/- English proof (translation)
Unfold `aF`. Establish `: (0 : ℝ) ≤ L₂ * δ` using `mul_nonneg (Nat.cast_nonneg _) h0`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma aF_le (h0 : 0 ≤ δ) : aF L₂ δ ≤ 1 / 2 := by
  unfold aF
  have : (0 : ℝ) ≤ L₂ * δ := mul_nonneg (Nat.cast_nonneg _) h0
  nlinarith

/- English proof (translation)
Establish `h2` using `two_sub_pos h1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma key_id (h1 : δ ≤ 1) : δ * 1 + (1 - δ) * ((1 - δ) / (2 - δ)) = 1 / (2 - δ) := by
  have h2 := two_sub_pos h1
  field_simp
  ring

/- English proof (translation)
Establish `h2` using `two_sub_pos h1`. Conclude with `div_le_div_of_nonneg_right (by linarith) h2.le`.
-/
lemma lo_le_hi (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : (1 - δ) / (2 - δ) ≤ 1 / (2 - δ) := by
  have h2 := two_sub_pos h1
  exact div_le_div_of_nonneg_right (by linarith) h2.le

/- English proof (translation)
Establish `h2` using `two_sub_pos h1`. Rewrite using `[div_le_one h2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma hi_le_one (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : 1 / (2 - δ) ≤ 1 := by
  have h2 := two_sub_pos h1
  rw [div_le_one h2]; linarith

/- English proof (translation)
Establish `h2` using `two_sub_pos h1`. Conclude with `div_nonneg (by linarith) h2.le`.
-/
lemma lo_nonneg (h1 : δ ≤ 1) : 0 ≤ (1 - δ) / (2 - δ) := by
  have h2 := two_sub_pos h1
  exact div_nonneg (by linarith) h2.le

/- English proof (translation)
Unfold `eF`. Use `split_ifs`. Conclude with `le_rfl`. Conclude with `lo_le_hi h0 h1`.
-/
lemma eF_lb (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (d : ℕ) : (1 - δ) / (2 - δ) ≤ eF δ d := by
  unfold eF; split_ifs
  · exact le_rfl
  · exact lo_le_hi h0 h1

/- English proof (translation)
Unfold `eF`. Use `split_ifs`. Conclude with `lo_le_hi h0 h1`. Conclude with `le_rfl`.
-/
lemma eF_ub (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (d : ℕ) : eF δ d ≤ 1 / (2 - δ) := by
  unfold eF; split_ifs
  · exact lo_le_hi h0 h1
  · exact le_rfl

/- English proof (translation)
Unfold `gF`. Use `split_ifs`. Conclude with `lo_nonneg h1`. Conclude with `(lo_nonneg h1).trans (lo_le_hi h0 h1)`. Conclude with `mul_nonneg (pow_nonneg (by linarith) _) ((lo_nonneg h1).trans (eF_lb h0 h1 _))`.
-/
lemma gF_nonneg (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j d : ℕ) (ev : Bool) : 0 ≤ gF L₂ δ j d ev := by
  unfold gF
  split_ifs
  · exact lo_nonneg h1
  · exact (lo_nonneg h1).trans (lo_le_hi h0 h1)
  · exact mul_nonneg (pow_nonneg (by linarith) _) ((lo_nonneg h1).trans (eF_lb h0 h1 _))

/- English proof (translation)
Unfold `gF`. Use `split_ifs`. Conclude with `(lo_le_hi h0 h1).trans (hi_le_one h0 h1)`. Conclude with `hi_le_one h0 h1`. Establish `hp : (1 - δ) ^ (L₂ / 2 - d) ≤ 1` using `pow_le_one₀ (by linarith) (by linarith)`.

Establish `he` using `(eF_ub h0 h1 (max d (L₂ / 2))).trans (hi_le_one h0 h1)`. Establish `he0` using `(lo_nonneg h1).trans (eF_lb h0 h1 (max d (L₂ / 2)))`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma gF_le_one (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j d : ℕ) (ev : Bool) : gF L₂ δ j d ev ≤ 1 := by
  unfold gF
  split_ifs
  · exact (lo_le_hi h0 h1).trans (hi_le_one h0 h1)
  · exact hi_le_one h0 h1
  · have hp : (1 - δ) ^ (L₂ / 2 - d) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have he := (eF_ub h0 h1 (max d (L₂ / 2))).trans (hi_le_one h0 h1)
    have he0 := (lo_nonneg h1).trans (eF_lb h0 h1 (max d (L₂ / 2)))
    calc (1 - δ) ^ (L₂ / 2 - d) * eF δ (max d (L₂ / 2)) ≤ 1 * 1 :=
          mul_le_mul hp he he0 zero_le_one
      _ = 1 := by ring

/- English proof (translation)
Establish `h1` using `d_le_one h0 hL hLδ`. Establish `h2` using `two_sub_pos h1`. Establish `hLr : (1 : ℝ) ≤ L₂` using `by exact_mod_cast hL`. Establish `hbase : aF L₂ δ ≤ (1 - δ) / (2 - δ)`. Unfold `aF`.

Rewrite using `[le_div_iff₀ h2]`. Use the polynomial consequences of the given equalities and inequalities. Unfold `gF`. Use `split_ifs with hj`. Conclude with `hbase`.

Conclude with `hbase.trans (lo_le_hi h0 h1)`. Establish `hh : L₂ / 2 + 1 ≤ L₂` using `by omega`. Establish `hbern : 1 - ((L₂ / 2 + 1 : ℕ) : ℝ) * δ ≤ (1 - δ) ^ (L₂ / 2 + 1)`. Use `one_add_mul_le_pow (a := -δ) (by linarith) (L₂ / 2 + 1)` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg, mul_neg]`.

Establish `hcast : ((L₂ / 2 + 1 : ℕ) : ℝ) ≤ L₂` using `by exact_mod_cast hh`. Establish `he` using `eF_lb h0 h1 (max 0 (L₂ / 2))`. Establish `hp0 : 0 ≤ (1 - δ) ^ (L₂ / 2)` using `pow_nonneg (by linarith) _`. Establish `hstep : (1 - δ) ^ (L₂ / 2) * ((1 - δ) / (2 - δ)) ≤ (1 - δ) ^ (L₂ / 2 - 0) * eF δ (max 0 (L₂ / 2))`. Simplify using `only [Nat.sub_zero]`.

Conclude with `mul_le_mul_of_nonneg_left he hp0`. Use `le_trans ?_ hstep` and prove the remaining obligations. Establish `hq : (1 - δ) ^ (L₂ / 2) * ((1 - δ) / (2 - δ)) = (1 - δ) ^ (L₂ / 2 + 1) / (2 - δ)`. Rewrite using `[pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hq, le_div_iff₀ h2]`. Unfold `aF`. Establish `hpow1 : (1 - δ) ^ (L₂ / 2 + 1) ≤ 1` using `pow_le_one₀ (by linarith) (by linarith)`. Establish `hpow0 : 0 ≤ (1 - δ) ^ (L₂ / 2 + 1)` using `pow_nonneg (by linarith) _`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma gF_lb (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (j : ℕ) (ev : Bool) :
    aF L₂ δ ≤ gF L₂ δ j 0 ev := by
  have h1 := d_le_one h0 hL hLδ
  have h2 := two_sub_pos h1
  have hLr : (1 : ℝ) ≤ L₂ := by exact_mod_cast hL

  have hbase : aF L₂ δ ≤ (1 - δ) / (2 - δ) := by
    unfold aF
    rw [le_div_iff₀ h2]
    nlinarith
  unfold gF
  split_ifs with hj
  · exact hbase
  · exact hbase.trans (lo_le_hi h0 h1)
  ·
    have hh : L₂ / 2 + 1 ≤ L₂ := by omega
    have hbern : 1 - ((L₂ / 2 + 1 : ℕ) : ℝ) * δ ≤ (1 - δ) ^ (L₂ / 2 + 1) := by
      have := one_add_mul_le_pow (a := -δ) (by linarith) (L₂ / 2 + 1)
      simpa [sub_eq_add_neg, mul_neg] using this
    have hcast : ((L₂ / 2 + 1 : ℕ) : ℝ) ≤ L₂ := by exact_mod_cast hh
    have he := eF_lb h0 h1 (max 0 (L₂ / 2))
    have hp0 : 0 ≤ (1 - δ) ^ (L₂ / 2) := pow_nonneg (by linarith) _
    have hstep : (1 - δ) ^ (L₂ / 2) * ((1 - δ) / (2 - δ)) ≤
        (1 - δ) ^ (L₂ / 2 - 0) * eF δ (max 0 (L₂ / 2)) := by
      simp only [Nat.sub_zero]
      exact mul_le_mul_of_nonneg_left he hp0
    refine le_trans ?_ hstep
    have hq : (1 - δ) ^ (L₂ / 2) * ((1 - δ) / (2 - δ)) = (1 - δ) ^ (L₂ / 2 + 1) / (2 - δ) := by
      rw [pow_succ]; ring
    rw [hq, le_div_iff₀ h2]
    unfold aF
    have hpow1 : (1 - δ) ^ (L₂ / 2 + 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hpow0 : 0 ≤ (1 - δ) ^ (L₂ / 2 + 1) := pow_nonneg (by linarith) _
    nlinarith

/- English proof (translation)
Establish `h2` using `two_sub_pos h1`. Distinguish the cases in `hj : j = 0`. Substitute `hj` using the available equality. Consider the cases of `ev`. Simplify using `only [okG, gF, if_true, Bool.not_false]`.

Simplify using the standard rewrite rules. Establish `k` using `key_id h1`. Rewrite `k` using `[one_div, mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [okG, gF, if_true, Bool.not_true]`.

Simplify using the standard rewrite rules. Rewrite using `[div_eq_mul_inv]`. Distinguish the cases in `hd : d < L₂ / 2`. Establish `hok : okG L₂ j d ev = false`. Simplify using `only [okG, hj, if_false]`.

Establish `: ¬ L₂ < 2 * (d + 1)` using `by omega`. Simplify using `[this]`. Rewrite using `[hok]`. Simplify using `only [gF, hj, if_false]`. Establish `hm1 : max d (L₂ / 2) = L₂ / 2` using `by omega`.

Establish `hm2 : max (d + 1) (L₂ / 2) = L₂ / 2` using `by omega`. Establish `hs : L₂ / 2 - d = (L₂ / 2 - (d + 1)) + 1` using `by omega`. Rewrite using `[hm1, hm2, hs, pow_succ]`. Simplify using the standard rewrite rules. Put the polynomial expressions in normal form.

Conclude with `le_rfl`. Establish `hm1 : max d (L₂ / 2) = d` using `by omega`. Establish `hm2 : max (d + 1) (L₂ / 2) = d + 1` using `by omega`. Establish `hs1 : L₂ / 2 - d = 0` using `by omega`. Establish `hs2 : L₂ / 2 - (d + 1) = 0` using `by omega`.

Establish `hlt : L₂ < 2 * (d + 1)` using `by omega`. Simplify using `only [gF, hj, if_false, hm1, hm2, hs1, hs2, pow_zero, one_mul]`. Break down `Nat.mod_two_eq_zero_or_one d with hp | hp` into its components or cases. Establish `hq : (d + 1) % 2 ≠ 0` using `by omega`. Establish `hok : okG L₂ j d ev = false` using `by simp [okG, hj, hq]`.

Rewrite using `[hok]`. Simplify using `only [eF, hp, hq, if_true, if_false]`. Simplify using the standard rewrite rules. Rewrite using `[div_eq_mul_inv]`. Establish `hq : (d + 1) % 2 = 0` using `by omega`.

Establish `hp' : d % 2 ≠ 0` using `by omega`. Establish `hok : okG L₂ j d ev = true` using `by simp [okG, hj, hq, hlt]`. Rewrite using `[hok]`. Simplify using `only [eF, hp', hq, if_true, if_false]`. Rewrite using `[key_id h1]`.
-/
lemma gF_step (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j d : ℕ) (ev : Bool) :
    gF L₂ δ j d ev ≤ δ * (if okG L₂ j d ev = true then 1 else 0) + (1 - δ) * gF L₂ δ j (d + 1) (!ev) := by
  have h2 := two_sub_pos h1
  by_cases hj : j = 0
  · subst hj
    cases ev
    · simp only [okG, gF, if_true, Bool.not_false]
      simp
      have k := key_id h1
      rw [one_div, mul_one] at k
      linarith
    · simp only [okG, gF, if_true, Bool.not_true]
      simp
      rw [div_eq_mul_inv]
  · by_cases hd : d < L₂ / 2
    · have hok : okG L₂ j d ev = false := by
        simp only [okG, hj, if_false]
        have : ¬ L₂ < 2 * (d + 1) := by omega
        simp [this]
      rw [hok]
      simp only [gF, hj, if_false]
      have hm1 : max d (L₂ / 2) = L₂ / 2 := by omega
      have hm2 : max (d + 1) (L₂ / 2) = L₂ / 2 := by omega
      have hs : L₂ / 2 - d = (L₂ / 2 - (d + 1)) + 1 := by omega
      rw [hm1, hm2, hs, pow_succ]
      simp; ring_nf; exact le_rfl
    · have hm1 : max d (L₂ / 2) = d := by omega
      have hm2 : max (d + 1) (L₂ / 2) = d + 1 := by omega
      have hs1 : L₂ / 2 - d = 0 := by omega
      have hs2 : L₂ / 2 - (d + 1) = 0 := by omega
      have hlt : L₂ < 2 * (d + 1) := by omega
      simp only [gF, hj, if_false, hm1, hm2, hs1, hs2, pow_zero, one_mul]
      rcases Nat.mod_two_eq_zero_or_one d with hp | hp
      · have hq : (d + 1) % 2 ≠ 0 := by omega
        have hok : okG L₂ j d ev = false := by simp [okG, hj, hq]
        rw [hok]
        simp only [eF, hp, hq, if_true, if_false]
        simp; rw [div_eq_mul_inv]
      · have hq : (d + 1) % 2 = 0 := by omega
        have hp' : d % 2 ≠ 0 := by omega
        have hok : okG L₂ j d ev = true := by simp [okG, hj, hq, hlt]
        rw [hok]
        simp only [eF, hp', hq, if_true, if_false]
        rw [key_id h1]

end arith

end Formalism.G0.TopsWeightFunctionBounds

noncomputable section
open scoped BigOperators

namespace Formalism.G0.TopsWeightFunctionBounds

section pot
variable {R L₂ : ℕ} {δ : ℝ}

/- English proof (translation)
The claim follows from `pow_le_one₀ (aF_nonneg hLδ) ((aF_le h0).trans (by norm_num))`.
-/
lemma aFpow_le (h0 : 0 ≤ δ) (hLδ : (L₂ : ℝ) * δ ≤ 1) (k : ℕ) : aF L₂ δ ^ k ≤ 1 :=
  pow_le_one₀ (aF_nonneg hLδ) ((aF_le h0).trans (by norm_num))

/- English proof (translation)
Combine the linear relations using `[aFpow_le h0 hLδ R]`.
-/
lemma c_nonneg (h0 : 0 ≤ δ) (hLδ : (L₂ : ℝ) * δ ≤ 1) : 0 ≤ 1 - aF L₂ δ ^ R := by
  linarith [aFpow_le h0 hLδ R]

/- English proof (translation)
Establish `h1` using `d_le_one h0 hL hLδ`. Unfold `GF`. Use `split_ifs`. Conclude with `mul_le_one₀ (aFpow_le h0 hLδ _) (gF_nonneg h0 h1 _ _ _) (gF_le_one h0 h1 _ _ _)`. Evaluate the numerical expressions.
-/
lemma GF_le_one (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (j d : ℕ) (al ev : Bool) :
    GF R L₂ δ j d al ev ≤ 1 := by
  have h1 := d_le_one h0 hL hLδ
  unfold GF; split_ifs
  · exact mul_le_one₀ (aFpow_le h0 hLδ _) (gF_nonneg h0 h1 _ _ _) (gF_le_one h0 h1 _ _ _)
  · norm_num

/- English proof (translation)
Consider the cases of `s with`. Consider the case `bad => simp [Phi]`. Consider the case `good => simp [Phi]`. Consider the case `run K j d al ev`. Simplify using `only [Phi]`.

Conclude with `mul_nonneg (pow_nonneg (c_nonneg h0 hLδ) _) (by linarith [GF_le_one (R := R) h0 hL hLδ j d al ev])`.
-/
lemma Phi_nonneg (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (s : St) :
    0 ≤ Phi R L₂ δ s := by
  cases s with
  | bad => simp [Phi]
  | good => simp [Phi]
  | run K j d al ev =>
    simp only [Phi]
    exact mul_nonneg (pow_nonneg (c_nonneg h0 hLδ) _) (by linarith [GF_le_one (R := R) h0 hL hLδ j d al ev])

/- English proof (translation)
Consider the cases of `s with`. Consider the case `bad => cases b <;> trivial`. Consider the case `good => cases b <;> trivial`. Consider the case `run K j d al ev`. Simplify using `only [WF] at hs`.

Consider the cases of `b`. Simplify `hs` using `[step, WF]`. Simplify using `only [step] split_ifs with h1 h2 h3`. Discharge the goal by the elementary cases of `trivial`. Discharge the goal by the elementary cases of `trivial`.

Simplify using `only [WF]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [WF]`. Use linear arithmetic over natural numbers and integers.
-/
lemma WF_step (hR : 1 ≤ R) (s : St) (hs : WF R s) (b : Bool) : WF R (step R L₂ s b) := by
  cases s with
  | bad => cases b <;> trivial
  | good => cases b <;> trivial
  | run K j d al ev =>
    simp only [WF] at hs
    cases b
    · simpa [step, WF] using hs
    · simp only [step]
      split_ifs with h1 h2 h3
      · trivial
      · trivial
      · simp only [WF]; omega
      · simp only [WF]; omega

/- English proof (translation)
Simplify using `only [Phi, GF, if_true, Nat.sub_zero]`. Establish `hg` using `gF_lb h0 hL hLδ 0 ev`. Establish `hle : aF L₂ δ ^ R ≤ aF L₂ δ ^ (R - 1) * gF L₂ δ 0 0 ev`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_succ]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Use `_ ≤ _ := mul_le_mul_of_nonneg_left hg (pow_nonneg (aF_nonneg hLδ) _)`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma Phi_init (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (hR : 1 ≤ R)
    {K : ℕ} (hK : 1 ≤ K) (ev : Bool) :
    Phi R L₂ δ (.run K 0 0 true ev) ≤ (1 - aF L₂ δ ^ R) ^ K := by
  simp only [Phi, GF, if_true, Nat.sub_zero]
  have hg := gF_lb h0 hL hLδ 0 ev
  have hle : aF L₂ δ ^ R ≤ aF L₂ δ ^ (R - 1) * gF L₂ δ 0 0 ev := by
    calc aF L₂ δ ^ R = aF L₂ δ ^ (R - 1) * aF L₂ δ := by
          rw [← pow_succ]; congr 1; omega
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (pow_nonneg (aF_nonneg hLδ) _)
  calc (1 - aF L₂ δ ^ R) ^ (K - 1) * (1 - aF L₂ δ ^ (R - 1) * gF L₂ δ 0 0 ev)
        ≤ (1 - aF L₂ δ ^ R) ^ (K - 1) * (1 - aF L₂ δ ^ R) :=
          mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (c_nonneg h0 hLδ) _)
    _ = (1 - aF L₂ δ ^ R) ^ K := by rw [← pow_succ, Nat.sub_add_cancel hK]

/- English proof (translation)
Establish `hC : 0 ≤ (1 - aF L₂ δ ^ R) ^ (K - 1)` using `pow_nonneg (c_nonneg h0 hLδ) _`. Simplify using `only [step]`. Distinguish the cases in `hjR : j + 1 = R`. Rewrite using `[if_pos hjR]`. Establish `hA : aF L₂ δ ^ (R - 1 - j) = 1` using `by rw [show R - 1 - j = 0 by omega, pow_zero]`.

Distinguish the cases in `hg : (al && okG L₂ j d ev) = true`. Rewrite using `[if_pos hg, if_pos hg, hA]`. Simplify using `[Phi]`. Rewrite using `[if_neg hg, if_neg hg]`. Distinguish the cases in `hK : K ≤ 1`.

Rewrite using `[if_pos hK]; simp only [Phi]; rw [show K - 1 = 0 by omega]; simp`. Rewrite using `[if_neg hK, sub_zero, mul_one]`. Establish `h` using `Phi_init (R := R) h0 hL hLδ hR (K := K - 1) (by omega) (!ev)`. Conclude with `h`. Rewrite using `[if_neg hjR]`.

Simplify using `only [Phi]`. Apply `mul_le_mul_of_nonneg_left _ hC` to reduce the goal to its premises. Unfold `GF`. Distinguish the cases in `hg : (al && okG L₂ j d ev) = true`. Rewrite using `[if_pos hg, if_pos hg]`.

Establish `: aF L₂ δ ^ (R - 1 - j) ≤ aF L₂ δ ^ (R - 1 - (j + 1)) * gF L₂ δ (j + 1) 0 (!ev)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Use `_ ≤ _ := mul_le_mul_of_nonneg_left (gF_lb h0 hL hLδ _ _) (pow_nonneg (aF_nonneg hLδ) _)`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg hg, if_neg hg]`.
-/
lemma phi_true (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (hR : 1 ≤ R)
    (K j d : ℕ) (al ev : Bool) (hj : j < R) :
    Phi R L₂ δ (step R L₂ (.run K j d al ev) true) ≤
      (1 - aF L₂ δ ^ R) ^ (K - 1) *
        (1 - (if (al && okG L₂ j d ev) = true then aF L₂ δ ^ (R - 1 - j) else 0)) := by
  have hC : 0 ≤ (1 - aF L₂ δ ^ R) ^ (K - 1) := pow_nonneg (c_nonneg h0 hLδ) _
  simp only [step]
  by_cases hjR : j + 1 = R
  · rw [if_pos hjR]
    have hA : aF L₂ δ ^ (R - 1 - j) = 1 := by rw [show R - 1 - j = 0 by omega, pow_zero]
    by_cases hg : (al && okG L₂ j d ev) = true
    · rw [if_pos hg, if_pos hg, hA]; simp [Phi]
    · rw [if_neg hg, if_neg hg]
      by_cases hK : K ≤ 1
      · rw [if_pos hK]; simp only [Phi]; rw [show K - 1 = 0 by omega]; simp
      · rw [if_neg hK, sub_zero, mul_one]
        have h := Phi_init (R := R) h0 hL hLδ hR (K := K - 1) (by omega) (!ev)
        exact h
  · rw [if_neg hjR]
    simp only [Phi]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold GF
    by_cases hg : (al && okG L₂ j d ev) = true
    · rw [if_pos hg, if_pos hg]
      have : aF L₂ δ ^ (R - 1 - j) ≤ aF L₂ δ ^ (R - 1 - (j + 1)) * gF L₂ δ (j + 1) 0 (!ev) := by
        calc aF L₂ δ ^ (R - 1 - j) = aF L₂ δ ^ (R - 1 - (j + 1)) * aF L₂ δ := by
              rw [← pow_succ]; congr 1; omega
          _ ≤ _ := mul_le_mul_of_nonneg_left (gF_lb h0 hL hLδ _ _) (pow_nonneg (aF_nonneg hLδ) _)
      linarith
    · rw [if_neg hg, if_neg hg]

/- English proof (translation)
Establish `h1` using `d_le_one h0 hL hLδ`. Consider the cases of `s with`. Consider the case `bad => simp only [step, Phi]`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `good => simp only [step, Phi]`.

Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `run K j d al ev`. Simplify using `only [WF] at hs`. Establish `ht` using `phi_true h0 hL hLδ hR K j d al ev hs`. Establish `hf : Phi R L₂ δ (step R L₂ (.run K j d al ev) false) = (1 - aF L₂ δ ^ R) ^ (K - 1) * (1 - GF R L₂ δ j (d + 1) al (!ev))`.

Simplify using `only [step, Phi]`. Rewrite using `[hf]`. Use `show _ ≤ (1 - aF L₂ δ ^ R) ^ (K - 1) * (1 - GF R L₂ δ j d al ev)`. Establish `hC : 0 ≤ (1 - aF L₂ δ ^ R) ^ (K - 1)` using `pow_nonneg (c_nonneg h0 hLδ) _`. Establish `hA : 0 ≤ aF L₂ δ ^ (R - 1 - j)` using `pow_nonneg (aF_nonneg hLδ) _`.

Consider the cases of `al`. Simplify using `only [GF, Bool.false_and, Bool.false_eq_true, if_false] at ht ⊢`. Establish `e1` using `mul_le_mul_of_nonneg_left ht h0`. Use the polynomial consequences of the given equalities and inequalities. Simplify using `only [GF, Bool.true_and, if_true] at ht ⊢`.

Establish `hg` using `gF_step (L₂ := L₂) h0 h1 j d ev`. Apply the tactic sequence `have ho : (if okG L₂ j d ev = true then aF L₂ δ ^ (R - 1 - j) else 0) = aF L₂ δ ^ (R - 1 - j) * (if okG L₂ j d ev = true then (1 : ℝ) else 0) := by split_ifs <;> simp`. Rewrite `ht` using `[ho]`. Establish `e1` using `mul_le_mul_of_nonneg_left ht h0`. Establish `e2` using `mul_le_mul_of_nonneg_left hg (mul_nonneg hC hA)`.

Use polynomial arithmetic with `[e1, e2]`.
-/
lemma phi_step (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (hR : 1 ≤ R)
    (s : St) (hs : WF R s) :
    δ * Phi R L₂ δ (step R L₂ s true) + (1 - δ) * Phi R L₂ δ (step R L₂ s false) ≤ Phi R L₂ δ s := by
  have h1 := d_le_one h0 hL hLδ
  cases s with
  | bad => simp only [step, Phi]; linarith
  | good => simp only [step, Phi]; linarith
  | run K j d al ev =>
    simp only [WF] at hs
    have ht := phi_true h0 hL hLδ hR K j d al ev hs
    have hf : Phi R L₂ δ (step R L₂ (.run K j d al ev) false) =
        (1 - aF L₂ δ ^ R) ^ (K - 1) * (1 - GF R L₂ δ j (d + 1) al (!ev)) := by
      simp only [step, Phi]
    rw [hf]
    show _ ≤ (1 - aF L₂ δ ^ R) ^ (K - 1) * (1 - GF R L₂ δ j d al ev)
    have hC : 0 ≤ (1 - aF L₂ δ ^ R) ^ (K - 1) := pow_nonneg (c_nonneg h0 hLδ) _
    have hA : 0 ≤ aF L₂ δ ^ (R - 1 - j) := pow_nonneg (aF_nonneg hLδ) _
    cases al
    · simp only [GF, Bool.false_and, Bool.false_eq_true, if_false] at ht ⊢
      have e1 := mul_le_mul_of_nonneg_left ht h0
      nlinarith
    · simp only [GF, Bool.true_and, if_true] at ht ⊢
      have hg := gF_step (L₂ := L₂) h0 h1 j d ev
      have ho : (if okG L₂ j d ev = true then aF L₂ δ ^ (R - 1 - j) else 0) =
          aF L₂ δ ^ (R - 1 - j) * (if okG L₂ j d ev = true then (1 : ℝ) else 0) := by
        split_ifs <;> simp
      rw [ho] at ht
      have e1 := mul_le_mul_of_nonneg_left ht h0
      have e2 := mul_le_mul_of_nonneg_left hg (mul_nonneg hC hA)
      nlinarith [e1, e2]

/- English proof (translation)
Establish `h1` using `d_le_one h0 hL hLδ`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `s hs`. Simplify using `only [Wt]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `[Phi]`. Conclude with `Phi_nonneg h0 hL hLδ s`. Consider the case `succ m ih`.

Introduce `s hs`. Simplify using `only [Wt]`. Establish `a1` using `ih _ (WF_step (L₂ := L₂) hR s hs true)`. Establish `a2` using `ih _ (WF_step (L₂ := L₂) hR s hs false)`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma Wt_le (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (hR : 1 ≤ R) (m : ℕ) :
    ∀ s, WF R s → Wt R L₂ δ m s ≤ Phi R L₂ δ s := by
  have h1 := d_le_one h0 hL hLδ
  induction m with
  | zero =>
    intro s hs
    simp only [Wt]
    split_ifs with h
    · subst h; simp [Phi]
    · exact Phi_nonneg h0 hL hLδ s
  | succ m ih =>
    intro s hs
    simp only [Wt]
    have a1 := ih _ (WF_step (L₂ := L₂) hR s hs true)
    have a2 := ih _ (WF_step (L₂ := L₂) hR s hs false)
    calc δ * Wt R L₂ δ m (step R L₂ s true) + (1 - δ) * Wt R L₂ δ m (step R L₂ s false)
        ≤ δ * Phi R L₂ δ (step R L₂ s true) + (1 - δ) * Phi R L₂ δ (step R L₂ s false) :=
          add_le_add (mul_le_mul_of_nonneg_left a1 h0) (mul_le_mul_of_nonneg_left a2 (by linarith))
      _ ≤ Phi R L₂ δ s := phi_step h0 hL hLδ hR s hs

end pot

end Formalism.G0.TopsWeightFunctionBounds

noncomputable section
open scoped BigOperators

namespace Formalism.G0.TopsWeightFunctionBounds

def wP (δ : ℝ) (U : Finset ℕ) (p : ℕ) : ℝ := if p ∈ U then δ else 1 - δ

section sums
variable {R L₂ : ℕ} {δ : ℝ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma runS_cons (s : St) (b : Bool) (bs : List Bool) :
    runS R L₂ s (b :: bs) = runS R L₂ (step R L₂ s b) bs := rfl

/- English proof (translation)
Simplify using `[runS, List.foldl_append]`.
-/
lemma runS_append (s : St) (l₁ l₂ : List Bool) :
    runS R L₂ s (l₁ ++ l₂) = runS R L₂ (runS R L₂ s l₁) l₂ := by
  simp [runS, List.foldl_append]

/- English proof (translation)
Proceed by induction on `bs with`. Consider the case `nil => rfl`. Consider the case `cons b bs ih`. Rewrite using `[runS_cons]`. Apply the tactic sequence `have : step R L₂ .bad b = .bad := by cases b <;> rfl`.

Rewrite using `[this, ih]`.
-/
lemma runS_bad (bs : List Bool) : runS R L₂ .bad bs = .bad := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [runS_cons]
    have : step R L₂ .bad b = .bad := by cases b <;> rfl
    rw [this, ih]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => intro s`. Simplify using `[Wt, runS]`. Consider the case `cons p l ih`. Introduce `s`.

Rewrite `hl` using `[List.nodup_cons]`. Take `⟨hp, hl'⟩` from `hl`. Establish `hp' : p ∉ l.toFinset` using `by simpa using hp`. Rewrite using `[List.toFinset_cons, Finset.sum_powerset_insert hp']`. Establish `e1 : ∀ U ∈ l.toFinset.powerset, (if runS R L₂ s ((p :: l).map (fun q => decide (q ∈ U))) = .bad then ∏ q ∈ insert p l.toFinset, wP δ U q else 0) = (1 - δ) * (if runS R L₂ (step R L₂ s false) (l.map (fun q => decide (q ∈ U))) = .bad then ∏ q ∈ l.toFinset, wP δ U q else 0)`.

Introduce `U hU`. Establish `hpU : p ∉ U` using `fun h => hp' (Finset.mem_powerset.1 hU h)`. Establish `hw : wP δ U p = 1 - δ` using `by simp [wP, hpU]`. Rewrite using `[Finset.prod_insert hp', hw, List.map_cons, runS_cons, decide_eq_false hpU]`. Apply the tactic sequence `split_ifs <;> ring`.

Establish `e2 : ∀ U ∈ l.toFinset.powerset, (if runS R L₂ s ((p :: l).map (fun q => decide (q ∈ insert p U))) = .bad then ∏ q ∈ insert p l.toFinset, wP δ (insert p U) q else 0) = δ * (if runS R L₂ (step R L₂ s true) (l.map (fun q => decide (q ∈ U))) = .bad then ∏ q ∈ l.toFinset, wP δ U q els …`. Introduce `U _`. Establish `hmap : l.map (fun q => decide (q ∈ insert p U)) = l.map (fun q => decide (q ∈ U))`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `q hq`.

Establish `: q ≠ p` using `fun h => hp (h ▸ hq)`. Simplify using `[Finset.mem_insert, this]`. Establish `hprod : ∏ q ∈ l.toFinset, wP δ (insert p U) q = ∏ q ∈ l.toFinset, wP δ U q`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `q hq`.

Establish `: q ≠ p` using `fun h => hp' (h ▸ hq)`. Simplify using `[wP, Finset.mem_insert, this]`. Establish `hw : wP δ (insert p U) p = δ` using `by simp [wP]`. Rewrite using `[Finset.prod_insert hp', hw, List.map_cons, runS_cons, hmap, hprod, decide_eq_true (Finset.mem_insert_self p U)]`. Apply the tactic sequence `split_ifs <;> ring`.

Rewrite using `[Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum, ih hl', ih hl']`. Simplify using `only [List.length_cons, Wt]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sum_list (l : List ℕ) (hl : l.Nodup) : ∀ s : St,
    ∑ U ∈ l.toFinset.powerset,
      (if runS R L₂ s (l.map (fun p => decide (p ∈ U))) = .bad then
        ∏ p ∈ l.toFinset, wP δ U p else 0) = Wt R L₂ δ l.length s := by
  induction l with
  | nil => intro s; simp [Wt, runS]
  | cons p l ih =>
    intro s
    rw [List.nodup_cons] at hl
    obtain ⟨hp, hl'⟩ := hl
    have hp' : p ∉ l.toFinset := by simpa using hp
    rw [List.toFinset_cons, Finset.sum_powerset_insert hp']
    have e1 : ∀ U ∈ l.toFinset.powerset,
        (if runS R L₂ s ((p :: l).map (fun q => decide (q ∈ U))) = .bad then
          ∏ q ∈ insert p l.toFinset, wP δ U q else 0) =
        (1 - δ) * (if runS R L₂ (step R L₂ s false) (l.map (fun q => decide (q ∈ U))) = .bad then
          ∏ q ∈ l.toFinset, wP δ U q else 0) := by
      intro U hU
      have hpU : p ∉ U := fun h => hp' (Finset.mem_powerset.1 hU h)
      have hw : wP δ U p = 1 - δ := by simp [wP, hpU]
      rw [Finset.prod_insert hp', hw, List.map_cons, runS_cons, decide_eq_false hpU]
      split_ifs <;> ring
    have e2 : ∀ U ∈ l.toFinset.powerset,
        (if runS R L₂ s ((p :: l).map (fun q => decide (q ∈ insert p U))) = .bad then
          ∏ q ∈ insert p l.toFinset, wP δ (insert p U) q else 0) =
        δ * (if runS R L₂ (step R L₂ s true) (l.map (fun q => decide (q ∈ U))) = .bad then
          ∏ q ∈ l.toFinset, wP δ U q else 0) := by
      intro U _
      have hmap : l.map (fun q => decide (q ∈ insert p U)) = l.map (fun q => decide (q ∈ U)) := by
        apply List.map_congr_left
        intro q hq
        have : q ≠ p := fun h => hp (h ▸ hq)
        simp [Finset.mem_insert, this]
      have hprod : ∏ q ∈ l.toFinset, wP δ (insert p U) q = ∏ q ∈ l.toFinset, wP δ U q := by
        apply Finset.prod_congr rfl
        intro q hq
        have : q ≠ p := fun h => hp' (h ▸ hq)
        simp [wP, Finset.mem_insert, this]
      have hw : wP δ (insert p U) p = δ := by simp [wP]
      rw [Finset.prod_insert hp', hw, List.map_cons, runS_cons, hmap, hprod,
        decide_eq_true (Finset.mem_insert_self p U)]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum,
      ih hl', ih hl']
    simp only [List.length_cons, Wt]
    ring

/- English proof (translation)
Unfold `wP`. Rewrite using `[Finset.prod_ite, Finset.prod_const, Finset.prod_const]`. Establish `h1 : (Finset.range n).filter (fun x => x ∈ T) = T`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`.

Conclude with `⟨fun h => h.2, fun h => ⟨Finset.mem_range.1 (hT h), h⟩⟩`. Establish `h2` using `Finset.card_filter_add_card_filter_not (s := Finset.range n) (fun x => x ∈ T)`. Rewrite `h2` using `[h1, Finset.card_range]`. Rewrite using `[h1, show ((Finset.range n).filter (fun x => ¬ x ∈ T)).card = n - T.card by omega]`.
-/
lemma prod_wP (n : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.range n) :
    ∏ p ∈ Finset.range n, wP δ T p = δ ^ T.card * (1 - δ) ^ (n - T.card) := by
  unfold wP
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.range n).filter (fun x => x ∈ T) = T := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.1 (hT h), h⟩⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.range n) (fun x => x ∈ T)
  rw [h1, Finset.card_range] at h2
  rw [h1, show ((Finset.range n).filter (fun x => ¬ x ∈ T)).card = n - T.card by omega]

def Lst (n i : ℕ) : List ℕ := (List.range (n - 1)).map (fun t => (i + t + 1) % n)

/- English proof (translation)
Establish `h' : x % n = y % n` using `Nat.ModEq.add_left_cancel' i h`. Rewrite `h'` using `[Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]`. Then use the resulting hypothesis.
-/
lemma mod_inj {n i x y : ℕ} (hx : x < n) (hy : y < n) (h : (i + x) % n = (i + y) % n) : x = y := by
  have h' : x % n = y % n := Nat.ModEq.add_left_cancel' i h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h'

/- English proof (translation)
Unfold `Lst`. Apply `List.Nodup.map_on _ List.nodup_range` to reduce the goal to its premises. Introduce `x hx y hy h`. Rewrite `hx`, `hy` using `[List.mem_range]`. Establish `: x + 1 = y + 1` using `mod_inj (n := n) (i := i) (x := x + 1) (y := y + 1) (by omega) (by omega) (by simpa [add_assoc] using h)`.

Use linear arithmetic over natural numbers and integers.
-/
lemma Lst_nodup (n i : ℕ) : (Lst n i).Nodup := by
  unfold Lst
  apply List.Nodup.map_on _ List.nodup_range
  intro x hx y hy h
  rw [List.mem_range] at hx hy
  have : x + 1 = y + 1 := mod_inj (n := n) (i := i) (x := x + 1) (y := y + 1) (by omega) (by omega) (by simpa [add_assoc] using h)
  omega

/- English proof (translation)
Use `symm`. Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[Finset.mem_erase, Finset.mem_range]`. Rewrite using `[List.mem_toFinset]`.

Unfold `Lst`. Rewrite using `[List.mem_map]`. Use `⟨(x + n - i) % n - 1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[List.mem_range]`. Use `Nat.mod_lt (x + n - i) (by omega : 0 < n)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hne : (x + n - i) % n ≠ 0`. Introduce `h0`. Establish `h1 : (x + n - i) % n = (i + n - i) % n` using `by rw [h0]; simp`. Distinguish the cases in `hxi : i ≤ x`.

Establish `: x - i < n` using `by omega`. Establish `e1 : (x + n - i) % n = (x - i) % n`. Rewrite using `[show x + n - i = (x - i) + n by omega, Nat.add_mod_right]`. Rewrite `h0` using `[e1, Nat.mod_eq_of_lt this]`. Use linear arithmetic over natural numbers and integers.

Establish `: x + n - i < n` using `by omega`. Rewrite `h0` using `[Nat.mod_eq_of_lt this]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[add_assoc, Nat.sub_add_cancel (Nat.pos_of_ne_zero hne)]`. Rewrite using `[Nat.add_mod_mod]`.

Rewrite using `[show i + (x + n - i) = x + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hx.2]`. Rewrite using `[List.toFinset_card_of_nodup (Lst_nodup n i), Finset.card_erase_of_mem (Finset.mem_range.2 hi)]`. Simplify using `[Lst]`.
-/
lemma Lst_toFinset {n i : ℕ} (hi : i < n) : (Lst n i).toFinset = (Finset.range n).erase i := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_erase, Finset.mem_range] at hx
    rw [List.mem_toFinset]
    unfold Lst
    rw [List.mem_map]

    refine ⟨(x + n - i) % n - 1, ?_, ?_⟩
    · rw [List.mem_range]
      have := Nat.mod_lt (x + n - i) (by omega : 0 < n)
      omega
    · have hne : (x + n - i) % n ≠ 0 := by
        intro h0
        have h1 : (x + n - i) % n = (i + n - i) % n := by rw [h0]; simp
        by_cases hxi : i ≤ x
        · have : x - i < n := by omega
          have e1 : (x + n - i) % n = (x - i) % n := by
            rw [show x + n - i = (x - i) + n by omega, Nat.add_mod_right]
          rw [e1, Nat.mod_eq_of_lt this] at h0
          omega
        · have : x + n - i < n := by omega
          rw [Nat.mod_eq_of_lt this] at h0
          omega
      rw [add_assoc, Nat.sub_add_cancel (Nat.pos_of_ne_zero hne)]
      rw [Nat.add_mod_mod]
      rw [show i + (x + n - i) = x + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hx.2]
  · rw [List.toFinset_card_of_nodup (Lst_nodup n i), Finset.card_erase_of_mem (Finset.mem_range.2 hi)]
    simp [Lst]

/- English proof (translation)
Establish `hS` using `Lst_toFinset hi`. Establish `hr : Finset.range n = insert i ((Finset.range n).erase i)` using `(Finset.insert_erase (Finset.mem_range.2 hi)).symm`. Establish `hiS : i ∉ (Finset.range n).erase i` using `Finset.notMem_erase i _`. Rewrite using `[hr, Finset.sum_powerset_insert hiS]`. Establish `z1 : ∑ U ∈ ((Finset.range n).erase i).powerset, (if i ∈ U ∧ runS R L₂ s ((Lst n i).map (fun p => decide (p ∈ U))) = .bad then ∏ p ∈ insert i ((Finset.range n).erase i), wP δ U p else 0) = 0`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `U hU`. Establish `: i ∉ U` using `fun h => hiS (Finset.mem_powerset.1 hU h)`. Simplify using `[this]`. Rewrite using `[z1, zero_add]`.

Establish `e2 : ∀ U ∈ ((Finset.range n).erase i).powerset, (if i ∈ insert i U ∧ runS R L₂ s ((Lst n i).map (fun p => decide (p ∈ insert i U))) = .bad then ∏ p ∈ insert i ((Finset.range n).erase i), wP δ (insert i U) p else 0) = δ * (if runS R L₂ s ((Lst n i).map (fun p => decide (p ∈ U))) = …`. Introduce `U _`. Establish `hmap : (Lst n i).map (fun q => decide (q ∈ insert i U)) = (Lst n i).map (fun q => decide (q ∈ U))`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `q hq`.

Establish `hq' : q ∈ (Finset.range n).erase i` using `by rw [← hS, List.mem_toFinset]; exact hq`. Establish `: q ≠ i` using `Finset.ne_of_mem_erase hq'`. Simplify using `[Finset.mem_insert, this]`. Establish `hprod : ∏ q ∈ (Finset.range n).erase i, wP δ (insert i U) q = ∏ q ∈ (Lst n i).toFinset, wP δ U q`. Rewrite using `[hS]`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `q hq`. Establish `: q ≠ i` using `Finset.ne_of_mem_erase hq`. Simplify using `[wP, Finset.mem_insert, this]`. Establish `hw : wP δ (insert i U) i = δ` using `by simp [wP]`.

Rewrite using `[Finset.prod_insert hiS, hw, hmap, hprod]`. Simplify using `only [Finset.mem_insert_self, true_and]`. Apply the tactic sequence `split_ifs <;> ring`. Rewrite using `[Finset.sum_congr rfl e2, ← Finset.mul_sum, ← hS, sum_list _ (Lst_nodup n i)]`. Simplify using `[Lst]`.
-/
lemma sum_event {n i : ℕ} (hi : i < n) (s : St) :
    ∑ T ∈ (Finset.range n).powerset,
      (if i ∈ T ∧ runS R L₂ s ((Lst n i).map (fun p => decide (p ∈ T))) = .bad then
        ∏ p ∈ Finset.range n, wP δ T p else 0) = δ * Wt R L₂ δ (n - 1) s := by
  have hS := Lst_toFinset hi
  have hr : Finset.range n = insert i ((Finset.range n).erase i) :=
    (Finset.insert_erase (Finset.mem_range.2 hi)).symm
  have hiS : i ∉ (Finset.range n).erase i := Finset.notMem_erase i _
  rw [hr, Finset.sum_powerset_insert hiS]
  have z1 : ∑ U ∈ ((Finset.range n).erase i).powerset,
      (if i ∈ U ∧ runS R L₂ s ((Lst n i).map (fun p => decide (p ∈ U))) = .bad then
        ∏ p ∈ insert i ((Finset.range n).erase i), wP δ U p else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro U hU
    have : i ∉ U := fun h => hiS (Finset.mem_powerset.1 hU h)
    simp [this]
  rw [z1, zero_add]
  have e2 : ∀ U ∈ ((Finset.range n).erase i).powerset,
      (if i ∈ insert i U ∧ runS R L₂ s ((Lst n i).map (fun p => decide (p ∈ insert i U))) = .bad then
        ∏ p ∈ insert i ((Finset.range n).erase i), wP δ (insert i U) p else 0) =
      δ * (if runS R L₂ s ((Lst n i).map (fun p => decide (p ∈ U))) = .bad then
        ∏ p ∈ (Lst n i).toFinset, wP δ U p else 0) := by
    intro U _
    have hmap : (Lst n i).map (fun q => decide (q ∈ insert i U)) =
        (Lst n i).map (fun q => decide (q ∈ U)) := by
      apply List.map_congr_left
      intro q hq
      have hq' : q ∈ (Finset.range n).erase i := by rw [← hS, List.mem_toFinset]; exact hq
      have : q ≠ i := Finset.ne_of_mem_erase hq'
      simp [Finset.mem_insert, this]
    have hprod : ∏ q ∈ (Finset.range n).erase i, wP δ (insert i U) q =
        ∏ q ∈ (Lst n i).toFinset, wP δ U q := by
      rw [hS]
      apply Finset.prod_congr rfl
      intro q hq
      have : q ≠ i := Finset.ne_of_mem_erase hq
      simp [wP, Finset.mem_insert, this]
    have hw : wP δ (insert i U) i = δ := by simp [wP]
    rw [Finset.prod_insert hiS, hw, hmap, hprod]
    simp only [Finset.mem_insert_self, true_and]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e2, ← Finset.mul_sum, ← hS, sum_list _ (Lst_nodup n i)]
  simp [Lst]

end sums

end Formalism.G0.TopsWeightFunctionBounds

noncomputable section
open scoped BigOperators

namespace Formalism.G0.TopsWeightFunctionBounds

section comb
variable (n : ℕ) (T : Finset ℕ) (L₂ R b K₀ : ℕ)

def cnt (t : ℕ) : ℕ := ((Finset.range (t + 1)).filter (fun d => (b + d) % n ∈ T)).card

def PRun (j t d : ℕ) (u : Fin j → ℕ) : Prop :=
  StrictMono u ∧ (∀ l, u l ≤ t) ∧ (∀ l, (b + u l) % n ∈ T) ∧ (∀ l, Even ((b + u l) % n)) ∧
  (∀ (l : Fin j) (h : l.val + 1 < j), L₂ < 2 * (u ⟨l.val + 1, h⟩ - u l) ∧
      ∀ x, u l < x → x < u ⟨l.val + 1, h⟩ → (b + x) % n ∉ T) ∧
  (∀ h : 0 < j, u ⟨j - 1, by omega⟩ = t - d)

def Inv (t : ℕ) : St → Prop
  | .bad => True
  | .good => GoodRun n T L₂ R b t
  | .run K j d al ev => 1 ≤ K ∧ K ≤ K₀ ∧ j < R ∧ d ≤ t ∧ ev = decide (Even (b + t)) ∧
      (b + (t - d)) % n ∈ T ∧ (∀ x, t - d < x → x ≤ t → (b + x) % n ∉ T) ∧
      cnt n T b t = 1 + R * (K₀ - K) + j ∧
      (al = true → ∃ u : Fin j → ℕ, PRun n T L₂ b j t d u)

def Ls (t m : ℕ) : List Bool := (List.range m).map (fun x => decide ((b + (t + 1 + x)) % n ∈ T))

end comb

def snocF {j : ℕ} (u : Fin j → ℕ) (v : ℕ) : Fin (j + 1) → ℕ :=
  fun l => if h : l.val < j then u ⟨l.val, h⟩ else v

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
lemma snocF_lt {j : ℕ} (u : Fin j → ℕ) (v : ℕ) (l : Fin (j + 1)) (h : l.val < j) :
    snocF u v l = u ⟨l.val, h⟩ := dif_pos h

/- English proof (translation)
The claim follows from `dif_neg h`.
-/
lemma snocF_last {j : ℕ} (u : Fin j → ℕ) (v : ℕ) (l : Fin (j + 1)) (h : ¬ l.val < j) :
    snocF u v l = v := dif_neg h

/- English proof (translation)
Rewrite using `[Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ (even_iff_two_dvd.1 hn)]`.
-/
lemma even_mod {n : ℕ} (hn : Even n) (x : ℕ) : Even (x % n) ↔ Even x := by
  rw [Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ (even_iff_two_dvd.1 hn)]

/- English proof (translation)
Unfold `cnt`. Rewrite using `[Finset.range_add_one (n := t + 1), Finset.filter_insert]`. Use `split_ifs with h`. Rewrite using `[Finset.card_insert_of_notMem]`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression.
-/
lemma cnt_succ (n : ℕ) (T : Finset ℕ) (b t : ℕ) :
    cnt n T b (t + 1) = cnt n T b t + (if (b + (t + 1)) % n ∈ T then 1 else 0) := by
  unfold cnt
  rw [Finset.range_add_one (n := t + 1), Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => a.elim0, fun l => l.elim0, fun l => l.elim0, fun l => l.elim0, fun l => l.elim0, fun h => absurd h (lt_irrefl 0)⟩`.
-/
lemma PRun_zero (n : ℕ) (T : Finset ℕ) (L₂ b t d : ℕ) (u : Fin 0 → ℕ) : PRun n T L₂ b 0 t d u :=
  ⟨fun a => a.elim0, fun l => l.elim0, fun l => l.elim0, fun l => l.elim0, fun l => l.elim0,
    fun h => absurd h (lt_irrefl 0)⟩

/- English proof (translation)
Take `⟨hmono, hle, htop, hevu, hgap, hlast⟩` from `hu`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a c hac`. Establish `hac' : a.val < c.val` using `hac`. Distinguish the cases in `ha : a.val < j`.

Rewrite using `[snocF_lt u _ a ha]`. Distinguish the cases in `hc : c.val < j`. Rewrite using `[snocF_lt u _ c hc]`. Conclude with `hmono (show (⟨a.val, ha⟩ : Fin j) < ⟨c.val, hc⟩ from hac')`. Rewrite using `[snocF_last u _ c hc]`.

Use `hle ⟨a.val, ha⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Use `c.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce `l`. Distinguish the cases in `hl : l.val < j`. Rewrite using `[snocF_lt u _ l hl]`. Conclude with `(hle _).trans (Nat.le_succ _)`. Rewrite using `[snocF_last u _ l hl]`.

Introduce `l`. Distinguish the cases in `hl : l.val < j`. Rewrite using `[snocF_lt u _ l hl]`. Conclude with `htop _`. Rewrite using `[snocF_last u _ l hl]`.

Conclude with `hT`. Introduce `l`. Distinguish the cases in `hl : l.val < j`. Rewrite using `[snocF_lt u _ l hl]`. Conclude with `hevu _`.

Rewrite using `[snocF_last u _ l hl, even_mod hn]`. Distinguish the cases in `hj : j = 0`. Establish `hev' : ev = false` using `by simpa [okG, hj] using hok`. Rewrite `hev` using `[hev']`. Establish `hne : ¬ Even (b + t)` using `by simpa using hev.symm`.

Rewrite using `[← add_assoc, Nat.even_add_one]`. Conclude with `hne`. Establish `hok' : (d + 1) % 2 = 0 ∧ L₂ < 2 * (d + 1)` using `by simpa [okG, hj] using hok`. Establish `hprev` using `hevu ⟨j - 1, by omega⟩`. Rewrite `hprev` using `[hlast (by omega), even_mod hn]`.

Establish `hdd : Even (d + 1)` using `Nat.even_iff.2 hok'.1`. Establish `: b + (t + 1) = (b + (t - d)) + (d + 1)` using `by omega`. Rewrite using `[this]`. Conclude with `hprev.add hdd`. Introduce `l hl`.

Establish `hl0 : l.val < j` using `by omega`. Rewrite using `[snocF_lt u _ l hl0]`. Distinguish the cases in `hl1 : l.val + 1 < j`. Rewrite using `[snocF_lt u _ ⟨l.val + 1, hl⟩ hl1]`. Conclude with `hgap ⟨l.val, hl0⟩ hl1`.

Rewrite using `[snocF_last u _ ⟨l.val + 1, hl⟩ hl1]`. Establish `hj : j ≠ 0` using `by omega`. Establish `hok' : (d + 1) % 2 = 0 ∧ L₂ < 2 * (d + 1)` using `by simpa [okG, hj] using hok`. Establish `hul : u ⟨l.val, hl0⟩ = t - d`. Use `hlast (by omega)` as an intermediate fact.

Establish `e : (⟨l.val, hl0⟩ : Fin j) = ⟨j - 1, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[e]`. Conclude with `this`. Rewrite using `[hul]`. Use `⟨by omega, ?_⟩` and prove the remaining obligations.

Introduce `x h1 h2`. Conclude with `hnone x h1 (by omega)`. Introduce `_`. Rewrite using `[snocF_last u _ _ (by simp)]`. Both sides reduce to the same expression.
-/
lemma PRun_ext {n : ℕ} (hn : Even n) {T : Finset ℕ} {L₂ b j t d : ℕ} {ev : Bool} {u : Fin j → ℕ}
    (hu : PRun n T L₂ b j t d u) (hd : d ≤ t) (hev : ev = decide (Even (b + t)))
    (hnone : ∀ x, t - d < x → x ≤ t → (b + x) % n ∉ T)
    (hT : (b + (t + 1)) % n ∈ T) (hok : okG L₂ j d ev = true) :
    PRun n T L₂ b (j + 1) (t + 1) 0 (snocF u (t + 1)) := by
  obtain ⟨hmono, hle, htop, hevu, hgap, hlast⟩ := hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a c hac
    have hac' : a.val < c.val := hac
    by_cases ha : a.val < j
    · rw [snocF_lt u _ a ha]
      by_cases hc : c.val < j
      · rw [snocF_lt u _ c hc]
        exact hmono (show (⟨a.val, ha⟩ : Fin j) < ⟨c.val, hc⟩ from hac')
      · rw [snocF_last u _ c hc]
        have := hle ⟨a.val, ha⟩
        omega
    · exfalso
      have := c.isLt
      omega
  · intro l
    by_cases hl : l.val < j
    · rw [snocF_lt u _ l hl]; exact (hle _).trans (Nat.le_succ _)
    · rw [snocF_last u _ l hl]
  · intro l
    by_cases hl : l.val < j
    · rw [snocF_lt u _ l hl]; exact htop _
    · rw [snocF_last u _ l hl]; exact hT
  · intro l
    by_cases hl : l.val < j
    · rw [snocF_lt u _ l hl]; exact hevu _
    · rw [snocF_last u _ l hl, even_mod hn]
      by_cases hj : j = 0
      · have hev' : ev = false := by simpa [okG, hj] using hok
        rw [hev'] at hev
        have hne : ¬ Even (b + t) := by simpa using hev.symm
        rw [← add_assoc, Nat.even_add_one]
        exact hne
      · have hok' : (d + 1) % 2 = 0 ∧ L₂ < 2 * (d + 1) := by simpa [okG, hj] using hok
        have hprev := hevu ⟨j - 1, by omega⟩
        rw [hlast (by omega), even_mod hn] at hprev
        have hdd : Even (d + 1) := Nat.even_iff.2 hok'.1
        have : b + (t + 1) = (b + (t - d)) + (d + 1) := by omega
        rw [this]
        exact hprev.add hdd
  · intro l hl
    have hl0 : l.val < j := by omega
    rw [snocF_lt u _ l hl0]
    by_cases hl1 : l.val + 1 < j
    · rw [snocF_lt u _ ⟨l.val + 1, hl⟩ hl1]
      exact hgap ⟨l.val, hl0⟩ hl1
    · rw [snocF_last u _ ⟨l.val + 1, hl⟩ hl1]
      have hj : j ≠ 0 := by omega
      have hok' : (d + 1) % 2 = 0 ∧ L₂ < 2 * (d + 1) := by simpa [okG, hj] using hok
      have hul : u ⟨l.val, hl0⟩ = t - d := by
        have := hlast (by omega)
        have e : (⟨l.val, hl0⟩ : Fin j) = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [e]; exact this
      rw [hul]
      refine ⟨by omega, ?_⟩
      intro x h1 h2
      exact hnone x h1 (by omega)
  · intro _
    rw [snocF_last u _ _ (by simp)]
    rfl

/- English proof (translation)
Consider the cases of `s with`. Consider the case `bad`. Establish `: step R L₂ .bad (decide ((b + (t + 1)) % n ∈ T)) = .bad`. Apply the tactic sequence `cases decide ((b + (t + 1)) % n ∈ T) <;> rfl`. Rewrite using `[this]`.

Conclude with `True.intro`. Consider the case `good`. Establish `: step R L₂ .good (decide ((b + (t + 1)) % n ∈ T)) = .good`. Apply the tactic sequence `cases decide ((b + (t + 1)) % n ∈ T) <;> rfl`. Rewrite using `[this]`.

Take `⟨u, h1, h2, h3, h4, h5⟩` from `hs`. Conclude with `⟨u, h1, fun l => (h2 l).trans (Nat.le_succ _), h3, h4, h5⟩`. Consider the case `run K j d al ev`. Take `⟨hK1, hK2, hj, hd, hev, htop, hnone, hcnt, hal⟩` from `hs`. Establish `hev' : (!ev) = decide (Even (b + (t + 1)))`.

Rewrite using `[hev, ← add_assoc]`. Distinguish the cases in `he : Even (b + t)`. Simplify using `[he, Nat.even_add_one]`. Simplify using `[he, Nat.even_add_one]`. Distinguish the cases in `hT : (b + (t + 1)) % n ∈ T`.

Rewrite using `[decide_eq_true hT]`. Establish `hext : (al && okG L₂ j d ev) = true → ∃ u : Fin (j + 1) → ℕ, PRun n T L₂ b (j + 1) (t + 1) 0 u`. Introduce `hg`. Rewrite `hg` using `[Bool.and_eq_true]`. Take `⟨u, hu⟩` from `hal hg.1`.

Conclude with `⟨_, PRun_ext hn hu hd hev hnone hT hg.2⟩`. Establish `hc1 : cnt n T b (t + 1) = cnt n T b t + 1` using `by rw [cnt_succ, if_pos hT]`. Simplify using `only [step]`. Use `split_ifs with hjR hg hK`. Take `⟨u, hu⟩` from `hext hg`.

Substitute `hjR` using the available equality. Conclude with `⟨u, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1⟩`. Conclude with `True.intro`. Use `⟨by omega, by omega, by omega, by omega, hev', by simpa using hT, fun x h1 h2 => by omega, ?_, fun _ => ⟨Fin.elim0, PRun_zero _ _ _ _ _ _ _⟩⟩` and prove the remaining obligations. Rewrite using `[hc1, hcnt]`.

Establish `e : K₀ - (K - 1) = (K₀ - K) + 1` using `by omega`. Rewrite using `[e, mul_add, mul_one]`. Use linear arithmetic over natural numbers and integers. Use `⟨hK1, hK2, by omega, by omega, hev', by simpa using hT, fun x h1 h2 => by omega, ?_, hext⟩` and prove the remaining obligations. Rewrite using `[hc1, hcnt]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[decide_eq_false hT]`. Simplify using `only [step]`. Use `⟨hK1, hK2, hj, by omega, hev', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show t + 1 - (d + 1) = t - d by omega]` and apply the resulting hypothesis.

Introduce `x h1 h2`. Break down `Nat.lt_or_ge x (t + 1) with h | h` into its components or cases. Conclude with `hnone x (by omega) (by omega)`. Establish `: x = t + 1` using `by omega`. Substitute `this` using the available equality.

Conclude with `hT`. Rewrite using `[cnt_succ, if_neg hT, hcnt, add_zero]`. Introduce `ha`. Take `⟨u, hmono, hle, htopu, hevu, hgap, hlast⟩` from `hal ha`. Use `⟨u, hmono, fun l => (hle l).trans (Nat.le_succ _), htopu, hevu, hgap, ?_⟩` and prove the remaining obligations.

Introduce `h`. Rewrite using `[hlast h]`. Use linear arithmetic over natural numbers and integers.
-/
lemma inv_step {n : ℕ} (hn : Even n) {T : Finset ℕ} {L₂ R b K₀ : ℕ} (hR : 1 ≤ R) (t : ℕ) (s : St)
    (hs : Inv n T L₂ R b K₀ t s) :
    Inv n T L₂ R b K₀ (t + 1) (step R L₂ s (decide ((b + (t + 1)) % n ∈ T))) := by
  cases s with
  | bad =>
    have : step R L₂ .bad (decide ((b + (t + 1)) % n ∈ T)) = .bad := by
      cases decide ((b + (t + 1)) % n ∈ T) <;> rfl
    rw [this]; exact True.intro
  | good =>
    have : step R L₂ .good (decide ((b + (t + 1)) % n ∈ T)) = .good := by
      cases decide ((b + (t + 1)) % n ∈ T) <;> rfl
    rw [this]
    obtain ⟨u, h1, h2, h3, h4, h5⟩ := hs
    exact ⟨u, h1, fun l => (h2 l).trans (Nat.le_succ _), h3, h4, h5⟩
  | run K j d al ev =>
    obtain ⟨hK1, hK2, hj, hd, hev, htop, hnone, hcnt, hal⟩ := hs
    have hev' : (!ev) = decide (Even (b + (t + 1))) := by
      rw [hev, ← add_assoc]
      by_cases he : Even (b + t)
      · simp [he, Nat.even_add_one]
      · simp [he, Nat.even_add_one]
    by_cases hT : (b + (t + 1)) % n ∈ T
    · rw [decide_eq_true hT]
      have hext : (al && okG L₂ j d ev) = true →
          ∃ u : Fin (j + 1) → ℕ, PRun n T L₂ b (j + 1) (t + 1) 0 u := by
        intro hg
        rw [Bool.and_eq_true] at hg
        obtain ⟨u, hu⟩ := hal hg.1
        exact ⟨_, PRun_ext hn hu hd hev hnone hT hg.2⟩
      have hc1 : cnt n T b (t + 1) = cnt n T b t + 1 := by rw [cnt_succ, if_pos hT]
      simp only [step]
      split_ifs with hjR hg hK
      · obtain ⟨u, hu⟩ := hext hg
        subst hjR
        exact ⟨u, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1⟩
      · exact True.intro
      · refine ⟨by omega, by omega, by omega, by omega, hev', by simpa using hT,
          fun x h1 h2 => by omega, ?_, fun _ => ⟨Fin.elim0, PRun_zero _ _ _ _ _ _ _⟩⟩
        rw [hc1, hcnt]
        have e : K₀ - (K - 1) = (K₀ - K) + 1 := by omega
        rw [e, mul_add, mul_one]
        omega
      · refine ⟨hK1, hK2, by omega, by omega, hev', by simpa using hT,
          fun x h1 h2 => by omega, ?_, hext⟩
        rw [hc1, hcnt]
        omega
    · rw [decide_eq_false hT]
      simp only [step]
      refine ⟨hK1, hK2, hj, by omega, hev', ?_, ?_, ?_, ?_⟩
      · rwa [show t + 1 - (d + 1) = t - d by omega]
      · intro x h1 h2
        rcases Nat.lt_or_ge x (t + 1) with h | h
        · exact hnone x (by omega) (by omega)
        · have : x = t + 1 := by omega
          subst this; exact hT
      · rw [cnt_succ, if_neg hT, hcnt, add_zero]
      · intro ha
        obtain ⟨u, hmono, hle, htopu, hevu, hgap, hlast⟩ := hal ha
        refine ⟨u, hmono, fun l => (hle l).trans (Nat.le_succ _), htopu, hevu, hgap, ?_⟩
        intro h
        rw [hlast h]
        omega

/- English proof (translation)
Unfold `Ls`. Rewrite using `[List.range_succ_eq_map, List.map_cons, List.map_map]`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `x _`.

Simplify using `only [Function.comp_apply]`. Rewrite using `[show t + 1 + (x + 1) = t + 1 + 1 + x by omega]`.
-/
lemma Ls_succ (n : ℕ) (T : Finset ℕ) (b t m : ℕ) :
    Ls n T b t (m + 1) = decide ((b + (t + 1)) % n ∈ T) :: Ls n T b (t + 1) m := by
  unfold Ls
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply]
  rw [show t + 1 + (x + 1) = t + 1 + 1 + x by omega]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro t s hs`. Simplify `hs` using `[Ls, runS]`. Consider the case `succ m ih`. Introduce `t s hs`.

Rewrite using `[Ls_succ, runS_cons]`. Use `ih (t + 1) _ (inv_step hn hR t s hs)` as an intermediate fact. Rewrite `this` using `[show t + 1 + m = t + (m + 1) by omega]`. Then use the resulting hypothesis.
-/
lemma inv_iter {n : ℕ} (hn : Even n) {T : Finset ℕ} {L₂ R b K₀ : ℕ} (hR : 1 ≤ R) (m : ℕ) :
    ∀ t s, Inv n T L₂ R b K₀ t s → Inv n T L₂ R b K₀ (t + m) (runS R L₂ s (Ls n T b t m)) := by
  induction m with
  | zero => intro t s hs; simpa [Ls, runS] using hs
  | succ m ih =>
    intro t s hs
    rw [Ls_succ, runS_cons]
    have := ih (t + 1) _ (inv_step hn hR t s hs)
    rwa [show t + 1 + m = t + (m + 1) by omega] at this

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, by unfold Ls; rw [List.range_add, List.map_append]⟩`.
-/
lemma Ls_add (n : ℕ) (T : Finset ℕ) (b t p q : ℕ) :
    ∃ rest, Ls n T b t (p + q) = Ls n T b t p ++ rest :=
  ⟨_, by unfold Ls; rw [List.range_add, List.map_append]⟩

def init (K : ℕ) (ev : Bool) : St := if K = 0 then .bad else .run K 0 0 true ev

/- English proof (translation)
Unfold `CondB at h`. Use `push_neg at h`. Take `⟨b, e, hb, he, hcount, hno⟩` from `h`. Establish `hex : ∃ d, d ≤ e ∧ (b + d) % n ∈ T`. Establish `hpos : 0 < ((Finset.range (e + 1)).filter fun d => (b + d) % n ∈ T).card` using `by omega`.

Take `⟨d, hd⟩` from `Finset.card_pos.1 hpos`. Rewrite `hd` using `[Finset.mem_filter, Finset.mem_range]`. Conclude with `⟨d, by omega, hd.2⟩`. Set `d₀` to `Nat.find hex`. Establish `hd₀ : d₀ ≤ e ∧ (b + d₀) % n ∈ T` using `Nat.find_spec hex`.

Establish `hmin : ∀ d < d₀, (b + d) % n ∉ T`. Introduce `d hd hdT`. Conclude with `Nat.find_min hex hd ⟨by omega, hdT⟩`. Establish `hi : (b + d₀) % n < n` using `Nat.mod_lt _ (by omega)`. Use `⟨(b + d₀) % n, hi, hd₀.2, ?_⟩` and prove the remaining obligations.

Establish `hevi : decide (Even ((b + d₀) % n)) = decide (Even (b + d₀))`. Simplify using `only [even_mod hn]`. Distinguish the cases in `hK0 : K₀ = 0`. Simplify using `only [init, hK0, if_true]`. Conclude with `runS_bad _`.

Rewrite using `[init, if_neg hK0, hevi]`. Establish `hR : 1 ≤ 3 * r` using `by omega`. Establish `hinit : Inv n T L₂ (3 * r) b K₀ d₀ (.run K₀ 0 0 true (decide (Even (b + d₀))))`. Use `⟨by omega, le_rfl, by omega, Nat.zero_le _, rfl, by simpa using hd₀.2, fun x h1 h2 => by omega, ?_, fun _ => ⟨Fin.elim0, PRun_zero _ _ _ _ _ _ _⟩⟩` and prove the remaining obligations. Establish `: (Finset.range (d₀ + 1)).filter (fun d => (b + d) % n ∈ T) = {d₀}`.

Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Assume the negation of the conclusion as `hne`.

Conclude with `hmin x (by omega) h2`. Introduce and unpack `rfl; exact ⟨by omega, hd₀.2⟩`. Unfold `cnt`. Rewrite using `[this, Finset.card_singleton]`. Simplify using the standard rewrite rules.

Establish `hI` using `inv_iter hn hR (e - d₀) d₀ _ hinit`. Rewrite `hI` using `[show d₀ + (e - d₀) = e by omega]`. Establish `hL : (Lst n ((b + d₀) % n)).map (fun p => decide (p ∈ T)) = Ls n T b d₀ (n - 1)`. Unfold `Lst Ls`. Rewrite using `[List.map_map]`.

Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `x _`. Simplify using `only [Function.comp_apply]`. Rewrite using `[add_assoc, Nat.mod_add_mod, show b + d₀ + (x + 1) = b + (d₀ + 1 + x) by omega]`. Rewrite using `[hL, show n - 1 = (e - d₀) + (n - 1 - (e - d₀)) by omega]`.

Take `⟨rest, hrest⟩` from `Ls_add n T b d₀ (e - d₀) (n - 1 - (e - d₀))`. Rewrite using `[hrest, runS_append]`. Generalize the expression as in `runS (3 * r) L₂ (St.run K₀ 0 0 true (decide (Even (b + d₀)))) (Ls n T b d₀ (e - d₀)) = st at hI ⊢`. Consider the cases of `st with`. Consider the case `bad => exact runS_bad _`.

Consider the case `good => exact absurd hI hno`. Consider the case `run K j d al ev`. It suffices to derive a contradiction. Take `⟨hK1, hK2, hj, -, -, -, -, hc, -⟩` from `hI`. Establish `hce : N₁ ≤ cnt n T b e` using `hcount`.

Establish `hm : 3 * r * (K₀ - K) + 3 * r ≤ 3 * r * K₀`. Rewrite using `[← mul_add_one]; exact Nat.mul_le_mul_left _ (by omega)`. Use linear arithmetic over natural numbers and integers.
-/
theorem comb {n : ℕ} (hn2 : 2 ≤ n) (hn : Even n) {L₂ r N₁ : ℕ} (hr : 1 ≤ r) (K₀ : ℕ)
    (hK : 1 + 3 * r * K₀ ≤ N₁) (T : Finset ℕ) (h : ¬ CondB n T L₂ r N₁) :
    ∃ i < n, i ∈ T ∧
      runS (3 * r) L₂ (init K₀ (decide (Even i))) ((Lst n i).map (fun p => decide (p ∈ T))) = .bad := by
  unfold CondB at h
  push_neg at h
  obtain ⟨b, e, hb, he, hcount, hno⟩ := h
  have hex : ∃ d, d ≤ e ∧ (b + d) % n ∈ T := by
    have hpos : 0 < ((Finset.range (e + 1)).filter fun d => (b + d) % n ∈ T).card := by omega
    obtain ⟨d, hd⟩ := Finset.card_pos.1 hpos
    rw [Finset.mem_filter, Finset.mem_range] at hd
    exact ⟨d, by omega, hd.2⟩
  classical
  let d₀ := Nat.find hex
  have hd₀ : d₀ ≤ e ∧ (b + d₀) % n ∈ T := Nat.find_spec hex
  have hmin : ∀ d < d₀, (b + d) % n ∉ T := by
    intro d hd hdT
    exact Nat.find_min hex hd ⟨by omega, hdT⟩
  have hi : (b + d₀) % n < n := Nat.mod_lt _ (by omega)
  refine ⟨(b + d₀) % n, hi, hd₀.2, ?_⟩
  have hevi : decide (Even ((b + d₀) % n)) = decide (Even (b + d₀)) := by
    simp only [even_mod hn]
  by_cases hK0 : K₀ = 0
  · simp only [init, hK0, if_true]; exact runS_bad _
  rw [init, if_neg hK0, hevi]
  have hR : 1 ≤ 3 * r := by omega
  have hinit : Inv n T L₂ (3 * r) b K₀ d₀ (.run K₀ 0 0 true (decide (Even (b + d₀)))) := by
    refine ⟨by omega, le_rfl, by omega, Nat.zero_le _, rfl, by simpa using hd₀.2,
      fun x h1 h2 => by omega, ?_, fun _ => ⟨Fin.elim0, PRun_zero _ _ _ _ _ _ _⟩⟩
    have : (Finset.range (d₀ + 1)).filter (fun d => (b + d) % n ∈ T) = {d₀} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        by_contra hne
        exact hmin x (by omega) h2
      · rintro rfl; exact ⟨by omega, hd₀.2⟩
    unfold cnt
    rw [this, Finset.card_singleton]
    simp
  have hI := inv_iter hn hR (e - d₀) d₀ _ hinit
  rw [show d₀ + (e - d₀) = e by omega] at hI
  have hL : (Lst n ((b + d₀) % n)).map (fun p => decide (p ∈ T)) = Ls n T b d₀ (n - 1) := by
    unfold Lst Ls
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    rw [add_assoc, Nat.mod_add_mod, show b + d₀ + (x + 1) = b + (d₀ + 1 + x) by omega]
  rw [hL, show n - 1 = (e - d₀) + (n - 1 - (e - d₀)) by omega]
  obtain ⟨rest, hrest⟩ := Ls_add n T b d₀ (e - d₀) (n - 1 - (e - d₀))
  rw [hrest, runS_append]
  generalize runS (3 * r) L₂ (St.run K₀ 0 0 true (decide (Even (b + d₀)))) (Ls n T b d₀ (e - d₀)) = st at hI ⊢
  cases st with
  | bad => exact runS_bad _
  | good => exact absurd hI hno
  | run K j d al ev =>
    exfalso
    obtain ⟨hK1, hK2, hj, -, -, -, -, hc, -⟩ := hI
    have hce : N₁ ≤ cnt n T b e := hcount
    have hm : 3 * r * (K₀ - K) + 3 * r ≤ 3 * r * K₀ := by
      rw [← mul_add_one]; exact Nat.mul_le_mul_left _ (by omega)
    omega

end Formalism.G0.TopsWeightFunctionBounds

noncomputable section
open scoped BigOperators

namespace Formalism.G0.TopsWeightFunctionBounds

/- English proof (translation)
Unfold `init`. Use `split_ifs`. Conclude with `True.intro`. Use `show 0 < R`. Use linear arithmetic over natural numbers and integers.
-/
lemma WF_init {R : ℕ} (hR : 1 ≤ R) (K : ℕ) (ev : Bool) : WF R (init K ev) := by
  unfold init
  split_ifs
  · exact True.intro
  · show 0 < R; omega

/- English proof (translation)
Unfold `init`. Use `split_ifs with hK`. Substitute `hK` using the available equality. Simplify using `[Phi]`. Conclude with `Phi_init h0 hL hLδ hR (by omega) ev`.
-/
lemma Phi_init' {R L₂ : ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1)
    (hR : 1 ≤ R) (K : ℕ) (ev : Bool) :
    Phi R L₂ δ (init K ev) ≤ (1 - aF L₂ δ ^ R) ^ K := by
  unfold init
  split_ifs with hK
  · subst hK; simp [Phi]
  · exact Phi_init h0 hL hLδ hR (by omega) ev

/- English proof (translation)
Use `split_ifs`. Apply the tactic sequence `exact Finset.prod_nonneg (fun p _ => by unfold wP; split_ifs <;> linarith)`. Conclude with `le_rfl`.
-/
lemma term_nonneg {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (P : Prop) [Decidable P] (T : Finset ℕ) (n : ℕ) :
    0 ≤ (if P then ∏ p ∈ Finset.range n, wP δ T p else 0) := by
  split_ifs
  · exact Finset.prod_nonneg (fun p _ => by unfold wP; split_ifs <;> linarith)
  · exact le_rfl

/- English proof (translation)
Introduce `n δ L₂ r N₁ hn hev hδ hL hLδ hr hN`. Establish `h1` using `d_le_one hδ hL hLδ`. Establish `hR : 1 ≤ 3 * r` using `by omega`. Establish `hk1 : 0 < N₁ / (3 * r)` using `Nat.div_pos hN (by omega)`. Establish `hK : 1 + 3 * r * (N₁ / (3 * r) - 1) ≤ N₁`.

Establish `a1 : 3 * r * (N₁ / (3 * r)) ≤ N₁` using `Nat.mul_div_le N₁ (3 * r)`. Establish `a2 : 3 * r * (N₁ / (3 * r) - 1) + 3 * r = 3 * r * (N₁ / (3 * r))`. Rewrite using `[← mul_add_one]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Generalize the expression as in `3 * r * (N₁ / (3 * r) - 1) = X at a2 ⊢`. Generalize the expression as in `3 * r * (N₁ / (3 * r)) = Y at a1 a2`. Use linear arithmetic over natural numbers and integers. Establish `hq : (1 - (1 / 2 : ℝ) ^ (3 * r) * (1 - L₂ * δ) ^ (3 * r)) = 1 - aF L₂ δ ^ (3 * r)`. Unfold `aF`.

Rewrite using `[mul_pow]`. Rewrite using `[hq]`. Establish `hc0 : 0 ≤ 1 - aF L₂ δ ^ (3 * r)` using `c_nonneg hδ hLδ`. Break down `hδ.eq_or_lt with hδ0 | hδpos` into its components or cases. Establish `hz : condProb n δ (fun T => ¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) = 0`.

Unfold `condProb`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `T _`. Use `split_ifs with h`. Establish `: 2 ≤ T.card` using `by have := h.2.2; omega`.

Rewrite using `[← hδ0, zero_pow (by omega), zero_mul]`. Both sides reduce to the same expression. Rewrite using `[hz]`. Conclude with `mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc0 _)`. Apply `le_of_mul_le_mul_left _ hδpos set K := N₁ / (3 * r) - 1 with hKdef` to reduce the goal to its premises.

Establish `step1 : δ * condProb n δ (fun T => ¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) ≤ ∑ i ∈ Finset.range n, ∑ T ∈ (Finset.range n).powerset, (if i ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even i))) ((Lst n i).map (fun p => decide (p ∈ T))) = .bad then ∏ p ∈ Finset.range n, wP δ T p else 0)`. Rewrite using `[Finset.sum_comm]`. Unfold `condProb`. Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `T hT`. Use `split_ifs with hA`. Take `⟨i, hi, hiT, hrun⟩` from `comb (by omega) hev hr K hK T hA.2.1`. Establish `hprod` using `prod_wP (δ := δ) n T (Finset.mem_powerset.1 hT)`. Establish `hc : 1 ≤ T.card` using `Finset.card_pos.2 ⟨0, hA.1⟩`.

Establish `hle : (if i ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even i))) ((Lst n i).map (fun p => decide (p ∈ T))) = .bad then ∏ p ∈ Finset.range n, wP δ T p else 0) ≤ ∑ j ∈ Finset.range n, (if j ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even j))) ((Lst n j).map (fun p => decide (p ∈ T))) = .ba …` using `Finset.single_le_sum (f := fun j => if j ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even j))) ((Lst n j).map (fun p => decide (p ∈ T))) = .bad then ∏ p ∈ Finset.range n, wP δ T p else 0) (fun j _ => term_nonneg hδ h1 _ T n) (Finset.mem_range.2 hi)`. Rewrite `hle` using `[if_pos ⟨hiT, hrun⟩]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hprod, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hc]`. Use `_ ≤ _ := hle`.

Rewrite using `[mul_zero]`. Conclude with `Finset.sum_nonneg (fun j _ => term_nonneg hδ h1 _ T n)`. Establish `step2 : ∑ i ∈ Finset.range n, ∑ T ∈ (Finset.range n).powerset, (if i ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even i))) ((Lst n i).map (fun p => decide (p ∈ T))) = .bad then ∏ p ∈ Finset.range n, wP δ T p else 0) ≤ ∑ i ∈ Finset.range n, δ * (1 - aF L₂ δ ^ (3 * r)) ^ K`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i hi`.

Rewrite using `[sum_event (Finset.mem_range.1 hi)]`. Apply `mul_le_mul_of_nonneg_left _ hδ` to reduce the goal to its premises. Conclude with `(Wt_le hδ hL hLδ hR (n - 1) _ (WF_init hR K _)).trans (Phi_init' hδ hL hLδ hR K _)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_range, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : TopsChoiceSecondBound := by
  intro n δ L₂ r N₁ hn hev hδ hL hLδ hr hN
  have h1 := d_le_one hδ hL hLδ
  have hR : 1 ≤ 3 * r := by omega
  have hk1 : 0 < N₁ / (3 * r) := Nat.div_pos hN (by omega)
  have hK : 1 + 3 * r * (N₁ / (3 * r) - 1) ≤ N₁ := by
    have a1 : 3 * r * (N₁ / (3 * r)) ≤ N₁ := Nat.mul_div_le N₁ (3 * r)
    have a2 : 3 * r * (N₁ / (3 * r) - 1) + 3 * r = 3 * r * (N₁ / (3 * r)) := by
      rw [← mul_add_one]; congr 1; omega
    generalize 3 * r * (N₁ / (3 * r) - 1) = X at a2 ⊢
    generalize 3 * r * (N₁ / (3 * r)) = Y at a1 a2
    omega
  have hq : (1 - (1 / 2 : ℝ) ^ (3 * r) * (1 - L₂ * δ) ^ (3 * r)) = 1 - aF L₂ δ ^ (3 * r) := by
    unfold aF; rw [mul_pow]
  rw [hq]
  have hc0 : 0 ≤ 1 - aF L₂ δ ^ (3 * r) := c_nonneg hδ hLδ
  rcases hδ.eq_or_lt with hδ0 | hδpos
  · have hz : condProb n δ (fun T => ¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) = 0 := by
      unfold condProb
      apply Finset.sum_eq_zero
      intro T _
      split_ifs with h
      · have : 2 ≤ T.card := by have := h.2.2; omega
        rw [← hδ0, zero_pow (by omega), zero_mul]
      · rfl
    rw [hz]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc0 _)
  · apply le_of_mul_le_mul_left _ hδpos
    set K := N₁ / (3 * r) - 1 with hKdef
    have step1 : δ * condProb n δ (fun T => ¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) ≤
        ∑ i ∈ Finset.range n, ∑ T ∈ (Finset.range n).powerset,
          (if i ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even i)))
              ((Lst n i).map (fun p => decide (p ∈ T))) = .bad then
            ∏ p ∈ Finset.range n, wP δ T p else 0) := by
      rw [Finset.sum_comm]
      unfold condProb
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro T hT
      split_ifs with hA
      · obtain ⟨i, hi, hiT, hrun⟩ := comb (by omega) hev hr K hK T hA.2.1
        have hprod := prod_wP (δ := δ) n T (Finset.mem_powerset.1 hT)
        have hc : 1 ≤ T.card := Finset.card_pos.2 ⟨0, hA.1⟩
        have hle : (if i ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even i)))
              ((Lst n i).map (fun p => decide (p ∈ T))) = .bad then
            ∏ p ∈ Finset.range n, wP δ T p else 0) ≤
            ∑ j ∈ Finset.range n, (if j ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even j)))
              ((Lst n j).map (fun p => decide (p ∈ T))) = .bad then
            ∏ p ∈ Finset.range n, wP δ T p else 0) :=
          Finset.single_le_sum (f := fun j => if j ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even j)))
              ((Lst n j).map (fun p => decide (p ∈ T))) = .bad then
            ∏ p ∈ Finset.range n, wP δ T p else 0)
            (fun j _ => term_nonneg hδ h1 _ T n) (Finset.mem_range.2 hi)
        rw [if_pos ⟨hiT, hrun⟩] at hle
        calc δ * (δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card))
            = ∏ p ∈ Finset.range n, wP δ T p := by
              rw [hprod, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hc]
          _ ≤ _ := hle
      · rw [mul_zero]
        exact Finset.sum_nonneg (fun j _ => term_nonneg hδ h1 _ T n)
    have step2 : ∑ i ∈ Finset.range n, ∑ T ∈ (Finset.range n).powerset,
          (if i ∈ T ∧ runS (3 * r) L₂ (init K (decide (Even i)))
              ((Lst n i).map (fun p => decide (p ∈ T))) = .bad then
            ∏ p ∈ Finset.range n, wP δ T p else 0) ≤
        ∑ i ∈ Finset.range n, δ * (1 - aF L₂ δ ^ (3 * r)) ^ K := by
      apply Finset.sum_le_sum
      intro i hi
      rw [sum_event (Finset.mem_range.1 hi)]
      apply mul_le_mul_of_nonneg_left _ hδ
      exact (Wt_le hδ hL hLδ hR (n - 1) _ (WF_init hR K _)).trans (Phi_init' hδ hL hLδ hR K _)
    calc δ * condProb n δ (fun T => ¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) ≤ _ := step1
      _ ≤ _ := step2
      _ = δ * (n * (1 - aF L₂ δ ^ (3 * r)) ^ K) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end Formalism.G0.TopsWeightFunctionBounds

namespace Formalism.G0

/- English proof (translation)
The claim follows from `TopsWeightFunctionBounds.main`.
-/
theorem tops_choice_part_b : TopsChoiceSecondBound := TopsWeightFunctionBounds.main

end Formalism.G0
