import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism.Per Filter Topology
open scoped Formalism.Per

namespace GlobalTheory.PSer.Laws

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Simplify using `[pw]`.
-/
theorem pw_zero (x : Fl l) : pw 0 x = x := by simp [pw]

/- English proof (translation)
Unfold `pw`. Rewrite using `[add_comm, zpow_add, zpow_one]`. Both sides reduce to the same expression.
-/
theorem pw_succ (k : ℤ) (x : Fl l) : pw (k + 1) x = pw k x ^ l := by
  unfold pw
  rw [add_comm, zpow_add, zpow_one]
  rfl

/- English proof (translation)
Unfold `pw`. Rewrite using `[zpow_add]`. Both sides reduce to the same expression.
-/
theorem pw_add (a b : ℤ) (x : Fl l) : pw (a + b) x = pw a (pw b x) := by
  unfold pw
  rw [zpow_add]
  rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [pw_zero]`. Consider the case `succ n ih => rw [Nat.cast_succ, pw_succ, ih, ← pow_mul, pow_succ]`.
-/
theorem pw_nat (n : ℕ) (x : Fl l) : pw (n : ℤ) x = x ^ l ^ n := by
  induction n with
  | zero => simp [pw_zero]
  | succ n ih => rw [Nat.cast_succ, pw_succ, ih, ← pow_mul, pow_succ]

/- English proof (translation)
Unfold `sh`. Rewrite using `[map_pow]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem sh_pow (x : Fl l) (n : ℕ) : sh (x ^ n) = sh x ^ n := by
  unfold sh
  rw [map_pow]; push_cast; rfl

/- English proof (translation)
Conclude with `(Fact.out : l.Prime).pos` after adjusting the coercions.
-/
theorem l_pos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
/- English proof (translation)
Conclude with `(Fact.out : l.Prime).two_le` after adjusting the coercions.
-/
theorem two_le_l : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le

/- English proof (translation)
Establish `hl` using `l_pos (l := l)`. Proceed by induction on `k using Int.induction_on with`. Consider the case `zero => simp [pw_zero]`. Consider the case `succ k ih`. Rewrite using `[pw_succ, sh_pow, norm_pow, ih, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), zpow_add_one₀ hl.ne']`.

Consider the case `pred k ih`. Establish `h1 : pw (-(k : ℤ)) x = pw (-(k : ℤ) - 1) x ^ l`. Rewrite using `[← pw_succ]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `ih` using `[h1, sh_pow, norm_pow]`. Establish `h2 : (‖sh x‖ ^ ((l : ℝ) ^ (-(k : ℤ) - 1))) ^ l = ‖sh x‖ ^ ((l : ℝ) ^ (-(k : ℤ)))`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← zpow_add_one₀ hl.ne']`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `ih` using `[← h2]`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _) (Fact.out : l.Prime).ne_zero).1 ih`.
-/
theorem norm_sh_pw (k : ℤ) (x : Fl l) : ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k) := by
  have hl := l_pos (l := l)
  induction k using Int.induction_on with
  | zero => simp [pw_zero]
  | succ k ih =>
    rw [pw_succ, sh_pow, norm_pow, ih, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
      zpow_add_one₀ hl.ne']
  | pred k ih =>
    have h1 : pw (-(k : ℤ)) x = pw (-(k : ℤ) - 1) x ^ l := by
      rw [← pw_succ]; congr 1; ring
    rw [h1, sh_pow, norm_pow] at ih
    have h2 : (‖sh x‖ ^ ((l : ℝ) ^ (-(k : ℤ) - 1))) ^ l = ‖sh x‖ ^ ((l : ℝ) ^ (-(k : ℤ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← zpow_add_one₀ hl.ne']
      congr 2; ring
    rw [← h2] at ih
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
      (Fact.out : l.Prime).ne_zero).1 ih

/- English proof (translation)
Rewrite using `[GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]`. Simplify using the standard rewrite rules.
-/
theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]; simp

def sz (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (n : ℤ) : ℝ :=
  ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))

/- English proof (translation)
Rewrite using `[norm_mul, norm_zpow, norm_sh_pw]`. Both sides reduce to the same expression.
-/
theorem norm_term (h j : ℕ) (x : Fl l) (n : ℤ) :
    ‖(l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)‖ = sz l h j ‖sh x‖ n := by
  rw [norm_mul, norm_zpow, norm_sh_pw]; rfl

/- English proof (translation)
The claim follows from `mul_nonneg (zpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hr _)`.
-/
theorem sz_nonneg (h j : ℕ) {r : ℝ} (hr : 0 ≤ r) (n : ℤ) : 0 ≤ sz l h j r n :=
  mul_nonneg (zpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hr _)

/- English proof (translation)
The claim follows from `mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr hrs (zpow_nonneg l_pos.le _)) (zpow_nonneg (norm_nonneg _) _)`.
-/
theorem sz_mono (h j : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (n : ℤ) :
    sz l h j r n ≤ sz l h j s n :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr hrs (zpow_nonneg l_pos.le _))
    (zpow_nonneg (norm_nonneg _) _)

/- English proof (translation)
Establish `hl` using `l_pos (l := l)`. Establish `hl2` using `two_le_l (l := l)`. Rewrite using `[Int.cofinite_eq, tendsto_sup]`. Prove the components needed by the constructor for the conclusion. Establish `hb : Tendsto (fun n : ℤ => (l : ℝ) ^ n) atBot (𝓝 0)`.

Use `(tendsto_rpow_atBot_of_base_gt_one (l : ℝ) (by linarith)).comp ((tendsto_intCast_atBot_iff (R := ℝ)).2 (tendsto_id (α := ℤ) (x := atBot)))` as an intermediate fact. Use `this.congr fun n => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `squeeze_zero (sz_nonneg h j hr) (fun n => ?_) hb` and prove the remaining obligations. Unfold `sz`.

Rewrite using `[norm_l, inv_zpow', neg_neg]`. Conclude with `mul_le_of_le_one_right (zpow_nonneg hl.le _) (Real.rpow_le_one hr hr1.le (zpow_nonneg hl.le _))`. Rewrite using `[← Nat.map_cast_int_atTop, tendsto_map'_iff]`. Establish `h1 : Tendsto (fun n : ℕ => l ^ n) atTop atTop` using `tendsto_pow_atTop_atTop_of_one_lt (Fact.out : l.Prime).one_lt`. Establish `h2` using `(tendsto_self_mul_const_pow_of_lt_one hr hr1).comp h1`.

Use `squeeze_zero (fun n => sz_nonneg h j hr _) (fun n => ?_) h2` and prove the remaining obligations. Simplify using `only [Function.comp, sz]`. Rewrite using `[norm_l, inv_zpow', neg_neg, zpow_natCast, Nat.cast_pow]`. Use `mul_le_mul_of_nonneg_left ?_ (pow_nonneg hl.le _)` and prove the remaining obligations. Establish `: ((n : ℤ) * h + j : ℤ) = ((n * h + j : ℕ) : ℤ)` using `by push_cast; ring`.

Rewrite using `[this, zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]`. Use `pow_le_pow_of_le_one hr hr1.le (Nat.pow_le_pow_right (Fact.out : l.Prime).pos ?_)` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem tendsto_sz {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (sz l h j r) cofinite (𝓝 0) := by
  have hl := l_pos (l := l)
  have hl2 := two_le_l (l := l)
  rw [Int.cofinite_eq, tendsto_sup]
  constructor
  · have hb : Tendsto (fun n : ℤ => (l : ℝ) ^ n) atBot (𝓝 0) := by
      have := (tendsto_rpow_atBot_of_base_gt_one (l : ℝ) (by linarith)).comp
        ((tendsto_intCast_atBot_iff (R := ℝ)).2 (tendsto_id (α := ℤ) (x := atBot)))
      refine this.congr fun n => ?_
      simp
    refine squeeze_zero (sz_nonneg h j hr) (fun n => ?_) hb
    unfold sz
    rw [norm_l, inv_zpow', neg_neg]
    exact mul_le_of_le_one_right (zpow_nonneg hl.le _)
      (Real.rpow_le_one hr hr1.le (zpow_nonneg hl.le _))
  · rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
    have h1 : Tendsto (fun n : ℕ => l ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (Fact.out : l.Prime).one_lt
    have h2 := (tendsto_self_mul_const_pow_of_lt_one hr hr1).comp h1
    refine squeeze_zero (fun n => sz_nonneg h j hr _) (fun n => ?_) h2
    simp only [Function.comp, sz]
    rw [norm_l, inv_zpow', neg_neg, zpow_natCast, Nat.cast_pow]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hl.le _)
    have : ((n : ℤ) * h + j : ℤ) = ((n * h + j : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
    refine pow_le_pow_of_le_one hr hr1.le (Nat.pow_le_pow_right (Fact.out : l.Prime).pos ?_)
    nlinarith

/- English proof (translation)
Apply `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` to reduce the goal to its premises. Rewrite using `[tendsto_zero_iff_norm_tendsto_zero]`. Simplify using `only [norm_term]`. Conclude with `tendsto_sz hh j (norm_nonneg _) hx`.
-/
theorem summable_lam {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {x : Fl l} (hx : ‖sh x‖ < 1) :
    Summable fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_term]
  exact tendsto_sz hh j (norm_nonneg _) hx

/- English proof (translation)
The claim follows from `(tendsto_sz hh j hr hr1).bddAbove_range_of_cofinite`.
-/
theorem bdd_sz {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    BddAbove (Set.range (sz l h j r)) :=
  (tendsto_sz hh j hr hr1).bddAbove_range_of_cofinite

/- English proof (translation)
The claim follows from `Real.iSup_nonneg (sz_nonneg h j hr)`.
-/
theorem gam_nonneg (h j : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ gam l h j r :=
  Real.iSup_nonneg (sz_nonneg h j hr)

/- English proof (translation)
Establish `h0 : 0 ≤ r` using `(norm_nonneg _).trans hx`. Use `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (gam_nonneg h j h0) fun n => ?_` and prove the remaining obligations. Rewrite using `[norm_term]`. Conclude with `(sz_mono h j (norm_nonneg _) hx n).trans (le_ciSup (bdd_sz hh j h0 hr) n)`.
-/
theorem norm_lam_le {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {x : Fl l} {r : ℝ} (hx : ‖sh x‖ ≤ r) (hr : r < 1) :
    ‖lam h j x‖ ≤ gam l h j r := by
  have h0 : 0 ≤ r := (norm_nonneg _).trans hx
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (gam_nonneg h j h0) fun n => ?_
  rw [norm_term]
  exact (sz_mono h j (norm_nonneg _) hx n).trans (le_ciSup (bdd_sz hh j h0 hr) n)

/- English proof (translation)
Unfold `lam`. Rewrite using `[← tsum_mul_left, ← (Equiv.addRight (1 : ℤ)).tsum_eq (fun n : ℤ => (l : ℂ_[l]) * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)))]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Establish `h1 : (n * h + ((j + h : ℕ) : ℤ)) = (n + 1) * h + j` using `by push_cast; ring`. Simplify using `only [Equiv.coe_addRight]`.

Rewrite using `[h1, ← mul_assoc, ← zpow_one_add₀ GlobalTheory.RingBasics.p_ne_zero]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lam_shift (h j : ℕ) (x : Fl l) : lam h (j + h) x = l * lam h j x := by
  unfold lam
  rw [← tsum_mul_left, ← (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun n : ℤ => (l : ℂ_[l]) * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)))]
  refine tsum_congr fun n => ?_
  have h1 : (n * h + ((j + h : ℕ) : ℤ)) = (n + 1) * h + j := by push_cast; ring
  simp only [Equiv.coe_addRight]
  rw [h1, ← mul_assoc, ← zpow_one_add₀ GlobalTheory.RingBasics.p_ne_zero]
  congr 2; ring

/- English proof (translation)
Unfold `lam`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[← pw_nat, ← pw_add]`. Use `congr 3`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lam_pow (h j k : ℕ) (x : Fl l) : lam h j (x ^ l ^ k) = lam h (j + k) x := by
  unfold lam
  refine tsum_congr fun n => ?_
  rw [← pw_nat, ← pw_add]
  congr 3
  push_cast; ring

end GlobalTheory.PSer.Laws

namespace GlobalTheory.PSer

open Laws

/- English proof (translation)
Introduce `l _ h j r x hh hr hx`. Use `⟨(summable_lam hh j (hx.trans_lt hr)).hasSum, norm_lam_le hh j hx hr, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[lam_pow, lam_shift]`. Use `lam_pow (l := l) h j 1 x` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis.
-/
theorem lam_hasSum_norm_le_frob : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x : Fl l), 1 ≤ h → r < 1 →
    ‖sh x‖ ≤ r → HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)) (lam h j x) ∧
      ‖lam h j x‖ ≤ gam l h j r ∧ lam h j (x ^ l ^ h) = (l : ℂ_[l]) * lam h j x ∧
      lam h j (x ^ l) = lam h (j + 1) x := by
  intro l _ h j r x hh hr hx
  refine ⟨(summable_lam hh j (hx.trans_lt hr)).hasSum, norm_lam_le hh j hx hr, ?_, ?_⟩
  · rw [lam_pow, lam_shift]
  · have := lam_pow (l := l) h j 1 x
    rwa [pow_one] at this

end GlobalTheory.PSer

end
