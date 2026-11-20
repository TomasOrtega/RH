import Formalism.IncomingBounds.LevelTail
import Formalism.IncomingBounds.FrobOrbitPeriod

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

/- English proof (translation)
Establish `hl0 : 0 < l` using `by linarith`. Establish `hq0 : 0 ≤ l⁻¹` using `inv_nonneg.mpr hl0.le`. Establish `hq1 : l⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl`. Use `Summable.of_norm_bounded (g := fun k : ℕ => (∑ i, |u i|) * l⁻¹ * (l⁻¹) ^ k) ((summable_geometric_of_lt_one hq0 hq1).mul_left _) ?_` and prove the remaining obligations. Introduce `k`.

Establish `h1 : |u (e k)| ≤ ∑ i, |u i|` using `Finset.single_le_sum (f := fun i => |u i|) (fun i _ => abs_nonneg _) (Finset.mem_univ _)`. Establish `h2 : (l ^ (k + 1))⁻¹ = l⁻¹ * l⁻¹ ^ k` using `by rw [← pow_succ', inv_pow]`. Rewrite using `[Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hl0 _), div_eq_mul_inv, h2, ← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hq0) (by positivity)`.
-/
private lemma summable_div_pow_succ {ι : Type} [Fintype ι] (l : ℝ) (hl : 1 < l)
    (u : ι → ℝ) (e : ℕ → ι) : Summable (fun k : ℕ => u (e k) / l ^ (k + 1)) := by
  have hl0 : 0 < l := by linarith
  have hq0 : 0 ≤ l⁻¹ := inv_nonneg.mpr hl0.le
  have hq1 : l⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  refine Summable.of_norm_bounded (g := fun k : ℕ => (∑ i, |u i|) * l⁻¹ * (l⁻¹) ^ k)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left _) ?_
  intro k
  have h1 : |u (e k)| ≤ ∑ i, |u i| :=
    Finset.single_le_sum (f := fun i => |u i|) (fun i _ => abs_nonneg _) (Finset.mem_univ _)
  have h2 : (l ^ (k + 1))⁻¹ = l⁻¹ * l⁻¹ ^ k := by rw [← pow_succ', inv_pow]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hl0 _), div_eq_mul_inv, h2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hq0) (by positivity)

/- English proof (translation)
Rewrite using `[mul_comm, pow_mul, inv_pow]`.
-/
private lemma inv_pow_succ_mul (p : ℝ) (k n : ℕ) : (p ^ ((n + 1) * k))⁻¹ = ((p ^ k)⁻¹) ^ (n + 1) := by
  rw [mul_comm, pow_mul, inv_pow]

/- English proof (translation)
Establish `hpk : 1 < p ^ k` using `one_lt_pow₀ hp (by omega)`. Establish `hq0 : 0 ≤ (p ^ k)⁻¹` using `inv_nonneg.mpr (by linarith)`. Establish `hq1 : (p ^ k)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hpk`. Use `Summable.of_norm_bounded (g := fun n : ℕ => M * ((p ^ k)⁻¹ * ((p ^ k)⁻¹) ^ n)) (((summable_geometric_of_lt_one hq0 hq1).mul_left _).mul_left _) ?_` and prove the remaining obligations. Introduce `n`.

Rewrite using `[Real.norm_eq_abs, abs_mul, inv_pow_succ_mul, abs_of_nonneg (pow_nonneg hq0 _), ← pow_succ', mul_comm M]`. Conclude with `mul_le_mul_of_nonneg_left (hb n) (pow_nonneg hq0 _)`.
-/
private lemma summable_inv_pow_mul_of_bounded (p : ℝ) (hp : 1 < p) (k : ℕ) (hk : 1 ≤ k) (b : ℕ → ℝ)
    (M : ℝ) (hb : ∀ n, |b n| ≤ M) : Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * b n) := by
  have hpk : 1 < p ^ k := one_lt_pow₀ hp (by omega)
  have hq0 : 0 ≤ (p ^ k)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (p ^ k)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpk
  refine Summable.of_norm_bounded (g := fun n : ℕ => M * ((p ^ k)⁻¹ * ((p ^ k)⁻¹) ^ n))
    (((summable_geometric_of_lt_one hq0 hq1).mul_left _).mul_left _) ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul, inv_pow_succ_mul, abs_of_nonneg (pow_nonneg hq0 _), ← pow_succ',
    mul_comm M]
  exact mul_le_mul_of_nonneg_left (hb n) (pow_nonneg hq0 _)

/- English proof (translation)
Introduce `q`. Proceed by induction on `q with`. Consider the case `zero => simp`. Consider the case `succ q ih => rw [Nat.mul_succ, pow_add φ (f * q) f, Equiv.Perm.mul_apply, hf, ih]`.
-/
private lemma pow_mul_apply_eq_self {α : Type} (φ : Equiv.Perm α) (τ : α) (f : ℕ)
    (hf : (φ ^ f) τ = τ) : ∀ q : ℕ, (φ ^ (f * q)) τ = τ := by
  intro q
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, pow_add φ (f * q) f, Equiv.Perm.mul_apply, hf, ih]

/- English proof (translation)
Use `conv_lhs => rw [← Nat.mod_add_div m f]`. Rewrite using `[pow_add φ (m % f) (f * (m / f)), Equiv.Perm.mul_apply, pow_mul_apply_eq_self φ τ f hf]`.
-/
private lemma pow_apply_eq_pow_mod_apply {α : Type} (φ : Equiv.Perm α) (τ : α) (f : ℕ)
    (hf : (φ ^ f) τ = τ) (m : ℕ) : (φ ^ m) τ = (φ ^ (m % f)) τ := by
  conv_lhs => rw [← Nat.mod_add_div m f]
  rw [pow_add φ (m % f) (f * (m / f)), Equiv.Perm.mul_apply, pow_mul_apply_eq_self φ τ f hf]

/- English proof (translation)
Establish `h` using `Nat.mod_add_div x d`. Establish `hq : Even (d * (x / d))` using `hd.mul_right _`. Prove the components needed by the constructor for the conclusion. Introduce `hm`. Rewrite using `[← h]`.

Conclude with `hm.add hq`. Introduce `hx`. Rewrite `hx` using `[← h]`. Conclude with `(Nat.even_add.mp hx).mpr hq`.
-/
private lemma even_mod_iff_of_even {d : ℕ} (hd : Even d) (x : ℕ) : Even (x % d) ↔ Even x := by
  have h := Nat.mod_add_div x d
  have hq : Even (d * (x / d)) := hd.mul_right _
  constructor
  · intro hm; rw [← h]; exact hm.add hq
  · intro hx
    rw [← h] at hx
    exact (Nat.even_add.mp hx).mpr hq

/- English proof (translation)
Rewrite using `[ZMod.val_add, even_mod_iff_of_even hd, ZMod.val_natCast, Nat.even_add, even_mod_iff_of_even hd]`. Conclude with `⟨fun h => h.mp ha, fun h => iff_of_true ha h⟩`.
-/
private lemma even_val_add_natCast_iff {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) (ha : Even a.val)
    (n : ℕ) : Even (a + (n : ZMod d)).val ↔ Even n := by
  rw [ZMod.val_add, even_mod_iff_of_even hd, ZMod.val_natCast, Nat.even_add, even_mod_iff_of_even hd]
  exact ⟨fun h => h.mp ha, fun h => iff_of_true ha h⟩

/- English proof (translation)
Rewrite using `[show f = g from funext hfg, ← hab]`. Conclude with `h`.
-/
private lemma hasSum_congr {f g : ℕ → ℝ} {a b : ℝ} (h : HasSum g b) (hfg : ∀ n, f n = g n)
    (hab : b = a) : HasSum f a := by
  rw [show f = g from funext hfg, ← hab]; exact h

/- English proof (translation)
Establish `hl0 : 0 < l` using `by linarith`. Establish `hsq : l ^ 2 - 1 ≠ 0` using `(by nlinarith : (0 : ℝ) < l ^ 2 - 1).ne'`. Establish `hq0 : 0 ≤ (l ^ 2)⁻¹` using `by positivity`. Establish `hq1 : (l ^ 2)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (one_lt_pow₀ hl two_ne_zero)`. Establish `h` using `(hasSum_geometric_of_lt_one hq0 hq1).mul_left l⁻¹`.

Establish `e : (fun m : ℕ => (l ^ (2 * m + 1))⁻¹) = fun m : ℕ => l⁻¹ * ((l ^ 2)⁻¹) ^ m`. Use function extensionality and compare the values at `m`. Rewrite using `[pow_succ, pow_mul, mul_inv, ← inv_pow, mul_comm]`. Use `hasSum_congr h (fun m => congrFun e m) ?_` and prove the remaining obligations. Establish `h1 : 1 - (l ^ 2)⁻¹ = (l ^ 2 - 1) / l ^ 2` using `by field_simp`.

Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts.
-/
private lemma hasSum_inv_pow_odd (l : ℝ) (hl : 1 < l) :
    HasSum (fun m : ℕ => (l ^ (2 * m + 1))⁻¹) (l / (l ^ 2 - 1)) := by
  have hl0 : 0 < l := by linarith
  have hsq : l ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < l ^ 2 - 1).ne'
  have hq0 : 0 ≤ (l ^ 2)⁻¹ := by positivity
  have hq1 : (l ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hl two_ne_zero)
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left l⁻¹
  have e : (fun m : ℕ => (l ^ (2 * m + 1))⁻¹) = fun m : ℕ => l⁻¹ * ((l ^ 2)⁻¹) ^ m := by
    funext m; rw [pow_succ, pow_mul, mul_inv, ← inv_pow, mul_comm]
  refine hasSum_congr h (fun m => congrFun e m) ?_
  have h1 : 1 - (l ^ 2)⁻¹ = (l ^ 2 - 1) / l ^ 2 := by field_simp
  rw [h1]
  field_simp

/- English proof (translation)
Establish `hl0 : 0 < l` using `by linarith`. Establish `hsq : l ^ 2 - 1 ≠ 0` using `(by nlinarith : (0 : ℝ) < l ^ 2 - 1).ne'`. Establish `hq0 : 0 ≤ (l ^ 2)⁻¹` using `by positivity`. Establish `hq1 : (l ^ 2)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (one_lt_pow₀ hl two_ne_zero)`. Establish `h` using `(hasSum_geometric_of_lt_one hq0 hq1).mul_left (l ^ 2)⁻¹`.

Establish `e : (fun m : ℕ => (l ^ (2 * m + 2))⁻¹) = fun m : ℕ => (l ^ 2)⁻¹ * ((l ^ 2)⁻¹) ^ m`. Use function extensionality and compare the values at `m`. Rewrite using `[show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul, ← inv_pow, pow_succ']`. Use `hasSum_congr h (fun m => congrFun e m) ?_` and prove the remaining obligations. Establish `h1 : 1 - (l ^ 2)⁻¹ = (l ^ 2 - 1) / l ^ 2` using `by field_simp`.

Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts.
-/
private lemma hasSum_inv_pow_even (l : ℝ) (hl : 1 < l) :
    HasSum (fun m : ℕ => (l ^ (2 * m + 2))⁻¹) (1 / (l ^ 2 - 1)) := by
  have hl0 : 0 < l := by linarith
  have hsq : l ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < l ^ 2 - 1).ne'
  have hq0 : 0 ≤ (l ^ 2)⁻¹ := by positivity
  have hq1 : (l ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hl two_ne_zero)
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (l ^ 2)⁻¹
  have e : (fun m : ℕ => (l ^ (2 * m + 2))⁻¹) = fun m : ℕ => (l ^ 2)⁻¹ * ((l ^ 2)⁻¹) ^ m := by
    funext m
    rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul, ← inv_pow, pow_succ']
  refine hasSum_congr h (fun m => congrFun e m) ?_
  have h1 : 1 - (l ^ 2)⁻¹ = (l ^ 2 - 1) / l ^ 2 := by field_simp
  rw [h1]
  field_simp

/- English proof (translation)
Introduce `d _ l hl h p x`. Establish `hl0 : 0 < l` using `by linarith`. Establish `hl0' : l ≠ 0` using `hl0.ne'`. Establish `hs : ∀ a : ZMod d, Summable (fun k : ℕ => (h - p (a + (k : ZMod d))) / l ^ k)`. Introduce `a`.

Use `summable_div_pow_succ l hl (fun b => h - p b) (fun k => a + ((k + 1 : ℕ) : ZMod d))` as an intermediate fact. Conclude with `(summable_nat_add_iff 1).mp this`. Establish `key : ∀ a : ZMod d, l * chSol d l h p (a - 1) = (h - p a) + chSol d l h p a`. Introduce `a`. Unfold `chSol`.

Rewrite using `[← tsum_mul_left]`. Establish `e1 : (fun k : ℕ => l * ((h - p (a - 1 + ((k + 1 : ℕ) : ZMod d))) / l ^ (k + 1))) = (fun k : ℕ => (h - p (a + (k : ZMod d))) / l ^ k)`. Use function extensionality and compare the values at `k`. Establish `: a - 1 + ((k + 1 : ℕ) : ZMod d) = a + (k : ZMod d)` using `by push_cast; ring`. Rewrite using `[this, pow_succ]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, (hs a).tsum_eq_zero_add]`. Use `congr 1`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Introduce `hx a`. Establish `hrec : ∀ b : ZMod d, x b - chSol d l h p b = l * (x (b - 1) - chSol d l h p (b - 1))`. Introduce `b`. Rewrite using `[mul_sub]`. Combine the linear relations using `[hx b, key b]`.

Establish `hit : ∀ n : ℕ, ∀ b : ZMod d, x b - chSol d l h p b = l ^ n * (x (b - n) - chSol d l h p (b - n))`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro b`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `b`. Rewrite using `[ih b, hrec (b - n)]`. Establish `: b - (n : ZMod d) - 1 = b - ((n + 1 : ℕ) : ZMod d)` using `by push_cast; ring`. Rewrite using `[this, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hd` using `hit d a`. Rewrite `hd` using `[ZMod.natCast_self, sub_zero]`. Establish `hld : 1 < l ^ d` using `one_lt_pow₀ hl (NeZero.ne d)`. Establish `h0 : (l ^ d - 1) * (x a - chSol d l h p a) = 0`.

Rewrite using `[sub_mul, one_mul, ← hd, sub_self]`. Break down `mul_eq_zero.mp h0 with h1 | h1` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `hx a`.

Rewrite using `[hx a, hx (a - 1)]`. Combine the linear relations using `[key a]`.
-/
theorem cayley_hamilton_recursion : CHRecursion := by
  intro d _ l hl h p x
  have hl0 : 0 < l := by linarith
  have hl0' : l ≠ 0 := hl0.ne'
  have hs : ∀ a : ZMod d, Summable (fun k : ℕ => (h - p (a + (k : ZMod d))) / l ^ k) := by
    intro a
    have := summable_div_pow_succ l hl (fun b => h - p b) (fun k => a + ((k + 1 : ℕ) : ZMod d))
    exact (summable_nat_add_iff 1).mp this
  have key : ∀ a : ZMod d, l * chSol d l h p (a - 1) = (h - p a) + chSol d l h p a := by
    intro a
    unfold chSol
    rw [← tsum_mul_left]
    have e1 : (fun k : ℕ => l * ((h - p (a - 1 + ((k + 1 : ℕ) : ZMod d))) / l ^ (k + 1))) =
        (fun k : ℕ => (h - p (a + (k : ZMod d))) / l ^ k) := by
      funext k
      have : a - 1 + ((k + 1 : ℕ) : ZMod d) = a + (k : ZMod d) := by push_cast; ring
      rw [this, pow_succ]
      field_simp
    rw [e1, (hs a).tsum_eq_zero_add]
    congr 1
    simp
  constructor
  · intro hx a
    have hrec : ∀ b : ZMod d, x b - chSol d l h p b = l * (x (b - 1) - chSol d l h p (b - 1)) := by
      intro b; rw [mul_sub]; linarith [hx b, key b]
    have hit : ∀ n : ℕ, ∀ b : ZMod d,
        x b - chSol d l h p b = l ^ n * (x (b - n) - chSol d l h p (b - n)) := by
      intro n
      induction n with
      | zero => intro b; simp
      | succ n ih =>
        intro b
        rw [ih b, hrec (b - n)]
        have : b - (n : ZMod d) - 1 = b - ((n + 1 : ℕ) : ZMod d) := by push_cast; ring
        rw [this, pow_succ]; ring
    have hd := hit d a
    rw [ZMod.natCast_self, sub_zero] at hd
    have hld : 1 < l ^ d := one_lt_pow₀ hl (NeZero.ne d)
    have h0 : (l ^ d - 1) * (x a - chSol d l h p a) = 0 := by
      rw [sub_mul, one_mul, ← hd, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · linarith
    · linarith
  · intro hx a
    rw [hx a, hx (a - 1)]
    linarith [key a]

/- English proof (translation)
Introduce `d _ l hl2 hd2 hd r j j' rh hrh hjr`. Establish `hl : (1 : ℝ) < l`. Establish `: 1 < l` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hl0 : (0 : ℝ) < l` using `by linarith`.

Establish `hpos : (0 : ℝ) < (l : ℝ) ^ 2 - 1` using `by nlinarith`. Establish `hl1 : (l : ℝ) - 1 ≠ 0` using `(by linarith : (0 : ℝ) < (l : ℝ) - 1).ne'`. Establish `hsq : (l : ℝ) ^ 2 - 1 ≠ 0` using `hpos.ne'`. Establish `hgr : gam l + rho l = 1 / ((l : ℝ) - 1)`. Unfold `gam rho`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hγ0 : 0 ≤ gam l` using `div_nonneg hl0.le hpos.le`. Establish `hρ0 : 0 ≤ rho l` using `div_nonneg zero_le_one hpos.le`. Establish `hgS : HasSum (fun m : ℕ => ((l : ℝ) ^ (2 * m + 1))⁻¹) (gam l)` using `hasSum_inv_pow_odd (l : ℝ) hl`.

Establish `hrS : HasSum (fun m : ℕ => ((l : ℝ) ^ (2 * m + 2))⁻¹) (rho l)` using `hasSum_inv_pow_even (l : ℝ) hl`. Establish `hrh0 : (0 : ℝ) ≤ rh` using `Nat.cast_nonneg _`. Establish `hj0 : (0 : ℝ) ≤ j` using `Nat.cast_nonneg _`. Establish `hj'0 : (0 : ℝ) ≤ j'` using `Nat.cast_nonneg _`. Use `⟨fun a ha => ?_, fun a => ?_⟩` and prove the remaining obligations.

Establish `hsum : HasSum (fun k : ℕ => ((r : ℝ) - rh - (if Even (a + ((k + 1 : ℕ) : ZMod d)).val then (r : ℝ) - j' else (j' : ℝ))) / (l : ℝ) ^ (k + 1)) (((r : ℝ) - j' - rh) * gam l + ((j' : ℝ) - rh) * rho l)`. Use `HasSum.even_add_odd ?_ ?_` and prove the remaining obligations. Use `hasSum_congr (hgS.mul_left ((r : ℝ) - j' - rh)) (fun m => ?_) rfl` and prove the remaining obligations. Establish `hodd : ¬ Even (a + ((2 * m + 1 : ℕ) : ZMod d)).val`. Rewrite using `[even_val_add_natCast_iff hd a ha]`.

Conclude with `Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)`. Simplify using `only [hodd, ↓reduceIte]`. Expand and normalize the polynomial expressions, which then agree. Use `hasSum_congr (hrS.mul_left ((j' : ℝ) - rh)) (fun m => ?_) rfl` and prove the remaining obligations. Establish `hev : Even (a + ((2 * m + 1 + 1 : ℕ) : ZMod d)).val`.

Rewrite using `[even_val_add_natCast_iff hd a ha]`. Conclude with `⟨m + 1, by ring⟩`. Simplify using `only [hev, ↓reduceIte]`. Expand and normalize the polynomial expressions, which then agree. Establish `hval : chSol d l ((r : ℝ) - rh) (fun b => if Even b.val then (r : ℝ) - j' else (j' : ℝ)) a = ((r : ℝ) - j' - rh) * gam l + ((j' : ℝ) - rh) * rho l` using `hsum.tsum_eq`.

Use `⟨hval, ?_⟩` and prove the remaining obligations. Rewrite using `[hval]`. Establish `hrj : ((r - j' - j : ℕ) : ℝ) = (r : ℝ) - j' - j`. Rewrite using `[Nat.cast_sub (show j ≤ r - j' by omega), Nat.cast_sub (show j' ≤ r by omega)]`. Rewrite using `[hrj, Nat.cast_add]`.

Establish `hgu : gam l ≤ 1 / ((l : ℝ) - 1)` using `by linarith`. Establish `hru : rho l ≤ 1 / ((l : ℝ) - 1)` using `by linarith`. Establish `e1 : ((j : ℝ) + j') / ((l : ℝ) - 1) = (j + j') * (1 / ((l : ℝ) - 1))` using `by ring`. Rewrite using `[e1]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hgu hj0, mul_le_mul_of_nonneg_left hru hj'0, mul_nonneg hrh0 hγ0, mul_nonneg hrh0 hρ0]`.

Establish `hq0 : (0 : ℝ) ≤ (l : ℝ)⁻¹` using `by positivity`. Establish `hq1 : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl`. Establish `hg` using `(hasSum_geometric_of_lt_one hq0 hq1).mul_left (((j' : ℝ) - rh) * (l : ℝ)⁻¹)`. Establish `hsum : HasSum (fun k : ℕ => ((r : ℝ) - rh - ((r : ℝ) - j')) / (l : ℝ) ^ (k + 1)) (((j' : ℝ) - rh) / ((l : ℝ) - 1))`. Use `hasSum_congr hg (fun k => ?_) ?_` and prove the remaining obligations.

Rewrite using `[inv_pow, pow_succ']`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : 1 - (l : ℝ)⁻¹ = ((l : ℝ) - 1) / l` using `by field_simp`. Rewrite using `[h1]`.

Clear the denominators using the available nonvanishing facts. Establish `hval : chSol d l ((r : ℝ) - rh) (fun _ => (r : ℝ) - j') a = ((j' : ℝ) - rh) / ((l : ℝ) - 1)` using `hsum.tsum_eq`. Use `⟨hval, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_add, div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < (l : ℝ) - 1)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cayley_hamilton_value_holds : CHValue := by
  intro d _ l hl2 hd2 hd r j j' rh hrh hjr
  have hl : (1 : ℝ) < l := by
    have : 1 < l := by omega
    exact_mod_cast this
  have hl0 : (0 : ℝ) < l := by linarith
  have hpos : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hl1 : (l : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < (l : ℝ) - 1).ne'
  have hsq : (l : ℝ) ^ 2 - 1 ≠ 0 := hpos.ne'
  have hgr : gam l + rho l = 1 / ((l : ℝ) - 1) := by
    unfold gam rho
    field_simp
    ring
  have hγ0 : 0 ≤ gam l := div_nonneg hl0.le hpos.le
  have hρ0 : 0 ≤ rho l := div_nonneg zero_le_one hpos.le
  have hgS : HasSum (fun m : ℕ => ((l : ℝ) ^ (2 * m + 1))⁻¹) (gam l) :=
    hasSum_inv_pow_odd (l : ℝ) hl
  have hrS : HasSum (fun m : ℕ => ((l : ℝ) ^ (2 * m + 2))⁻¹) (rho l) :=
    hasSum_inv_pow_even (l : ℝ) hl
  have hrh0 : (0 : ℝ) ≤ rh := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hj'0 : (0 : ℝ) ≤ j' := Nat.cast_nonneg _
  refine ⟨fun a ha => ?_, fun a => ?_⟩
  · have hsum : HasSum (fun k : ℕ => ((r : ℝ) - rh -
        (if Even (a + ((k + 1 : ℕ) : ZMod d)).val then (r : ℝ) - j' else (j' : ℝ))) /
          (l : ℝ) ^ (k + 1)) (((r : ℝ) - j' - rh) * gam l + ((j' : ℝ) - rh) * rho l) := by
      refine HasSum.even_add_odd ?_ ?_
      · refine hasSum_congr (hgS.mul_left ((r : ℝ) - j' - rh)) (fun m => ?_) rfl
        have hodd : ¬ Even (a + ((2 * m + 1 : ℕ) : ZMod d)).val := by
          rw [even_val_add_natCast_iff hd a ha]
          exact Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)
        simp only [hodd, ↓reduceIte]
        ring
      · refine hasSum_congr (hrS.mul_left ((j' : ℝ) - rh)) (fun m => ?_) rfl
        have hev : Even (a + ((2 * m + 1 + 1 : ℕ) : ZMod d)).val := by
          rw [even_val_add_natCast_iff hd a ha]
          exact ⟨m + 1, by ring⟩
        simp only [hev, ↓reduceIte]
        ring
    have hval : chSol d l ((r : ℝ) - rh) (fun b => if Even b.val then (r : ℝ) - j' else (j' : ℝ)) a =
        ((r : ℝ) - j' - rh) * gam l + ((j' : ℝ) - rh) * rho l := hsum.tsum_eq
    refine ⟨hval, ?_⟩
    rw [hval]
    have hrj : ((r - j' - j : ℕ) : ℝ) = (r : ℝ) - j' - j := by
      rw [Nat.cast_sub (show j ≤ r - j' by omega), Nat.cast_sub (show j' ≤ r by omega)]
    rw [hrj, Nat.cast_add]
    have hgu : gam l ≤ 1 / ((l : ℝ) - 1) := by linarith
    have hru : rho l ≤ 1 / ((l : ℝ) - 1) := by linarith
    have e1 : ((j : ℝ) + j') / ((l : ℝ) - 1) = (j + j') * (1 / ((l : ℝ) - 1)) := by ring
    rw [e1]
    nlinarith [mul_le_mul_of_nonneg_left hgu hj0, mul_le_mul_of_nonneg_left hru hj'0,
      mul_nonneg hrh0 hγ0, mul_nonneg hrh0 hρ0]
  · have hq0 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
    have hq1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
    have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (((j' : ℝ) - rh) * (l : ℝ)⁻¹)
    have hsum : HasSum (fun k : ℕ => ((r : ℝ) - rh - ((r : ℝ) - j')) / (l : ℝ) ^ (k + 1))
        (((j' : ℝ) - rh) / ((l : ℝ) - 1)) := by
      refine hasSum_congr hg (fun k => ?_) ?_
      · rw [inv_pow, pow_succ']
        field_simp
        ring
      · have h1 : 1 - (l : ℝ)⁻¹ = ((l : ℝ) - 1) / l := by field_simp
        rw [h1]
        field_simp
    have hval : chSol d l ((r : ℝ) - rh) (fun _ => (r : ℝ) - j') a =
        ((j' : ℝ) - rh) / ((l : ℝ) - 1) := hsum.tsum_eq
    refine ⟨hval, ?_⟩
    rw [Nat.cast_add, div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < (l : ℝ) - 1)]
    linarith

/- English proof (translation)
Introduce `α _ φ p hp k hk a`. Establish `hpk : 1 < p ^ k` using `one_lt_pow₀ hp (by omega)`. Establish `hq0 : 0 ≤ (p ^ k)⁻¹` using `inv_nonneg.mpr (by linarith)`. Establish `hq1 : (p ^ k)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hpk`. Establish `hs : ∀ τ : α, Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ))`.

Introduce `τ`. Use `summable_inv_pow_mul_of_bounded p hp k hk _ (∑ σ, |a σ|) (fun n => ?_)` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun σ => |a σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)`. Rewrite using `[Finset.sum_sub_distrib, ← Summable.tsum_finsetSum (fun τ _ => hs τ)]`. Establish `e : ∀ n : ℕ, ∑ τ : α, (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ) = ((p ^ k)⁻¹) ^ (n + 1) * ∑ τ, a τ`.

Introduce `n`. Rewrite using `[← Finset.mul_sum, Equiv.sum_comp (φ ^ (n + 1)) a, inv_pow_succ_mul]`. Establish `hne : p ^ k - 1 ≠ 0` using `(by linarith : (0 : ℝ) < p ^ k - 1).ne'`. Establish `hne' : p ^ k ≠ 0` using `(by linarith : (0 : ℝ) < p ^ k).ne'`. Establish `hg : ∑' n : ℕ, ((p ^ k)⁻¹) ^ (n + 1) = 1 / (p ^ k - 1)`.

Rewrite using `[tsum_congr (fun n => pow_succ' ((p ^ k)⁻¹) n), tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[tsum_congr e, tsum_mul_right, hg, ← Finset.sum_div]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frobenius_orbit_sum_holds : FrobOrbitSum := by
  intro α _ φ p hp k hk a
  have hpk : 1 < p ^ k := one_lt_pow₀ hp (by omega)
  have hq0 : 0 ≤ (p ^ k)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (p ^ k)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpk
  have hs : ∀ τ : α, Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ)) := by
    intro τ
    refine summable_inv_pow_mul_of_bounded p hp k hk _ (∑ σ, |a σ|) (fun n => ?_)
    exact Finset.single_le_sum (f := fun σ => |a σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  rw [Finset.sum_sub_distrib, ← Summable.tsum_finsetSum (fun τ _ => hs τ)]
  have e : ∀ n : ℕ, ∑ τ : α, (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ) =
      ((p ^ k)⁻¹) ^ (n + 1) * ∑ τ, a τ := by
    intro n
    rw [← Finset.mul_sum, Equiv.sum_comp (φ ^ (n + 1)) a, inv_pow_succ_mul]
  have hne : p ^ k - 1 ≠ 0 := (by linarith : (0 : ℝ) < p ^ k - 1).ne'
  have hne' : p ^ k ≠ 0 := (by linarith : (0 : ℝ) < p ^ k).ne'
  have hg : ∑' n : ℕ, ((p ^ k)⁻¹) ^ (n + 1) = 1 / (p ^ k - 1) := by
    rw [tsum_congr (fun n => pow_succ' ((p ^ k)⁻¹) n), tsum_mul_left,
      tsum_geometric_of_lt_one hq0 hq1]
    field_simp
  rw [tsum_congr e, tsum_mul_right, hg, ← Finset.sum_div]
  ring

/- English proof (translation)
Introduce `α φ p hp k hk a τ f hf hfix`. Use `set c : ℕ → ℝ := fun n => (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ) with hc`. Use `show ∑' n, c n = (∑ n ∈ Finset.range f, c n) / (1 - (p ^ (f * k))⁻¹)`. Establish `hbd : ∀ n, |a ((φ ^ (n + 1)) τ)| ≤ ∑ r ∈ Finset.range f, |a ((φ ^ r) τ)|`. Introduce `n`.

Rewrite using `[pow_apply_eq_pow_mod_apply φ τ f hfix (n + 1)]`. Conclude with `Finset.single_le_sum (f := fun r => |a ((φ ^ r) τ)|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))`. Establish `hs : Summable c` using `summable_inv_pow_mul_of_bounded p hp k hk _ _ hbd`. Establish `hshift : ∀ n, c (n + f) = (p ^ (f * k))⁻¹ * c n`. Introduce `n`.

Simplify using `only [hc]`. Establish `e1 : (φ ^ (n + f + 1)) τ = (φ ^ (n + 1)) τ`. Rewrite using `[show n + f + 1 = (n + 1) + f by omega, pow_add φ (n + 1) f, Equiv.Perm.mul_apply, hfix]`. Rewrite using `[e1, show (n + f + 1) * k = (n + 1) * k + f * k by ring, pow_add p ((n + 1) * k) (f * k), mul_inv]`. Expand and normalize the polynomial expressions, which then agree.

Establish `htail : ∑' i, c (i + f) = (p ^ (f * k))⁻¹ * ∑' i, c i`. Rewrite using `[← tsum_mul_left]`. Conclude with `tsum_congr hshift`. Establish `hsplit` using `hs.sum_add_tsum_nat_add f`. Rewrite `hsplit` using `[htail]`.

Establish `hpf : 1 < p ^ (f * k)` using `one_lt_pow₀ hp (Nat.mul_ne_zero (by omega) (by omega))`. Establish `hq : (p ^ (f * k))⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hpf`. Establish `hne : 1 - (p ^ (f * k))⁻¹ ≠ 0` using `(by linarith : (0 : ℝ) < 1 - (p ^ (f * k))⁻¹).ne'`. Rewrite using `[eq_div_iff hne]`. Take the linear combination `-hsplit`.
-/
theorem frobenius_orbit_period_holds : FrobOrbitPeriod := by
  intro α φ p hp k hk a τ f hf hfix
  set c : ℕ → ℝ := fun n => (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ) with hc
  show ∑' n, c n = (∑ n ∈ Finset.range f, c n) / (1 - (p ^ (f * k))⁻¹)
  have hbd : ∀ n, |a ((φ ^ (n + 1)) τ)| ≤ ∑ r ∈ Finset.range f, |a ((φ ^ r) τ)| := by
    intro n
    rw [pow_apply_eq_pow_mod_apply φ τ f hfix (n + 1)]
    exact Finset.single_le_sum (f := fun r => |a ((φ ^ r) τ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
  have hs : Summable c := summable_inv_pow_mul_of_bounded p hp k hk _ _ hbd
  have hshift : ∀ n, c (n + f) = (p ^ (f * k))⁻¹ * c n := by
    intro n
    simp only [hc]
    have e1 : (φ ^ (n + f + 1)) τ = (φ ^ (n + 1)) τ := by
      rw [show n + f + 1 = (n + 1) + f by omega, pow_add φ (n + 1) f, Equiv.Perm.mul_apply, hfix]
    rw [e1, show (n + f + 1) * k = (n + 1) * k + f * k by ring, pow_add p ((n + 1) * k) (f * k),
      mul_inv]
    ring
  have htail : ∑' i, c (i + f) = (p ^ (f * k))⁻¹ * ∑' i, c i := by
    rw [← tsum_mul_left]; exact tsum_congr hshift
  have hsplit := hs.sum_add_tsum_nat_add f
  rw [htail] at hsplit
  have hpf : 1 < p ^ (f * k) := one_lt_pow₀ hp (Nat.mul_ne_zero (by omega) (by omega))
  have hq : (p ^ (f * k))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpf
  have hne : 1 - (p ^ (f * k))⁻¹ ≠ 0 := (by linarith : (0 : ℝ) < 1 - (p ^ (f * k))⁻¹).ne'
  rw [eq_div_iff hne]
  linear_combination -hsplit

end Formalism.IncomingBounds
