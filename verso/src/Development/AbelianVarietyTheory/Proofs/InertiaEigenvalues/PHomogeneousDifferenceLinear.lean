import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PHomCalc

def RightAffine (f : ℝ → ℝ) (r k : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc r (r + δ), f t = f r + k * (t - r)

/- English proof (translation)
Take `⟨δ, hδ, hf⟩` from `h`. Take `⟨δ', hδ', hf'⟩` from `h'`. Establish `hε : 0 < min δ δ'` using `lt_min hδ hδ'`. Establish `h1` using `hf (r + min δ δ') ⟨by linarith, by linarith [min_le_left δ δ']⟩`. Establish `h2` using `hf' (r + min δ δ') ⟨by linarith, by linarith [min_le_right δ δ']⟩`.

Establish `: k * min δ δ' = k' * min δ δ'`. Use `h1.symm.trans h2` as an intermediate fact. Simplify using `only [add_sub_cancel_left] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `mul_right_cancel₀ hε.ne' this`.
-/
lemma RightAffine.unique {f : ℝ → ℝ} {r k k' : ℝ} (h : RightAffine f r k)
    (h' : RightAffine f r k') : k = k' := by
  obtain ⟨δ, hδ, hf⟩ := h
  obtain ⟨δ', hδ', hf'⟩ := h'
  have hε : 0 < min δ δ' := lt_min hδ hδ'
  have h1 := hf (r + min δ δ') ⟨by linarith, by linarith [min_le_left δ δ']⟩
  have h2 := hf' (r + min δ δ') ⟨by linarith, by linarith [min_le_right δ δ']⟩
  have : k * min δ δ' = k' * min δ δ' := by
    have := h1.symm.trans h2
    simp only [add_sub_cancel_left] at this
    linarith
  exact mul_right_cancel₀ hε.ne' this

/- English proof (translation)
Take `⟨δ, hδ, hf⟩` from `hf`. Take `⟨δ', hδ', hg⟩` from `hg`. Use `⟨min δ δ', lt_min hδ hδ', fun t ht => ?_⟩` and prove the remaining obligations. Establish `h1` using `hf t ⟨ht.1, ht.2.trans (by linarith [min_le_left δ δ'])⟩`. Establish `h2` using `hg t ⟨ht.1, ht.2.trans (by linarith [min_le_right δ δ'])⟩`.

Simplify using `only`. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma RightAffine.sub_mul {f g : ℝ → ℝ} {r k k' : ℝ} (c : ℝ) (hf : RightAffine f r k)
    (hg : RightAffine g r k') : RightAffine (fun t => f t - c * g t) r (k - c * k') := by
  obtain ⟨δ, hδ, hf⟩ := hf
  obtain ⟨δ', hδ', hg⟩ := hg
  refine ⟨min δ δ', lt_min hδ hδ', fun t ht => ?_⟩
  have h1 := hf t ⟨ht.1, ht.2.trans (by linarith [min_le_left δ δ'])⟩
  have h2 := hg t ⟨ht.1, ht.2.trans (by linarith [min_le_right δ δ'])⟩
  simp only
  rw [h1, h2]; ring

/- English proof (translation)
Take `⟨δ, hδ, hf⟩` from `hf`. Conclude with `⟨δ, hδ, fun t ht => by simp only; rw [hf t ht]; ring⟩`.
-/
lemma RightAffine.add_linear {f : ℝ → ℝ} {r k : ℝ} (c : ℝ) (hf : RightAffine f r k) :
    RightAffine (fun t => f t + c * t) r (k + c) := by
  obtain ⟨δ, hδ, hf⟩ := hf
  exact ⟨δ, hδ, fun t ht => by simp only; rw [hf t ht]; ring⟩

/- English proof (translation)
Take `⟨δ, hδ, hf⟩` from `hf`. Conclude with `⟨δ, hδ, fun t ht => by simp only; rw [hf t ht]; ring⟩`.
-/
lemma RightAffine.const_mul {f : ℝ → ℝ} {r k : ℝ} (c : ℝ) (hf : RightAffine f r k) :
    RightAffine (fun t => c * f t) r (c * k) := by
  obtain ⟨δ, hδ, hf⟩ := hf
  exact ⟨δ, hδ, fun t ht => by simp only; rw [hf t ht]; ring⟩

/- English proof (translation)
Substitute `hcr` using the available equality. Take `⟨δ, hδ, hf⟩` from `hf`. Use `⟨δ / c, div_pos hδ hc, fun t ht => ?_⟩` and prove the remaining obligations. Establish `hmem : c * t ∈ Set.Icc (c * r) (c * r + δ)`. Prove the components needed by the constructor for the conclusion.

Conclude with `mul_le_mul_of_nonneg_left ht.1 hc.le`. Use `mul_le_mul_of_nonneg_left ht.2 hc.le` as an intermediate fact. Rewrite `this` using `[mul_add, mul_div_cancel₀ _ hc.ne']`. Conclude with `this`. Simplify using `only`.

Rewrite using `[hf _ hmem]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma RightAffine.comp_mul {f : ℝ → ℝ} {r r' k c : ℝ} (hc : 0 < c) (hcr : c * r = r')
    (hf : RightAffine f r' k) : RightAffine (fun t => f (c * t)) r (c * k) := by
  subst hcr
  obtain ⟨δ, hδ, hf⟩ := hf
  refine ⟨δ / c, div_pos hδ hc, fun t ht => ?_⟩
  have hmem : c * t ∈ Set.Icc (c * r) (c * r + δ) := by
    constructor
    · exact mul_le_mul_of_nonneg_left ht.1 hc.le
    · have := mul_le_mul_of_nonneg_left ht.2 hc.le
      rw [mul_add, mul_div_cancel₀ _ hc.ne'] at this
      exact this
  simp only
  rw [hf _ hmem]; ring

/- English proof (translation)
Take `⟨δ, hδ, hf⟩` from `hf`. Use `⟨min δ ε, lt_min hδ hε, fun t ht => ?_⟩` and prove the remaining obligations. Establish `ht1 : t ∈ Set.Icc r (r + δ)` using `⟨ht.1, ht.2.trans (by linarith [min_le_left δ ε])⟩`. Establish `ht2 : t ∈ Set.Icc r (r + ε)` using `⟨ht.1, ht.2.trans (by linarith [min_le_right δ ε])⟩`. Establish `hr : r ∈ Set.Icc r (r + ε)` using `⟨le_rfl, by linarith⟩`.

Rewrite using `[← hfg t ht2, ← hfg r hr, hf t ht1]`.
-/
lemma RightAffine.congr {f g : ℝ → ℝ} {r k ε : ℝ} (hε : 0 < ε)
    (hfg : ∀ t ∈ Set.Icc r (r + ε), f t = g t) (hf : RightAffine f r k) : RightAffine g r k := by
  obtain ⟨δ, hδ, hf⟩ := hf
  refine ⟨min δ ε, lt_min hδ hε, fun t ht => ?_⟩
  have ht1 : t ∈ Set.Icc r (r + δ) := ⟨ht.1, ht.2.trans (by linarith [min_le_left δ ε])⟩
  have ht2 : t ∈ Set.Icc r (r + ε) := ⟨ht.1, ht.2.trans (by linarith [min_le_right δ ε])⟩
  have hr : r ∈ Set.Icc r (r + ε) := ⟨le_rfl, by linarith⟩
  rw [← hfg t ht2, ← hfg r hr, hf t ht1]

/- English proof (translation)
Take `⟨δ, hδ, hf⟩` from `h`. Establish `hlin : HasDerivWithinAt (fun t => f r + k * (t - r)) k (Set.Ici r) r`. Use `(((hasDerivAt_id r).sub_const r).const_mul k).const_add (f r)` as an intermediate fact. Simplify using `using this.hasDerivWithinAt`. Apply `hlin.congr_of_eventuallyEq` to reduce the goal to its premises.

Use `filter_upwards [Icc_mem_nhdsGE (show r < r + δ by linarith)] with t ht`. Conclude with `hf t ht`. Simplify using the standard rewrite rules.
-/
lemma RightAffine.hasDerivWithinAt {f : ℝ → ℝ} {r k : ℝ} (h : RightAffine f r k) :
    HasDerivWithinAt f k (Set.Ici r) r := by
  obtain ⟨δ, hδ, hf⟩ := h
  have hlin : HasDerivWithinAt (fun t => f r + k * (t - r)) k (Set.Ici r) r := by
    have := (((hasDerivAt_id r).sub_const r).const_mul k).const_add (f r)
    simpa using this.hasDerivWithinAt
  apply hlin.congr_of_eventuallyEq
  · filter_upwards [Icc_mem_nhdsGE (show r < r + δ by linarith)] with t ht
    exact hf t ht
  · simp

/- English proof (translation)
Take `⟨δ, hδ, hfr⟩` from `hk`. Take `⟨δ', hδ', hft⟩` from `hk'`. Establish `hz : t < min (t + δ') 1` using `lt_min (by linarith) ht1`. Establish `hz1 : min (t + δ') 1 ≤ 1` using `min_le_right _ _`. Use `set z := min (t + δ') 1 with hzdef`.

Establish `hzmem : z ∈ Set.Ioc (0:ℝ) 1` using `⟨by linarith, hz1⟩`. Establish `hg` using `hf.neg`. Establish `e1 : f z - f t = k' * (z - t)`. Rewrite using `[hft z ⟨hz.le, min_le_left _ _⟩]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hε : 0 < min δ (z - r)` using `lt_min hδ (by linarith)`. Establish `hεz : min δ (z - r) ≤ z - r` using `min_le_right _ _`. Use `set ε := min δ (z - r) with hεdef`. Establish `e2 : f (r + ε) - f r = k * ε`. Rewrite using `[hfr (r + ε) ⟨by linarith, by linarith [min_le_left δ (z - r)]⟩]; ring`.

Establish `s1` using `hg.secant_mono (a := z) (x := r) (y := t) hzmem ⟨hr, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith) (by linarith) hrt.le`. Establish `s2` using `hg.secant_mono (a := r) (x := r + ε) (y := z) ⟨hr, by linarith⟩ ⟨by linarith, by linarith⟩ hzmem (by linarith) (by linarith) (by linarith)`. Simplify using `only [Pi.neg_apply] at s1 s2`. Establish `q1 : (-f t - -f z) / (t - z) = -k'`. Rewrite using `[div_eq_iff (by linarith)]; linarith`.

Establish `q2 : (-f (r + ε) - -f r) / (r + ε - r) = -k`. Rewrite using `[div_eq_iff (by linarith)]; linarith`. Establish `q3 : (-f r - -f z) / (r - z) = (-f z - -f r) / (z - r)`. Rewrite using `[div_eq_div_iff (by linarith) (by linarith)]; ring`. Rewrite `s1` using `[q1, q3]`.

Rewrite `s2` using `[q2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma RightAffine.anti_of_concave {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ioc 0 1) f)
    {r t k k' : ℝ} (hr : 0 < r) (hrt : r < t) (ht1 : t < 1) (hk : RightAffine f r k)
    (hk' : RightAffine f t k') : k' ≤ k := by
  obtain ⟨δ, hδ, hfr⟩ := hk
  obtain ⟨δ', hδ', hft⟩ := hk'
  have hz : t < min (t + δ') 1 := lt_min (by linarith) ht1
  have hz1 : min (t + δ') 1 ≤ 1 := min_le_right _ _
  set z := min (t + δ') 1 with hzdef
  have hzmem : z ∈ Set.Ioc (0:ℝ) 1 := ⟨by linarith, hz1⟩
  have hg := hf.neg
  have e1 : f z - f t = k' * (z - t) := by
    rw [hft z ⟨hz.le, min_le_left _ _⟩]; ring
  have hε : 0 < min δ (z - r) := lt_min hδ (by linarith)
  have hεz : min δ (z - r) ≤ z - r := min_le_right _ _
  set ε := min δ (z - r) with hεdef
  have e2 : f (r + ε) - f r = k * ε := by
    rw [hfr (r + ε) ⟨by linarith, by linarith [min_le_left δ (z - r)]⟩]; ring
  have s1 := hg.secant_mono (a := z) (x := r) (y := t) hzmem ⟨hr, by linarith⟩
    ⟨by linarith, by linarith⟩ (by linarith) (by linarith) hrt.le
  have s2 := hg.secant_mono (a := r) (x := r + ε) (y := z) ⟨hr, by linarith⟩
    ⟨by linarith, by linarith⟩ hzmem (by linarith) (by linarith) (by linarith)
  simp only [Pi.neg_apply] at s1 s2
  have q1 : (-f t - -f z) / (t - z) = -k' := by
    rw [div_eq_iff (by linarith)]; linarith
  have q2 : (-f (r + ε) - -f r) / (r + ε - r) = -k := by
    rw [div_eq_iff (by linarith)]; linarith
  have q3 : (-f r - -f z) / (r - z) = (-f z - -f r) / (z - r) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  rw [q1, q3] at s1
  rw [q2] at s2
  linarith

/- English proof (translation)
Introduce `x hx`. Use `constant_of_has_deriv_right_zero (hc.mono (fun y hy => ⟨by linarith [hx.1, hy.1], hy.2⟩)) (fun y hy => (hd y ⟨by linarith [hx.1, hy.1], hy.2⟩).hasDerivWithinAt) 1 ⟨hx.2, le_rfl⟩` as an intermediate fact. Conclude with `this.symm`.
-/
lemma const_of_rightAffine_zero {H : ℝ → ℝ} (hc : ContinuousOn H (Set.Ioc 0 1))
    (hd : ∀ r ∈ Set.Ioo (0:ℝ) 1, RightAffine H r 0) : ∀ x ∈ Set.Ioc (0:ℝ) 1, H x = H 1 := by
  intro x hx
  have := constant_of_has_deriv_right_zero
    (hc.mono (fun y hy => ⟨by linarith [hx.1, hy.1], hy.2⟩))
    (fun y hy => (hd y ⟨by linarith [hx.1, hy.1], hy.2⟩).hasDerivWithinAt) 1 ⟨hx.2, le_rfl⟩
  exact this.symm

/- English proof (translation)
Establish `hp0 : (0:ℝ) < p` using `by exact_mod_cast (by omega : 0 < p)`. Establish `hp1 : (1:ℝ) < p` using `by exact_mod_cast (by omega : 1 < p)`. Take `⟨g, hgdef⟩ : ∃ g : ℝ → ℤ, ∀ r, g r = a r - m * b r` from `⟨_, fun _ => rfl⟩`. Establish `hper : ∀ r : ℝ, 0 < r → r < 1 → ∀ i : ℕ, g (r / (p:ℝ) ^ i) = g r`. Introduce `r hr hr1 i`.

Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Establish `hpos : 0 < r / (p:ℝ) ^ (i + 1)` using `by positivity`. Establish `hlt : r / (p:ℝ) ^ (i + 1) < 1 / (p:ℝ)`.

Rewrite using `[pow_succ, ← div_div]`. Apply `div_lt_div_of_pos_right _ hp0` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `hg _ hpos hlt` as an intermediate fact. Establish `e : (p:ℝ) * (r / (p:ℝ) ^ (i + 1)) = r / (p:ℝ) ^ i`.

Rewrite using `[pow_succ]`. Clear the denominators using the available nonvanishing facts. Rewrite `this` using `[e]`. Rewrite `ih`, the goal using `[hgdef]`. Rewrite using `[← this]`.

Conclude with `ih`. Establish `hstep : ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ < r₂ → r₂ < 1 → r₂ < p * r₁ → g r₂ ≤ g r₁`. Introduce `r₁ r₂ h1 h12 h2 h2p`. Establish `hr2 : 0 < r₂` using `by linarith`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hclaim : ∀ i : ℕ, b r₂ + i ≤ b (r₂ / (p:ℝ) ^ i)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simp`.

Consider the case `succ i ih`. Establish `hpi : (0:ℝ) < (p:ℝ) ^ i` using `by positivity`. Establish `hu : 0 < r₁ / (p:ℝ) ^ i` using `by positivity`. Establish `huv : r₁ / (p:ℝ) ^ i < r₂ / (p:ℝ) ^ i` using `div_lt_div_of_pos_right h12 hpi`. Establish `hv1 : r₂ / (p:ℝ) ^ i < 1` using `lt_of_le_of_lt (div_le_self (by linarith) (one_le_pow₀ hp1.le)) h2`.

Establish `gu : g (r₁ / (p:ℝ) ^ i) = g r₁` using `hper r₁ h1 (by linarith) i`. Establish `gv : g (r₂ / (p:ℝ) ^ i) = g r₂` using `hper r₂ (by linarith) h2 i`. Establish `hau` using `ha _ _ hu huv hv1`. Rewrite `gu`, `gv`, `hcon` using `[hgdef, hgdef]`. Establish `hdrop : b (r₂ / (p:ℝ) ^ i) + 1 ≤ b (r₁ / (p:ℝ) ^ i)`.

Establish `h3 : (m:ℤ) * b (r₂ / (p:ℝ) ^ i) < m * b (r₁ / (p:ℝ) ^ i)` using `by linarith`. Use `lt_of_mul_lt_mul_left h3 (by positivity)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hw : r₂ / (p:ℝ) ^ (i + 1) < r₁ / (p:ℝ) ^ i`. Rewrite using `[div_lt_div_iff₀ (by positivity) hpi, pow_succ]`.

Use polynomial arithmetic with `[mul_lt_mul_of_pos_left h2p hpi]`. Establish `hbw` using `hb _ _ (by positivity) hw (by linarith)`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use `hclaim h` as an intermediate fact.

Rewrite `this` using `[hbq r₂ (by linarith) h2]`. Use linear arithmetic over natural numbers and integers. Establish `hle : ∀ r t : ℝ, 0 < r → r ≤ t → t < 1 → g t = g r`. Introduce `r t hr hrt ht`. Take `⟨n, hn1, hn2⟩` from `exists_nat_pow_near (x := t / r) (y := (p:ℝ)) (by rw [le_div_iff₀ hr]; linarith) hp1`.

Establish `hpn : (0:ℝ) < (p:ℝ) ^ n` using `by positivity`. Establish `ht'1 : r ≤ t / (p:ℝ) ^ n`. Rewrite using `[le_div_iff₀ hpn]`. Rewrite `hn1` using `[le_div_iff₀ hr]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `ht'2 : t / (p:ℝ) ^ n < p * r`. Rewrite using `[div_lt_iff₀ hpn]`. Rewrite `hn2` using `[div_lt_iff₀ hr, pow_succ]`. Use the polynomial consequences of the given equalities and inequalities. Establish `ht'lt : t / (p:ℝ) ^ n < 1` using `lt_of_le_of_lt (div_le_self (by linarith) (one_le_pow₀ hp1.le)) ht`.

Establish `hgt : g (t / (p:ℝ) ^ n) = g t` using `hper t (by linarith) ht n`. Rewrite using `[← hgt]`. Use `set t' := t / (p:ℝ) ^ n`. Establish `ht'0 : 0 < t'` using `by linarith`. Break down `ht'1.lt_or_eq with hlt | heq` into its components or cases.

Apply `le_antisymm (hstep r t' hr hlt ht'lt ht'2)` to reduce the goal to its premises. Establish `e : g (t' / p) = g t'` using `by simpa using hper t' (by linarith) ht'lt 1`. Rewrite using `[← e]`. Apply `hstep (t' / p) r (by positivity) ?_ (by linarith) ?_` to reduce the goal to its premises. Rewrite using `[div_lt_iff₀ hp0]`.

Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[mul_div_cancel₀ _ hp0.ne']`. Conclude with `hlt`. Rewrite using `[heq]`. Introduce `r t hr hr1 ht ht1`.

Rewrite using `[← hgdef, ← hgdef]`. Break down `le_total r t with h' | h'` into its components or cases. Conclude with `hle r t hr h' ht1`. Conclude with `(hle t r ht h' hr1).symm`.
-/
lemma slopes_const {p h s m : ℕ} (hp : 2 ≤ p) (hs : s < h) (hm : 1 ≤ m) (a b : ℝ → ℤ)
    (ha : ∀ r t : ℝ, 0 < r → r < t → t < 1 → a t ≤ a r)
    (hb : ∀ r t : ℝ, 0 < r → r < t → t < 1 → b t ≤ b r)
    (hbq : ∀ r : ℝ, 0 < r → r < 1 → b (r / (p:ℝ) ^ h) = b r + s)
    (hg : ∀ r : ℝ, 0 < r → r < 1 / (p:ℝ) → a (p * r) - m * b (p * r) = a r - m * b r) :
    ∀ r t : ℝ, 0 < r → r < 1 → 0 < t → t < 1 → a t - m * b t = a r - m * b r := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1:ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℤ, ∀ r, g r = a r - m * b r := ⟨_, fun _ => rfl⟩
  have hper : ∀ r : ℝ, 0 < r → r < 1 → ∀ i : ℕ, g (r / (p:ℝ) ^ i) = g r := by
    intro r hr hr1 i
    induction i with
    | zero => simp
    | succ i ih =>
      have hpos : 0 < r / (p:ℝ) ^ (i + 1) := by positivity
      have hlt : r / (p:ℝ) ^ (i + 1) < 1 / (p:ℝ) := by
        rw [pow_succ, ← div_div]
        apply div_lt_div_of_pos_right _ hp0
        calc r / (p:ℝ) ^ i ≤ r := div_le_self hr.le (one_le_pow₀ hp1.le)
          _ < 1 := hr1
      have := hg _ hpos hlt
      have e : (p:ℝ) * (r / (p:ℝ) ^ (i + 1)) = r / (p:ℝ) ^ i := by
        rw [pow_succ]; field_simp
      rw [e] at this
      rw [hgdef] at ih ⊢
      rw [← this]; exact ih
  have hstep : ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ < r₂ → r₂ < 1 → r₂ < p * r₁ → g r₂ ≤ g r₁ := by
    intro r₁ r₂ h1 h12 h2 h2p
    have hr2 : 0 < r₂ := by linarith
    by_contra hcon
    push_neg at hcon
    have hclaim : ∀ i : ℕ, b r₂ + i ≤ b (r₂ / (p:ℝ) ^ i) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have hpi : (0:ℝ) < (p:ℝ) ^ i := by positivity
        have hu : 0 < r₁ / (p:ℝ) ^ i := by positivity
        have huv : r₁ / (p:ℝ) ^ i < r₂ / (p:ℝ) ^ i := div_lt_div_of_pos_right h12 hpi
        have hv1 : r₂ / (p:ℝ) ^ i < 1 :=
          lt_of_le_of_lt (div_le_self (by linarith) (one_le_pow₀ hp1.le)) h2
        have gu : g (r₁ / (p:ℝ) ^ i) = g r₁ := hper r₁ h1 (by linarith) i
        have gv : g (r₂ / (p:ℝ) ^ i) = g r₂ := hper r₂ (by linarith) h2 i
        have hau := ha _ _ hu huv hv1
        rw [hgdef, hgdef] at gu gv hcon
        have hdrop : b (r₂ / (p:ℝ) ^ i) + 1 ≤ b (r₁ / (p:ℝ) ^ i) := by
          have h3 : (m:ℤ) * b (r₂ / (p:ℝ) ^ i) < m * b (r₁ / (p:ℝ) ^ i) := by linarith
          have := lt_of_mul_lt_mul_left h3 (by positivity)
          omega
        have hw : r₂ / (p:ℝ) ^ (i + 1) < r₁ / (p:ℝ) ^ i := by
          rw [div_lt_div_iff₀ (by positivity) hpi, pow_succ]
          nlinarith [mul_lt_mul_of_pos_left h2p hpi]
        have hbw := hb _ _ (by positivity) hw (by linarith)
        push_cast
        linarith
    have := hclaim h
    rw [hbq r₂ (by linarith) h2] at this
    omega
  have hle : ∀ r t : ℝ, 0 < r → r ≤ t → t < 1 → g t = g r := by
    intro r t hr hrt ht
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := t / r) (y := (p:ℝ))
      (by rw [le_div_iff₀ hr]; linarith) hp1
    have hpn : (0:ℝ) < (p:ℝ) ^ n := by positivity
    have ht'1 : r ≤ t / (p:ℝ) ^ n := by
      rw [le_div_iff₀ hpn]; rw [le_div_iff₀ hr] at hn1; linarith
    have ht'2 : t / (p:ℝ) ^ n < p * r := by
      rw [div_lt_iff₀ hpn]; rw [div_lt_iff₀ hr, pow_succ] at hn2; nlinarith
    have ht'lt : t / (p:ℝ) ^ n < 1 :=
      lt_of_le_of_lt (div_le_self (by linarith) (one_le_pow₀ hp1.le)) ht
    have hgt : g (t / (p:ℝ) ^ n) = g t := hper t (by linarith) ht n
    rw [← hgt]
    set t' := t / (p:ℝ) ^ n
    have ht'0 : 0 < t' := by linarith
    rcases ht'1.lt_or_eq with hlt | heq
    · apply le_antisymm (hstep r t' hr hlt ht'lt ht'2)
      have e : g (t' / p) = g t' := by simpa using hper t' (by linarith) ht'lt 1
      rw [← e]
      apply hstep (t' / p) r (by positivity) ?_ (by linarith) ?_
      · rw [div_lt_iff₀ hp0]; nlinarith
      · rw [mul_div_cancel₀ _ hp0.ne']; exact hlt
    · rw [heq]
  intro r t hr hr1 ht ht1
  rw [← hgdef, ← hgdef]
  rcases le_total r t with h' | h'
  · exact hle r t hr h' ht1
  · exact (hle t r ht h' hr1).symm

/- English proof (translation)
Introduce `p h s m hp hs hm A B hAc hBc hAcont hBcont hA hB hBq hG`. Establish `hp0 : (0:ℝ) < p` using `by exact_mod_cast (by omega : 0 < p)`. Establish `hp1 : (1:ℝ) < p` using `by exact_mod_cast (by omega : 1 < p)`. Establish `hq0 : (0:ℝ) < (p:ℝ) ^ h` using `by positivity`. Establish `hq1 : (1:ℝ) ≤ (p:ℝ) ^ h` using `one_le_pow₀ hp1.le`.

Use `choose! kA δA hδA hδA1 hA' using hA`. Use `choose! kB δB hδB hδB1 hB' using hB`. Establish `raA : ∀ r ∈ Set.Ioo (0:ℝ) 1, RightAffine A r (kA r)` using `fun r hr => ⟨δA r, hδA r hr, hA' r hr⟩`. Establish `raB : ∀ r ∈ Set.Ioo (0:ℝ) 1, RightAffine B r (kB r)` using `fun r hr => ⟨δB r, hδB r hr, hB' r hr⟩`. Establish `antiA : ∀ r t : ℝ, 0 < r → r < t → t < 1 → kA t ≤ kA r` using `fun r t hr hrt ht => by`.

Conclude with `RightAffine.anti_of_concave hAc hr hrt ht (raA r ⟨hr, by linarith⟩) (raA t ⟨by linarith, ht⟩)` after adjusting the coercions. Establish `antiB : ∀ r t : ℝ, 0 < r → r < t → t < 1 → kB t ≤ kB r` using `fun r t hr hrt ht => by`. Conclude with `RightAffine.anti_of_concave hBc hr hrt ht (raB r ⟨hr, by linarith⟩) (raB t ⟨by linarith, ht⟩)` after adjusting the coercions. Establish `hbq : ∀ r : ℝ, 0 < r → r < 1 → kB (r / (p:ℝ) ^ h) = kB r + s`. Introduce `r hr hr1`.

Establish `hrq : r / (p:ℝ) ^ h ∈ Set.Ioo (0:ℝ) 1` using `⟨by positivity, lt_of_le_of_lt (div_le_self hr.le hq1) hr1⟩`. Establish `h1` using `((raB _ hrq).comp_mul (c := 1 / (p:ℝ) ^ h) (r := r) (by positivity) (by ring)).const_mul ((p:ℝ) ^ h)`. Establish `h2` using `(raB r ⟨hr, hr1⟩).add_linear (s:ℝ)`. Establish `h3 : RightAffine (fun t => B t + s * t) r ((p:ℝ) ^ h * (1 / (p:ℝ) ^ h * kB (r / (p:ℝ) ^ h)))`. Use `h1.congr (ε := 1 - r) (by linarith) (fun t ht => ?_)` and prove the remaining obligations.

Use `hBq t ⟨by linarith [ht.1], by linarith [ht.2]⟩` as an intermediate fact. Rewrite using `[show 1 / (p:ℝ) ^ h * t = t / (p:ℝ) ^ h by ring]; exact this`. Use `h3.unique h2` as an intermediate fact. Rewrite `this` using `[← mul_assoc, mul_one_div_cancel hq0.ne', one_mul]`. Conclude with `this` after adjusting the coercions.

Establish `hgp : ∀ r : ℝ, 0 < r → r < 1 / (p:ℝ) → kA (p * r) - m * kB (p * r) = kA r - m * kB r`. Introduce `r hr hrp`. Establish `hpr1 : (p:ℝ) * r < 1` using `by rwa [lt_div_iff₀ hp0, mul_comm] at hrp`. Establish `hp1' : 1 / (p:ℝ) < 1` using `by rw [div_lt_one hp0]; exact hp1`. Establish `hr1 : r < 1` using `by linarith`.

Establish `hpr : (p:ℝ) * r ∈ Set.Ioo (0:ℝ) 1` using `⟨by positivity, hpr1⟩`. Establish `h1` using `((raA _ hpr).sub_mul (m:ℝ) (raB _ hpr)).comp_mul (r := r) hp0 rfl`. Establish `h2` using `((raA r ⟨hr, hr1⟩).sub_mul (m:ℝ) (raB r ⟨hr, hr1⟩)).const_mul (p:ℝ)`. Establish `h3` using `h1.congr (ε := 1 / (p:ℝ) - r) (by linarith) (fun t ht => by`. Conclude with `hG t ⟨by linarith [ht.1], by linarith [ht.2]⟩)`.

Use `h3.unique h2` as an intermediate fact. Use `mul_left_cancel₀ hp0.ne' this` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hconst` using `slopes_const hp hs hm kA kB antiA antiB hbq hgp`. Take `⟨n, hn⟩ : ∃ n : ℤ, n = kA (1/2) - m * kB (1/2)` from `⟨_, rfl⟩`.

Establish `raG : ∀ r ∈ Set.Ioo (0:ℝ) 1, RightAffine (fun t => A t - m * B t) r n`. Introduce `r hr`. Use `(raA r hr).sub_mul (m:ℝ) (raB r hr)` as an intermediate fact. Establish `e` using `hconst (1/2) r (by norm_num) (by norm_num) hr.1 hr.2`. Establish `e' : ((kA r : ℝ) - m * kB r) = (n:ℝ)` using `by rw [hn]; exact_mod_cast e`.

Rewrite `this` using `[e']`. Then use the resulting hypothesis. Establish `raH : ∀ r ∈ Set.Ioo (0:ℝ) 1, RightAffine (fun t => (fun t => A t - m * B t) t + (-(n:ℝ)) * t) r 0`. Introduce `r hr`. Use `(raG r hr).add_linear (-(n:ℝ))` as an intermediate fact. Rewrite `this` using `[add_neg_cancel]`. Then use the resulting hypothesis.

Establish `hcont : ContinuousOn (fun t => (fun t => A t - m * B t) t + (-(n:ℝ)) * t) (Set.Ioc 0 1)` using `(hAcont.sub (continuousOn_const.mul hBcont)).add (continuousOn_const.mul continuousOn_id)`. Establish `hH` using `const_of_rightAffine_zero hcont raH`. Establish `hpinv : (p:ℝ) * (1 / p) = 1` using `mul_one_div_cancel hp0.ne'`. Establish `hpm : (1:ℝ) / p ∈ Set.Ioc (0:ℝ) (1 / p)` using `⟨by positivity, le_rfl⟩`. Establish `hGp` using `hG (1 / p) hpm`.

Rewrite `hGp` using `[hpinv]`. Establish `hHp` using `hH (1 / p) ⟨by positivity, by rw [div_le_one hp0]; exact hp1.le⟩`. Simplify using `only at hHp`. Establish `key : ((p:ℝ) - 1) * ((A 1 - m * B 1) - n) = 0`. Take the linear combination `(-1) * hGp + (-(p:ℝ)) * hHp + (-(n:ℝ)) * hpinv`.

Establish `hG1 : A 1 - m * B 1 = n`. Establish `hne : (p:ℝ) - 1 ≠ 0` using `by linarith`. Use `(mul_eq_zero.mp key).resolve_left hne` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨n, fun r hr => ?_⟩` and prove the remaining obligations.

Use `hH r hr` as an intermediate fact. Simplify using `only at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem p_homogeneous_difference_linear : ∀ (p h s m : ℕ), 2 ≤ p → s < h → 1 ≤ m → ∀ A B : ℝ → ℝ, ConcaveOn ℝ (Set.Ioc 0 1) A → ConcaveOn ℝ (Set.Ioc 0 1) B → ContinuousOn A (Set.Ioc 0 1) → ContinuousOn B (Set.Ioc 0 1) → (∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧ ∀ t ∈ Set.Icc r (r + δ), A t = A r + k * (t - r)) → (∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧ ∀ t ∈ Set.Icc r (r + δ), B t = B r + k * (t - r)) → (∀ r ∈ Set.Ioc (0 : ℝ) 1, (p : ℝ) ^ h * B (r / (p : ℝ) ^ h) = B r + s * r) → (∀ r ∈ Set.Ioc (0 : ℝ) (1 / p), A (p * r) - m * B (p * r) = p * (A r - m * B r)) → ∃ n : ℤ, ∀ r ∈ Set.Ioc (0 : ℝ) 1, A r - m * B r = n * r := by
  intro p h s m hp hs hm A B hAc hBc hAcont hBcont hA hB hBq hG
  have hp0 : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1:ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hq0 : (0:ℝ) < (p:ℝ) ^ h := by positivity
  have hq1 : (1:ℝ) ≤ (p:ℝ) ^ h := one_le_pow₀ hp1.le
  choose! kA δA hδA hδA1 hA' using hA
  choose! kB δB hδB hδB1 hB' using hB
  have raA : ∀ r ∈ Set.Ioo (0:ℝ) 1, RightAffine A r (kA r) :=
    fun r hr => ⟨δA r, hδA r hr, hA' r hr⟩
  have raB : ∀ r ∈ Set.Ioo (0:ℝ) 1, RightAffine B r (kB r) :=
    fun r hr => ⟨δB r, hδB r hr, hB' r hr⟩
  have antiA : ∀ r t : ℝ, 0 < r → r < t → t < 1 → kA t ≤ kA r := fun r t hr hrt ht => by
    exact_mod_cast RightAffine.anti_of_concave hAc hr hrt ht (raA r ⟨hr, by linarith⟩)
      (raA t ⟨by linarith, ht⟩)
  have antiB : ∀ r t : ℝ, 0 < r → r < t → t < 1 → kB t ≤ kB r := fun r t hr hrt ht => by
    exact_mod_cast RightAffine.anti_of_concave hBc hr hrt ht (raB r ⟨hr, by linarith⟩)
      (raB t ⟨by linarith, ht⟩)
  have hbq : ∀ r : ℝ, 0 < r → r < 1 → kB (r / (p:ℝ) ^ h) = kB r + s := by
    intro r hr hr1
    have hrq : r / (p:ℝ) ^ h ∈ Set.Ioo (0:ℝ) 1 :=
      ⟨by positivity, lt_of_le_of_lt (div_le_self hr.le hq1) hr1⟩
    have h1 := ((raB _ hrq).comp_mul (c := 1 / (p:ℝ) ^ h) (r := r) (by positivity)
      (by ring)).const_mul ((p:ℝ) ^ h)
    have h2 := (raB r ⟨hr, hr1⟩).add_linear (s:ℝ)
    have h3 : RightAffine (fun t => B t + s * t) r
        ((p:ℝ) ^ h * (1 / (p:ℝ) ^ h * kB (r / (p:ℝ) ^ h))) := by
      refine h1.congr (ε := 1 - r) (by linarith) (fun t ht => ?_)
      have := hBq t ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rw [show 1 / (p:ℝ) ^ h * t = t / (p:ℝ) ^ h by ring]; exact this
    have := h3.unique h2
    rw [← mul_assoc, mul_one_div_cancel hq0.ne', one_mul] at this
    exact_mod_cast this
  have hgp : ∀ r : ℝ, 0 < r → r < 1 / (p:ℝ) →
      kA (p * r) - m * kB (p * r) = kA r - m * kB r := by
    intro r hr hrp
    have hpr1 : (p:ℝ) * r < 1 := by rwa [lt_div_iff₀ hp0, mul_comm] at hrp
    have hp1' : 1 / (p:ℝ) < 1 := by rw [div_lt_one hp0]; exact hp1
    have hr1 : r < 1 := by linarith
    have hpr : (p:ℝ) * r ∈ Set.Ioo (0:ℝ) 1 := ⟨by positivity, hpr1⟩
    have h1 := ((raA _ hpr).sub_mul (m:ℝ) (raB _ hpr)).comp_mul (r := r) hp0 rfl
    have h2 := ((raA r ⟨hr, hr1⟩).sub_mul (m:ℝ) (raB r ⟨hr, hr1⟩)).const_mul (p:ℝ)
    have h3 := h1.congr (ε := 1 / (p:ℝ) - r) (by linarith) (fun t ht => by
      exact hG t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have := h3.unique h2
    have := mul_left_cancel₀ hp0.ne' this
    exact_mod_cast this
  have hconst := slopes_const hp hs hm kA kB antiA antiB hbq hgp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = kA (1/2) - m * kB (1/2) := ⟨_, rfl⟩
  have raG : ∀ r ∈ Set.Ioo (0:ℝ) 1, RightAffine (fun t => A t - m * B t) r n := by
    intro r hr
    have := (raA r hr).sub_mul (m:ℝ) (raB r hr)
    have e := hconst (1/2) r (by norm_num) (by norm_num) hr.1 hr.2
    have e' : ((kA r : ℝ) - m * kB r) = (n:ℝ) := by rw [hn]; exact_mod_cast e
    rwa [e'] at this
  have raH : ∀ r ∈ Set.Ioo (0:ℝ) 1,
      RightAffine (fun t => (fun t => A t - m * B t) t + (-(n:ℝ)) * t) r 0 := by
    intro r hr
    have := (raG r hr).add_linear (-(n:ℝ))
    rwa [add_neg_cancel] at this
  have hcont : ContinuousOn (fun t => (fun t => A t - m * B t) t + (-(n:ℝ)) * t)
      (Set.Ioc 0 1) :=
    (hAcont.sub (continuousOn_const.mul hBcont)).add (continuousOn_const.mul continuousOn_id)
  have hH := const_of_rightAffine_zero hcont raH
  have hpinv : (p:ℝ) * (1 / p) = 1 := mul_one_div_cancel hp0.ne'
  have hpm : (1:ℝ) / p ∈ Set.Ioc (0:ℝ) (1 / p) := ⟨by positivity, le_rfl⟩
  have hGp := hG (1 / p) hpm
  rw [hpinv] at hGp
  have hHp := hH (1 / p) ⟨by positivity, by rw [div_le_one hp0]; exact hp1.le⟩
  simp only at hHp
  have key : ((p:ℝ) - 1) * ((A 1 - m * B 1) - n) = 0 := by
    linear_combination (-1) * hGp + (-(p:ℝ)) * hHp + (-(n:ℝ)) * hpinv
  have hG1 : A 1 - m * B 1 = n := by
    have hne : (p:ℝ) - 1 ≠ 0 := by linarith
    have := (mul_eq_zero.mp key).resolve_left hne
    linarith
  refine ⟨n, fun r hr => ?_⟩
  have := hH r hr
  simp only at this
  linarith

end GlobalTheory.PHomCalc
