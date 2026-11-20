import Mathlib
import Formalism.DropLevelBounds.Statement
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds

namespace GlobalTheory.FlowScaling

variable {l d : ℕ} [NeZero d]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ => le_rfl, fun s => by simpa using hD s⟩`.
-/
lemma isFlow_zero {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) : IsFlow l d D (fun _ _ => 0) :=
  ⟨fun _ _ => le_rfl, fun s => by simpa using hD s⟩

/- English proof (translation)
Establish `hl1 : (1 : ℝ) ≤ l` using `by exact_mod_cast hl`. Unfold `flowVal`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations. Establish `h2` using `hx.2 a`.

Establish `h3 : 0 ≤ ∑ i ∈ oddLevels d, x (a - (i : ZMod d)) i` using `Finset.sum_nonneg fun i _ => hx.1 _ i`. Establish `h4 : (l : ℝ) * ∑ i ∈ oddLevels d, x a i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun i hi => ?_` and prove the remaining obligations. Establish `hi0 : i ≠ 0`.

Introduce and unpack `rfl`. Conclude with `absurd (Finset.mem_filter.1 hi).2 (by decide)`. Conclude with `mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi0) (hx.1 a i)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma mul_flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    (l : ℝ) * flowVal d x ≤ ∑ a, D a := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  unfold flowVal
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have h2 := hx.2 a
  have h3 : 0 ≤ ∑ i ∈ oddLevels d, x (a - (i : ZMod d)) i :=
    Finset.sum_nonneg fun i _ => hx.1 _ i
  have h4 : (l : ℝ) * ∑ i ∈ oddLevels d, x a i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact absurd (Finset.mem_filter.1 hi).2 (by decide)
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi0) (hx.1 a i)
  linarith

/- English proof (translation)
Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast hl`. Rewrite using `[le_div_iff₀ hl0, mul_comm]`. Conclude with `mul_flowVal_le hl hx`.
-/
lemma flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ (∑ a, D a) / l := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  rw [le_div_iff₀ hl0, mul_comm]
  exact mul_flowVal_le hl hx

/- English proof (translation)
Use `le_csSup ⟨(∑ a, D a) / l, ?_⟩ ⟨x, hx, rfl⟩` and prove the remaining obligations. Introduce and unpack `t ⟨y, hy, rfl⟩`. Conclude with `flowVal_le hl hy`.
-/
lemma le_maxFlow (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ maxFlow l d D := by
  refine le_csSup ⟨(∑ a, D a) / l, ?_⟩ ⟨x, hx, rfl⟩
  rintro t ⟨y, hy, rfl⟩
  exact flowVal_le hl hy

/- English proof (translation)
Use `csSup_le ⟨_, _, isFlow_zero hD, rfl⟩ ?_` and prove the remaining obligations. Introduce and unpack `t ⟨y, hy, rfl⟩`. Conclude with `h y hy`.
-/
lemma maxFlow_le {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) {B : ℝ}
    (h : ∀ x, IsFlow l d D x → flowVal d x ≤ B) : maxFlow l d D ≤ B := by
  refine csSup_le ⟨_, _, isFlow_zero hD, rfl⟩ ?_
  rintro t ⟨y, hy, rfl⟩
  exact h y hy

/- English proof (translation)
The claim follows from `maxFlow_le hD fun _ hx => flowVal_le hl hx`.
-/
lemma maxFlow_le_div (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    maxFlow l d D ≤ (∑ a, D a) / l :=
  maxFlow_le hD fun _ hx => flowVal_le hl hx

/- English proof (translation)
Use `le_maxFlow hl (isFlow_zero (l := l) hD)` as an intermediate fact. Simplify `this` using `[flowVal]`.
-/
lemma maxFlow_nonneg (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    0 ≤ maxFlow l d D := by
  have := le_maxFlow hl (isFlow_zero (l := l) hD)
  simpa [flowVal] using this

/- English proof (translation)
Break down `hc.eq_or_lt with rfl | hc0` into its components or cases. Rewrite using `[zero_mul]`. Conclude with `maxFlow_nonneg hl fun a => by simpa using h a`. Rewrite using `[← le_div_iff₀' hc0]`. Use `maxFlow_le hD fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[le_div_iff₀' hc0]`. Establish `hf : IsFlow l d D' (fun a i => c * x a i)`. Use `⟨fun s i => mul_nonneg hc (hx.1 s i), fun s => le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_left (hx.2 s) hc).trans (h s))⟩` and prove the remaining obligations. Rewrite using `[mul_add, Finset.mul_sum, Finset.mul_sum]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Establish `hv : flowVal d (fun a i => c * x a i) = c * flowVal d x`. Simplify using `only [flowVal, Finset.mul_sum]`. Rewrite using `[← hv]`. Conclude with `le_maxFlow hl hf`.
-/
lemma mul_maxFlow_le (hl : 1 ≤ l) {c : ℝ} {D D' : ZMod d → ℝ} (hc : 0 ≤ c) (hD : ∀ a, 0 ≤ D a)
    (h : ∀ a, c * D a ≤ D' a) : c * maxFlow l d D ≤ maxFlow l d D' := by
  rcases hc.eq_or_lt with rfl | hc0
  · rw [zero_mul]
    exact maxFlow_nonneg hl fun a => by simpa using h a
  · rw [← le_div_iff₀' hc0]
    refine maxFlow_le hD fun x hx => ?_
    rw [le_div_iff₀' hc0]
    have hf : IsFlow l d D' (fun a i => c * x a i) := by
      refine ⟨fun s i => mul_nonneg hc (hx.1 s i), fun s => le_trans (le_of_eq ?_)
        ((mul_le_mul_of_nonneg_left (hx.2 s) hc).trans (h s))⟩
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have hv : flowVal d (fun a i => c * x a i) = c * flowVal d x := by
      simp only [flowVal, Finset.mul_sum]
    rw [← hv]
    exact le_maxFlow hl hf

/- English proof (translation)
Use `le_antisymm ?_ (mul_maxFlow_le hl hc hD fun _ => le_rfl)` and prove the remaining obligations. Break down `hc.eq_or_lt with rfl | hc0` into its components or cases. Use `maxFlow_le_div (D := fun a => 0 * D a) hl (fun a => by simp)` as an intermediate fact. Simplify using `using this`. Use `mul_maxFlow_le (c := c⁻¹) (D := fun a => c * D a) (D' := D) hl (inv_nonneg.2 hc) (fun a => mul_nonneg hc (hD a)) (fun a => by rw [inv_mul_cancel_left₀ hc0.ne'])` as an intermediate fact.

Rewrite `this` using `[inv_mul_le_iff₀ hc0]`. Then use the resulting hypothesis.
-/
lemma maxFlow_mul (hl : 1 ≤ l) {c : ℝ} {D : ZMod d → ℝ} (hc : 0 ≤ c) (hD : ∀ a, 0 ≤ D a) :
    maxFlow l d (fun a => c * D a) = c * maxFlow l d D := by
  refine le_antisymm ?_ (mul_maxFlow_le hl hc hD fun _ => le_rfl)
  rcases hc.eq_or_lt with rfl | hc0
  · have := maxFlow_le_div (D := fun a => 0 * D a) hl (fun a => by simp)
    simpa using this
  · have := mul_maxFlow_le (c := c⁻¹) (D := fun a => c * D a) (D' := D) hl (inv_nonneg.2 hc)
      (fun a => mul_nonneg hc (hD a)) (fun a => by rw [inv_mul_cancel_left₀ hc0.ne'])
    rwa [inv_mul_le_iff₀ hc0] at this

/- English proof (translation)
Introduce `l d _ hl c D hc hD`. Unfold `Fnum`. Rewrite using `[maxFlow_mul (by omega) hc hD, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fScale : FScale := by
  intro l d _ hl c D hc hD
  unfold Fnum
  rw [maxFlow_mul (by omega) hc hD, ← Finset.mul_sum]
  ring

/- English proof (translation)
Introduce `l d _ hl _ _ n T θ w W th hT hw hW hth hθ`. Establish `hl1 : 1 ≤ l` using `by omega`. Establish `hl3 : (3 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `hθ0 : 0 ≤ θ` using `(hth 0).1.trans (hth 0).2`.

Establish `hW0 : ∀ a, 0 ≤ W a` using `fun a => by`. Establish `h1 : 0 ≤ T * W a`. Rewrite using `[hW a]`. Conclude with `mul_nonneg (hw a).le (by linarith [(hth a).2])`. Conclude with `(mul_nonneg_iff_of_pos_left hT).1 h1`.

Establish `hnw : ∀ a, 0 ≤ (n : ℝ) * w a` using `fun a => mul_nonneg hn (hw a).le`. Establish `h1 : (1 - θ) * maxFlow l d (fun a => (n : ℝ) * w a) ≤ maxFlow l d (fun a => T * ((n : ℝ) * W a))`. Use `mul_maxFlow_le hl1 (by linarith) hnw fun a => ?_` and prove the remaining obligations. Establish `e : T * ((n : ℝ) * W a) = (1 - th a) * ((n : ℝ) * w a)`. Rewrite using `[mul_left_comm, hW a]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_le_mul_of_nonneg_right (by linarith [(hth a).2]) (hnw a)`. Establish `h2 : maxFlow l d (fun a => (n : ℝ) * w a) ≤ (∑ a, (n : ℝ) * w a) / l` using `maxFlow_le_div hl1 hnw`. Establish `h3 : ∑ a, T * ((n : ℝ) * W a) ≤ ∑ a, (n : ℝ) * w a`.

Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations. Establish `e : T * ((n : ℝ) * W a) = (1 - th a) * ((n : ℝ) * w a)`. Rewrite using `[mul_left_comm, hW a]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `mul_le_of_le_one_left (hnw a) (by linarith [(hth a).1])`. Establish `hg : 0 ≤ gam l` using `div_nonneg (by linarith) (by nlinarith)`. Establish `h4` using `mul_le_mul_of_nonneg_left h3 hg`. Establish `h5` using `mul_le_mul_of_nonneg_left h2 hθ0`. Establish `h6 : 0 ≤ θ * ((∑ a, (n : ℝ) * w a) / l)` using `mul_nonneg hθ0 (div_nonneg (Finset.sum_nonneg fun a _ => hnw a) (by linarith))`.

Establish `h7 : 6 * θ * n * (∑ a, w a) / l = 6 * (θ * ((∑ a, (n : ℝ) * w a) / l))`. Rewrite using `[← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← fScale l d (by omega) T (fun a => (n : ℝ) * W a) hT.le (fun a => mul_nonneg hn (hW0 a)), h7]`. Unfold `Fnum`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thetaShift : ThetaShift := by
  intro l d _ hl _ _ n T θ w W th hT hw hW hth hθ
  have hl1 : 1 ≤ l := by omega
  have hl3 : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hθ0 : 0 ≤ θ := (hth 0).1.trans (hth 0).2
  have hW0 : ∀ a, 0 ≤ W a := fun a => by
    have h1 : 0 ≤ T * W a := by
      rw [hW a]
      exact mul_nonneg (hw a).le (by linarith [(hth a).2])
    exact (mul_nonneg_iff_of_pos_left hT).1 h1
  have hnw : ∀ a, 0 ≤ (n : ℝ) * w a := fun a => mul_nonneg hn (hw a).le
  have h1 : (1 - θ) * maxFlow l d (fun a => (n : ℝ) * w a) ≤
      maxFlow l d (fun a => T * ((n : ℝ) * W a)) := by
    refine mul_maxFlow_le hl1 (by linarith) hnw fun a => ?_
    have e : T * ((n : ℝ) * W a) = (1 - th a) * ((n : ℝ) * w a) := by
      rw [mul_left_comm, hW a]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (by linarith [(hth a).2]) (hnw a)
  have h2 : maxFlow l d (fun a => (n : ℝ) * w a) ≤ (∑ a, (n : ℝ) * w a) / l :=
    maxFlow_le_div hl1 hnw
  have h3 : ∑ a, T * ((n : ℝ) * W a) ≤ ∑ a, (n : ℝ) * w a := by
    refine Finset.sum_le_sum fun a _ => ?_
    have e : T * ((n : ℝ) * W a) = (1 - th a) * ((n : ℝ) * w a) := by
      rw [mul_left_comm, hW a]; ring
    rw [e]
    exact mul_le_of_le_one_left (hnw a) (by linarith [(hth a).1])
  have hg : 0 ≤ gam l := div_nonneg (by linarith) (by nlinarith)
  have h4 := mul_le_mul_of_nonneg_left h3 hg
  have h5 := mul_le_mul_of_nonneg_left h2 hθ0
  have h6 : 0 ≤ θ * ((∑ a, (n : ℝ) * w a) / l) :=
    mul_nonneg hθ0 (div_nonneg (Finset.sum_nonneg fun a _ => hnw a) (by linarith))
  have h7 : 6 * θ * n * (∑ a, w a) / l = 6 * (θ * ((∑ a, (n : ℝ) * w a) / l)) := by
    rw [← Finset.mul_sum]; ring
  rw [← fScale l d (by omega) T (fun a => (n : ℝ) * W a) hT.le
    (fun a => mul_nonneg hn (hW0 a)), h7]
  unfold Fnum
  linarith

/- English proof (translation)
Introduce `n m D T hm hD hT h`. Establish `hm' : (0 : ℝ) < m` using `by exact_mod_cast hm`. Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Rewrite `h` using `[div_le_iff₀ hm']`. Establish `e : 6 * ((D + 4) / T) * n = 6 * (D + 4) * n / T` using `by ring`.

Rewrite using `[e, div_le_iff₀ hT]`. Use polynomial arithmetic with `[mul_nonneg hn (sub_nonneg.2 hD)]`.
-/
theorem thetaConst : ThetaConst := by
  intro n m D T hm hD hT h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_iff₀ hm'] at h
  have e : 6 * ((D + 4) / T) * n = 6 * (D + 4) * n / T := by ring
  rw [e, div_le_iff₀ hT]
  nlinarith [mul_nonneg hn (sub_nonneg.2 hD)]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fScale, thetaShift, thetaConst⟩`.
-/
theorem main : FScale ∧ ThetaShift ∧ ThetaConst := ⟨fScale, thetaShift, thetaConst⟩

end GlobalTheory.FlowScaling
