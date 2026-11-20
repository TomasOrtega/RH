import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LogbNn

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

/- English proof (translation)
Establish `hL : (11:ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `h0 : (0:ℝ) < l` using `by linarith`. Establish `h1 : (0:ℝ) < (l:ℝ) - 1` using `by linarith`. Establish `e0 : (l:ℝ) * (l:ℝ)⁻¹ = 1` using `mul_inv_cancel₀ h0.ne'`. Establish `e1 : ((l:ℝ) - 1) * ((l:ℝ) - 1)⁻¹ = 1` using `mul_inv_cancel₀ h1.ne'`.

Establish `p0 : 0 < (l:ℝ)⁻¹` using `inv_pos.mpr h0`. Establish `q0 : 0 < ((l:ℝ) - 1)⁻¹` using `inv_pos.mpr h1`. Establish `e2 : ((l:ℝ) - 1)⁻¹ - (l:ℝ)⁻¹ = (l:ℝ)⁻¹ * ((l:ℝ) - 1)⁻¹`. Take the linear combination `(-((l:ℝ) - 1)⁻¹) * e0 + (l:ℝ)⁻¹ * e1`. Establish `p11 : (l:ℝ)⁻¹ ≤ 1 / 11`.

Use `mul_le_mul_of_nonneg_right hL p0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `q10 : ((l:ℝ) - 1)⁻¹ ≤ 1 / 10`. Use `mul_le_mul_of_nonneg_right (show (10:ℝ) ≤ (l:ℝ) - 1 by linarith) q0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hqp : ((l:ℝ) - 1)⁻¹ ≤ 11 / 10 * (l:ℝ)⁻¹`. Use `mul_le_mul_of_nonneg_left q10 p0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩`.
-/
private theorem natCast_inv_and_sub_one_inv_bounds_of_eleven_le (l : ℕ) (hl : 11 ≤ l) :
    (l:ℝ) * (l:ℝ)⁻¹ = 1 ∧ ((l:ℝ) - 1) * ((l:ℝ) - 1)⁻¹ = 1 ∧ 0 < (l:ℝ)⁻¹ ∧ 0 < ((l:ℝ) - 1)⁻¹ ∧
      (l:ℝ)⁻¹ ≤ 1 / 11 ∧ ((l:ℝ) - 1)⁻¹ ≤ 1 / 10 ∧ ((l:ℝ) - 1)⁻¹ ≤ 11 / 10 * (l:ℝ)⁻¹ ∧
      ((l:ℝ) - 1)⁻¹ - (l:ℝ)⁻¹ = (l:ℝ)⁻¹ * ((l:ℝ) - 1)⁻¹ := by
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  have h0 : (0:ℝ) < l := by linarith
  have h1 : (0:ℝ) < (l:ℝ) - 1 := by linarith
  have e0 : (l:ℝ) * (l:ℝ)⁻¹ = 1 := mul_inv_cancel₀ h0.ne'
  have e1 : ((l:ℝ) - 1) * ((l:ℝ) - 1)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
  have p0 : 0 < (l:ℝ)⁻¹ := inv_pos.mpr h0
  have q0 : 0 < ((l:ℝ) - 1)⁻¹ := inv_pos.mpr h1
  have e2 : ((l:ℝ) - 1)⁻¹ - (l:ℝ)⁻¹ = (l:ℝ)⁻¹ * ((l:ℝ) - 1)⁻¹ := by
    linear_combination (-((l:ℝ) - 1)⁻¹) * e0 + (l:ℝ)⁻¹ * e1
  have p11 : (l:ℝ)⁻¹ ≤ 1 / 11 := by
    have := mul_le_mul_of_nonneg_right hL p0.le
    linarith
  have q10 : ((l:ℝ) - 1)⁻¹ ≤ 1 / 10 := by
    have := mul_le_mul_of_nonneg_right (show (10:ℝ) ≤ (l:ℝ) - 1 by linarith) q0.le
    linarith
  have hqp : ((l:ℝ) - 1)⁻¹ ≤ 11 / 10 * (l:ℝ)⁻¹ := by
    have := mul_le_mul_of_nonneg_left q10 p0.le
    linarith
  exact ⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩

/- English proof (translation)
Establish `hL : (11:ℝ) ≤ l` using `by exact_mod_cast hl`. Conclude with `Real.logb_nonneg (by linarith) hx`.
-/
private theorem logb_natCast_nonneg_of_one_le_of_eleven_le (l : ℕ) (hl : 11 ≤ l) {x : ℝ} (hx : 1 ≤ x) : 0 ≤ Real.logb l x := by
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  exact Real.logb_nonneg (by linarith) hx

/- English proof (translation)
Establish `hL : (11:ℝ) ≤ l` using `by exact_mod_cast hl`. Conclude with `Real.logb_le_logb_of_le (by linarith) hx hxy`.
-/
private theorem logb_natCast_le_logb_of_le_of_eleven_le (l : ℕ) (hl : 11 ≤ l) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.logb l x ≤ Real.logb l y := by
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  exact Real.logb_le_logb_of_le (by linarith) hx hxy

/- English proof (translation)
Establish `hHc : ((b + η + S : ℕ) : ℝ) = (b:ℝ) + η + S` using `by push_cast; ring`. Establish `hb1 : (1:ℝ) ≤ b` using `by exact_mod_cast hb`. Establish `hη0 : (0:ℝ) ≤ η` using `by positivity`. Establish `hS0 : (0:ℝ) ≤ S` using `by positivity`. Use `⟨?_, by positivity, by positivity, by positivity, by positivity, logb_natCast_nonneg_of_one_le_of_eleven_le l hl (by rw [hHc]; linarith), hHc⟩` and prove the remaining obligations.

Unfold `Sg`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem real_bounds_logb_and_nonneg_inv_mul_of_eleven_le (l : ℕ) (hl : 11 ≤ l) (b wm S η : ℕ) (hb : 1 ≤ b) :
    Sg l (b + η + S) wm S η = ((b + η + S : ℕ) : ℝ) * ((l:ℝ)⁻¹) ^ 2 + (wm:ℝ) * (l:ℝ)⁻¹ +
      (S:ℝ) * (l:ℝ)⁻¹ + (η:ℝ) * (l:ℝ)⁻¹ + Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) + 1 ∧
    0 ≤ ((b + η + S : ℕ) : ℝ) * ((l:ℝ)⁻¹) ^ 2 ∧ 0 ≤ (wm:ℝ) * (l:ℝ)⁻¹ ∧ 0 ≤ (S:ℝ) * (l:ℝ)⁻¹ ∧
    0 ≤ (η:ℝ) * (l:ℝ)⁻¹ ∧ 0 ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) ∧
    ((b + η + S : ℕ) : ℝ) = (b:ℝ) + η + S := by
  have hHc : ((b + η + S : ℕ) : ℝ) = (b:ℝ) + η + S := by push_cast; ring
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hη0 : (0:ℝ) ≤ η := by positivity
  have hS0 : (0:ℝ) ≤ S := by positivity
  refine ⟨?_, by positivity, by positivity, by positivity, by positivity,
    logb_natCast_nonneg_of_one_le_of_eleven_le l hl (by rw [hHc]; linarith), hHc⟩
  unfold Sg
  ring

/- English proof (translation)
Take `⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩` from `natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl`. Take `⟨hES, n1, n2, n3, n4, hlg, hHc⟩` from `real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb`. Establish `hL : (11:ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hl0 : (0:ℝ) < l` using `by linarith`. Establish `hb1 : (1:ℝ) ≤ b` using `by exact_mod_cast hb`.

Establish `hη0 : (0:ℝ) ≤ η` using `by positivity`. Establish `hS0 : (0:ℝ) ≤ S` using `by positivity`. Establish `hw0 : (0:ℝ) ≤ w` using `by positivity`. Establish `hbb0 : (b:ℝ) ≤ b₀` using `by exact_mod_cast hb₀`. Establish `hb0b : (b₀:ℝ) ≤ b + η` using `by exact_mod_cast hb₀'`.

Establish `h1r : (l:ℝ) * w + l * S ≤ b₀`. Establish `e : ((l * (w + S) : ℕ) : ℝ) = (l:ℝ) * w + l * S` using `by push_cast; ring`. Rewrite using `[← e]`. Conclude with `h1` after adjusting the coercions. Establish `h2r : (b₀:ℝ) ≤ l * w + l * S + l * η + η`.

Establish `e : ((l * (w + S + η) + η : ℕ) : ℝ) = (l:ℝ) * w + l * S + l * η + η` using `by push_cast; ring`. Rewrite using `[← e]`. Conclude with `h2` after adjusting the coercions. Establish `hlog0 : Real.logb l (b₀:ℝ) ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ))` using `logb_natCast_le_logb_of_le_of_eleven_le l hl (by linarith) (by rw [hHc]; linarith)`. Establish `hq : (b₀:ℝ) / l ≤ w + S + η + η * (l:ℝ)⁻¹`.

Establish `h3` using `mul_le_mul_of_nonneg_right h2r p0.le`. Establish `h4 : ((l:ℝ) * w + l * S + l * η + η) * (l:ℝ)⁻¹ = w + S + η + η * (l:ℝ)⁻¹`. Take the linear combination `((w:ℝ) + S + η) * e0`. Rewrite using `[div_eq_mul_inv]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmax : max 0 ((b₀ : ℝ) / l - (w + S) + 2 + Real.logb l b₀) ≤ η + η * (l:ℝ)⁻¹ + 2 + Real.logb l (2 * ((b + η + S : ℕ) : ℝ))` using `max_le (by linarith) (by linarith)`. Use `⟨by linarith, ?_⟩` and prove the remaining obligations. Introduce `Cb hCb`. Simplify using `only [div_eq_mul_inv]`. Establish `a1 : 0 ≤ (l:ℝ) * η` using `by positivity`.

Establish `a2 : 0 ≤ (l:ℝ) * S` using `by positivity`. Establish `a3 : 0 ≤ (b:ℝ) * (l:ℝ)⁻¹` using `by positivity`. Establish `a4 : 0 ≤ (l:ℝ) * Real.logb l (2 * ((b + η + S : ℕ) : ℝ))` using `mul_nonneg hl0.le hlg`. Establish `hηl : (η:ℝ) ≤ l * η` using `by nlinarith`. Establish `hX0 : 0 ≤ (l:ℝ) * η + l * S + b * (l:ℝ)⁻¹ + w + l * Real.logb l (2 * ((b + η + S : ℕ) : ℝ))` using `by linarith`.

Establish `hCX` using `mul_le_mul_of_nonneg_right hCb hX0`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem case1c (l : ℕ) (hl : 11 ≤ l) (b wm w S η b₀ : ℕ) (hb : 1 ≤ b) (hη : 20 * η ≤ b) (hS : 20 * S ≤ b)
    (hwm : 20 * wm ≤ b) (hw : w ≤ wm) (hb₀ : b ≤ b₀) (hb₀' : b₀ ≤ b + η)
    (h1 : l * (w + S) ≤ b₀) (h2 : b₀ ≤ l * (w + S + η) + η) (de : ℝ)
    (hde : de ≤ max 0 ((b₀ : ℝ) / l - (w + S) + 2 + Real.logb l b₀) + 1) :
    de + 6 * Sg l (b + η + S) wm S η ≤ η + 9 * Sg l (b + η + S) wm S η ∧
    ∀ Cb : ℝ, 2 ≤ Cb → |(l : ℝ) * w - b| ≤
      Cb * ((l : ℝ) * η + (l : ℝ) * S + (b : ℝ) / l + w + (l : ℝ) * Real.logb l (2 * ((b + η + S : ℕ) : ℝ))) := by
  obtain ⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩ := natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl
  obtain ⟨hES, n1, n2, n3, n4, hlg, hHc⟩ := real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hη0 : (0:ℝ) ≤ η := by positivity
  have hS0 : (0:ℝ) ≤ S := by positivity
  have hw0 : (0:ℝ) ≤ w := by positivity
  have hbb0 : (b:ℝ) ≤ b₀ := by exact_mod_cast hb₀
  have hb0b : (b₀:ℝ) ≤ b + η := by exact_mod_cast hb₀'
  have h1r : (l:ℝ) * w + l * S ≤ b₀ := by
    have e : ((l * (w + S) : ℕ) : ℝ) = (l:ℝ) * w + l * S := by push_cast; ring
    rw [← e]; exact_mod_cast h1
  have h2r : (b₀:ℝ) ≤ l * w + l * S + l * η + η := by
    have e : ((l * (w + S + η) + η : ℕ) : ℝ) = (l:ℝ) * w + l * S + l * η + η := by push_cast; ring
    rw [← e]; exact_mod_cast h2
  have hlog0 : Real.logb l (b₀:ℝ) ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) :=
    logb_natCast_le_logb_of_le_of_eleven_le l hl (by linarith) (by rw [hHc]; linarith)
  have hq : (b₀:ℝ) / l ≤ w + S + η + η * (l:ℝ)⁻¹ := by
    have h3 := mul_le_mul_of_nonneg_right h2r p0.le
    have h4 : ((l:ℝ) * w + l * S + l * η + η) * (l:ℝ)⁻¹ = w + S + η + η * (l:ℝ)⁻¹ := by
      linear_combination ((w:ℝ) + S + η) * e0
    rw [div_eq_mul_inv]
    linarith
  have hmax : max 0 ((b₀ : ℝ) / l - (w + S) + 2 + Real.logb l b₀) ≤
      η + η * (l:ℝ)⁻¹ + 2 + Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) :=
    max_le (by linarith) (by linarith)
  refine ⟨by linarith, ?_⟩
  intro Cb hCb
  simp only [div_eq_mul_inv]
  have a1 : 0 ≤ (l:ℝ) * η := by positivity
  have a2 : 0 ≤ (l:ℝ) * S := by positivity
  have a3 : 0 ≤ (b:ℝ) * (l:ℝ)⁻¹ := by positivity
  have a4 : 0 ≤ (l:ℝ) * Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) := mul_nonneg hl0.le hlg
  have hηl : (η:ℝ) ≤ l * η := by nlinarith
  have hX0 : 0 ≤ (l:ℝ) * η + l * S + b * (l:ℝ)⁻¹ + w +
      l * Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) := by linarith
  have hCX := mul_le_mul_of_nonneg_right hCb hX0
  rw [abs_le]
  constructor <;> linarith

/- English proof (translation)
Take `⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩` from `natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl`. Take `⟨hES, n1, n2, n3, n4, hlg, hHc⟩` from `real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb`. Establish `hL : (11:ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hl0 : (0:ℝ) < l` using `by linarith`. Establish `hb1 : (1:ℝ) ≤ b` using `by exact_mod_cast hb`.

Establish `hη0 : (0:ℝ) ≤ η` using `by positivity`. Establish `hS0 : (0:ℝ) ≤ S` using `by positivity`. Establish `hw1r : (1:ℝ) ≤ w` using `by exact_mod_cast hw1`. Establish `hwwm : (w:ℝ) ≤ wm` using `by exact_mod_cast hw`. Establish `hwmb : 20 * (wm:ℝ) ≤ b` using `by exact_mod_cast hwm`.

Establish `hbb0 : (b:ℝ) ≤ b₀` using `by exact_mod_cast hb₀`. Establish `hb0b : (b₀:ℝ) ≤ b + η` using `by exact_mod_cast hb₀'`. Establish `hE1 : 1 ≤ Sg l (b + η + S) wm S η` using `by linarith`. Simplify using `only [div_eq_mul_inv] at hA ⊢`. Prove the components needed by the constructor for the conclusion.

Establish `hlogw : Real.logb l (w:ℝ) ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ))` using `logb_natCast_le_logb_of_le_of_eleven_le l hl (by linarith) (by rw [hHc]; linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `Cb hCb hle hnot`. Establish `hler : (b₀:ℝ) + S ≤ l * w` using `by exact_mod_cast hle`. Rewrite `hnot` using `[not_le, abs_of_nonneg (by linarith : (0:ℝ) ≤ (l:ℝ) * w - b)]`.

Establish `a1 : 0 ≤ (l:ℝ) * η` using `by positivity`. Establish `a2 : 0 ≤ (l:ℝ) * S` using `by positivity`. Establish `a3 : 0 ≤ (b:ℝ) * (l:ℝ)⁻¹` using `by positivity`. Establish `a4 : 0 ≤ (l:ℝ) * Real.logb l (2 * ((b + η + S : ℕ) : ℝ))` using `mul_nonneg hl0.le hlg`. Establish `hX0 : 0 ≤ (l:ℝ) * η + l * S + b * (l:ℝ)⁻¹ + w + l * Real.logb l (2 * ((b + η + S : ℕ) : ℝ))` using `by linarith`.

Establish `hCX` using `mul_le_mul_of_nonneg_right hCb hX0`. Establish `hlA` using `mul_le_mul_of_nonneg_left hwA hl0.le`. Establish `hA'` using `mul_le_mul_of_nonneg_left hA hl0.le`. Establish `iA : (l:ℝ) * (((b₀:ℝ) + S + η) * (l:ℝ)⁻¹) = b₀ + S + η`. Take the linear combination `((b₀:ℝ) + S + η) * e0`.

Establish `hSl : (S:ℝ) ≤ l * S` using `by nlinarith`. Establish `key : (l:ℝ) * η - 2 * η < 2 * ((l:ℝ) * Sg l (b + η + S) wm S η)` using `by linarith`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Combine the linear relations using `[mul_le_mul_of_nonneg_left hc (show (0:ℝ) ≤ (l:ℝ) - 2 by linarith), mul_nonneg (show (0:ℝ) ≤ (l:ℝ) - 4 by linarith) (show (0:ℝ) ≤ Sg l (b + η + S) wm S η by linarith)]`.
-/
theorem case2b (l : ℕ) (hl : 11 ≤ l) (b wm w S η b₀ : ℕ) (hb : 1 ≤ b) (hη : 20 * η ≤ b) (hS : 20 * S ≤ b)
    (hwm : 20 * wm ≤ b) (hw : w ≤ wm) (hw1 : 1 ≤ w) (hb₀ : b ≤ b₀) (hb₀' : b₀ ≤ b + η) (A : ℝ)
    (hA : A ≤ ((b₀ : ℝ) + S + η) / l + 2 * Sg l (b + η + S) wm S η) (hwA : (w : ℝ) ≤ A + η) :
    (w : ℝ) - ((b₀ : ℝ) + S) / l + 2 + Real.logb l w ≤ η + 5 * Sg l (b + η + S) wm S η - 1 ∧
    ∀ Cb : ℝ, 2 ≤ Cb → b₀ + S ≤ l * w →
      ¬ |(l : ℝ) * w - b| ≤
        Cb * ((l : ℝ) * η + (l : ℝ) * S + (b : ℝ) / l + w + (l : ℝ) * Real.logb l (2 * ((b + η + S : ℕ) : ℝ))) →
      (η : ℝ) < 4 * Sg l (b + η + S) wm S η := by
  obtain ⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩ := natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl
  obtain ⟨hES, n1, n2, n3, n4, hlg, hHc⟩ := real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hη0 : (0:ℝ) ≤ η := by positivity
  have hS0 : (0:ℝ) ≤ S := by positivity
  have hw1r : (1:ℝ) ≤ w := by exact_mod_cast hw1
  have hwwm : (w:ℝ) ≤ wm := by exact_mod_cast hw
  have hwmb : 20 * (wm:ℝ) ≤ b := by exact_mod_cast hwm
  have hbb0 : (b:ℝ) ≤ b₀ := by exact_mod_cast hb₀
  have hb0b : (b₀:ℝ) ≤ b + η := by exact_mod_cast hb₀'
  have hE1 : 1 ≤ Sg l (b + η + S) wm S η := by linarith
  simp only [div_eq_mul_inv] at hA ⊢
  constructor
  · have hlogw : Real.logb l (w:ℝ) ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) :=
      logb_natCast_le_logb_of_le_of_eleven_le l hl (by linarith) (by rw [hHc]; linarith)
    linarith
  · intro Cb hCb hle hnot
    have hler : (b₀:ℝ) + S ≤ l * w := by exact_mod_cast hle
    rw [not_le, abs_of_nonneg (by linarith : (0:ℝ) ≤ (l:ℝ) * w - b)] at hnot
    have a1 : 0 ≤ (l:ℝ) * η := by positivity
    have a2 : 0 ≤ (l:ℝ) * S := by positivity
    have a3 : 0 ≤ (b:ℝ) * (l:ℝ)⁻¹ := by positivity
    have a4 : 0 ≤ (l:ℝ) * Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) := mul_nonneg hl0.le hlg
    have hX0 : 0 ≤ (l:ℝ) * η + l * S + b * (l:ℝ)⁻¹ + w +
        l * Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) := by linarith
    have hCX := mul_le_mul_of_nonneg_right hCb hX0
    have hlA := mul_le_mul_of_nonneg_left hwA hl0.le
    have hA' := mul_le_mul_of_nonneg_left hA hl0.le
    have iA : (l:ℝ) * (((b₀:ℝ) + S + η) * (l:ℝ)⁻¹) = b₀ + S + η := by
      linear_combination ((b₀:ℝ) + S + η) * e0
    have hSl : (S:ℝ) ≤ l * S := by nlinarith
    have key : (l:ℝ) * η - 2 * η < 2 * ((l:ℝ) * Sg l (b + η + S) wm S η) := by linarith
    by_contra hc
    push_neg at hc
    linarith [mul_le_mul_of_nonneg_left hc (show (0:ℝ) ≤ (l:ℝ) - 2 by linarith),
      mul_nonneg (show (0:ℝ) ≤ (l:ℝ) - 4 by linarith)
        (show (0:ℝ) ≤ Sg l (b + η + S) wm S η by linarith)]

/- English proof (translation)
Take `⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩` from `natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl`. Take `⟨hES, n1, n2, n3, n4, hlg, hHc⟩` from `real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb`. Establish `hL : (11:ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hl0 : (0:ℝ) < l` using `by linarith`. Establish `hb1 : (1:ℝ) ≤ b` using `by exact_mod_cast hb`.

Establish `hη0 : (0:ℝ) ≤ η` using `by positivity`. Establish `hS0 : (0:ℝ) ≤ S` using `by positivity`. Establish `hηA : 0 ≤ ((η : ℝ) + A) / l` using `div_nonneg (by linarith) hl0.le`. Establish `hx0 : 0 ≤ (11 / 10 : ℝ) * (2 * σ + ((η : ℝ) + A) / l + 2 + Real.logb l (2 * ((b + η + S : ℕ) : ℝ)))` using `by linarith`. Establish `hfl` using `Nat.floor_le hx0`.

Rewrite using `[Nat.cast_add_one]`. Simplify using `only [div_eq_mul_inv] at hfl hA ⊢`. Establish `f1` using `mul_le_mul_of_nonneg_right hA p0.le`. Establish `f2` using `mul_le_mul_of_nonneg_right hqp p0.le`. Establish `hHη : 0 ≤ ((b + η + S : ℕ) : ℝ) + η` using `by positivity`.

Establish `f3` using `mul_le_mul_of_nonneg_left f2 hHη`. Establish `f4` using `mul_le_mul_of_nonneg_left p11 n4`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem floor_succ_le_ten_mul_errorScale (l : ℕ) (hl : 11 ≤ l) (b wm S η : ℕ) (hb : 1 ≤ b) (hη : 20 * η ≤ b) (hS : 20 * S ≤ b)
    (hwm : 20 * wm ≤ b) (σ A : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 3 * Sg l (b + η + S) wm S η) (hA0 : 0 ≤ A)
    (hA : A ≤ (((b + η + S : ℕ) : ℝ) + η) / ((l : ℝ) - 1) + 1) :
    ((⌊(11 / 10 : ℝ) * (2 * σ + ((η : ℝ) + A) / l + 2 + Real.logb l (2 * ((b + η + S : ℕ) : ℝ)))⌋₊ + 1 : ℕ) : ℝ) ≤
      10 * Sg l (b + η + S) wm S η := by
  obtain ⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩ := natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl
  obtain ⟨hES, n1, n2, n3, n4, hlg, hHc⟩ := real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hη0 : (0:ℝ) ≤ η := by positivity
  have hS0 : (0:ℝ) ≤ S := by positivity
  have hηA : 0 ≤ ((η : ℝ) + A) / l := div_nonneg (by linarith) hl0.le
  have hx0 : 0 ≤ (11 / 10 : ℝ) * (2 * σ + ((η : ℝ) + A) / l + 2 +
      Real.logb l (2 * ((b + η + S : ℕ) : ℝ))) := by linarith
  have hfl := Nat.floor_le hx0
  rw [Nat.cast_add_one]
  simp only [div_eq_mul_inv] at hfl hA ⊢
  have f1 := mul_le_mul_of_nonneg_right hA p0.le
  have f2 := mul_le_mul_of_nonneg_right hqp p0.le
  have hHη : 0 ≤ ((b + η + S : ℕ) : ℝ) + η := by positivity
  have f3 := mul_le_mul_of_nonneg_left f2 hHη
  have f4 := mul_le_mul_of_nonneg_left p11 n4
  linarith

/- English proof (translation)
Take `⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩` from `natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl`. Take `⟨hES, n1, n2, n3, n4, hlg, hHc⟩` from `real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb`. Establish `hL : (11:ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hl0 : (0:ℝ) < l` using `by linarith`. Establish `hb1 : (1:ℝ) ≤ b` using `by exact_mod_cast hb`.

Establish `hη0 : (0:ℝ) ≤ η` using `by positivity`. Establish `hS0 : (0:ℝ) ≤ S` using `by positivity`. Establish `hηr : 20 * (η:ℝ) ≤ b` using `by exact_mod_cast hη`. Establish `hSr : 20 * (S:ℝ) ≤ b` using `by exact_mod_cast hS`. Establish `hb₁r : (b:ℝ) ≤ b₁` using `by exact_mod_cast hb₁`.

Simplify using `only [div_eq_mul_inv] at hA`. Establish `hHη : 0 ≤ ((b + η + S : ℕ) : ℝ) + η` using `by positivity`. Establish `f1` using `mul_le_mul_of_nonneg_left q10 hHη`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_sub_sub_sub (l : ℕ) (hl : 11 ≤ l) (b wm S η b₁ : ℕ) (hb : 1 ≤ b) (hη : 20 * η ≤ b) (hS : 20 * S ≤ b)
    (hwm : 20 * wm ≤ b) (hb₁ : b ≤ b₁) (hsm : 40 * Sg l (b + η + S) wm S η ≤ (b : ℝ) / 4) (A s₁ : ℝ)
    (hA : A ≤ (((b + η + S : ℕ) : ℝ) + η) / ((l : ℝ) - 1) + 1) (hs₁ : s₁ ≤ 10 * Sg l (b + η + S) wm S η) :
    1 ≤ (b₁ : ℝ) - η - A - s₁ + 1 := by
  obtain ⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩ := natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl
  obtain ⟨hES, n1, n2, n3, n4, hlg, hHc⟩ := real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hη0 : (0:ℝ) ≤ η := by positivity
  have hS0 : (0:ℝ) ≤ S := by positivity
  have hηr : 20 * (η:ℝ) ≤ b := by exact_mod_cast hη
  have hSr : 20 * (S:ℝ) ≤ b := by exact_mod_cast hS
  have hb₁r : (b:ℝ) ≤ b₁ := by exact_mod_cast hb₁
  simp only [div_eq_mul_inv] at hA
  have hHη : 0 ≤ ((b + η + S : ℕ) : ℝ) + η := by positivity
  have f1 := mul_le_mul_of_nonneg_left q10 hHη
  linarith

/- English proof (translation)
Take `⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩` from `natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl`. Establish `hh : (1:ℝ) ≤ h` using `by exact_mod_cast h1`. Establish `hlg : 0 ≤ Real.logb l (2 * (h:ℝ))` using `logb_natCast_nonneg_of_one_le_of_eleven_le l hl (by linarith)`. Establish `hlogy : Real.logb l y ≤ Real.logb l (2 * (h:ℝ))` using `logb_natCast_le_logb_of_le_of_eleven_le l hl (by linarith) hy2`. Simplify using `only [div_eq_mul_inv] at hy hs₁ ⊢`.

Establish `hηA : 0 ≤ (η + A) * (l:ℝ)⁻¹` using `mul_nonneg (by linarith) p0.le`. Establish `hs0 : 0 < s₁` using `by linarith`. Establish `hsP` using `mul_le_mul_of_nonneg_left p11 hs0.le`. Introduce `hcon`. Break down `le_max_iff.mp hcon with hc | hc` into its components or cases.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_le_max_of_lt (l : ℕ) (hl : 11 ≤ l) (h : ℕ) (h1 : 1 ≤ h) (σ A s₁ η b₁ y : ℝ) (hσ0 : 0 ≤ σ)
    (hA0 : 0 ≤ A) (hη0 : 0 ≤ η) (hy1 : 1 ≤ y) (hy : y ≤ b₁ / l) (hy2 : y ≤ 2 * h)
    (hs₁ : (11 / 10 : ℝ) * (2 * σ + (η + A) / l + 2 + Real.logb l (2 * (h : ℝ))) < s₁) :
    ¬ (s₁ - 2 * σ ≤ max 0 (y - (b₁ - η - A - s₁ + 1) / l + 2 + Real.logb l y)) := by
  obtain ⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩ := natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl
  have hh : (1:ℝ) ≤ h := by exact_mod_cast h1
  have hlg : 0 ≤ Real.logb l (2 * (h:ℝ)) := logb_natCast_nonneg_of_one_le_of_eleven_le l hl (by linarith)
  have hlogy : Real.logb l y ≤ Real.logb l (2 * (h:ℝ)) := logb_natCast_le_logb_of_le_of_eleven_le l hl (by linarith) hy2
  simp only [div_eq_mul_inv] at hy hs₁ ⊢
  have hηA : 0 ≤ (η + A) * (l:ℝ)⁻¹ := mul_nonneg (by linarith) p0.le
  have hs0 : 0 < s₁ := by linarith
  have hsP := mul_le_mul_of_nonneg_left p11 hs0.le
  intro hcon
  rcases le_max_iff.mp hcon with hc | hc
  · linarith
  · linarith

/- English proof (translation)
Take `⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩` from `natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl`. Take `⟨hES, n1, n2, n3, n4, hlg, hHc⟩` from `real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb`. Establish `hL : (11:ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hl0 : (0:ℝ) < l` using `by linarith`. Establish `hb1 : (1:ℝ) ≤ b` using `by exact_mod_cast hb`.

Establish `hη0 : (0:ℝ) ≤ η` using `by positivity`. Establish `hS0 : (0:ℝ) ≤ S` using `by positivity`. Establish `hH0 : (0:ℝ) ≤ H` using `by positivity`. Establish `hHr : (H:ℝ) ≤ b + 2 * η + S` using `by exact_mod_cast hH`. Establish `hb₁r : (b:ℝ) ≤ b₁` using `by exact_mod_cast hb₁`.

Establish `hb₁r' : (b₁:ℝ) ≤ b + η` using `by exact_mod_cast hb₁'`. Establish `hlc : ((cW l H : ℕ) : ℝ) ≤ 2 + Real.logb l (2 * ((b + η + S : ℕ) : ℝ))`. Establish `hlogH : Real.logb l ((H:ℝ) + 1) ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ))` using `logb_natCast_le_logb_of_le_of_eleven_le l hl (by linarith) (by rw [hHc]; linarith)`. Establish `hlogH0 : 0 ≤ Real.logb l ((H:ℝ) + 1)` using `logb_natCast_nonneg_of_one_le_of_eleven_le l hl (by linarith)`. Establish `hc` using `Nat.ceil_lt_add_one (show (0:ℝ) ≤ 1 + Real.logb l ((H:ℝ) + 1) by linarith)`.

Unfold `cW`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlb : Real.logb l ((b₁:ℝ) + η - 1) ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ))`. Break down `eq_or_lt_of_le (show (0:ℝ) ≤ (b₁:ℝ) + η - 1 by linarith) with hz | hz` into its components or cases. Rewrite using `[← hz, Real.logb_zero]`.

Conclude with `hlg`. Conclude with `logb_natCast_le_logb_of_le_of_eleven_le l hl hz (by rw [hHc]; linarith)`. Simplify using `only [div_eq_mul_inv, ← inv_pow] at ha ⊢`. Establish `g1` using `mul_le_mul_of_nonneg_right ha q0.le`. Establish `hT : (2 * (l:ℝ) - 1) * ((l:ℝ) - 1)⁻¹ ≤ 21 / 10` using `by linarith`.

Establish `hQ2` using `mul_le_mul hqp hqp q0.le (by positivity)`. Establish `g2` using `mul_le_mul (mul_le_mul_of_nonneg_left hT hH0) hQ2 (mul_nonneg q0.le q0.le) (by positivity)`. Establish `g3` using `mul_le_mul_of_nonneg_right (show (H:ℝ) ≤ ((b + η + S : ℕ) : ℝ) + η by rw [hHc]; linarith) (mul_nonneg p0.le p0.le)`. Establish `g4` using `mul_le_mul_of_nonneg_left p11 n4`. Establish `g5` using `mul_le_mul_of_nonneg_right hlc q0.le`.

Establish `g6` using `mul_le_mul_of_nonneg_left q10 (show (0:ℝ) ≤ 2 + Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) by linarith)`. Establish `g7` using `mul_le_mul_of_nonneg_left hqp (show (0:ℝ) ≤ (S:ℝ) + 2 * η by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem div_add_logb_le_eight_mul_errorScale (l : ℕ) (hl : 11 ≤ l) (b wm S η b₁ H : ℕ) (hb : 1 ≤ b) (hη : 20 * η ≤ b) (hS : 20 * S ≤ b)
    (hwm : 20 * wm ≤ b) (hb₁ : b ≤ b₁) (hb₁' : b₁ ≤ b + η) (hH : H ≤ b + 2 * η + S) (a : ℝ) (ha0 : 1 ≤ a)
    (ha : a ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + cW l H + 1) :
    (3 * a + S + 2 * η - 2) / ((l : ℝ) - 1) + Real.logb l ((b₁ : ℝ) + η - 1) ≤ 8 * Sg l (b + η + S) wm S η := by
  obtain ⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩ := natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl
  obtain ⟨hES, n1, n2, n3, n4, hlg, hHc⟩ := real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hη0 : (0:ℝ) ≤ η := by positivity
  have hS0 : (0:ℝ) ≤ S := by positivity
  have hH0 : (0:ℝ) ≤ H := by positivity
  have hHr : (H:ℝ) ≤ b + 2 * η + S := by exact_mod_cast hH
  have hb₁r : (b:ℝ) ≤ b₁ := by exact_mod_cast hb₁
  have hb₁r' : (b₁:ℝ) ≤ b + η := by exact_mod_cast hb₁'
  have hlc : ((cW l H : ℕ) : ℝ) ≤ 2 + Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) := by
    have hlogH : Real.logb l ((H:ℝ) + 1) ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) :=
      logb_natCast_le_logb_of_le_of_eleven_le l hl (by linarith) (by rw [hHc]; linarith)
    have hlogH0 : 0 ≤ Real.logb l ((H:ℝ) + 1) := logb_natCast_nonneg_of_one_le_of_eleven_le l hl (by linarith)
    have hc := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 1 + Real.logb l ((H:ℝ) + 1) by linarith)
    unfold cW
    linarith
  have hlb : Real.logb l ((b₁:ℝ) + η - 1) ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) := by
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ (b₁:ℝ) + η - 1 by linarith) with hz | hz
    · rw [← hz, Real.logb_zero]; exact hlg
    · exact logb_natCast_le_logb_of_le_of_eleven_le l hl hz (by rw [hHc]; linarith)
  simp only [div_eq_mul_inv, ← inv_pow] at ha ⊢
  have g1 := mul_le_mul_of_nonneg_right ha q0.le
  have hT : (2 * (l:ℝ) - 1) * ((l:ℝ) - 1)⁻¹ ≤ 21 / 10 := by linarith
  have hQ2 := mul_le_mul hqp hqp q0.le (by positivity)
  have g2 := mul_le_mul (mul_le_mul_of_nonneg_left hT hH0) hQ2 (mul_nonneg q0.le q0.le)
    (by positivity)
  have g3 := mul_le_mul_of_nonneg_right
    (show (H:ℝ) ≤ ((b + η + S : ℕ) : ℝ) + η by rw [hHc]; linarith) (mul_nonneg p0.le p0.le)
  have g4 := mul_le_mul_of_nonneg_left p11 n4
  have g5 := mul_le_mul_of_nonneg_right hlc q0.le
  have g6 := mul_le_mul_of_nonneg_left q10
    (show (0:ℝ) ≤ 2 + Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) by linarith)
  have g7 := mul_le_mul_of_nonneg_left hqp (show (0:ℝ) ≤ (S:ℝ) + 2 * η by positivity)
  linarith

/- English proof (translation)
Take `⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩` from `natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl`. Take `⟨hES, n1, n2, n3, n4, hlg, hHc⟩` from `real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb`. Simplify using `only [div_eq_mul_inv, ← inv_pow] at hσ₁ hv`. Establish `hBqp : B * ((l:ℝ) - 1)⁻¹ - B * (l:ℝ)⁻¹ = B * ((l:ℝ)⁻¹ * ((l:ℝ) - 1)⁻¹)`. Take the linear combination `B * e2`.

Establish `f1` using `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqp p0.le) hB0`. Establish `f2` using `mul_le_mul_of_nonneg_right hB (sq_nonneg (l:ℝ)⁻¹)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sub_le_fourteen_mul_errorScale (l : ℕ) (hl : 11 ≤ l) (b wm S η : ℕ) (hb : 1 ≤ b) (σ₁ E σ B w b₁ v : ℝ) (hB0 : 0 ≤ B)
    (hB : B ≤ ((b + η + S : ℕ) : ℝ)) (hσ₁ : σ₁ ≤ B / ((l : ℝ) - 1) + 1)
    (hE : E ≤ 8 * Sg l (b + η + S) wm S η) (hσ : σ ≤ 3 * Sg l (b + η + S) wm S η)
    (hv : (w + S - b₁) + B / l - B / (l : ℝ) ^ 2 - 2 - Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) ≤ v) :
    (σ₁ + E + σ + w + S - b₁) - v ≤ 14 * Sg l (b + η + S) wm S η := by
  obtain ⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩ := natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl
  obtain ⟨hES, n1, n2, n3, n4, hlg, hHc⟩ := real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb
  simp only [div_eq_mul_inv, ← inv_pow] at hσ₁ hv
  have hBqp : B * ((l:ℝ) - 1)⁻¹ - B * (l:ℝ)⁻¹ = B * ((l:ℝ)⁻¹ * ((l:ℝ) - 1)⁻¹) := by
    linear_combination B * e2
  have f1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqp p0.le) hB0
  have f2 := mul_le_mul_of_nonneg_right hB (sq_nonneg (l:ℝ)⁻¹)
  linarith

/- English proof (translation)
Take `⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩` from `natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl`. Take `⟨hES, n1, n2, n3, n4, hlg, hHc⟩` from `real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb`. Establish `hL : (11:ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hl0 : (0:ℝ) < l` using `by linarith`. Establish `hb1 : (1:ℝ) ≤ b` using `by exact_mod_cast hb`.

Establish `hη0 : (0:ℝ) ≤ η` using `by positivity`. Establish `hS0 : (0:ℝ) ≤ S` using `by positivity`. Establish `hw0 : (0:ℝ) ≤ w` using `by positivity`. Establish `hb₁r : (b:ℝ) ≤ b₁` using `by exact_mod_cast hb₁`. Establish `hb₁r' : (b₁:ℝ) ≤ b + η` using `by exact_mod_cast hb₁'`.

Establish `hE1 : 1 ≤ Sg l (b + η + S) wm S η` using `by linarith`. Establish `hηP` using `mul_le_mul_of_nonneg_left p11 hη0`. Simplify using `only [div_eq_mul_inv] at hA hs`. Use `split_ifs with hc`. Apply the tactic sequence `rcases le_max_iff.mp hs with h' | h' <;> linarith`.

Rewrite `hc` using `[not_le]`. Simplify using `only [div_eq_mul_inv] at hc`. Establish `a1 : 0 ≤ (l:ℝ) * η` using `by positivity`. Establish `a2 : 0 ≤ (l:ℝ) * S` using `by positivity`. Establish `a3 : 0 ≤ (b:ℝ) * (l:ℝ)⁻¹` using `by positivity`.

Establish `a4 : 0 ≤ (l:ℝ) * Real.logb l (2 * ((b + η + S : ℕ) : ℝ))` using `mul_nonneg hl0.le hlg`. Establish `hX0 : 0 ≤ (l:ℝ) * η + l * S + b * (l:ℝ)⁻¹ + w + l * Real.logb l (2 * ((b + η + S : ℕ) : ℝ))` using `by linarith`. Establish `hCX` using `mul_le_mul_of_nonneg_right hCb hX0`. Break down `lt_abs.mp hc with hc' | hc'` into its components or cases. Establish `hlw` using `mul_lt_mul_of_pos_left hth hl0`.

Establish `hA'` using `mul_le_mul_of_nonneg_left hA hl0.le`. Establish `iA : (l:ℝ) * (((b₁:ℝ) + S + η) * (l:ℝ)⁻¹) = b₁ + S + η`. Take the linear combination `((b₁:ℝ) + S + η) * e0`. Establish `hσ'` using `mul_le_mul_of_nonneg_left hσ hl0.le`. Establish `hLE` using `mul_le_mul_of_nonneg_left hE1 hl0.le`.

Establish `hSl : (S:ℝ) ≤ l * S` using `by nlinarith`. Establish `key : (l:ℝ) * η - 2 * η < 21 / 2 * ((l:ℝ) * Sg l (b + η + S) wm S η)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hηb : (η:ℝ) ≤ 77 / 6 * Sg l (b + η + S) wm S η`. Assume the negation of the conclusion as `hcc`.

Use `push_neg at hcc`. Combine the linear relations using `[mul_le_mul_of_nonneg_left hcc.le (show (0:ℝ) ≤ (l:ℝ) - 2 by linarith), mul_nonneg (show (0:ℝ) ≤ (l:ℝ) - 11 by linarith) (show (0:ℝ) ≤ Sg l (b + η + S) wm S η by linarith)]`. Apply the tactic sequence `rcases le_max_iff.mp hs with h' | h' <;> linarith`. Establish `hlw : (l:ℝ) * w < b` using `by linarith`. Establish `hwP` using `mul_lt_mul_of_pos_right hlw p0`.

Establish `iw : (l:ℝ) * w * (l:ℝ)⁻¹ = w` using `by linear_combination (w:ℝ) * e0`. Establish `hbP` using `mul_le_mul_of_nonneg_right hb₁r p0.le`. Apply the tactic sequence `rcases le_max_iff.mp hs with h' | h' <;> linarith`.
-/
theorem le_band_add_errorScale (l : ℕ) (hl : 11 ≤ l) (b wm w S η b₁ : ℕ) (hb : 1 ≤ b) (hη : 20 * η ≤ b) (hS : 20 * S ≤ b)
    (hwm : 20 * wm ≤ b) (hw : w ≤ wm) (hb₁ : b ≤ b₁) (hb₁' : b₁ ≤ b + η) (A σ s Cb : ℝ) (hCb : 2 ≤ Cb)
    (hA : A ≤ ((b₁ : ℝ) + S + η) / l + 5 / 2 * Sg l (b + η + S) wm S η) (hσ : σ ≤ 3 * Sg l (b + η + S) wm S η)
    (hth : (w : ℝ) < A + η + 2 * σ + 2)
    (hs : s ≤ max 1 ((w : ℝ) - ((b₁ : ℝ) + S) / l + 16 / 5 * Sg l (b + η + S) wm S η)) :
    s ≤ η * (if |(l : ℝ) * w - b| ≤
        Cb * ((l : ℝ) * η + (l : ℝ) * S + (b : ℝ) / l + w + (l : ℝ) * Real.logb l (2 * ((b + η + S : ℕ) : ℝ)))
        then 1 else 0) + 28 * Sg l (b + η + S) wm S η := by
  obtain ⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩ := natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl
  obtain ⟨hES, n1, n2, n3, n4, hlg, hHc⟩ := real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hη0 : (0:ℝ) ≤ η := by positivity
  have hS0 : (0:ℝ) ≤ S := by positivity
  have hw0 : (0:ℝ) ≤ w := by positivity
  have hb₁r : (b:ℝ) ≤ b₁ := by exact_mod_cast hb₁
  have hb₁r' : (b₁:ℝ) ≤ b + η := by exact_mod_cast hb₁'
  have hE1 : 1 ≤ Sg l (b + η + S) wm S η := by linarith
  have hηP := mul_le_mul_of_nonneg_left p11 hη0
  simp only [div_eq_mul_inv] at hA hs
  split_ifs with hc
  · rcases le_max_iff.mp hs with h' | h' <;> linarith
  · rw [not_le] at hc
    simp only [div_eq_mul_inv] at hc
    have a1 : 0 ≤ (l:ℝ) * η := by positivity
    have a2 : 0 ≤ (l:ℝ) * S := by positivity
    have a3 : 0 ≤ (b:ℝ) * (l:ℝ)⁻¹ := by positivity
    have a4 : 0 ≤ (l:ℝ) * Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) := mul_nonneg hl0.le hlg
    have hX0 : 0 ≤ (l:ℝ) * η + l * S + b * (l:ℝ)⁻¹ + w +
        l * Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) := by linarith
    have hCX := mul_le_mul_of_nonneg_right hCb hX0
    rcases lt_abs.mp hc with hc' | hc'
    · have hlw := mul_lt_mul_of_pos_left hth hl0
      have hA' := mul_le_mul_of_nonneg_left hA hl0.le
      have iA : (l:ℝ) * (((b₁:ℝ) + S + η) * (l:ℝ)⁻¹) = b₁ + S + η := by
        linear_combination ((b₁:ℝ) + S + η) * e0
      have hσ' := mul_le_mul_of_nonneg_left hσ hl0.le
      have hLE := mul_le_mul_of_nonneg_left hE1 hl0.le
      have hSl : (S:ℝ) ≤ l * S := by nlinarith
      have key : (l:ℝ) * η - 2 * η < 21 / 2 * ((l:ℝ) * Sg l (b + η + S) wm S η) := by
        linarith
      have hηb : (η:ℝ) ≤ 77 / 6 * Sg l (b + η + S) wm S η := by
        by_contra hcc
        push_neg at hcc
        linarith [mul_le_mul_of_nonneg_left hcc.le (show (0:ℝ) ≤ (l:ℝ) - 2 by linarith),
          mul_nonneg (show (0:ℝ) ≤ (l:ℝ) - 11 by linarith)
            (show (0:ℝ) ≤ Sg l (b + η + S) wm S η by linarith)]
      rcases le_max_iff.mp hs with h' | h' <;> linarith
    · have hlw : (l:ℝ) * w < b := by linarith
      have hwP := mul_lt_mul_of_pos_right hlw p0
      have iw : (l:ℝ) * w * (l:ℝ)⁻¹ = w := by linear_combination (w:ℝ) * e0
      have hbP := mul_le_mul_of_nonneg_right hb₁r p0.le
      rcases le_max_iff.mp hs with h' | h' <;> linarith

/- English proof (translation)
Take `⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩` from `natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl`. Take `⟨hES, n1, n2, n3, n4, hlg, hHc⟩` from `real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb`. Establish `hs1` using `le_trans (le_max_left _ _) hsi`. Establish `hs2` using `le_trans (le_max_right _ _) hsi`. Simplify using `only [div_eq_mul_inv, ← inv_pow] at hs2 hs`.

Establish `g` using `mul_le_mul_of_nonneg_left p11 n4`. Apply `max_le` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Apply the tactic sequence `rcases le_max_iff.mp hs with h' | h' <;> linarith`.
-/
theorem max_sub_le_errorScale (l : ℕ) (hl : 11 ≤ l) (b wm w S η : ℕ) (hb : 1 ≤ b) (B s si' : ℝ)
    (hsi : max 0 ((w : ℝ) - B / l - η / (l : ℝ) ^ 2 - 1) ≤ si')
    (hs : s ≤ max 1 ((w : ℝ) - B / l + 16 / 5 * Sg l (b + η + S) wm S η)) :
    max 0 (s - si') ≤ 43 / 10 * Sg l (b + η + S) wm S η := by
  obtain ⟨e0, e1, p0, q0, p11, q10, hqp, e2⟩ := natCast_inv_and_sub_one_inv_bounds_of_eleven_le l hl
  obtain ⟨hES, n1, n2, n3, n4, hlg, hHc⟩ := real_bounds_logb_and_nonneg_inv_mul_of_eleven_le l hl b wm S η hb
  have hs1 := le_trans (le_max_left _ _) hsi
  have hs2 := le_trans (le_max_right _ _) hsi
  simp only [div_eq_mul_inv, ← inv_pow] at hs2 hs
  have g := mul_le_mul_of_nonneg_left p11 n4
  apply max_le
  · linarith
  · rcases le_max_iff.mp hs with h' | h' <;> linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
