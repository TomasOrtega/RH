import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramProductIdentities

namespace Formalism.FourierDecayAlt.P.PBD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd

def LevelOneWordEstimate : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (q : ℝ → ℝ) (w : List (Letter ℝ S)) (N : ℕ) (dl Y : ℝ),
    8 ≤ N → w.length ≤ N → (N : ℝ) ^ 2 / 8 ≤ dl →
    (∀ l ∈ w, if l.plus then dl ≤ |Y - l.pt| else dl ≤ |Y - l.pt| ∧ dl ≤ |Y - (l.pt - 1)|) →
    q Y ≠ 0 →
    Real.exp (-2) ≤ qw q w Y / q Y ∧ qw q w Y / q Y ≤ Real.exp 2

/- English proof (translation)
Establish `hdl0 : 0 < dl` using `by linarith`. Establish `hz0 : z ≠ 0`. Introduce `h`. Rewrite `hz` using `[h, abs_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hx : |1 / z| ≤ 1 / dl`. Rewrite using `[abs_div, abs_one]`. Conclude with `one_div_le_one_div_of_le hdl0 hz`. Establish `hx8 : 1 / dl ≤ 1 / 8` using `one_div_le_one_div_of_le (by norm_num) hdl`. Establish `hx0 : 0 < 1 / dl` using `by positivity`.

Rewrite using `[add_div, div_self hz0]`. Establish `h1` using `abs_le.mp hx`. Prove the components needed by the constructor for the conclusion. Establish `hexp : 1 + 2 * (1 / dl) ≤ Real.exp (2 * (1 / dl))`. Combine the linear relations using `[Real.add_one_le_exp (2 * (1 / dl))]`.

Establish `hone : Real.exp (-2 * (1 / dl)) * Real.exp (2 * (1 / dl)) = 1`. Rewrite using `[← Real.exp_add]`. Simplify using the standard rewrite rules. Establish `hpos` using `Real.exp_pos (-2 * (1 / dl))`. Establish `h2 : Real.exp (-2 * (1 / dl)) * (1 + 2 * (1 / dl)) ≤ 1`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3 : Real.exp (-2 * (1 / dl)) ≤ 1 - 1 / dl`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h4 : (1 - 1 / dl) * (1 + 2 * (1 / dl)) < Real.exp (-2 * (1 / dl)) * (1 + 2 * (1 / dl))` using `mul_lt_mul_of_pos_right hc (by positivity)`.

Use polynomial arithmetic with `[mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ 1 - 2 * (1 / dl))]`. Combine the linear relations using `[h1.1]`. Combine the linear relations using `[Real.add_one_le_exp (1 / dl), h1.2]`.
-/
private lemma exp_le_succ_div_self_le_exp_of_le_abs {z dl : ℝ} (hdl : 8 ≤ dl) (hz : dl ≤ |z|) :
    Real.exp (-2 * (1 / dl)) ≤ (z + 1) / z ∧ (z + 1) / z ≤ Real.exp (1 / dl) := by
  have hdl0 : 0 < dl := by linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, abs_zero] at hz
    linarith
  have hx : |1 / z| ≤ 1 / dl := by
    rw [abs_div, abs_one]
    exact one_div_le_one_div_of_le hdl0 hz
  have hx8 : 1 / dl ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hdl
  have hx0 : 0 < 1 / dl := by positivity
  rw [add_div, div_self hz0]
  have h1 := abs_le.mp hx
  constructor
  · have hexp : 1 + 2 * (1 / dl) ≤ Real.exp (2 * (1 / dl)) := by
      linarith [Real.add_one_le_exp (2 * (1 / dl))]
    have hone : Real.exp (-2 * (1 / dl)) * Real.exp (2 * (1 / dl)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hpos := Real.exp_pos (-2 * (1 / dl))
    have h2 : Real.exp (-2 * (1 / dl)) * (1 + 2 * (1 / dl)) ≤ 1 := by
      calc Real.exp (-2 * (1 / dl)) * (1 + 2 * (1 / dl))
          ≤ Real.exp (-2 * (1 / dl)) * Real.exp (2 * (1 / dl)) := mul_le_mul_of_nonneg_left hexp hpos.le
        _ = 1 := hone
    have h3 : Real.exp (-2 * (1 / dl)) ≤ 1 - 1 / dl := by
      by_contra hc
      push_neg at hc
      have h4 : (1 - 1 / dl) * (1 + 2 * (1 / dl)) < Real.exp (-2 * (1 / dl)) * (1 + 2 * (1 / dl)) :=
        mul_lt_mul_of_pos_right hc (by positivity)
      nlinarith [mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ 1 - 2 * (1 / dl))]
    linarith [h1.1]
  · linarith [Real.add_one_le_exp (1 / dl), h1.2]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simp [qw, div_self hq]`. Consider the case `cons l w ih`. Take `⟨ih1, ih2⟩` from `ih (fun l' hl' => hw l' (List.mem_cons_of_mem l hl'))`. Establish `hl` using `hw l (List.mem_cons.2 (Or.inl rfl))`.

Choose the witnesses or unpack the hypotheses as in `⟨F, hF, hF1, hF2⟩ : ∃ F, qw q (l :: w) Y / q Y = qw q w Y / q Y * F ∧ Real.exp (-2 * (1 / dl)) ≤ F ∧ F ≤ Real.exp (1 / dl) := by`. Consider the cases of `hp : l.plus`. Simplify using `only [hp, Bool.false_eq_true, ↓reduceIte] at hl`. Establish `hz : dl ≤ |l.pt - Y - 1|`. Rewrite using `[show l.pt - Y - 1 = -(Y - (l.pt - 1)) by ring, abs_neg]`.

Conclude with `hl.2`. Use `⟨(l.pt - Y - 1 + 1) / (l.pt - Y - 1), ?_, exp_le_succ_div_self_le_exp_of_le_abs hdl hz⟩` and prove the remaining obligations. Simplify using `only [qw, hp, Bool.false_eq_true, ↓reduceIte]`. Rewrite using `[mul_div_right_comm, show l.pt - Y - 1 + 1 = l.pt - Y by ring]`. Simplify using `only [hp, ↓reduceIte] at hl`.

Use `⟨(Y - l.pt + 1) / (Y - l.pt), ?_, exp_le_succ_div_self_le_exp_of_le_abs hdl hl⟩` and prove the remaining obligations. Simplify using `only [qw, hp, ↓reduceIte]`. Rewrite using `[mul_div_right_comm]`. Establish `hA : 0 < Real.exp (-2 * (1 / dl) * w.length)` using `Real.exp_pos _`. Establish `hr0 : 0 ≤ qw q w Y / q Y` using `le_trans hA.le ih1`.

Establish `hF0 : 0 ≤ F` using `le_trans (Real.exp_pos _).le hF1`. Rewrite using `[hF, List.length_cons]`. Use `push_cast`. Prove the components needed by the constructor for the conclusion. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Use `_ ≤ qw q w Y / q Y * F := mul_le_mul ih1 hF1 (Real.exp_pos _).le hr0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_add]`.

Put the polynomial expressions in normal form.
-/
private lemma exp_le_qw_div_le_exp_of_far_letters {S : Type} (q : ℝ → ℝ) (dl Y : ℝ) (hdl : 8 ≤ dl) (hq : q Y ≠ 0)
    (w : List (Letter ℝ S))
    (hw : ∀ l ∈ w, if l.plus then dl ≤ |Y - l.pt| else dl ≤ |Y - l.pt| ∧ dl ≤ |Y - (l.pt - 1)|) :
    Real.exp (-2 * (1 / dl) * w.length) ≤ qw q w Y / q Y ∧ qw q w Y / q Y ≤ Real.exp (1 / dl * w.length) := by
  induction w with
  | nil => simp [qw, div_self hq]
  | cons l w ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun l' hl' => hw l' (List.mem_cons_of_mem l hl'))
    have hl := hw l (List.mem_cons.2 (Or.inl rfl))
    obtain ⟨F, hF, hF1, hF2⟩ : ∃ F, qw q (l :: w) Y / q Y = qw q w Y / q Y * F ∧
        Real.exp (-2 * (1 / dl)) ≤ F ∧ F ≤ Real.exp (1 / dl) := by
      cases hp : l.plus
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hl
        have hz : dl ≤ |l.pt - Y - 1| := by
          rw [show l.pt - Y - 1 = -(Y - (l.pt - 1)) by ring, abs_neg]
          exact hl.2
        refine ⟨(l.pt - Y - 1 + 1) / (l.pt - Y - 1), ?_, exp_le_succ_div_self_le_exp_of_le_abs hdl hz⟩
        simp only [qw, hp, Bool.false_eq_true, ↓reduceIte]
        rw [mul_div_right_comm, show l.pt - Y - 1 + 1 = l.pt - Y by ring]
      · simp only [hp, ↓reduceIte] at hl
        refine ⟨(Y - l.pt + 1) / (Y - l.pt), ?_, exp_le_succ_div_self_le_exp_of_le_abs hdl hl⟩
        simp only [qw, hp, ↓reduceIte]
        rw [mul_div_right_comm]
    have hA : 0 < Real.exp (-2 * (1 / dl) * w.length) := Real.exp_pos _
    have hr0 : 0 ≤ qw q w Y / q Y := le_trans hA.le ih1
    have hF0 : 0 ≤ F := le_trans (Real.exp_pos _).le hF1
    rw [hF, List.length_cons]
    push_cast
    constructor
    · calc Real.exp (-2 * (1 / dl) * ((w.length : ℝ) + 1))
          = Real.exp (-2 * (1 / dl) * w.length) * Real.exp (-2 * (1 / dl)) := by
            rw [← Real.exp_add]
            ring_nf
        _ ≤ qw q w Y / q Y * F := mul_le_mul ih1 hF1 (Real.exp_pos _).le hr0
    · calc qw q w Y / q Y * F ≤ Real.exp (1 / dl * w.length) * Real.exp (1 / dl) :=
          mul_le_mul ih2 hF2 hF0 (Real.exp_pos _).le
        _ = Real.exp (1 / dl * ((w.length : ℝ) + 1)) := by
            rw [← Real.exp_add]
            ring_nf

/- English proof (translation)
Introduce `S _ _ q w N dl Y hN hlen hdl hw hq`. Establish `hN8 : (8 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hdl8 : 8 ≤ dl` using `by nlinarith [mul_le_mul hN8 hN8 (by norm_num) (by linarith)]`. Take `⟨h1, h2⟩` from `exp_le_qw_div_le_exp_of_far_letters q dl Y hdl8 hq w hw`. Establish `hdl0 : 0 < dl` using `by linarith`.

Establish `hlenR : (w.length : ℝ) ≤ N` using `by exact_mod_cast hlen`. Establish `hx : (1 / dl) * w.length ≤ 1`. Rewrite using `[div_mul_eq_mul_div, one_mul, div_le_one hdl0]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hN8 (by linarith : (0 : ℝ) ≤ N)]`. Prove the components needed by the constructor for the conclusion.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem level_one_word_estimate : LevelOneWordEstimate := by
  intro S _ _ q w N dl Y hN hlen hdl hw hq
  have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hdl8 : 8 ≤ dl := by nlinarith [mul_le_mul hN8 hN8 (by norm_num) (by linarith)]
  obtain ⟨h1, h2⟩ := exp_le_qw_div_le_exp_of_far_letters q dl Y hdl8 hq w hw
  have hdl0 : 0 < dl := by linarith
  have hlenR : (w.length : ℝ) ≤ N := by exact_mod_cast hlen
  have hx : (1 / dl) * w.length ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hdl0]
    nlinarith [mul_le_mul_of_nonneg_left hN8 (by linarith : (0 : ℝ) ≤ N)]
  constructor
  · calc Real.exp (-2) ≤ Real.exp (-2 * (1 / dl) * w.length) := Real.exp_le_exp.2 (by nlinarith)
      _ ≤ _ := h1
  · calc _ ≤ Real.exp (1 / dl * w.length) := h2
      _ ≤ Real.exp 2 := Real.exp_le_exp.2 (by linarith)

end Formalism.FourierDecayAlt.P.PBD

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.PBD.level_one_word_estimate`.
-/
theorem Formalism.FourierDecayAlt.P.level_one_word_estimate' : Formalism.FourierDecayAlt.P.PBD.LevelOneWordEstimate := Formalism.FourierDecayAlt.P.PBD.level_one_word_estimate
