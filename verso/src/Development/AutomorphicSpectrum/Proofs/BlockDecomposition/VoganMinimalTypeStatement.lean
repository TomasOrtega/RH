import Mathlib
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass

namespace GlobalTheory.CompanionTheory.DiscreteSeries

/- English proof (translation)
Establish `hA : ({y | x < y ∧ ε y ≠ ε x} : Finset (Fin n)).card + ({y | x < y ∧ ε y = ε x} : Finset (Fin n)).card = ({y | x < y} : Finset (Fin n)).card`. Rewrite using `[Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun y _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases h : x < y <;> by_cases h' : ε y = ε x <;> simp [h, h']`. Establish `hB : ({y | y < x ∧ ε y ≠ ε x} : Finset (Fin n)).card + ({y | y < x ∧ ε y = ε x} : Finset (Fin n)).card = ({y | y < x} : Finset (Fin n)).card`.

Rewrite using `[Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun y _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases h : y < x <;> by_cases h' : ε y = ε x <;> simp [h, h']`. Establish `hA' : (({y | x < y ∧ ε y ≠ ε x} : Finset (Fin n)).card : ℝ) + (({y | x < y ∧ ε y = ε x} : Finset (Fin n)).card : ℝ) = (({y | x < y} : Finset (Fin n)).card : ℝ)`. Conclude with `hA` after adjusting the coercions.

Establish `hB' : (({y | y < x ∧ ε y ≠ ε x} : Finset (Fin n)).card : ℝ) + (({y | y < x ∧ ε y = ε x} : Finset (Fin n)).card : ℝ) = (({y | y < x} : Finset (Fin n)).card : ℝ)`. Conclude with `hB` after adjusting the coercions. Simplify using `only [Formalism.REAL.rhoN, Formalism.REAL.rhoC]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma two_mul_rhoN_add_rhoC_eq_card_sub_card {n : ℕ} (ε : Fin n → Bool) (x : Fin n) :
    2 * (Formalism.REAL.rhoN ε x + Formalism.REAL.rhoC ε x) =
      (({y | x < y} : Finset (Fin n)).card : ℝ) - (({y | y < x} : Finset (Fin n)).card : ℝ) := by
  have hA : ({y | x < y ∧ ε y ≠ ε x} : Finset (Fin n)).card
      + ({y | x < y ∧ ε y = ε x} : Finset (Fin n)).card = ({y | x < y} : Finset (Fin n)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h : x < y <;> by_cases h' : ε y = ε x <;> simp [h, h']
  have hB : ({y | y < x ∧ ε y ≠ ε x} : Finset (Fin n)).card
      + ({y | y < x ∧ ε y = ε x} : Finset (Fin n)).card = ({y | y < x} : Finset (Fin n)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h : y < x <;> by_cases h' : ε y = ε x <;> simp [h, h']
  have hA' : (({y | x < y ∧ ε y ≠ ε x} : Finset (Fin n)).card : ℝ)
      + (({y | x < y ∧ ε y = ε x} : Finset (Fin n)).card : ℝ)
      = (({y | x < y} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast hA
  have hB' : (({y | y < x ∧ ε y ≠ ε x} : Finset (Fin n)).card : ℝ)
      + (({y | y < x ∧ ε y = ε x} : Finset (Fin n)).card : ℝ)
      = (({y | y < x} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast hB
  simp only [Formalism.REAL.rhoN, Formalism.REAL.rhoC]
  linarith

/- English proof (translation)
Establish `h1` using `two_mul_rhoN_add_rhoC_eq_card_sub_card ε a`. Establish `h2` using `two_mul_rhoN_add_rhoC_eq_card_sub_card ε b`. Establish `c1 : ({y | b < y} : Finset (Fin n)).card ≤ ({y | a < y} : Finset (Fin n)).card`. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `y hy`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢`. Conclude with `lt_trans hab hy`. Establish `c2 : ({y | y < a} : Finset (Fin n)).card ≤ ({y | y < b} : Finset (Fin n)).card`. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `y hy`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢`. Conclude with `lt_trans hy hab`. Establish `c1' : (({y | b < y} : Finset (Fin n)).card : ℝ) ≤ (({y | a < y} : Finset (Fin n)).card : ℝ)`. Conclude with `c1` after adjusting the coercions. Establish `c2' : (({y | y < a} : Finset (Fin n)).card : ℝ) ≤ (({y | y < b} : Finset (Fin n)).card : ℝ)`.

Conclude with `c2` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma rhoN_add_rhoC_le_of_lt {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) :
    Formalism.REAL.rhoN ε b + Formalism.REAL.rhoC ε b ≤ Formalism.REAL.rhoN ε a + Formalism.REAL.rhoC ε a := by
  have h1 := two_mul_rhoN_add_rhoC_eq_card_sub_card ε a
  have h2 := two_mul_rhoN_add_rhoC_eq_card_sub_card ε b
  have c1 : ({y | b < y} : Finset (Fin n)).card ≤ ({y | a < y} : Finset (Fin n)).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact lt_trans hab hy
  have c2 : ({y | y < a} : Finset (Fin n)).card ≤ ({y | y < b} : Finset (Fin n)).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact lt_trans hy hab
  have c1' : (({y | b < y} : Finset (Fin n)).card : ℝ) ≤ (({y | a < y} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast c1
  have c2' : (({y | y < a} : Finset (Fin n)).card : ℝ) ≤ (({y | y < b} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast c2
  linarith

/- English proof (translation)
Unfold `Formalism.REAL.nsq Formalism.REAL.dot at *`. Establish `h2 : 0 ≤ ∑ a, w a * w a` using `Finset.sum_nonneg (fun a _ => mul_self_nonneg (w a))`. Establish `e : ∑ a, (v + w) a * (v + w) a = ∑ a, v a * v a + 2 * ∑ a, v a * w a + ∑ a, w a * w a`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl (fun a _ => by simp only [Pi.add_apply]; ring)`.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma nsq_le_nsq_add_of_dot_nonneg {n : ℕ} (v w : Fin n → ℝ) (h : 0 ≤ Formalism.REAL.dot v w) :
    Formalism.REAL.nsq v ≤ Formalism.REAL.nsq (v + w) := by
  unfold Formalism.REAL.nsq Formalism.REAL.dot at *
  have h2 : 0 ≤ ∑ a, w a * w a := Finset.sum_nonneg (fun a _ => mul_self_nonneg (w a))
  have e : ∑ a, (v + w) a * (v + w) a = ∑ a, v a * v a + 2 * ∑ a, v a * w a + ∑ a, w a * w a := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by simp only [Pi.add_apply]; ring)
  rw [e]
  linarith

/- English proof (translation)
Establish `hdot : Formalism.REAL.dot v (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) = ∑ a, ∑ b, (c a b : ℝ) * (v a - v b)`. Unfold `Formalism.REAL.dot`. Simplify using `only [Finset.sum_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, Formalism.REAL.root, Pi.sub_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hdot]`.

Use `Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => ?_))` and prove the remaining obligations. Distinguish the cases in `h0 : c a b = 0`. Simplify using `[h0]`. Conclude with `mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hmono a b (hc a b h0)))`.
-/
private lemma dot_nonneg_sum_root_of_antitone {n : ℕ} (v : Fin n → ℝ) (c : Fin n → Fin n → ℕ)
    (hc : ∀ a b : Fin n, c a b ≠ 0 → a < b) (hmono : ∀ a b : Fin n, a < b → v b ≤ v a) :
    0 ≤ Formalism.REAL.dot v (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) := by
  have hdot : Formalism.REAL.dot v (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b)
      = ∑ a, ∑ b, (c a b : ℝ) * (v a - v b) := by
    unfold Formalism.REAL.dot
    simp only [Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, Formalism.REAL.root, Pi.sub_apply, Pi.single_apply, mul_sub,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [hdot]
  refine Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => ?_))
  by_cases h0 : c a b = 0
  · simp [h0]
  · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hmono a b (hc a b h0)))

open GlobalTheory.LowestKTypeDetermines in

/- English proof (translation)
Introduce `n ε lam η hlam hη`. Take `⟨c, hc, rfl⟩` from `hη`. Establish `hk : ReciprocityTheory.ChartRestriction.DS.lowK ε lam = Formalism.QuantumDeterminants.lowK ε lam` using `by rfl`. Unfold `Formalism.MainNotions.S.vNormSq`. Rewrite using `[hk, add_right_comm]`.

Apply `nsq_le_nsq_add_of_dot_nonneg` to reduce the goal to its premises. Apply `dot_nonneg_sum_root_of_antitone _ c hc` to reduce the goal to its premises. Introduce `a b hab`. Simplify using `only [Formalism.QuantumDeterminants.lowK, two_nsmul, two_smul, Pi.add_apply, Pi.sub_apply]`. Establish `h1` using `rhoN_add_rhoC_le_of_lt ε hab`.

Establish `h2` using `hlam.1 hab`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem stepVogan : PositivityTheory.RgDs.Hilb.StepVogan := by
  intro n ε lam η hlam hη
  obtain ⟨c, hc, rfl⟩ := hη
  have hk : ReciprocityTheory.ChartRestriction.DS.lowK ε lam = Formalism.QuantumDeterminants.lowK ε lam := by rfl
  unfold Formalism.MainNotions.S.vNormSq
  rw [hk, add_right_comm]
  apply nsq_le_nsq_add_of_dot_nonneg
  apply dot_nonneg_sum_root_of_antitone _ c hc
  intro a b hab
  simp only [Formalism.QuantumDeterminants.lowK, two_nsmul, two_smul, Pi.add_apply, Pi.sub_apply]
  have h1 := rhoN_add_rhoC_le_of_lt ε hab
  have h2 := hlam.1 hab
  linarith

end GlobalTheory.CompanionTheory.DiscreteSeries
