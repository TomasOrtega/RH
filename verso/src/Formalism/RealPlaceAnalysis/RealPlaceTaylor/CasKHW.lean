import Formalism.RealPlaceAnalysis.StatementA

open Finset

noncomputable section

namespace Formalism.REAL

/- English proof (translation)
Rewrite using `[Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]`. Unfold `rhoC`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma casKHW_two_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    2 * rhoC ε a = ∑ b, ((if a < b ∧ ε b = ε a then (1:ℝ) else 0) -
      (if b < a ∧ ε b = ε a then (1:ℝ) else 0)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
  unfold rhoC; ring

def casKHW_coef {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) (a b : Fin n) : ℝ :=
  if ε a = ε b then (if a = b then μ a ^ 2 else if a < b then μ a - μ b else 0) else 0

/- English proof (translation)
Unfold `casKHW_coef`. Distinguish the cases in `h : ε a = ε b`. Simplify using `only [h, if_true]`. Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases. Establish `hne : a ≠ b` using `ne_of_lt hab`.

Simplify using `only [hne, if_false, hab, if_true]`. Establish `h1` using `congrArg (fun T : Module.End ℂ V => T w) (hG a b b a)`. Simplify using `only [if_true, LinearMap.sub_apply, Module.End.mul_apply] at h1`. Establish `h0 : E a b w = 0` using `hK.2 a b hab h`. Rewrite `h1` using `[h0, map_zero, sub_zero, hK.1 a, hK.1 b]`.

Rewrite using `[Module.End.mul_apply, h1]`. Use `push_cast`. Rewrite using `[sub_smul]`. Simplify using `only [if_true, Module.End.mul_apply, hK.1 a, map_smul, smul_smul] push_cast`. Put the polynomial expressions in normal form.

Establish `hne : a ≠ b` using `ne_of_gt hab`. Establish `hnl : ¬ a < b` using `not_lt_of_gt hab`. Simplify using `only [hne, if_false, hnl]`. Rewrite using `[Module.End.mul_apply, hK.2 b a hab h.symm, map_zero]`. Simplify using the standard rewrite rules.

Simplify using `[h]`.
-/
lemma casKHW_term (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V)
    (hG : GlRel E) (hK : KHighest ε E μ w) (a b : Fin n) :
    (if ε a = ε b then E a b * E b a else 0) w = ((casKHW_coef ε μ a b : ℝ) : ℂ) • w := by
  unfold casKHW_coef
  by_cases h : ε a = ε b
  · simp only [h, if_true]
    rcases lt_trichotomy a b with hab | rfl | hab
    · have hne : a ≠ b := ne_of_lt hab
      simp only [hne, if_false, hab, if_true]
      have h1 := congrArg (fun T : Module.End ℂ V => T w) (hG a b b a)
      simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply] at h1
      have h0 : E a b w = 0 := hK.2 a b hab h
      rw [h0, map_zero, sub_zero, hK.1 a, hK.1 b] at h1
      rw [Module.End.mul_apply, h1]
      push_cast
      rw [sub_smul]
    · simp only [if_true, Module.End.mul_apply, hK.1 a, map_smul, smul_smul]
      push_cast; ring_nf
    · have hne : a ≠ b := ne_of_gt hab
      have hnl : ¬ a < b := not_lt_of_gt hab
      simp only [hne, if_false, hnl]
      rw [Module.End.mul_apply, hK.2 b a hab h.symm, map_zero]
      simp
  · simp [h]

/- English proof (translation)
Establish `hpt : ∀ a b, casKHW_coef ε μ a b = (if a = b then μ a ^ 2 else 0) + (if a < b ∧ ε b = ε a then μ a else 0) - (if a < b ∧ ε a = ε b then μ b else 0)`. Introduce `a b`. Unfold `casKHW_coef`. Distinguish the cases in `h : ε a = ε b`. Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases.

Simplify using `[h, hab, ne_of_lt hab]`. Simplify using the standard rewrite rules. Simplify using `[h, ne_of_gt hab, not_lt_of_gt hab]`. Establish `h' : ¬ ε b = ε a` using `fun e => h e.symm`. Distinguish the cases in `hab : a = b`.

Conclude with `absurd (congrArg ε hab) h`. Simplify using `[h, h', hab]`. Repeatedly rewrite using `[hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]`. Establish `e1 : ∑ a : Fin n, ∑ b : Fin n, (if a = b then μ a ^ 2 else 0) = ∑ a, μ a ^ 2`. Simplify using the standard rewrite rules.

Establish `e2 : ∑ a : Fin n, ∑ b : Fin n, (if a < b ∧ ε a = ε b then μ b else 0) = ∑ a : Fin n, ∑ b : Fin n, (if b < a ∧ ε b = ε a then μ a else 0)`. Rewrite using `[Finset.sum_comm]`. Establish `e3 : ∀ a, ∑ b : Fin n, (if a < b ∧ ε b = ε a then μ a else 0) - ∑ b : Fin n, (if b < a ∧ ε b = ε a then μ a else 0) = μ a * (2 * rhoC ε a)`. Introduce `a`. Rewrite using `[casKHW_two_rhoC, Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`. Rewrite using `[e1, e2, add_sub_assoc, ← Finset.sum_sub_distrib]`. Repeatedly rewrite using `[e3]`. Unfold `nsq dot`.

Rewrite using `[← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma casKHW_arith {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) :
    ∑ a, ∑ b, casKHW_coef ε μ a b = nsq (μ + rhoC ε) - nsq (rhoC ε) := by
  have hpt : ∀ a b, casKHW_coef ε μ a b =
      (if a = b then μ a ^ 2 else 0) + (if a < b ∧ ε b = ε a then μ a else 0) -
        (if a < b ∧ ε a = ε b then μ b else 0) := by
    intro a b
    unfold casKHW_coef
    by_cases h : ε a = ε b
    · rcases lt_trichotomy a b with hab | rfl | hab
      · simp [h, hab, ne_of_lt hab]
      · simp
      · simp [h, ne_of_gt hab, not_lt_of_gt hab]
    · have h' : ¬ ε b = ε a := fun e => h e.symm
      by_cases hab : a = b
      · exact absurd (congrArg ε hab) h
      · simp [h, h', hab]
  simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have e1 : ∑ a : Fin n, ∑ b : Fin n, (if a = b then μ a ^ 2 else 0) = ∑ a, μ a ^ 2 := by
    simp
  have e2 : ∑ a : Fin n, ∑ b : Fin n, (if a < b ∧ ε a = ε b then μ b else 0) =
      ∑ a : Fin n, ∑ b : Fin n, (if b < a ∧ ε b = ε a then μ a else 0) := by
    rw [Finset.sum_comm]
  have e3 : ∀ a, ∑ b : Fin n, (if a < b ∧ ε b = ε a then μ a else 0) -
      ∑ b : Fin n, (if b < a ∧ ε b = ε a then μ a else 0) = μ a * (2 * rhoC ε a) := by
    intro a
    rw [casKHW_two_rhoC, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [e1, e2, add_sub_assoc, ← Finset.sum_sub_distrib]
  simp_rw [e3]
  unfold nsq dot
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply]; ring

/- English proof (translation)
Introduce `V _ _ n ε E μ w hG hK`. Unfold `CasK`. Simplify using `only [LinearMap.sum_apply]`. Repeatedly rewrite using `[casKHW_term V n ε E μ w hG hK]`. Rewrite using `[← casKHW_arith ε μ]`.

Repeatedly rewrite using `[← Finset.sum_smul]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem compactCasimirOnHighestWeight_holds : CasKHighest := by
  intro V _ _ n ε E μ w hG hK
  unfold CasK
  simp only [LinearMap.sum_apply]
  simp_rw [casKHW_term V n ε E μ w hG hK]
  rw [← casKHW_arith ε μ]
  simp_rw [← Finset.sum_smul]
  push_cast
  rfl

end Formalism.REAL
