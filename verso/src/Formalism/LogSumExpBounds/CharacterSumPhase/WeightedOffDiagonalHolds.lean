import Formalism.LogSumExpBounds.NuclearBound

namespace Formalism.NuclearRankWeightBounds.P

open Finset Formalism.NuclearRankWeightBounds.D

/- English proof (translation)
Introduce `N s ep h Y hY hz hh`. Take `⟨T, hT⟩ : ∃ T : Fin N → Fin N → ℝ, T = fun a b => ∑ i ∈ Ico 1 N, if a.val < i ∧ i ≤ b.val then s i else 0` from `⟨_, rfl⟩`. Establish `hsym : ∀ a b, ‖Y b a‖ = ‖Y a b‖`. Introduce `a b`. Rewrite using `[← hY.apply b a, norm_star]`.

Establish `hTlt : ∀ a b : Fin N, a < b → T a b = ∑ i ∈ Ico (a.val + 1) (b.val + 1), s i`. Introduce `a b hab`. Establish `hab' : a.val < b.val` using `hab`. Establish `hb` using `b.isLt`. Rewrite using `[hT]`.

Simplify using `only`. Rewrite using `[← Finset.sum_filter]`. Use `congr 1`. Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_Ico]`.

Use linear arithmetic over natural numbers and integers. Establish `hTgt : ∀ a b : Fin N, a < b → T b a = 0`. Introduce `a b hab`. Establish `hab' : a.val < b.val` using `hab`. Rewrite using `[hT]`.

Simplify using `only`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`. Use linear arithmetic over natural numbers and integers. Establish `hpt : ∀ a b, h * ‖Y a b‖ ^ 2 ≤ ‖Y a b‖ ^ 2 * T a b + ‖Y b a‖ ^ 2 * T b a`.

Introduce `a b`. Distinguish the cases in `he : ep a = ep b`. Simplify using `[hz a b he, hz b a he.symm]`. Rewrite using `[hsym a b]`. Break down `lt_trichotomy a b with hab | hab | hab` into its components or cases.

Establish `h3` using `hh b a hab (fun e => he e.symm)`. Rewrite using `[hTgt a b hab, mul_zero, add_zero, mul_comm, hTlt a b hab]`. Conclude with `mul_le_mul_of_nonneg_left h3 (sq_nonneg _)`. Conclude with `absurd (congrArg ep hab) he`. Establish `h3` using `hh a b hab he`.

Rewrite using `[hTgt b a hab, mul_zero, zero_add, mul_comm, hTlt b a hab]`. Conclude with `mul_le_mul_of_nonneg_left h3 (sq_nonneg _)`. Establish `hi : ∀ i : ℕ, (∑ a ∈ univ.filter (fun a : Fin N => a.val < i), ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2) = ∑ a, ∑ b, if a.val < i ∧ i ≤ b.val then ‖Y a b‖ ^ 2 else 0`. Introduce `i`. Rewrite using `[Finset.sum_filter]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_filter]`. Apply the tactic sequence `by_cases ha : a.val < i <;> simp [ha]`. Establish `hrhs : (∑ i ∈ Ico 1 N, s i * ∑ a ∈ univ.filter (fun a : Fin N => a.val < i), ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2) = ∑ a, ∑ b, ‖Y a b‖ ^ 2 * T a b`. Repeatedly rewrite using `[hi, hT, Finset.mul_sum]`.

Use `(Finset.sum_comm).trans ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `(Finset.sum_comm).trans ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> ring`. Establish `hhs : hs Y ^ 2 = ∑ a, ∑ b, ‖Y a b‖ ^ 2` using `Real.sq_sqrt (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity)`. Establish `hswap : (∑ a, ∑ b, ‖Y b a‖ ^ 2 * T b a) = ∑ a, ∑ b, ‖Y a b‖ ^ 2 * T a b` using `Finset.sum_comm`. Establish `hsum` using `Finset.sum_le_sum (fun a (_ : a ∈ (univ : Finset (Fin N))) => Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin N))) => hpt a b))`. Simplify using `only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum`.

Rewrite `hsum` using `[hswap]`. Rewrite using `[hrhs, hhs]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weighted_off_diagonal_holds : Formalism.NuclearRankWeightBounds.D.WeightedOff := by
  intro N s ep h Y hY hz hh
  classical
  obtain ⟨T, hT⟩ : ∃ T : Fin N → Fin N → ℝ,
      T = fun a b => ∑ i ∈ Ico 1 N, if a.val < i ∧ i ≤ b.val then s i else 0 := ⟨_, rfl⟩
  have hsym : ∀ a b, ‖Y b a‖ = ‖Y a b‖ := by
    intro a b
    rw [← hY.apply b a, norm_star]
  have hTlt : ∀ a b : Fin N, a < b → T a b = ∑ i ∈ Ico (a.val + 1) (b.val + 1), s i := by
    intro a b hab
    have hab' : a.val < b.val := hab
    have hb := b.isLt
    rw [hT]
    simp only
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  have hTgt : ∀ a b : Fin N, a < b → T b a = 0 := by
    intro a b hab
    have hab' : a.val < b.val := hab
    rw [hT]
    simp only
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    omega
  have hpt : ∀ a b, h * ‖Y a b‖ ^ 2 ≤ ‖Y a b‖ ^ 2 * T a b + ‖Y b a‖ ^ 2 * T b a := by
    intro a b
    by_cases he : ep a = ep b
    · simp [hz a b he, hz b a he.symm]
    rw [hsym a b]
    rcases lt_trichotomy a b with hab | hab | hab
    · have h3 := hh b a hab (fun e => he e.symm)
      rw [hTgt a b hab, mul_zero, add_zero, mul_comm, hTlt a b hab]
      exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    · exact absurd (congrArg ep hab) he
    · have h3 := hh a b hab he
      rw [hTgt b a hab, mul_zero, zero_add, mul_comm, hTlt b a hab]
      exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
  have hi : ∀ i : ℕ, (∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
      ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2)
      = ∑ a, ∑ b, if a.val < i ∧ i ≤ b.val then ‖Y a b‖ ^ 2 else 0 := by
    intro i
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter]
    by_cases ha : a.val < i <;> simp [ha]
  have hrhs : (∑ i ∈ Ico 1 N, s i *
      ∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
        ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2)
      = ∑ a, ∑ b, ‖Y a b‖ ^ 2 * T a b := by
    simp_rw [hi, hT, Finset.mul_sum]
    refine (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    refine (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  have hhs : hs Y ^ 2 = ∑ a, ∑ b, ‖Y a b‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity)
  have hswap : (∑ a, ∑ b, ‖Y b a‖ ^ 2 * T b a) = ∑ a, ∑ b, ‖Y a b‖ ^ 2 * T a b :=
    Finset.sum_comm
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (univ : Finset (Fin N))) =>
    Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin N))) => hpt a b))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hswap] at hsum
  rw [hrhs, hhs]
  linarith

end Formalism.NuclearRankWeightBounds.P
