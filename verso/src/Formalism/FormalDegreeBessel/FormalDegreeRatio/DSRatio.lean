import Formalism.FormalDegreeBessel.StatementDS
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds

open Finset Formalism.REAL

noncomputable section

namespace Formalism.QuantumDeterminants

/- English proof (translation)
Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `a _`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `b hb`. Establish `hab : a < b` using `by simpa using hb`.

Establish `: ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem fdegDen_ne_zero (n : ℕ) :
    (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro a _
  rw [Finset.prod_ne_zero_iff]
  intro b hb
  have hab : a < b := by simpa using hb
  have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

/- English proof (translation)
Introduce `n μ s hinj hint hinj'`. Establish `hD` using `fdegDen_ne_zero n`. Establish `hN : ∀ a b : Fin n, a < b → |μ a - μ b| ≠ 0` using `fun a b h => abs_ne_zero.mpr (sub_ne_zero.mpr (hinj.ne h.ne))`. Establish `es : ((μ + Pi.single s 1 : Fin n → ℝ)) s = μ s + 1` using `by simp`. Establish `eo : ∀ t, t ≠ s → ((μ + Pi.single s 1 : Fin n → ℝ)) t = μ t` using `fun t ht => by simp [Pi.single_apply, ht]`.

Use `set h : Fin n → ℝ := fun t => (μ s + 1 - μ t) / (μ s - μ t) with hh`. Establish `hsign : ∀ t, t ≠ s → |μ s + 1 - μ t| / |μ s - μ t| = h t`. Introduce `t ht`. Take `⟨m, hm⟩` from `hint s t`. Establish `h1 : μ s - μ t ≠ 0` using `sub_ne_zero.mpr (hinj.ne ht.symm)`.

Establish `h2 : μ s + 1 - μ t ≠ 0`. Use `hinj'.ne ht.symm` as an intermediate fact. Rewrite `this` using `[es, eo t ht]`. Conclude with `sub_ne_zero.mpr this`. Establish `e2 : μ s + 1 - μ t = (m : ℝ) + 1` using `by linarith`.

Rewrite `h1` using `[hm]`. Rewrite `h2` using `[e2]`. Establish `hm0 : m ≠ 0` using `by exact_mod_cast h1`. Establish `hm1 : m + 1 ≠ 0` using `by exact_mod_cast h2`. Rewrite using `[← abs_div, abs_of_pos]`.

Rewrite using `[e2, hm]`. Break down `lt_or_gt_of_ne hm0 with hneg | hpos` into its components or cases. Establish `hle : m ≤ -2` using `by omega`. Establish `: (m : ℝ) ≤ -2` using `by exact_mod_cast hle`. Apply the tactic sequence `apply div_pos_of_neg_of_neg <;> linarith`.

Establish `: (1 : ℝ) ≤ m` using `by exact_mod_cast hpos`. Apply the tactic sequence `apply div_pos <;> linarith`. Establish `hr : ∀ a b : Fin n, a < b → |((μ + Pi.single s 1 : Fin n → ℝ)) a - ((μ + Pi.single s 1 : Fin n → ℝ)) b| / |μ a - μ b| = (if a = s then h b else 1) * (if b = s then h a else 1)`. Introduce `a b hab`. Distinguish the cases in `has : a = s`.

Establish `hbs : b ≠ s` using `has ▸ hab.ne'`. Rewrite using `[if_pos has, if_neg hbs, mul_one, has, es, eo b hbs]`. Conclude with `hsign b hbs`. Distinguish the cases in `hbs : b = s`. Rewrite using `[if_neg has, if_pos hbs, one_mul, hbs, es, eo a has, abs_sub_comm (μ a), abs_sub_comm (μ a)]`.

Conclude with `hsign a has`. Rewrite using `[if_neg has, if_neg hbs, mul_one, eo a has, eo b hbs]`. Conclude with `div_self (hN a b hab)`. Unfold `fdegHC`. Rewrite using `[div_div_div_cancel_right₀ hD, ← Finset.prod_div_distrib]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_div_distrib]`. Conclude with `Finset.prod_congr rfl fun b hb => hr a b (by simpa using hb)`. Use `_ = ∏ t : Fin n, ((if s < t then h t else 1) * (if t < s then h t else 1)) := by`.

Simplify using `only [Finset.prod_mul_distrib]`. Use `congr 1`. Rewrite using `[Finset.prod_eq_single s]`. Rewrite using `[Finset.prod_filter]`. Conclude with `Finset.prod_congr rfl fun t _ => by simp`.

Introduce `a _ has`. Conclude with `Finset.prod_eq_one fun b _ => if_neg has`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ s) h'`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_ite_eq']`. Simplify using the standard rewrite rules. Use `_ = ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s') := by`. Rewrite using `[← Finset.filter_ne' univ s, Finset.prod_filter]`. Use `Finset.prod_congr rfl fun t _ => ?_` and prove the remaining obligations.

Break down `lt_trichotomy s t with hst | hst | hst` into its components or cases. Simplify using `[hst, hst.ne', not_lt.mpr hst.le, hh]`. Substitute `hst` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hst, hst.ne, not_lt.mpr hst.le, hh]`.
-/
theorem formalDegreeShiftRatio_holds : FdegRatio := by
  intro n μ s hinj hint hinj'
  have hD := fdegDen_ne_zero n
  have hN : ∀ a b : Fin n, a < b → |μ a - μ b| ≠ 0 := fun a b h =>
    abs_ne_zero.mpr (sub_ne_zero.mpr (hinj.ne h.ne))
  have es : ((μ + Pi.single s 1 : Fin n → ℝ)) s = μ s + 1 := by simp
  have eo : ∀ t, t ≠ s → ((μ + Pi.single s 1 : Fin n → ℝ)) t = μ t := fun t ht => by simp [Pi.single_apply, ht]
  set h : Fin n → ℝ := fun t => (μ s + 1 - μ t) / (μ s - μ t) with hh
  have hsign : ∀ t, t ≠ s → |μ s + 1 - μ t| / |μ s - μ t| = h t := by
    intro t ht
    obtain ⟨m, hm⟩ := hint s t
    have h1 : μ s - μ t ≠ 0 := sub_ne_zero.mpr (hinj.ne ht.symm)
    have h2 : μ s + 1 - μ t ≠ 0 := by
      have := hinj'.ne ht.symm
      rw [es, eo t ht] at this
      exact sub_ne_zero.mpr this
    have e2 : μ s + 1 - μ t = (m : ℝ) + 1 := by linarith
    rw [hm] at h1
    rw [e2] at h2
    have hm0 : m ≠ 0 := by exact_mod_cast h1
    have hm1 : m + 1 ≠ 0 := by exact_mod_cast h2
    rw [← abs_div, abs_of_pos]
    rw [e2, hm]
    rcases lt_or_gt_of_ne hm0 with hneg | hpos
    · have hle : m ≤ -2 := by omega
      have : (m : ℝ) ≤ -2 := by exact_mod_cast hle
      apply div_pos_of_neg_of_neg <;> linarith
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hpos
      apply div_pos <;> linarith
  have hr : ∀ a b : Fin n, a < b → |((μ + Pi.single s 1 : Fin n → ℝ)) a - ((μ + Pi.single s 1 : Fin n → ℝ)) b| / |μ a - μ b| =
      (if a = s then h b else 1) * (if b = s then h a else 1) := by
    intro a b hab
    by_cases has : a = s
    · have hbs : b ≠ s := has ▸ hab.ne'
      rw [if_pos has, if_neg hbs, mul_one, has, es, eo b hbs]
      exact hsign b hbs
    · by_cases hbs : b = s
      · rw [if_neg has, if_pos hbs, one_mul, hbs, es, eo a has, abs_sub_comm (μ a), abs_sub_comm (μ a)]
        exact hsign a has
      · rw [if_neg has, if_neg hbs, mul_one, eo a has, eo b hbs]
        exact div_self (hN a b hab)
  unfold fdegHC
  rw [div_div_div_cancel_right₀ hD, ← Finset.prod_div_distrib]
  calc ∏ a : Fin n, (∏ b ∈ univ.filter (fun b : Fin n => a < b),
          |((μ + Pi.single s 1 : Fin n → ℝ)) a - ((μ + Pi.single s 1 : Fin n → ℝ)) b|) /
          ∏ b ∈ univ.filter (fun b : Fin n => a < b), |μ a - μ b|
      = ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
          ((if a = s then h b else 1) * (if b = s then h a else 1)) := by
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [← Finset.prod_div_distrib]
        exact Finset.prod_congr rfl fun b hb => hr a b (by simpa using hb)
    _ = ∏ t : Fin n, ((if s < t then h t else 1) * (if t < s then h t else 1)) := by
        simp only [Finset.prod_mul_distrib]
        congr 1
        · rw [Finset.prod_eq_single s]
          · rw [Finset.prod_filter]
            exact Finset.prod_congr rfl fun t _ => by simp
          · intro a _ has
            exact Finset.prod_eq_one fun b _ => if_neg has
          · intro h'; exact absurd (Finset.mem_univ s) h'
        · refine Finset.prod_congr rfl fun a _ => ?_
          rw [Finset.prod_ite_eq']
          simp
    _ = ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s') := by
        rw [← Finset.filter_ne' univ s, Finset.prod_filter]
        refine Finset.prod_congr rfl fun t _ => ?_
        rcases lt_trichotomy s t with hst | hst | hst
        · simp [hst, hst.ne', not_lt.mpr hst.le, hh]
        · subst hst; simp
        · simp [hst, hst.ne, not_lt.mpr hst.le, hh]

/- English proof (translation)
Introduce `k hk`. Simplify using `only [fdegHC, Finset.prod_filter, Fin.prod_univ_two]`. Evaluate the numerical expressions. Apply the tactic sequence `all_goals first | linarith | (rw [abs_of_nonneg (by linarith)]; ring)`.
-/
theorem formalDegreeTwoByTwo_holds : FormalDegreeTwoByTwo := by
  intro k hk
  simp only [fdegHC, Finset.prod_filter, Fin.prod_univ_two]
  norm_num
  all_goals first | linarith | (rw [abs_of_nonneg (by linarith)]; ring)

/- English proof (translation)
Simplify using `only [Finset.prod_filter]`. Rewrite using `[Fin.prod_univ_succ]`. Use `congr 1`. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `[Fin.succ_pos]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `[Fin.succ_lt_succ_iff]`.
-/
private theorem prod_pairs_succ {n : ℕ} (f : Fin (n + 1) → Fin (n + 1) → ℝ) :
    (∏ x : Fin (n + 1), ∏ y ∈ univ.filter (fun y : Fin (n + 1) => x < y), f x y) =
      (∏ j : Fin n, f 0 j.succ) *
        ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j), f i.succ j.succ := by
  simp only [Finset.prod_filter]
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_lt_succ_iff]

/- English proof (translation)
Introduce `n a b hn`. Unfold `fdegHC`. Rewrite using `[prod_pairs_succ, prod_pairs_succ]`. Establish `hpair : ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j), |lamHol n a b i.succ - lamHol n a b j.succ| = ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j), (((j.succ : ℕ) : ℝ) - ((i.succ : ℕ) : ℝ))`. Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations.

Establish `hij : i < j` using `by simpa using hj`. Establish `hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ)` using `by exact_mod_cast hij`. Simplify using `only [lamHol, Fin.succ_ne_zero, if_false, Fin.val_succ]`. Use `push_cast`. Rewrite using `[abs_of_nonneg (by linarith)]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hP : ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j), (((j.succ : ℕ) : ℝ) - ((i.succ : ℕ) : ℝ)) ≠ 0`. Establish `e : ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j), (((j.succ : ℕ) : ℝ) - ((i.succ : ℕ) : ℝ)) = ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j), (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))` using `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by`. Simplify using `only [Fin.val_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `fdegDen_ne_zero n`. Rewrite using `[hpair, mul_div_mul_right _ _ hP]`. Establish `hB : ∏ j : Fin n, (((j.succ : ℕ) : ℝ) - (((0 : Fin (n + 1)) : ℕ) : ℝ)) = (n.factorial : ℝ)`.

Rewrite using `[← Finset.prod_range_add_one_eq_factorial]`. Use `push_cast`. Rewrite using `[← Fin.prod_univ_eq_prod_range (fun j : ℕ => (j : ℝ) + 1)]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[Fin.val_succ]`.

Establish `hA : ∏ j : Fin n, |lamHol n a b 0 - lamHol n a b j.succ| = ∏ j ∈ Icc 1 n, (b - a - (j : ℝ))`. Establish `e1 : ∏ j : Fin n, |lamHol n a b 0 - lamHol n a b j.succ| = ∏ j ∈ range n, (b - a - n + (j : ℝ))`. Rewrite using `[← Fin.prod_univ_eq_prod_range (fun j : ℕ => b - a - n + (j : ℝ))]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [lamHol, Fin.succ_ne_zero, if_false, if_true, Fin.val_succ]`.

Use `push_cast`. Rewrite using `[abs_of_nonneg (by have : (0:ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)]`. Expand and normalize the polynomial expressions, which then agree. Establish `eI : Icc 1 n = Ico 1 (n + 1)` using `by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega`. Rewrite using `[e1, ← Finset.prod_range_reflect, eI, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]`.

Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj' : j < n` using `Finset.mem_range.mp hj`. Establish `e : ((n - 1 - j : ℕ) : ℝ) = (n : ℝ) - 1 - j`. Rewrite using `[Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring`. Rewrite using `[e]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hA, hB]`.
-/
theorem holomorphicFormalDegree_holds : HolFdeg := by
  intro n a b hn
  unfold fdegHC
  rw [prod_pairs_succ, prod_pairs_succ]
  have hpair : ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j),
      |lamHol n a b i.succ - lamHol n a b j.succ| =
      ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j),
        (((j.succ : ℕ) : ℝ) - ((i.succ : ℕ) : ℝ)) := by
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
    have hij : i < j := by simpa using hj
    have hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    simp only [lamHol, Fin.succ_ne_zero, if_false, Fin.val_succ]
    push_cast
    rw [abs_of_nonneg (by linarith)]
    ring
  have hP : ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j),
      (((j.succ : ℕ) : ℝ) - ((i.succ : ℕ) : ℝ)) ≠ 0 := by
    have e : ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j),
        (((j.succ : ℕ) : ℝ) - ((i.succ : ℕ) : ℝ)) =
        ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i < j), (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) :=
      Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by
        simp only [Fin.val_succ]; push_cast; ring
    rw [e]; exact fdegDen_ne_zero n
  rw [hpair, mul_div_mul_right _ _ hP]
  have hB : ∏ j : Fin n, (((j.succ : ℕ) : ℝ) - (((0 : Fin (n + 1)) : ℕ) : ℝ)) = (n.factorial : ℝ) := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    push_cast
    rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => (j : ℝ) + 1)]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [Fin.val_succ]
  have hA : ∏ j : Fin n, |lamHol n a b 0 - lamHol n a b j.succ| =
      ∏ j ∈ Icc 1 n, (b - a - (j : ℝ)) := by
    have e1 : ∏ j : Fin n, |lamHol n a b 0 - lamHol n a b j.succ| =
        ∏ j ∈ range n, (b - a - n + (j : ℝ)) := by
      rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => b - a - n + (j : ℝ))]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [lamHol, Fin.succ_ne_zero, if_false, if_true, Fin.val_succ]
      push_cast
      rw [abs_of_nonneg (by have : (0:ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)]
      ring
    have eI : Icc 1 n = Ico 1 (n + 1) := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e1, ← Finset.prod_range_reflect, eI, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : j < n := Finset.mem_range.mp hj
    have e : ((n - 1 - j : ℕ) : ℝ) = (n : ℝ) - 1 - j := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [e]; push_cast; ring
  rw [hA, hB]

/- English proof (translation)
Introduce `V _ _ n E ν v hG hHW Y`. Rewrite using `[quantumDetHighestWeight_holds V n E ν v hG hHW]`. Use `congr 1`. Unfold `capP`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [rhoStd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem capelliHighestWeight_holds : CapelliHW := by
  intro V _ _ n E ν v hG hHW Y
  rw [quantumDetHighestWeight_holds V n E ν v hG hHW]
  congr 1
  unfold capP
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [rhoStd]
  push_cast
  ring

/- English proof (translation)
Introduce `n lam σ Y`. Unfold `capP`. Conclude with `Equiv.prod_comp σ (fun s => Y + lam s)`.
-/
theorem capelliPolynomialPermInvariant_holds : CapPPerm := by
  intro n lam σ Y
  unfold capP
  exact Equiv.prod_comp σ (fun s => Y + lam s)

end Formalism.QuantumDeterminants
