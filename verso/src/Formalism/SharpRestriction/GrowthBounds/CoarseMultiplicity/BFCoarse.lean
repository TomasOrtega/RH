import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFTrueDeg
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Kummer

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

/- English proof (translation)
Break down `v with ⟨a, c⟩ | ⟨l, bo⟩` into its components or cases. Use `right`. Establish `hc : c = 0`. Assume the negation of the conclusion as `hc`. Conclude with `h (by show mu0F C0 CE1 CE2 X j b (Sum.inl (a, c)) = 0; simp [mu0F, hc])`.

Substitute `hc` using the available equality. Simplify using `only [symVar]`. Apply the tactic sequence `split_ifs <;> rfl`. Use `left`. Simplify using `only [symVar]`.

Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem symbol_variable_first_columns (b : SegBlock (segS X.TT j) X.m) (v : BV C0 CE1 CE2 X j) (h : mu0 C0 CE1 CE2 X j b v ≠ 0) :
    (symVar C0 CE1 CE2 X j v).2 = 0 ∨ (symVar C0 CE1 CE2 X j v).2 = Fin.succ 0 := by
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · right
    have hc : c = 0 := by
      by_contra hc
      exact h (by show mu0F C0 CE1 CE2 X j b (Sum.inl (a, c)) = 0; simp [mu0F, hc])
    subst hc
    simp only [symVar]
    split_ifs <;> rfl
  · left
    simp only [symVar]
    split_ifs <;> rfl

/- English proof (translation)
Establish `hsub : (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => (symVar C0 CE1 CE2 X j v).1 = x ∧ mu0 C0 CE1 CE2 X j b v ≠ 0)) ⊆ (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => symVar C0 CE1 CE2 X j v = (x, 0))) ∪ (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => symVar C0 CE1 CE2 X j …`. Introduce `v hv`. Take `⟨h1, h2⟩` from `(Finset.mem_filter.1 hv).2`. Break down `symbol_variable_first_columns C0 CE1 CE2 X j b v h2 with h | h` into its components or cases. Conclude with `Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, Prod.ext h1 h⟩)`.

Conclude with `Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, Prod.ext h1 h⟩)`. Establish `hone : ∀ y, (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => symVar C0 CE1 CE2 X j v = y)).card ≤ 1`. Introduce `y`. Use `Finset.card_le_one.2 fun v hv v' hv' => ?_` and prove the remaining obligations. Conclude with `symVar_inj C0 CE1 CE2 X j (((Finset.mem_filter.1 hv).2).trans ((Finset.mem_filter.1 hv').2).symm)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_supp_le (b : SegBlock (segS X.TT j) X.m) (x : X.TT × Bool) :
    open Classical in
    (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => (symVar C0 CE1 CE2 X j v).1 = x ∧
      mu0 C0 CE1 CE2 X j b v ≠ 0)).card ≤ 2 := by
  classical
  have hsub : (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => (symVar C0 CE1 CE2 X j v).1 = x ∧
      mu0 C0 CE1 CE2 X j b v ≠ 0)) ⊆
      (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => symVar C0 CE1 CE2 X j v = (x, 0))) ∪
      (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => symVar C0 CE1 CE2 X j v = (x, Fin.succ 0))) := by
    intro v hv
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hv).2
    rcases symbol_variable_first_columns C0 CE1 CE2 X j b v h2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, Prod.ext h1 h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, Prod.ext h1 h⟩)
  have hone : ∀ y, (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => symVar C0 CE1 CE2 X j v = y)).card ≤ 1 := by
    intro y
    refine Finset.card_le_one.2 fun v hv v' hv' => ?_
    exact symVar_inj C0 CE1 CE2 X j (((Finset.mem_filter.1 hv).2).trans ((Finset.mem_filter.1 hv').2).symm)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add (hone _) (hone _)

/- English proof (translation)
Rewrite using `[← sum_fiber C0 CE1 CE2 X j b (mu0 C0 CE1 CE2 X j b) (leading_exponent_homogeneous C0 CE1 CE2 X j b) x]`. Use `set μ0 := mu0 C0 CE1 CE2 X j b`. Establish `hco : ∀ c : Fin (X.m + 1), (μ0.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)) (x, c) = ∑ v : BV C0 CE1 CE2 X j, if symVar C0 CE1 CE2 X j v = (x, c) then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0`. Introduce `c`. Rewrite using `[Finsupp.sum_apply, Finsupp.sum_fintype _ _ (fun v => by simp)]`.

Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply]`. Establish `hswap : (∑ c : Fin (X.m + 1), ∑ v : BV C0 CE1 CE2 X j, (if symVar C0 CE1 CE2 X j v = (x, c) then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0)) = ∑ v : BV C0 CE1 CE2 X j, if (symVar C0 CE1 CE2 X j v).1 = x then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h : (symVar C0 CE1 CE2 X j v).1 = x`. Rewrite using `[if_pos h, Finset.sum_eq_single (symVar C0 CE1 CE2 X j v).2]`. Rewrite using `[if_pos (Prod.ext h rfl : symVar C0 CE1 CE2 X j v = (x, (symVar C0 CE1 CE2 X j v).2))]`. Introduce `c _ hc`. Rewrite using `[if_neg (fun e => hc (by rw [e]))]`.

Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`. Rewrite using `[if_neg h]`. Conclude with `Finset.sum_eq_zero fun c _ => if_neg (fun e => h (by rw [e]))`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_le_sum fun v _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `Nat.le_mul_of_pos_left _ (symLev_pos C0 CE1 CE2 X hp j v)`. Conclude with `le_rfl`. Use `_ = ∑ c : Fin (X.m + 1), (μ0.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)) (x, c) := by`.

Rewrite using `[Finset.sum_congr rfl fun c _ => hco c, hswap]`. Use `_ ≤ tdeg C0 CE1 CE2 X j b x := by`. Unfold `tdeg multideg ioExp`. Use `Finset.sum_le_sum fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.add_apply]`.

Conclude with `Nat.le_add_left _ _`.
-/
theorem cdeg_le_tdeg (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m) (x : X.TT × Bool) :
    cdeg C0 CE1 CE2 X j b x ≤ tdeg C0 CE1 CE2 X j b x := by
  classical
  rw [← sum_fiber C0 CE1 CE2 X j b (mu0 C0 CE1 CE2 X j b) (leading_exponent_homogeneous C0 CE1 CE2 X j b) x]
  set μ0 := mu0 C0 CE1 CE2 X j b
  have hco : ∀ c : Fin (X.m + 1), (μ0.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v)
      (symLev X.p C0 CE1 CE2 X j v * n)) (x, c) =
      ∑ v : BV C0 CE1 CE2 X j, if symVar C0 CE1 CE2 X j v = (x, c) then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0 := by
    intro c
    rw [Finsupp.sum_apply, Finsupp.sum_fintype _ _ (fun v => by simp)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finsupp.single_apply]
  have hswap : (∑ c : Fin (X.m + 1), ∑ v : BV C0 CE1 CE2 X j,
      (if symVar C0 CE1 CE2 X j v = (x, c) then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0)) =
      ∑ v : BV C0 CE1 CE2 X j, if (symVar C0 CE1 CE2 X j v).1 = x then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : (symVar C0 CE1 CE2 X j v).1 = x
    · rw [if_pos h, Finset.sum_eq_single (symVar C0 CE1 CE2 X j v).2]
      · rw [if_pos (Prod.ext h rfl : symVar C0 CE1 CE2 X j v = (x, (symVar C0 CE1 CE2 X j v).2))]
      · intro c _ hc
        rw [if_neg (fun e => hc (by rw [e]))]
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun c _ => if_neg (fun e => h (by rw [e]))
  calc (∑ v ∈ Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => (symVar C0 CE1 CE2 X j v).1 = x), μ0 v)
      = ∑ v : BV C0 CE1 CE2 X j, if (symVar C0 CE1 CE2 X j v).1 = x then μ0 v else 0 := Finset.sum_filter _ _
    _ ≤ ∑ v : BV C0 CE1 CE2 X j, if (symVar C0 CE1 CE2 X j v).1 = x then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0 := by
        refine Finset.sum_le_sum fun v _ => ?_
        split_ifs
        · exact Nat.le_mul_of_pos_left _ (symLev_pos C0 CE1 CE2 X hp j v)
        · exact le_rfl
    _ = ∑ c : Fin (X.m + 1), (μ0.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v)
          (symLev X.p C0 CE1 CE2 X j v * n)) (x, c) := by
        rw [Finset.sum_congr rfl fun c _ => hco c, hswap]
    _ ≤ tdeg C0 CE1 CE2 X j b x := by
        unfold tdeg multideg ioExp
        refine Finset.sum_le_sum fun c _ => ?_
        rw [Finsupp.add_apply]
        exact Nat.le_add_left _ _

end

/- English proof (translation)
Introduce `X _ hD1 hH hc j b hb`. Establish `hp : 0 < X.p` using `hD1.1.pos`. Establish `ho` using `hO X hD1 hH hc j b hb`. Use `set μ0 := mu0 C0 CE1 CE2 X j b with hμ0`. Set `F : X.TT × Bool → Finset (BV C0 CE1 CE2 X j)` to `fun x => Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => (symVar C0 CE1 CE2 X j v).1 = x)`.

Set `s : X.TT × Bool → Finset (BV C0 CE1 CE2 X j)` to `fun x => (F x).filter (fun v => μ0 v ≠ 0)`. Establish `hfac : ∀ x, (cdeg C0 CE1 CE2 X j b x).factorial = (∏ v ∈ F x, (μ0 v).factorial) * Nat.multinomial (s x) μ0`. Introduce `x`. Rewrite using `[← sum_fiber C0 CE1 CE2 X j b μ0 (leading_exponent_homogeneous C0 CE1 CE2 X j b) x]`. Use `show (∑ v ∈ F x, μ0 v).factorial = _`.

Rewrite using `[← Finset.sum_filter_ne_zero, ← Finset.prod_filter_of_ne (p := fun v => μ0 v ≠ 0) (fun v _ hv h0 => hv (by rw [h0]; rfl))]`. Conclude with `(Nat.multinomial_spec _ _).symm`. Establish `hE : expFact μ0 = ∏ x : X.TT × Bool, ∏ v ∈ F x, (μ0 v).factorial`. Unfold `expFact`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => rfl)]`.

Conclude with `(Finset.prod_fiberwise Finset.univ (fun v => (symVar C0 CE1 CE2 X j v).1) (fun v => (μ0 v).factorial)).symm`. Establish `hE0 : expFact μ0 ≠ 0`. Unfold `expFact`. Conclude with `Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _`. Establish `hM0 : ∀ x ∈ (Finset.univ : Finset (X.TT × Bool)), Nat.multinomial (s x) μ0 ≠ 0` using `fun x _ => (Nat.multinomial_pos _ _).ne'`.

Rewrite using `[Finset.prod_congr rfl (fun x _ => hfac x), Finset.prod_mul_distrib, ← hE, Nat.factorization_mul hE0 (Finset.prod_ne_zero_iff.2 hM0), Finsupp.add_apply, Nat.factorization_prod hM0, Finsupp.finsetSum_apply]`. Use `Nat.add_le_add_left ?_ _` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun x _ => (multinomial_val X.p (s x) μ0).trans ?_` and prove the remaining obligations. Establish `hc2 : (s x).card ≤ 2`.

Use `card_supp_le C0 CE1 CE2 X j b x` as an intermediate fact. Simplify using `only [s, F, Finset.filter_filter]`. Use `this` and compare the differences between its conclusion and the goal. Rewrite using `[Finset.sum_filter_ne_zero]`. Use `show ((s x).card - 1) * Nat.log X.p (∑ v ∈ F x, μ0 v) ≤ _`.

Rewrite using `[sum_fiber C0 CE1 CE2 X j b μ0 (leading_exponent_homogeneous C0 CE1 CE2 X j b) x]`. Combine the equalities or inequalities in the displayed calculation. Use `_ ≤ ∑ x : X.TT × Bool, Nat.log X.p (tdeg C0 CE1 CE2 X j b x) := Finset.sum_le_sum fun x _ => Nat.log_mono_right (cdeg_le_tdeg C0 CE1 CE2 X j hp b x)`. Use `_ = lgSeg X j := by`. Rewrite using `[sum_tdeg C0 CE1 CE2 X j (Nat.log X.p) (Nat.log_zero_right _) b hb ho]`.

Unfold `lgSeg`. Rewrite using `[Finset.sum_add_distrib]`.
-/
theorem coarseMultAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hO : OPlusAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    CoarseMultAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ hD1 hH hc j b hb
  have hp : 0 < X.p := hD1.1.pos
  have ho := hO X hD1 hH hc j b hb
  set μ0 := mu0 C0 CE1 CE2 X j b with hμ0
  let F : X.TT × Bool → Finset (BV C0 CE1 CE2 X j) :=
    fun x => Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => (symVar C0 CE1 CE2 X j v).1 = x)
  let s : X.TT × Bool → Finset (BV C0 CE1 CE2 X j) := fun x => (F x).filter (fun v => μ0 v ≠ 0)
  have hfac : ∀ x, (cdeg C0 CE1 CE2 X j b x).factorial =
      (∏ v ∈ F x, (μ0 v).factorial) * Nat.multinomial (s x) μ0 := by
    intro x
    rw [← sum_fiber C0 CE1 CE2 X j b μ0 (leading_exponent_homogeneous C0 CE1 CE2 X j b) x]
    show (∑ v ∈ F x, μ0 v).factorial = _
    rw [← Finset.sum_filter_ne_zero, ← Finset.prod_filter_of_ne (p := fun v => μ0 v ≠ 0)
      (fun v _ hv h0 => hv (by rw [h0]; rfl))]
    exact (Nat.multinomial_spec _ _).symm
  have hE : expFact μ0 = ∏ x : X.TT × Bool, ∏ v ∈ F x, (μ0 v).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl)]
    exact (Finset.prod_fiberwise Finset.univ (fun v => (symVar C0 CE1 CE2 X j v).1) (fun v => (μ0 v).factorial)).symm
  have hE0 : expFact μ0 ≠ 0 := by
    unfold expFact; exact Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hM0 : ∀ x ∈ (Finset.univ : Finset (X.TT × Bool)), Nat.multinomial (s x) μ0 ≠ 0 :=
    fun x _ => (Nat.multinomial_pos _ _).ne'
  rw [Finset.prod_congr rfl (fun x _ => hfac x), Finset.prod_mul_distrib, ← hE,
    Nat.factorization_mul hE0 (Finset.prod_ne_zero_iff.2 hM0), Finsupp.add_apply, Nat.factorization_prod hM0,
    Finsupp.finsetSum_apply]
  refine Nat.add_le_add_left ?_ _
  calc (∑ x : X.TT × Bool, (Nat.multinomial (s x) μ0).factorization X.p)
      ≤ ∑ x : X.TT × Bool, Nat.log X.p (cdeg C0 CE1 CE2 X j b x) := by
        refine Finset.sum_le_sum fun x _ => (multinomial_val X.p (s x) μ0).trans ?_
        have hc2 : (s x).card ≤ 2 := by
          have := card_supp_le C0 CE1 CE2 X j b x
          simp only [s, F, Finset.filter_filter]
          convert this
        rw [Finset.sum_filter_ne_zero]
        show ((s x).card - 1) * Nat.log X.p (∑ v ∈ F x, μ0 v) ≤ _
        rw [sum_fiber C0 CE1 CE2 X j b μ0 (leading_exponent_homogeneous C0 CE1 CE2 X j b) x]
        calc ((s x).card - 1) * Nat.log X.p (cdeg C0 CE1 CE2 X j b x) ≤ 1 * Nat.log X.p (cdeg C0 CE1 CE2 X j b x) :=
              Nat.mul_le_mul_right _ (by omega)
          _ = _ := one_mul _
    _ ≤ ∑ x : X.TT × Bool, Nat.log X.p (tdeg C0 CE1 CE2 X j b x) :=
        Finset.sum_le_sum fun x _ => Nat.log_mono_right (cdeg_le_tdeg C0 CE1 CE2 X j hp b x)
    _ = lgSeg X j := by
        rw [sum_tdeg C0 CE1 CE2 X j (Nat.log X.p) (Nat.log_zero_right _) b hb ho]
        unfold lgSeg
        rw [Finset.sum_add_distrib]

end Formalism.MainNotions.ColumnSystems.Pf
