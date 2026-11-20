import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadLApply
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprEqZeroOfCardNe

set_option autoImplicit false

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm GlobalTheory.LocFub
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.LocFub.TopDens

/- English proof (translation)
Simplify using `[dens, mul_div_assoc]`.
-/
theorem dens_smul {n : ℕ} (c : ℂ) (α : Alt n) : dens (c • α) = c * dens α := by
  simp [dens, mul_div_assoc]

/- English proof (translation)
Simplify using `[dens, add_div]`.
-/
theorem dens_add {n : ℕ} (α β : Alt n) : dens (α + β) = dens α + dens β := by
  simp [dens, add_div]

/- English proof (translation)
Simplify using `[dens]`.
-/
theorem dens_zero {n : ℕ} : dens (0 : Alt n) = 0 := by simp [dens]

/- English proof (translation)
Rewrite using `[← (bas n).sum_repr η]`. Use `Submodule.sum_mem _ fun S _ => ?_` and prove the remaining obligations. Distinguish the cases in `hS : (bas n).repr η S = 0`. Simplify using `[hS]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `h S hS`. Take `⟨i, hi⟩` from `Finset.card_eq_one.1 h1`. Take `⟨j, hj⟩` from `Finset.card_eq_one.1 h2`. Establish `hi' : i.val < n` using `(Finset.mem_filter.1 (hi.ge (Finset.mem_singleton_self i))).2`. Establish `hj' : n ≤ j.val` using `(Finset.mem_filter.1 (hj.ge (Finset.mem_singleton_self j))).2`.

Establish `hS' : S = {i} ∪ {j}`. Rewrite using `[← hi, ← hj, ← Finset.filter_or, Finset.filter_true_of_mem fun x _ => lt_or_ge _ _]`. Establish `ei : i = finSumFinEquiv (Sum.inl ⟨i.val, hi'⟩ : Fin n ⊕ Fin n)` using `by ext; simp`. Establish `ej : j = finSumFinEquiv (Sum.inr ⟨j.val - n, by omega⟩ : Fin n ⊕ Fin n)` using `by ext; simp; omega`. Take `⟨ε, hε⟩` from `bas_mul (n := n) (S := {i}) (T := {j}) (Finset.disjoint_singleton.2 (by rintro rfl; omega))`.

Establish `: bas n S = ε⁻¹ • (bas n {i} * bas n {j})` using `by rw [hε, inv_smul_smul, hS']`. Rewrite using `[this, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨(⟨i.val, hi'⟩, ⟨j.val - n, by omega⟩), ?_⟩)` and prove the remaining obligations. Use `conv_rhs => rw [ei, ej, bas_singleton, bas_singleton]`. Both sides reduce to the same expression.
-/
theorem mem_span_of_isType {n : ℕ} {η : Alt n} (h : IsType 1 1 η) :
    η ∈ Submodule.span ℂ (Set.range fun x : Fin n × Fin n => dz x.1 * dzb x.2) := by
  rw [← (bas n).sum_repr η]
  refine Submodule.sum_mem _ fun S _ => ?_
  by_cases hS : (bas n).repr η S = 0
  · simp [hS]
  refine Submodule.smul_mem _ _ ?_
  obtain ⟨h1, h2⟩ := h S hS
  obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h1
  obtain ⟨j, hj⟩ := Finset.card_eq_one.1 h2
  have hi' : i.val < n := (Finset.mem_filter.1 (hi.ge (Finset.mem_singleton_self i))).2
  have hj' : n ≤ j.val := (Finset.mem_filter.1 (hj.ge (Finset.mem_singleton_self j))).2
  have hS' : S = {i} ∪ {j} := by
    rw [← hi, ← hj, ← Finset.filter_or, Finset.filter_true_of_mem fun x _ => lt_or_ge _ _]
  have ei : i = finSumFinEquiv (Sum.inl ⟨i.val, hi'⟩ : Fin n ⊕ Fin n) := by ext; simp
  have ej : j = finSumFinEquiv (Sum.inr ⟨j.val - n, by omega⟩ : Fin n ⊕ Fin n) := by ext; simp; omega
  obtain ⟨ε, hε⟩ := bas_mul (n := n) (S := {i}) (T := {j}) (Finset.disjoint_singleton.2 (by rintro rfl; omega))
  have : bas n S = ε⁻¹ • (bas n {i} * bas n {j}) := by rw [hε, inv_smul_smul, hS']
  rw [this, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(⟨i.val, hi'⟩, ⟨j.val - n, by omega⟩), ?_⟩)
  conv_rhs => rw [ei, ej, bas_singleton, bas_singleton]
  rfl

/- English proof (translation)
Rewrite using `[(pull_dz _ a).1, (pull_dz _ a).2]`. Simplify using `[headL_apply, coordVec, EuclideanSpace.single_apply]`.
-/
theorem pull_headL_dz {n : ℕ} (a : Fin n) :
    pull (headL n) (dz a) = dz a.castSucc ∧ pull (headL n) (dzb a) = dzb a.castSucc := by
  rw [(pull_dz _ a).1, (pull_dz _ a).2]
  simp [headL_apply, coordVec, EuclideanSpace.single_apply]

/- English proof (translation)
Rewrite using `[(pull_dz _ _).1, (pull_dz _ _).2]`. Simplify using `[fibL_apply, EuclideanSpace.single_apply, Fin.castSucc_ne_last]`.
-/
theorem pull_fibL_castSucc {n : ℕ} (a : Fin n) :
    pull (fibL n) (dz a.castSucc) = 0 ∧ pull (fibL n) (dzb a.castSucc) = 0 := by
  rw [(pull_dz _ _).1, (pull_dz _ _).2]
  simp [fibL_apply, EuclideanSpace.single_apply, Fin.castSucc_ne_last]

/- English proof (translation)
Rewrite using `[(pull_dz _ _).1, (pull_dz _ _).2]`. Simplify using `[fibL_apply, coordVec]`.
-/
theorem pull_fibL_last {n : ℕ} :
    pull (fibL n) (dz (Fin.last n)) = dz 0 ∧ pull (fibL n) (dzb (Fin.last n)) = dzb 0 := by
  rw [(pull_dz _ _).1, (pull_dz _ _).2]
  simp [fibL_apply, coordVec]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha, Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, ih]`. Use `congr 1`.

Simplify using `[sym, (pull_headL_dz a).1, (pull_headL_dz a).2]`.
-/
theorem pull_headL_prod {n : ℕ} (s : Finset (Fin n)) :
    pull (headL n) ((∏ a ∈ s, (Complex.I / 2) • sym (a, a) : Ev n) : Alt n) =
      ((∏ a ∈ s, (Complex.I / 2) • sym (a.castSucc, a.castSucc) : Ev (n + 1)) : Alt (n + 1)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, ih]
    congr 1
    simp [sym, (pull_headL_dz a).1, (pull_headL_dz a).2]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Express the relevant statement in the definitionally equal form `dz a * (dz a * dzb a) = 0`. Rewrite using `[← mul_assoc, dz, ExteriorAlgebra.ι_sq_zero, zero_mul]`. Rewrite using `[Subalgebra.mem_center_iff.1 (sym (a, a)).2]`. Express the relevant statement in the definitionally equal form `(dz a * dzb a) * dzb a = 0`.

Rewrite using `[mul_assoc, dzb, ExteriorAlgebra.ι_sq_zero, mul_zero]`.
-/
theorem dz_mul_sym {n : ℕ} (a : Fin n) : dz a * (sym (a, a) : Alt n) = 0 ∧ dzb a * (sym (a, a) : Alt n) = 0 := by
  constructor
  · change dz a * (dz a * dzb a) = 0
    rw [← mul_assoc, dz, ExteriorAlgebra.ι_sq_zero, zero_mul]
  · rw [Subalgebra.mem_center_iff.1 (sym (a, a)).2]
    change (dz a * dzb a) * dzb a = 0
    rw [mul_assoc, dzb, ExteriorAlgebra.ι_sq_zero, mul_zero]

/- English proof (translation)
Rewrite using `[vol, pull_headL_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ a), Subalgebra.coe_mul, Subalgebra.coe_smul, ← mul_assoc, ← mul_assoc, mul_smul_comm, mul_smul_comm, (dz_mul_sym _).1, (dz_mul_sym _).2]`. Simplify using the standard rewrite rules.
-/
theorem dz_mul_pull_vol {n : ℕ} (a : Fin n) :
    dz a.castSucc * pull (headL n) (vol n : Alt n) = 0 ∧ dzb a.castSucc * pull (headL n) (vol n : Alt n) = 0 := by
  rw [vol, pull_headL_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ a), Subalgebra.coe_mul, Subalgebra.coe_smul,
    ← mul_assoc, ← mul_assoc, mul_smul_comm, mul_smul_comm, (dz_mul_sym _).1, (dz_mul_sym _).2]
  simp

/- English proof (translation)
Break down `Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl` into its components or cases. Rewrite using `[mul_assoc, (dz_mul_pull_vol b).2, map_mul, (pull_fibL_castSucc b).2, mul_zero, mul_zero, dens_zero, dens_zero]`. Break down `Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl` into its components or cases. Rewrite using `[map_mul, (pull_fibL_castSucc a).1, zero_mul, dens_zero, dz, dzb, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _), neg_mul, mul_assoc]`. Use `(dz_mul_pull_vol a).1` as an intermediate fact.

Rewrite `this` using `[dz]`. Rewrite using `[this, mul_zero, neg_zero, dens_zero]`. Establish `hI : (Complex.I / 2 : ℂ) ≠ 0` using `by simp`. Use `mul_left_cancel₀ hI ?_` and prove the remaining obligations. Rewrite using `[← dens_smul, ← dens_smul, map_mul, pull_fibL_last.1, pull_fibL_last.2]`.

Establish `e1 : (Complex.I / 2) • (dz 0 * dzb 0 : Alt 1) = (vol 1 : Alt 1)`. Rewrite using `[vol, Fin.prod_univ_one]`. Both sides reduce to the same expression. Establish `e2 : (Complex.I / 2) • (dz (Fin.last n) * dzb (Fin.last n) * pull (headL n) (vol n : Alt n)) = (vol (n + 1) : Alt (n + 1))`. Rewrite using `[vol, pull_headL_prod, vol, Fin.prod_univ_castSucc, mul_comm (∏ _, _), Subalgebra.coe_mul, Subalgebra.coe_smul, smul_mul_assoc]`.

Both sides reduce to the same expression. Rewrite using `[e1, e2, dens_vol, dens_vol]`.
-/
theorem dens_mul_pull_vol {n : ℕ} (a b : Fin (n + 1)) :
    dens (dz a * dzb b * pull (headL n) (vol n : Alt n)) = dens (pull (fibL n) (dz a * dzb b)) := by
  rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl
  · rw [mul_assoc, (dz_mul_pull_vol b).2, map_mul, (pull_fibL_castSucc b).2, mul_zero, mul_zero, dens_zero, dens_zero]
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl
  · rw [map_mul, (pull_fibL_castSucc a).1, zero_mul, dens_zero, dz, dzb,
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _), neg_mul, mul_assoc]
    have := (dz_mul_pull_vol a).1
    rw [dz] at this
    rw [this, mul_zero, neg_zero, dens_zero]
  have hI : (Complex.I / 2 : ℂ) ≠ 0 := by simp
  refine mul_left_cancel₀ hI ?_
  rw [← dens_smul, ← dens_smul, map_mul, pull_fibL_last.1, pull_fibL_last.2]
  have e1 : (Complex.I / 2) • (dz 0 * dzb 0 : Alt 1) = (vol 1 : Alt 1) := by
    rw [vol, Fin.prod_univ_one]; rfl
  have e2 : (Complex.I / 2) • (dz (Fin.last n) * dzb (Fin.last n) * pull (headL n) (vol n : Alt n)) =
      (vol (n + 1) : Alt (n + 1)) := by
    rw [vol, pull_headL_prod, vol, Fin.prod_univ_castSucc, mul_comm (∏ _, _), Subalgebra.coe_mul,
      Subalgebra.coe_smul, smul_mul_assoc]
    rfl
  rw [e1, e2, dens_vol, dens_vol]

/- English proof (translation)
Establish `hc : T.card < n + n` using `by simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.2 hT)`. Establish `hm : dz a * dzb b * pull (headL n) (bas n T) ∈ ⋀[ℂ]^(1 + 1 + T.card) (Fin (n + 1) ⊕ Fin (n + 1) → ℂ)`. Use `SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin (n + 1) ⊕ Fin (n + 1) → ℂ)) (SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin (n + 1) ⊕ Fin (n + 1) → ℂ)) ?_ ?_) ?_` and prove the remaining obligations. Simplify using `[dz, ExteriorAlgebra.exteriorPower]`. Simplify using `[dzb, ExteriorAlgebra.exteriorPower]`.

Rewrite using `[bas, ExteriorAlgebra.basis_apply _ T, pull, ExteriorAlgebra.map_apply_ιMulti, ← exteriorPower.ιMulti_apply_coe]`. Conclude with `Subtype.property _`. Use `GlobalTheory.PullTop.repr_eq_zero_of_card_ne ((Pi.basisFun ℂ (Fin (n + 1) ⊕ Fin (n + 1))).reindex finSumFinEquiv) ⟨_, hm⟩ (S := Finset.univ) (by simp; omega)` as an intermediate fact. Rewrite using `[dens]`. Conclude with `div_eq_zero_iff.2 (Or.inl this)`.
-/
theorem dens_mul_pull_bas {n : ℕ} (a b : Fin (n + 1)) {T : Finset (Fin (n + n))} (hT : T ≠ Finset.univ) :
    dens (dz a * dzb b * pull (headL n) (bas n T)) = 0 := by
  have hc : T.card < n + n := by simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.2 hT)
  have hm : dz a * dzb b * pull (headL n) (bas n T) ∈ ⋀[ℂ]^(1 + 1 + T.card) (Fin (n + 1) ⊕ Fin (n + 1) → ℂ) := by
    refine SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin (n + 1) ⊕ Fin (n + 1) → ℂ))
      (SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin (n + 1) ⊕ Fin (n + 1) → ℂ)) ?_ ?_) ?_
    · simp [dz, ExteriorAlgebra.exteriorPower]
    · simp [dzb, ExteriorAlgebra.exteriorPower]
    · rw [bas, ExteriorAlgebra.basis_apply _ T, pull, ExteriorAlgebra.map_apply_ιMulti,
        ← exteriorPower.ιMulti_apply_coe]
      exact Subtype.property _
  have := GlobalTheory.PullTop.repr_eq_zero_of_card_ne
    ((Pi.basisFun ℂ (Fin (n + 1) ⊕ Fin (n + 1))).reindex finSumFinEquiv) ⟨_, hm⟩ (S := Finset.univ) (by simp; omega)
  rw [dens]
  exact div_eq_zero_iff.2 (Or.inl this)

/- English proof (translation)
Establish `hζ : ζ ∈ Submodule.span ℂ (Set.range (bas n))` using `by rw [(bas n).span_eq]; trivial`. Proceed by induction on `hζ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨T, rfl⟩` from `hx`. Distinguish the cases in `hT : T = Finset.univ`.

Take `⟨c, hc, e⟩` from `vol_eq n`. Establish `e' : bas n T = c⁻¹ • (vol n : Alt n)` using `by rw [e, hT, inv_smul_smul₀ hc]`. Rewrite using `[e', map_smul, mul_smul_comm, dens_smul, dens_smul, dens_vol, dens_mul_pull_vol]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[dens_mul_pull_bas a b hT]`.

Simplify using `[dens, hT]`. Consider the case `zero => simp [dens_zero]`. Consider the case `add x y _ _ hx hy => rw [map_add, mul_add, dens_add, dens_add, hx, hy, mul_add]`. Consider the case `smul c x _ hx => rw [map_smul, mul_smul_comm, dens_smul, dens_smul, hx]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dens_gen {n : ℕ} (a b : Fin (n + 1)) (ζ : Alt n) :
    dens (dz a * dzb b * pull (headL n) ζ) = dens (pull (fibL n) (dz a * dzb b)) * dens ζ := by
  have hζ : ζ ∈ Submodule.span ℂ (Set.range (bas n)) := by rw [(bas n).span_eq]; trivial
  induction hζ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, rfl⟩ := hx
    by_cases hT : T = Finset.univ
    · obtain ⟨c, hc, e⟩ := vol_eq n
      have e' : bas n T = c⁻¹ • (vol n : Alt n) := by rw [e, hT, inv_smul_smul₀ hc]
      rw [e', map_smul, mul_smul_comm, dens_smul, dens_smul, dens_vol, dens_mul_pull_vol]
      ring
    · rw [dens_mul_pull_bas a b hT]
      simp [dens, hT]
  | zero => simp [dens_zero]
  | add x y _ _ hx hy => rw [map_add, mul_add, dens_add, dens_add, hx, hy, mul_add]
  | smul c x _ hx => rw [map_smul, mul_smul_comm, dens_smul, dens_smul, hx]; ring

/- English proof (translation)
Establish `hη` using `mem_span_of_isType h`. Use `clear h`. Proceed by induction on `hη using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨x, rfl⟩ := hx`. Conclude with `dens_gen _ _ _`.

Consider the case `zero => simp [dens_zero]`. Consider the case `add x y _ _ hx hy => rw [map_add, add_mul, dens_add, dens_add, hx, hy, add_mul]`. Consider the case `smul c x _ hx => rw [map_smul, smul_mul_assoc, dens_smul, dens_smul, hx, mul_assoc]`.
-/
theorem dens_mul_pull_headL {n : ℕ} (η : Alt (n + 1)) (ζ : Alt n) (h : IsType 1 1 η) :
    dens (η * pull (headL n) ζ) = dens (pull (fibL n) η) * dens ζ := by
  have hη := mem_span_of_isType h
  clear h
  induction hη using Submodule.span_induction with
  | mem x hx => obtain ⟨x, rfl⟩ := hx; exact dens_gen _ _ _
  | zero => simp [dens_zero]
  | add x y _ _ hx hy => rw [map_add, add_mul, dens_add, dens_add, hx, hy, add_mul]
  | smul c x _ hx => rw [map_smul, smul_mul_assoc, dens_smul, dens_smul, hx, mul_assoc]

end GlobalTheory.LocFub.TopDens
