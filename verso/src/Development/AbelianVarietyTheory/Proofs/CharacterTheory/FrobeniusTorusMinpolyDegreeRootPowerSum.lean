import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F] [Finite F]

open Polynomial in
variable {F : Type} [Field F] [Finite F] in

/- English proof (translation)
Rewrite using `[(minpoly.irreducible (Algebra.IsIntegral.isIntegral α)).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff]`. Simplify using `[sub_eq_zero]`.
-/
theorem _root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow (α : AlgebraicClosure F) (m : ℕ) :
    (minpoly F α).natDegree ∣ m ↔ α ^ Nat.card F ^ m = α := by
  rw [(minpoly.irreducible (Algebra.IsIntegral.isIntegral α)).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X,
    minpoly.dvd_iff]
  simp [sub_eq_zero]

/- English proof (translation)
Use `letI := Fintype.ofFinite F`. Use `⟨FiniteField.frobeniusAlgHom F (AlgebraicClosure F) ^ i, fun x => ?_⟩` and prove the remaining obligations. Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`.

Rewrite using `[pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom, pow_succ, pow_mul, Nat.card_eq_fintype_card]`.
-/
theorem exists_algHom_pow_card_pow (i : ℕ) :
    ∃ f : AlgebraicClosure F →ₐ[F] AlgebraicClosure F, ∀ x, f x = x ^ Nat.card F ^ i := by
  letI := Fintype.ofFinite F
  refine ⟨FiniteField.frobeniusAlgHom F (AlgebraicClosure F) ^ i, fun x => ?_⟩
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom, pow_succ, pow_mul,
      Nat.card_eq_fintype_card]

open Polynomial in
variable {F : Type} [Field F] [Finite F] in

/- English proof (translation)
Establish `: Fintype F` using `Fintype.ofFinite F`. Use `set σ := FiniteField.frobeniusAlgEquivOfAlgebraic F (AlgebraicClosure F)`. Establish `hσ : ∀ (i : ℕ) (x : AlgebraicClosure F), (σ ^ i) x = x ^ Nat.card F ^ i` using `fun i x => by`. Rewrite using `[AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, Nat.card_eq_fintype_card]`. Establish `hint : IsIntegral F α` using `Algebra.IsIntegral.isIntegral α`.

Establish `hne : (minpoly F α).map (algebraMap F (AlgebraicClosure F)) ≠ 0` using `Polynomial.map_ne_zero (minpoly.ne_zero hint)`. Establish `key : ∀ i j, i < j → j < (minpoly F α).natDegree → α ^ Nat.card F ^ i = α ^ Nat.card F ^ j → False`. Introduce `i j hij hj h`. Establish `hfix : α ^ Nat.card F ^ (j - i) = α`. Apply `(σ ^ i).injective` to reduce the goal to its premises.

Rewrite using `[hσ, hσ, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]`. Conclude with `h.symm`. Establish `hdvd` using `(_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α (j - i)).mpr hfix`. Use `Nat.le_of_dvd (by omega) hdvd` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hnodup : ((Multiset.range (minpoly F α).natDegree).map fun i => α ^ Nat.card F ^ i).Nodup`. Use `(Multiset.nodup_range _).map_on ?_` and prove the remaining obligations. Introduce `i hi j hj hij`. Rewrite `hi`, `hj` using `[Multiset.mem_range]`. Break down `lt_trichotomy i j with h | h | h` into its components or cases.

Conclude with `(key i j h hj hij).elim`. Conclude with `h`. Conclude with `(key j i h hi hij.symm).elim`. Use `(Multiset.eq_of_le_of_card_le ?_ ?_).symm` and prove the remaining obligations. Rewrite using `[Multiset.le_iff_subset hnodup]`.

Introduce `x hx`. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.mp hx`. Rewrite using `[mem_roots hne, IsRoot, eval_map_algebraMap, ← hσ, aeval_algHom_apply, minpoly.aeval, map_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem _root_.GlobalTheory.CuspGL.roots_minpoly_eq_map_range (α : AlgebraicClosure F) :
    ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).roots =
      (Multiset.range (minpoly F α).natDegree).map fun i => α ^ Nat.card F ^ i := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set σ := FiniteField.frobeniusAlgEquivOfAlgebraic F (AlgebraicClosure F)
  have hσ : ∀ (i : ℕ) (x : AlgebraicClosure F), (σ ^ i) x = x ^ Nat.card F ^ i := fun i x => by
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      Nat.card_eq_fintype_card]
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hne : (minpoly F α).map (algebraMap F (AlgebraicClosure F)) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint)
  have key : ∀ i j, i < j → j < (minpoly F α).natDegree →
      α ^ Nat.card F ^ i = α ^ Nat.card F ^ j → False := by
    intro i j hij hj h
    have hfix : α ^ Nat.card F ^ (j - i) = α := by
      apply (σ ^ i).injective
      rw [hσ, hσ, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
      exact h.symm
    have hdvd := (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α (j - i)).mpr hfix
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hnodup : ((Multiset.range (minpoly F α).natDegree).map
      fun i => α ^ Nat.card F ^ i).Nodup := by
    refine (Multiset.nodup_range _).map_on ?_
    intro i hi j hj hij
    rw [Multiset.mem_range] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact (key i j h hj hij).elim
    · exact h
    · exact (key j i h hi hij.symm).elim
  refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
  · rw [Multiset.le_iff_subset hnodup]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    rw [mem_roots hne, IsRoot, eval_map_algebraMap, ← hσ, aeval_algHom_apply, minpoly.aeval,
      map_zero]
  · calc ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).roots.card
        ≤ ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).natDegree := card_roots' _
      _ = (minpoly F α).natDegree := natDegree_map _
      _ = _ := by simp

open Polynomial in
variable {F : Type} [Field F] [Finite F] in
/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => simp`. Consider the case `succ e ih`. Rewrite using `[Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun i _ => hf i e`.
-/
private theorem sum_range_mul_eq_nsmul_of_periodic {M : Type} [AddCommMonoid M] (f : ℕ → M) (d : ℕ)
    (hf : ∀ i j, f (d * j + i) = f i) (e : ℕ) :
    ∑ i ∈ Finset.range (d * e), f i = e • ∑ i ∈ Finset.range d, f i := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hf i e

open Polynomial in
variable {F : Type} [Field F] [Finite F] in

/- English proof (translation)
Introduce `F _ _ θ n hn α hα`. Rewrite `hα` using `[Set.mem_setOf_eq]`. Establish `hq : 1 < Nat.card F` using `Finite.one_lt_card`. Establish `hqn : 1 < Nat.card F ^ n` using `Nat.one_lt_pow (by omega) hq`. Establish `hfix : α ^ Nat.card F ^ n = α`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_succ, Nat.sub_add_cancel hqn.le]`. Use `_ = α := by rw [hα, one_mul]`. Establish `hd` using `(_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α n).mpr hfix`. Establish `hα0 : α ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hα` using `[zero_pow (by omega)]`. Conclude with `zero_ne_one hα`. Establish `hint : IsIntegral F α` using `Algebra.IsIntegral.isIntegral α`. Use `⟨hd, minpoly.coeff_zero_ne_zero hint hα0, fun k => ?_⟩` and prove the remaining obligations.

Take `⟨e, he⟩` from `hd`. Establish `hdpos : 0 < (minpoly F α).natDegree` using `minpoly.natDegree_pos hint`. Establish `hper : ∀ i j, α ^ Nat.card F ^ ((minpoly F α).natDegree * j + i) = α ^ Nat.card F ^ i` using `fun i j => by`. Rewrite using `[pow_add, pow_mul, (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α _).mp (dvd_mul_right _ _)]`. Rewrite using `[he, Nat.mul_div_cancel_left e hdpos, sum_range_mul_eq_nsmul_of_periodic (fun i => θ (α ^ Nat.card F ^ i) ^ k) _ (fun i j => by simp only [hper]) e]`.

Unfold `_root_.GlobalTheory.CuspGL.rootSum`. Rewrite using `[Polynomial.map_pow, roots_pow, _root_.GlobalTheory.CuspGL.roots_minpoly_eq_map_range, Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.map_map, Finset.sum_eq_multiset_sum]`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.CuspGL.torus_minpoly : ∀ (F : Type) [Field F] [Finite F]
    (θ : AlgebraicClosure F →* ℂ) (n : ℕ), 0 < n →
    ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1},
      (minpoly F α).natDegree ∣ n ∧ (minpoly F α).coeff 0 ≠ 0 ∧
        ∀ k : ℕ, _root_.GlobalTheory.CuspGL.rootSum θ k
            (minpoly F α ^ (n / (minpoly F α).natDegree)) =
          ∑ i ∈ Finset.range n, θ (α ^ Nat.card F ^ i) ^ k := by
  intro F _ _ θ n hn α hα
  rw [Set.mem_setOf_eq] at hα
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqn : 1 < Nat.card F ^ n := Nat.one_lt_pow (by omega) hq
  have hfix : α ^ Nat.card F ^ n = α := by
    calc α ^ Nat.card F ^ n = α ^ (Nat.card F ^ n - 1) * α := by
          rw [← pow_succ, Nat.sub_add_cancel hqn.le]
      _ = α := by rw [hα, one_mul]
  have hd := (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α n).mpr hfix
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hα
    exact zero_ne_one hα
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  refine ⟨hd, minpoly.coeff_zero_ne_zero hint hα0, fun k => ?_⟩
  obtain ⟨e, he⟩ := hd
  have hdpos : 0 < (minpoly F α).natDegree := minpoly.natDegree_pos hint
  have hper : ∀ i j, α ^ Nat.card F ^ ((minpoly F α).natDegree * j + i) =
      α ^ Nat.card F ^ i := fun i j => by
    rw [pow_add, pow_mul,
      (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α _).mp (dvd_mul_right _ _)]
  rw [he, Nat.mul_div_cancel_left e hdpos,
    sum_range_mul_eq_nsmul_of_periodic (fun i => θ (α ^ Nat.card F ^ i) ^ k) _
      (fun i j => by simp only [hper]) e]
  unfold _root_.GlobalTheory.CuspGL.rootSum
  rw [Polynomial.map_pow, roots_pow, _root_.GlobalTheory.CuspGL.roots_minpoly_eq_map_range, Multiset.map_nsmul,
    Multiset.sum_nsmul, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

end GlobalTheory.CuspGL
