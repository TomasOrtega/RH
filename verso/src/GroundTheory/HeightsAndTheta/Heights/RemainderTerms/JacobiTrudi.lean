import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms.Schur

open MvPolynomial Finset

noncomputable section

section Complete

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/- English proof (translation)
Rewrite using `[hsymm]`. Use `Finset.sum_bij' (fun s _ => Multiset.toFinsupp s.1) (fun l hl => (⟨Finsupp.toMultiset l, ?_⟩ : Sym σ n)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite `hl` using `[mem_finsuppAntidiag]`. Rewrite using `[Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (by simp)]`. Conclude with `hl.1`.

Introduce `s _`. Rewrite using `[mem_finsuppAntidiag]`. Use `⟨?_, subset_univ _⟩` and prove the remaining obligations. Use `Multiset.toFinsupp_sum_eq s.1` as an intermediate fact. Rewrite `this` using `[Finsupp.sum_fintype _ _ (by simp)]`.

Simplify using `only [id] at this`. Express the relevant statement in the definitionally equal form `∑ i, (Multiset.toFinsupp s.1) i = n`. Rewrite using `[this]`. Conclude with `s.2`. Introduce `s _`.

Conclude with `mem_univ _`. Introduce `s _`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Introduce `l _`.

Simplify using the standard rewrite rules. Introduce `s _`. Rewrite using `[Finset.prod_multiset_map_count]`. Rewrite using `[Finset.prod_subset (subset_univ _)]`. Simplify using `[Multiset.toFinsupp_apply]`.

Introduce `i _ hi`. Rewrite `hi` using `[Multiset.mem_toFinset]`. Rewrite using `[Multiset.count_eq_zero.mpr hi, pow_zero]`.
-/
theorem hsymm_eq_sum_finsuppAntidiag (n : ℕ) :
    hsymm σ ℚ n = ∑ l ∈ finsuppAntidiag (univ : Finset σ) n, ∏ i, (X i : MvPolynomial σ ℚ) ^ l i := by
  rw [hsymm]
  refine Finset.sum_bij' (fun s _ => Multiset.toFinsupp s.1)
    (fun l hl => (⟨Finsupp.toMultiset l, ?_⟩ : Sym σ n)) ?_ ?_ ?_ ?_ ?_
  · rw [mem_finsuppAntidiag] at hl
    rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (by simp)]
    exact hl.1
  · intro s _
    rw [mem_finsuppAntidiag]
    refine ⟨?_, subset_univ _⟩
    have := Multiset.toFinsupp_sum_eq s.1
    rw [Finsupp.sum_fintype _ _ (by simp)] at this
    simp only [id] at this
    change ∑ i, (Multiset.toFinsupp s.1) i = n
    rw [this]; exact s.2
  · intro s _; exact mem_univ _
  · intro s _
    apply Subtype.ext
    simp
  · intro l _
    simp
  · intro s _
    rw [Finset.prod_multiset_map_count]
    rw [Finset.prod_subset (subset_univ _)]
    · simp [Multiset.toFinsupp_apply]
    · intro i _ hi
      rw [Multiset.mem_toFinset] at hi
      rw [Multiset.count_eq_zero.mpr hi, pow_zero]

end Complete

section Series

variable {R : Type*} [CommRing R]

def geomSeries (a : R) : PowerSeries R := PowerSeries.mk fun n => a ^ n

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm (geomSeries a) (PowerSeries.C a)]`. Break down `n with _ | n` into its components or cases. Simplify using `[geomSeries]`. Rewrite using `[PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C_mul]`.

Simplify using `[geomSeries, pow_succ, mul_comm]`.
-/
theorem geomSeries_mul (a : R) :
    geomSeries a * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm (geomSeries a) (PowerSeries.C a)]
  rcases n with _ | n
  · simp [geomSeries]
  · rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C_mul]
    simp [geomSeries, pow_succ, mul_comm]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `c hc`. Simplify using `only [prod_empty, PowerSeries.coeff_one]`. Simplify using `at hc`.

Simplify using `[Nat.pos_iff_ne_zero.mp hc]`. Consider the case `insert j s hj ih`. Introduce `c hc`. Rewrite `hc` using `[card_insert_of_notMem hj]`. Rewrite using `[prod_insert hj, sub_mul, one_mul, map_sub, ih c (by omega)]`.

Take `⟨c, rfl⟩ : ∃ c', c = c' + 1` from `⟨c - 1, by omega⟩`. Rewrite using `[mul_assoc, mul_comm PowerSeries.X, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X, ih c (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem coeff_prod_one_sub_eq_zero {ι : Type*} [DecidableEq ι] (a : ι → R) (s : Finset ι) :
    ∀ c : ℕ, s.card < c →
      PowerSeries.coeff c (∏ i ∈ s, (1 - PowerSeries.C (a i) * PowerSeries.X)) = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro c hc
    simp only [prod_empty, PowerSeries.coeff_one]
    simp at hc; simp [Nat.pos_iff_ne_zero.mp hc]
  | insert j s hj ih =>
    intro c hc
    rw [card_insert_of_notMem hj] at hc
    rw [prod_insert hj, sub_mul, one_mul, map_sub, ih c (by omega)]
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [mul_assoc, mul_comm PowerSeries.X, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X,
      ih c (by omega)]
    simp

end Series

section Generating

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_prod, hsymm_eq_sum_finsuppAntidiag]`. Simplify using `[geomSeries, PowerSeries.coeff_mk]`.
-/
theorem coeff_prod_geomSeries (n : ℕ) :
    PowerSeries.coeff n (∏ i : σ, geomSeries (X i : MvPolynomial σ ℚ)) = hsymm σ ℚ n := by
  rw [PowerSeries.coeff_prod, hsymm_eq_sum_finsuppAntidiag]
  simp [geomSeries, PowerSeries.coeff_mk]

def omitProduct (j : σ) : PowerSeries (MvPolynomial σ ℚ) :=
  ∏ i ∈ univ.erase j, (1 - PowerSeries.C (X i) * PowerSeries.X)

/- English proof (translation)
Rewrite using `[← Finset.mul_prod_erase univ _ (mem_univ j), omitProduct, mul_left_comm, ← prod_mul_distrib, prod_eq_one, mul_one]`. Introduce `i _`. Rewrite using `[mul_comm, geomSeries_mul]`.
-/
theorem omitProduct_mul_prod_geomSeries (j : σ) :
    omitProduct j * ∏ i : σ, geomSeries (X i : MvPolynomial σ ℚ) = geomSeries (X j) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ j), omitProduct, mul_left_comm,
    ← prod_mul_distrib, prod_eq_one, mul_one]
  intro i _
  rw [mul_comm, geomSeries_mul]

/- English proof (translation)
Apply `coeff_prod_one_sub_eq_zero` to reduce the goal to its premises. Rewrite using `[card_erase_of_mem (mem_univ j), card_univ]`. Establish `: 0 < Fintype.card σ` using `Fintype.card_pos_iff.mpr ⟨j⟩`. Use linear arithmetic over natural numbers and integers.
-/
theorem coeff_omitProduct_eq_zero (j : σ) (c : ℕ) (hc : Fintype.card σ ≤ c) :
    PowerSeries.coeff c (omitProduct j) = 0 := by
  apply coeff_prod_one_sub_eq_zero
  rw [card_erase_of_mem (mem_univ j), card_univ]
  have : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr ⟨j⟩
  omega

/- English proof (translation)
Establish `key` using `congrArg (PowerSeries.coeff α) (omitProduct_mul_prod_geomSeries j)`. Rewrite `key` using `[PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a (omitProduct j) * PowerSeries.coeff b (∏ i : σ, geomSeries (X i : MvPolynomial σ ℚ)))]`. Simplify using `only [coeff_prod_geomSeries] at key`. Rewrite `key` using `[geomSeries, PowerSeries.coeff_mk]`. Rewrite using `[← key]`.

Establish `hbig : ∀ s : Finset ℕ, ∀ f : ℕ → MvPolynomial σ ℚ, ∑ c ∈ s, PowerSeries.coeff c (omitProduct j) * f c = ∑ c ∈ s.filter (· < Fintype.card σ), PowerSeries.coeff c (omitProduct j) * f c`. Introduce `s f`. Rewrite using `[sum_filter]`. Apply `sum_congr rfl` to reduce the goal to its premises. Introduce `c _`.

Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[coeff_omitProduct_eq_zero j c (by omega), zero_mul]`. Rewrite using `[hbig, hbig (range (α + 1))]`. Rewrite using `[sum_filter, sum_filter]`.

Establish `e1 : ∑ c ∈ range (Fintype.card σ), (if c < Fintype.card σ then PowerSeries.coeff c (omitProduct j) * (if c ≤ α then hsymm σ ℚ (α - c) else 0) else 0) = ∑ c ∈ range (α + 1 + Fintype.card σ), (if c < Fintype.card σ then PowerSeries.coeff c (omitProduct j) * (if c ≤ α then hsymm σ ℚ …`. Apply `sum_subset (range_subset_range.mpr (by omega))` to reduce the goal to its premises. Introduce `c _ hc`. Simplify using `at hc`. Simplify using `[show ¬ c < Fintype.card σ by omega]`.

Establish `e2 : ∑ c ∈ range (α + 1), (if c < Fintype.card σ then PowerSeries.coeff c (omitProduct j) * hsymm σ ℚ (α - c) else 0) = ∑ c ∈ range (α + 1 + Fintype.card σ), (if c < Fintype.card σ then PowerSeries.coeff c (omitProduct j) * (if c ≤ α then hsymm σ ℚ (α - c) else 0) else 0)`. Rewrite using `[← sum_subset (range_subset_range.mpr (show α + 1 ≤ α + 1 + Fintype.card σ by omega))]`. Apply `sum_congr rfl` to reduce the goal to its premises. Introduce `c hc`. Simplify using `at hc`.

Simplify using `[show c ≤ α by omega]`. Introduce `c _ hc`. Simplify using `at hc`. Simplify using `[show ¬ c ≤ α by omega]`. Rewrite using `[e1, e2]`.
-/
theorem sum_hsymm_mul_coeff_omitProduct (j : σ) (α : ℕ) :
    ∑ c ∈ range (Fintype.card σ), PowerSeries.coeff c (omitProduct j) *
      (if c ≤ α then hsymm σ ℚ (α - c) else 0) = X j ^ α := by
  have key := congrArg (PowerSeries.coeff α) (omitProduct_mul_prod_geomSeries j)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (omitProduct j) *
      PowerSeries.coeff b (∏ i : σ, geomSeries (X i : MvPolynomial σ ℚ)))] at key
  simp only [coeff_prod_geomSeries] at key
  rw [geomSeries, PowerSeries.coeff_mk] at key
  rw [← key]
  have hbig : ∀ s : Finset ℕ, ∀ f : ℕ → MvPolynomial σ ℚ,
      ∑ c ∈ s, PowerSeries.coeff c (omitProduct j) * f c =
        ∑ c ∈ s.filter (· < Fintype.card σ), PowerSeries.coeff c (omitProduct j) * f c := by
    intro s f
    rw [sum_filter]
    apply sum_congr rfl
    intro c _
    split_ifs with h
    · rfl
    · rw [coeff_omitProduct_eq_zero j c (by omega), zero_mul]
  rw [hbig, hbig (range (α + 1))]
  rw [sum_filter, sum_filter]
  have e1 : ∑ c ∈ range (Fintype.card σ), (if c < Fintype.card σ then
      PowerSeries.coeff c (omitProduct j) * (if c ≤ α then hsymm σ ℚ (α - c) else 0) else 0) =
      ∑ c ∈ range (α + 1 + Fintype.card σ), (if c < Fintype.card σ then
      PowerSeries.coeff c (omitProduct j) * (if c ≤ α then hsymm σ ℚ (α - c) else 0) else 0) := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro c _ hc
    simp at hc
    simp [show ¬ c < Fintype.card σ by omega]
  have e2 : ∑ c ∈ range (α + 1), (if c < Fintype.card σ then
      PowerSeries.coeff c (omitProduct j) * hsymm σ ℚ (α - c) else 0) =
      ∑ c ∈ range (α + 1 + Fintype.card σ), (if c < Fintype.card σ then
      PowerSeries.coeff c (omitProduct j) * (if c ≤ α then hsymm σ ℚ (α - c) else 0) else 0) := by
    rw [← sum_subset (range_subset_range.mpr (show α + 1 ≤ α + 1 + Fintype.card σ by omega))]
    · apply sum_congr rfl
      intro c hc
      simp at hc
      simp [show c ≤ α by omega]
    · intro c _ hc
      simp at hc
      simp [show ¬ c ≤ α by omega]
  rw [e1, e2]

end Generating

section Bialternant

variable {m : ℕ}

/- English proof (translation)
Unfold `completeSymmetric`. Use `split_ifs with h1 h2 h2`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.
-/
theorem completeSymmetric_natSub (σ : Type*) [Fintype σ] [DecidableEq σ] (a c : ℕ) :
    completeSymmetric σ ((a : ℤ) - (c : ℤ)) = if c ≤ a then hsymm σ ℚ (a - c) else 0 := by
  unfold completeSymmetric
  split_ifs with h1 h2 h2
  · congr 1; omega
  · omega
  · omega
  · rfl

def omitProductCoeffMatrix (m : ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m) ℚ) :=
  Matrix.of fun c j => PowerSeries.coeff (m - 1 - (c : ℕ)) (omitProduct j)

def hMatrix (α : Fin m → ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m) ℚ) :=
  Matrix.of fun i c => completeSymmetric (Fin m) ((α i : ℤ) - ((m - 1 - (c : ℕ) : ℕ) : ℤ))

/- English proof (translation)
Apply `Matrix.ext` to reduce the goal to its premises. Introduce `i j`. Rewrite using `[Matrix.mul_apply, Matrix.of_apply]`. Simplify using `only [hMatrix, omitProductCoeffMatrix, Matrix.of_apply, completeSymmetric_natSub]`. Rewrite using `[← sum_hsymm_mul_coeff_omitProduct j (α i), Fintype.card_fin]`.

Rewrite using `[Fin.sum_univ_eq_sum_range (fun c => (if m - 1 - c ≤ α i then hsymm (Fin m) ℚ (α i - (m - 1 - c)) else 0) * PowerSeries.coeff (m - 1 - c) (omitProduct j)) m]`. Rewrite using `[← sum_range_reflect]`. Apply `sum_congr rfl` to reduce the goal to its premises. Introduce `c hc`. Rewrite `hc` using `[mem_range]`.

Rewrite using `[mul_comm]`.
-/
theorem powMatrix_eq_mul (α : Fin m → ℕ) :
    (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℚ) ^ α i) =
      hMatrix α * omitProductCoeffMatrix m := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, Matrix.of_apply]
  simp only [hMatrix, omitProductCoeffMatrix, Matrix.of_apply, completeSymmetric_natSub]
  rw [← sum_hsymm_mul_coeff_omitProduct j (α i), Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun c => (if m - 1 - c ≤ α i then hsymm (Fin m) ℚ (α i - (m - 1 - c))
    else 0) * PowerSeries.coeff (m - 1 - c) (omitProduct j)) m]
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro c hc
  rw [mem_range] at hc
  rw [mul_comm]

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular]`. Apply `prod_eq_one` to reduce the goal to its premises. Introduce `i _`. Use `i.isLt` as an intermediate fact. Simplify using `only [hMatrix, Matrix.of_apply, completeSymmetric_natSub]`.

Rewrite using `[if_pos (by omega), show m - 1 - (i : ℕ) - (m - 1 - (i : ℕ)) = 0 by omega, hsymm_zero]`. Introduce `i c hci`. Simplify using `only [hMatrix, Matrix.of_apply, completeSymmetric_natSub]`. Rewrite using `[if_neg]`. Use `c.isLt` as an intermediate fact.

Establish `: (c : ℕ) < i` using `hci`. Use linear arithmetic over natural numbers and integers.
-/
theorem det_hMatrix_staircase :
    (hMatrix (fun i : Fin m => m - 1 - (i : ℕ))).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · apply prod_eq_one
    intro i _
    have := i.isLt
    simp only [hMatrix, Matrix.of_apply, completeSymmetric_natSub]
    rw [if_pos (by omega), show m - 1 - (i : ℕ) - (m - 1 - (i : ℕ)) = 0 by omega, hsymm_zero]
  · intro i c hci
    simp only [hMatrix, Matrix.of_apply, completeSymmetric_natSub]
    rw [if_neg]
    have := c.isLt
    have : (c : ℕ) < i := hci
    omega

/- English proof (translation)
Rewrite using `[powMatrix_eq_mul, powMatrix_eq_mul (fun i : Fin m => m - 1 - (i : ℕ)), Matrix.det_mul, Matrix.det_mul, det_hMatrix_staircase, one_mul]`. Rewrite using `[schur]`. Use `congr 2`. Apply `Matrix.ext` to reduce the goal to its premises. Introduce `i c`.

Simplify using `only [hMatrix, Matrix.of_apply]`. Use `congr 1`. Use `i.isLt` as an intermediate fact. Use `c.isLt` as an intermediate fact. Move the coercions through the operations in `[Nat.sub_sub, Nat.cast_sub (show 1 + (c : ℕ) ≤ m by omega), Nat.cast_sub (show 1 + (i : ℕ) ≤ m by omega)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_pow_add_staircase (lam : Fin m → ℕ) :
    (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℚ) ^ (lam i + (m - 1 - (i : ℕ)))).det =
      schur (Fin m) lam *
        (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℚ) ^ (m - 1 - (i : ℕ))).det := by
  rw [powMatrix_eq_mul, powMatrix_eq_mul (fun i : Fin m => m - 1 - (i : ℕ)), Matrix.det_mul,
    Matrix.det_mul, det_hMatrix_staircase, one_mul]
  rw [schur]
  congr 2
  apply Matrix.ext
  intro i c
  simp only [hMatrix, Matrix.of_apply]
  congr 1
  have := i.isLt
  have := c.isLt
  push_cast [Nat.sub_sub, Nat.cast_sub (show 1 + (c : ℕ) ≤ m by omega),
    Nat.cast_sub (show 1 + (i : ℕ) ≤ m by omega)]
  ring

/- English proof (translation)
Rewrite using `[← Matrix.det_transpose]`. Establish `h1 : (Matrix.of fun i j : Fin m => v j ^ (m - 1 - (i : ℕ))).transpose = (Matrix.vandermonde (v ∘ Fin.rev)).submatrix Fin.revPerm Fin.revPerm`. Use extensionality with `a b`. Simplify using `[Matrix.vandermonde, Fin.val_rev]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[h1, Matrix.det_submatrix_equiv_self, Matrix.det_vandermonde, vandermondeOf]`. Establish `h2 : ∀ g : Fin m → Fin m → R, ∏ i : Fin m, ∏ j ∈ Ioi i, g i j = ∏ i : Fin m, ∏ j : Fin m, if i < j then g i j else 1`. Introduce `g`. Apply `prod_congr rfl` to reduce the goal to its premises.

Introduce `i _`. Rewrite using `[← prod_filter]`. Use `congr 1`. Use extensionality with `j`. Simplify using the standard rewrite rules.

Rewrite using `[h2, h2]`. Establish `h3 : (∏ i : Fin m, ∏ j : Fin m, if i < j then (v ∘ Fin.rev) j - (v ∘ Fin.rev) i else 1) = ∏ a : Fin m, ∏ b : Fin m, if b < a then v b - v a else 1`. Rewrite using `[← Fintype.prod_equiv Fin.revPerm (fun a => ∏ j : Fin m, if Fin.rev a < j then (v ∘ Fin.rev) j - (v ∘ Fin.rev) (Fin.rev a) else 1)]`. Apply `prod_congr rfl` to reduce the goal to its premises. Introduce `a _`.

Rewrite using `[← Fintype.prod_equiv Fin.revPerm (fun b => if Fin.rev a < Fin.rev b then (v ∘ Fin.rev) (Fin.rev b) - (v ∘ Fin.rev) (Fin.rev a) else 1)]`. Apply `prod_congr rfl` to reduce the goal to its premises. Introduce `b _`. Simplify using `[Fin.rev_lt_rev]`. Introduce `b`.

Both sides reduce to the same expression. Introduce `a`. Both sides reduce to the same expression. Rewrite using `[h3, prod_comm]`.
-/
theorem det_pow_staircase_eq_vandermondeOf {R : Type*} [CommRing R] (v : Fin m → R) :
    (Matrix.of fun i j : Fin m => v j ^ (m - 1 - (i : ℕ))).det = vandermondeOf v := by
  rw [← Matrix.det_transpose]
  have h1 : (Matrix.of fun i j : Fin m => v j ^ (m - 1 - (i : ℕ))).transpose =
      (Matrix.vandermonde (v ∘ Fin.rev)).submatrix Fin.revPerm Fin.revPerm := by
    ext a b
    simp [Matrix.vandermonde, Fin.val_rev]
    congr 1
    omega
  rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_vandermonde, vandermondeOf]
  have h2 : ∀ g : Fin m → Fin m → R,
      ∏ i : Fin m, ∏ j ∈ Ioi i, g i j = ∏ i : Fin m, ∏ j : Fin m, if i < j then g i j else 1 := by
    intro g
    apply prod_congr rfl
    intro i _
    rw [← prod_filter]
    congr 1
    ext j; simp
  rw [h2, h2]
  have h3 : (∏ i : Fin m, ∏ j : Fin m, if i < j then (v ∘ Fin.rev) j - (v ∘ Fin.rev) i else 1) =
      ∏ a : Fin m, ∏ b : Fin m, if b < a then v b - v a else 1 := by
    rw [← Fintype.prod_equiv Fin.revPerm (fun a => ∏ j : Fin m,
      if Fin.rev a < j then (v ∘ Fin.rev) j - (v ∘ Fin.rev) (Fin.rev a) else 1)]
    · apply prod_congr rfl
      intro a _
      rw [← Fintype.prod_equiv Fin.revPerm (fun b => if Fin.rev a < Fin.rev b then
        (v ∘ Fin.rev) (Fin.rev b) - (v ∘ Fin.rev) (Fin.rev a) else 1)]
      · apply prod_congr rfl
        intro b _
        simp [Fin.rev_lt_rev]
      · intro b; rfl
    · intro a; rfl
  rw [h3, prod_comm]

end Bialternant

section Padding

variable (σ : Type*) [Fintype σ] [DecidableEq σ]

def padPartition {r : ℕ} (n : ℕ) (lam : Fin r → ℕ) : Fin n → ℕ :=
  fun i => if h : (i : ℕ) < r then lam ⟨i, h⟩ else 0

/- English proof (translation)
Unfold `schur`. Rewrite using `[Matrix.det_succ_row _ (Fin.last n)]`. Rewrite using `[Fintype.sum_eq_single (Fin.last n)]`. Simplify using `only [Matrix.of_apply, h, Fin.val_last, Fin.succAbove_last]`. Rewrite using `[show ((0 : ℕ) : ℤ) - (n : ℤ) + (n : ℤ) = 0 by ring]`.

Simplify using `[completeSymmetric, ← two_mul]`. Both sides reduce to the same expression. Introduce `j hj`. Establish `hj' : (j : ℕ) < n`. Use `j.isLt` as an intermediate fact.

Establish `: (j : ℕ) ≠ n` using `fun e => hj (Fin.ext e)`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Matrix.of_apply, h, Fin.val_last]`. Rewrite using `[show completeSymmetric σ (((0 : ℕ) : ℤ) - (n : ℤ) + ((j : ℕ) : ℤ)) = 0 by`. Unfold `completeSymmetric; rw [if_neg (by omega)]]`.

Simplify using the standard rewrite rules.
-/
theorem schur_eq_of_last_eq_zero {n : ℕ} (lam : Fin (n + 1) → ℕ) (h : lam (Fin.last n) = 0) :
    schur σ lam = schur σ (fun i : Fin n => lam i.castSucc) := by
  unfold schur
  rw [Matrix.det_succ_row _ (Fin.last n)]
  rw [Fintype.sum_eq_single (Fin.last n)]
  · simp only [Matrix.of_apply, h, Fin.val_last, Fin.succAbove_last]
    rw [show ((0 : ℕ) : ℤ) - (n : ℤ) + (n : ℤ) = 0 by ring]
    simp [completeSymmetric, ← two_mul]
    rfl
  · intro j hj
    have hj' : (j : ℕ) < n := by
      have := j.isLt
      have : (j : ℕ) ≠ n := fun e => hj (Fin.ext e)
      omega
    simp only [Matrix.of_apply, h, Fin.val_last]
    rw [show completeSymmetric σ (((0 : ℕ) : ℤ) - (n : ℤ) + ((j : ℕ) : ℤ)) = 0 by
      unfold completeSymmetric; rw [if_neg (by omega)]]
    simp

/- English proof (translation)
Introduce `n hn`. Proceed by induction on `n, hn using Nat.le_induction with`. Consider the case `base`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `[padPartition]`. Consider the case `succ n hrn ih`. Rewrite using `[schur_eq_of_last_eq_zero]`. Rewrite using `[← ih]`. Use `congr 1`.

Simplify using `[padPartition]`. Use linear arithmetic over natural numbers and integers.
-/
theorem schur_padPartition {r : ℕ} (lam : Fin r → ℕ) :
    ∀ n : ℕ, r ≤ n → schur σ (padPartition n lam) = schur σ lam := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    congr 1
    funext i
    simp [padPartition]
  | succ n hrn ih =>
    rw [schur_eq_of_last_eq_zero]
    · rw [← ih]
      congr 1
    · simp [padPartition]
      omega

end Padding

section Symmetric

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/- English proof (translation)
Unfold `completeSymmetric`. Use `split_ifs`. Conclude with `hsymm_isSymmetric (σ := σ) (R := ℚ) _ e`. Simplify using the standard rewrite rules.
-/
theorem rename_completeSymmetric (e : Equiv.Perm σ) (d : ℤ) :
    rename e (completeSymmetric σ d) = completeSymmetric σ d := by
  unfold completeSymmetric
  split_ifs
  · exact hsymm_isSymmetric (σ := σ) (R := ℚ) _ e
  · simp

/- English proof (translation)
Introduce `e`. Unfold `schur`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Apply `Matrix.ext` to reduce the goal to its premises.

Introduce `i j`. Simplify using `[rename_completeSymmetric]`.
-/
theorem schur_isSymmetric {r : ℕ} (lam : Fin r → ℕ) : (schur σ lam).IsSymmetric := by
  intro e
  unfold schur
  rw [AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  simp [rename_completeSymmetric]

end Symmetric

/- English proof (translation)
Rewrite using `[det_pow_add_staircase, det_pow_staircase_eq_vandermondeOf]`.
-/
theorem det_pow_add_staircase_eq {m : ℕ} (lam : Fin m → ℕ) :
    (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℚ) ^ (lam i + (m - 1 - (i : ℕ)))).det =
      schur (Fin m) lam * vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) := by
  rw [det_pow_add_staircase, det_pow_staircase_eq_vandermondeOf]

end

end GroundTheory.Heights₂.Heights.RestTerms.Schur
