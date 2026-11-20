import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagPivotIdentity
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace FlagPivotIdentity

variable {R : Type} [CommRing R] {n : ℕ}

def leadDet (M : Matrix (Fin n) (Fin n) R) (k : ℕ) : R :=
  if h : k ≤ n then (M.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

def pivotCof (M : Matrix (Fin n) (Fin n) R) {a : ℕ} (ha : a + 1 ≤ n) (i : Fin (a + 1)) : R :=
  (-1) ^ ((i : ℕ) + a) * (M.submatrix (Fin.castLE ha ∘ i.succAbove) (Fin.castLE (by omega))).det

/- English proof (translation)
Unfold `pivotMinor`. Rewrite using `[Matrix.det_succ_column _ (Fin.last a)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hcol : pivotCols a b ∘ (Fin.last (a : ℕ)).succAbove = Fin.castLE (by have` using `a.2; omega) := by`. Use function extensionality and compare the values at `c`.

Rewrite using `[Fin.succAbove_last]`. Use `ext`. Simplify using `[pivotCols]`. Establish `hlast : pivotCols a b (Fin.last a) = b` using `by simp [pivotCols]`. Simplify using `only [pivotCof, Matrix.submatrix_apply, Matrix.submatrix_submatrix, Fin.val_last, hlast, hcol]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pivotMinor_eq_sum (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n) :
    pivotMinor M a b = ∑ i : Fin (a + 1),
      pivotCof M (a := a) (by have := a.2; omega) i * M (Fin.castLE (by have := a.2; omega) i) b := by
  unfold pivotMinor
  rw [Matrix.det_succ_column _ (Fin.last a)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcol : pivotCols a b ∘ (Fin.last (a : ℕ)).succAbove = Fin.castLE (by have := a.2; omega) := by
    funext c
    rw [Fin.succAbove_last]
    ext
    simp [pivotCols]
  have hlast : pivotCols a b (Fin.last a) = b := by simp [pivotCols]
  simp only [pivotCof, Matrix.submatrix_apply, Matrix.submatrix_submatrix, Fin.val_last, hlast, hcol]
  ring

def pivotCoeff (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) : Matrix (Fin (j + 1)) (Fin (j + 1)) R :=
  Matrix.of fun a i =>
    if h : (i : ℕ) ≤ a then pivotCof M (a := a) (by have := j.2; have := a.2; omega) ⟨i, by omega⟩ else 0

/- English proof (translation)
Establish `e : ∑ i : Fin k, f (Fin.castLE h i) = ∑ i ∈ Finset.univ.map (Fin.castLEEmb h), f i`. Rewrite using `[Finset.sum_map]`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hf i ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Conclude with `hi (Finset.mem_map.2 ⟨⟨i, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)`.
-/
theorem sum_castLE {m k : ℕ} (h : k ≤ m) (f : Fin m → R) (hf : ∀ i : Fin m, k ≤ (i : ℕ) → f i = 0) :
    ∑ i : Fin k, f (Fin.castLE h i) = ∑ i : Fin m, f i := by
  have e : ∑ i : Fin k, f (Fin.castLE h i) = ∑ i ∈ Finset.univ.map (Fin.castLEEmb h), f i := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hf i ?_
  by_contra hlt
  push Not at hlt
  exact hi (Finset.mem_map.2 ⟨⟨i, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/- English proof (translation)
Use extensionality with `a b`. Establish `ha : (a : ℕ) < n - 1` using `by have := j.2; have := a.2; omega`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.submatrix_apply, pivotMatrix, Matrix.of_apply, Fin.val_castLE, dif_pos ha]`. Rewrite using `[pivotMinor_eq_sum M ⟨a, ha⟩ (e b)]`.

Rewrite using `[← sum_castLE (m := (j : ℕ) + 1) (k := (a : ℕ) + 1) (Nat.succ_le_of_lt a.2)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hi : ((Fin.castLE (n` using `(a : ℕ) + 1) (m := (j : ℕ) + 1) (Nat.succ_le_of_lt a.2) i) : ℕ) ≤ a := Nat.lt_succ_iff.mp i.2`. Simplify using `only [pivotCoeff, Matrix.of_apply]`. Rewrite using `[dif_pos hi]`.

Both sides reduce to the same expression. Introduce `i hi`. Establish `: ¬ ((i : ℕ) ≤ a)` using `by omega`. Simplify using `only [pivotCoeff, Matrix.of_apply]`. Rewrite using `[dif_neg this, zero_mul]`.
-/
theorem pivotMatrix_rows (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) {m : ℕ} (e : Fin m → Fin n) :
    (pivotMatrix M).submatrix (Fin.castLE (n := (j : ℕ) + 1) (by have := j.2; omega)) e =
      pivotCoeff M j * M.submatrix (Fin.castLE (n := (j : ℕ) + 1) (by have := j.2; omega)) e := by
  ext a b
  have ha : (a : ℕ) < n - 1 := by have := j.2; have := a.2; omega
  rw [Matrix.mul_apply]
  simp only [Matrix.submatrix_apply, pivotMatrix, Matrix.of_apply, Fin.val_castLE, dif_pos ha]
  rw [pivotMinor_eq_sum M ⟨a, ha⟩ (e b)]
  rw [← sum_castLE (m := (j : ℕ) + 1) (k := (a : ℕ) + 1) (Nat.succ_le_of_lt a.2)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi : ((Fin.castLE (n := (a : ℕ) + 1) (m := (j : ℕ) + 1) (Nat.succ_le_of_lt a.2) i) : ℕ) ≤ a :=
      Nat.lt_succ_iff.mp i.2
    simp only [pivotCoeff, Matrix.of_apply]
    rw [dif_pos hi]
    rfl
  · intro i hi
    have : ¬ ((i : ℕ) ≤ a) := by omega
    simp only [pivotCoeff, Matrix.of_apply]
    rw [dif_neg this, zero_mul]

/- English proof (translation)
Introduce `a i hai`. Establish `hai' : (a : ℕ) < i` using `OrderDual.toDual_lt_toDual.mp hai`. Establish `: ¬ ((i : ℕ) ≤ a)` using `by omega`. Simplify using `only [pivotCoeff, Matrix.of_apply, dif_neg this]`.
-/
theorem pivotCoeff_isLowerTriangular (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) :
    (pivotCoeff M j).IsLowerTriangular := by
  intro a i hai
  have hai' : (a : ℕ) < i := OrderDual.toDual_lt_toDual.mp hai
  have : ¬ ((i : ℕ) ≤ a) := by omega
  simp only [pivotCoeff, Matrix.of_apply, dif_neg this]

/- English proof (translation)
Establish `ha : (a : ℕ) ≤ n` using `by have := j.2; have := a.2; omega`. Simplify using `only [pivotCoeff, Matrix.of_apply, dif_pos le_rfl, pivotCof, leadDet, dif_pos ha]`. Establish `hl : (⟨a, Nat.lt_succ_self _⟩ : Fin ((a : ℕ) + 1)) = Fin.last a` using `rfl`. Rewrite using `[hl, Fin.succAbove_last, Even.neg_one_pow ⟨a, rfl⟩, one_mul]`. Both sides reduce to the same expression.
-/
theorem pivotCoeff_diag (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) (a : Fin (j + 1)) :
    pivotCoeff M j a a = leadDet M a := by
  have ha : (a : ℕ) ≤ n := by have := j.2; have := a.2; omega
  simp only [pivotCoeff, Matrix.of_apply, dif_pos le_rfl, pivotCof, leadDet, dif_pos ha]
  have hl : (⟨a, Nat.lt_succ_self _⟩ : Fin ((a : ℕ) + 1)) = Fin.last a := rfl
  rw [hl, Fin.succAbove_last, Even.neg_one_pow ⟨a, rfl⟩, one_mul]
  rfl

/- English proof (translation)
Establish `h : (a : ℕ) + 1 ≤ n` using `by have := a.2; omega`. Unfold `leadMinor pivotMinor leadDet`. Rewrite using `[dif_pos h]`. Use `congr 2`. Use function extensionality and compare the values at `c`.

Break down `c with ⟨c, hc⟩` into its components or cases. Use `ext`. Simplify using `only [pivotCols, Fin.castLE_mk]`. Apply the tactic sequence `split_ifs <;> (simp; try omega)`.
-/
theorem leadMinor_eq (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) :
    leadMinor M a = leadDet M (a + 1) := by
  have h : (a : ℕ) + 1 ≤ n := by have := a.2; omega
  unfold leadMinor pivotMinor leadDet
  rw [dif_pos h]
  congr 2
  funext c
  rcases c with ⟨c, hc⟩
  ext
  simp only [pivotCols, Fin.castLE_mk]
  split_ifs <;> (simp; try omega)

/- English proof (translation)
Simplify using `[leadDet]`.
-/
theorem leadDet_zero (M : Matrix (Fin n) (Fin n) R) : leadDet M 0 = 1 := by
  simp [leadDet]

/- English proof (translation)
Introduce `R _ n M j S`. Establish `hP : flagMinor (pivotMatrix M) j S = (∏ k ∈ Finset.range j, leadDet M (k + 1)) * flagMinor M j S`. Unfold `flagMinor`. Rewrite using `[pivotMatrix_rows, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ (pivotCoeff_isLowerTriangular M j)]`. Simplify using `only [pivotCoeff_diag]`.

Rewrite using `[Fin.prod_univ_eq_prod_range (fun k => leadDet M k), Finset.prod_range_succ', leadDet_zero, mul_one]`. Establish `hI : ∏ a ∈ Finset.Iic j, leadMinor M a = ∏ k ∈ Finset.range (j + 1), leadDet M (k + 1)`. Simplify using `only [leadMinor_eq]`. Establish `e` using `Finset.prod_map (Finset.Iic j) Fin.valEmbedding (fun k => leadDet M (k + 1))`. Rewrite `e` using `[Fin.map_valEmbedding_Iic]`.

Rewrite using `[← show (Finset.Iic (j : ℕ)) = Finset.range (j + 1) by ext; simp, e]`. Both sides reduce to the same expression. Rewrite using `[hP, hI, Finset.prod_range_succ, leadMinor_eq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem proof : FlagPivotIdentity.Statement := by
  intro R _ n M j S
  have hP : flagMinor (pivotMatrix M) j S =
      (∏ k ∈ Finset.range j, leadDet M (k + 1)) * flagMinor M j S := by
    unfold flagMinor
    rw [pivotMatrix_rows, Matrix.det_mul,
      Matrix.det_of_isLowerTriangular _ (pivotCoeff_isLowerTriangular M j)]
    simp only [pivotCoeff_diag]
    rw [Fin.prod_univ_eq_prod_range (fun k => leadDet M k), Finset.prod_range_succ', leadDet_zero, mul_one]
  have hI : ∏ a ∈ Finset.Iic j, leadMinor M a = ∏ k ∈ Finset.range (j + 1), leadDet M (k + 1) := by
    simp only [leadMinor_eq]
    have e := Finset.prod_map (Finset.Iic j) Fin.valEmbedding (fun k => leadDet M (k + 1))
    rw [Fin.map_valEmbedding_Iic] at e
    rw [← show (Finset.Iic (j : ℕ)) = Finset.range (j + 1) by ext; simp, e]
    rfl
  rw [hP, hI, Finset.prod_range_succ, leadMinor_eq]
  ring

end FlagPivotIdentity

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
