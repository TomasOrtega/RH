import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DetSubUpper

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

open Matrix ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {n : ℕ}

abbrev lb (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Matrix (Fin i) (Fin i) ℂ :=
  M.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem det_lb (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (lb M i).det = lminor M (Fin.castSucc i) := rfl

def wv (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Fin i → ℂ :=
  vecMul (fun j : Fin i => M i (Fin.castLE i.isLt.le j)) (lb M i)⁻¹

def Lm (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => if h : (k : ℕ) < i then -wv M i ⟨k, h⟩ else if k = i then 1 else 0

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem row_expand (N M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    (hup : ∀ k : Fin n, i < k → N i k = 0) (hd : N i i = 1) :
    (N * M) i j = (∑ k : Fin i, N i (Fin.castLE i.isLt.le k) * M (Fin.castLE i.isLt.le k) j) + M i j := by
  classical
  rw [Matrix.mul_apply]
  have h1 : ∑ k : Fin n, N i k * M k j = ∑ k ∈ Finset.univ.filter (fun k => k ≤ i), N i k * M k j := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rfl
    · rw [hup k (lt_of_not_ge hk), zero_mul]
  have h2 : Finset.univ.filter (fun k : Fin n => k ≤ i) = insert i (Finset.univ.filter (fun k => k < i)) := by
    ext k
    simp [le_iff_lt_or_eq, or_comm]
  have h3 : ∑ k ∈ Finset.univ.filter (fun k : Fin n => k < i), N i k * M k j =
      ∑ k : Fin i, N i (Fin.castLE i.isLt.le k) * M (Fin.castLE i.isLt.le k) j := by
    refine Finset.sum_bij' (fun k hk => (⟨k, (Finset.mem_filter.mp hk).2⟩ : Fin i))
      (fun k _ => Fin.castLE i.isLt.le k) (fun _ _ => Finset.mem_univ _) (fun k _ => ?_)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact k.isLt
  rw [h1, h2, Finset.sum_insert (by simp), h3, hd, one_mul, add_comm]

/- English proof (translation)
Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem Lm_up (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) (h : i < k) : Lm M i k = 0 := by
  simp only [Lm, Matrix.of_apply]
  have h' : ¬ ((k : ℕ) < i) := by rw [Fin.lt_iff_val_lt_val] at h; omega
  rw [dif_neg h', if_neg (ne_of_gt h)]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem Lm_diag (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Lm M i i = 1 := by
  simp [Lm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem Lm_det (M : Matrix (Fin n) (Fin n) ℂ) : (Lm M).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun i k h => Lm_up M i k (OrderDual.toDual_lt_toDual.mp h))]
  simp [Lm_diag]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem row_sys (N M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hup : ∀ k : Fin n, i < k → N i k = 0) (hd : N i i = 1)
    (hz : ∀ j : Fin n, j < i → (N * M) i j = 0) :
    vecMul (fun k : Fin i => N i (Fin.castLE i.isLt.le k)) (lb M i) =
      -fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by
  funext j'
  have hrow := row_expand N M i (Fin.castLE i.isLt.le j') hup hd
  rw [hz _ (by simp [Fin.lt_iff_val_lt_val])] at hrow
  simp only [vecMul, dotProduct, lb, submatrix_apply, Pi.neg_apply]
  linear_combination (-1 : ℂ) * hrow

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion repeatedly using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem Lm_mul_up (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k : Fin (n + 1), lminor M k ≠ 0)
    (i j : Fin n) (h : j < i) : (Lm M * M) i j = 0 := by
  have hdet : IsUnit (lb M i).det := by rw [det_lb]; exact isUnit_iff_ne_zero.mpr (hM _)
  rw [row_expand (Lm M) M i j (fun k hk => Lm_up M i k hk) (Lm_diag M i)]
  have hL : ∀ k : Fin i, Lm M i (Fin.castLE i.isLt.le k) = -wv M i k := by
    intro k
    simp only [Lm, Matrix.of_apply]
    rw [dif_pos (by simp)]
    rfl
  simp_rw [hL]
  have key : vecMul (wv M i) (lb M i) = fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by
    rw [wv, vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, vecMul_one]
  have hk := congrFun key ⟨j, h⟩
  simp only [vecMul, dotProduct, lb, submatrix_apply] at hk
  have hk' : ∑ k : Fin i, wv M i k * M (Fin.castLE i.isLt.le k) j = M i j := hk
  simp only [neg_mul, Finset.sum_neg_distrib, hk', neg_add_cancel]

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem Lm_unique (N M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k : Fin (n + 1), lminor M k ≠ 0)
    (hup : ∀ i k : Fin n, i < k → N i k = 0) (hd : ∀ i, N i i = 1)
    (hz : ∀ i j : Fin n, j < i → (N * M) i j = 0) : N = Lm M := by
  ext i k
  have hdet : IsUnit (lb M i).det := by rw [det_lb]; exact isUnit_iff_ne_zero.mpr (hM _)
  have h1 := row_sys N M i (hup i) (hd i) (hz i)
  have h2 := row_sys (Lm M) M i (fun k hk => Lm_up M i k hk) (Lm_diag M i)
    (fun j hj => Lm_mul_up M hM i j hj)
  have heq : (fun k : Fin i => N i (Fin.castLE i.isLt.le k)) = fun k => Lm M i (Fin.castLE i.isLt.le k) := by
    have h3 := congrArg (fun v => vecMul v (lb M i)⁻¹) (h1.trans h2.symm)
    simpa only [vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, vecMul_one] using h3
  rcases lt_trichotomy k i with hk | rfl | hk
  · exact congrFun heq ⟨k, hk⟩
  · rw [hd, Lm_diag]
  · rw [hup i k hk, Lm_up M i k hk]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Use symmetry to reverse the relation.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem lminor_nb (N B : Matrix (Fin n) (Fin n) ℂ) (hup : ∀ i k : Fin n, i < k → N i k = 0)
    (hd : ∀ i, N i i = 1) (hB : B.BlockTriangular id) (k : Fin (n + 1)) :
    lminor (N * B) k = ∏ j : Fin k, B (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
  set e : Fin k → Fin n := Fin.castLE (Nat.le_of_lt_succ k.isLt) with he
  have hmono : ∀ a b : Fin k, a < b → e a < e b := fun a b h => h
  have hsub : (N * B).submatrix e e = N.submatrix e e * B.submatrix e e := by
    ext a b
    simp only [submatrix_apply, mul_apply]
    symm
    refine Fintype.sum_of_injective e (Fin.castLE_injective _) _ _ (fun c hc => ?_) (fun _ => rfl)
    have hc' : (k : ℕ) ≤ c := by
      by_contra hlt
      exact hc ⟨⟨c, by omega⟩, Fin.ext rfl⟩
    have hac : e a < c := by
      rw [Fin.lt_iff_val_lt_val]
      show (a : ℕ) < c
      omega
    rw [hup _ _ hac, zero_mul]
  have hNt : (N.submatrix e e).BlockTriangular OrderDual.toDual :=
    fun a b h => hup _ _ (hmono _ _ (OrderDual.toDual_lt_toDual.mp h))
  have hBt : (B.submatrix e e).BlockTriangular id := fun a b h => hB (hmono _ _ h)
  rw [lminor, ← he, hsub, det_mul, Matrix.det_of_lowerTriangular _ hNt,
    Matrix.det_of_upperTriangular hBt]
  simp [hd]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
