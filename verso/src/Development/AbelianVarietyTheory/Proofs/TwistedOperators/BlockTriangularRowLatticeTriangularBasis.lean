import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

open GlobalTheory.InertZeta Matrix Formalism.UG

noncomputable section
namespace GlobalTheory.InertZeta.RowSpan
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

def rowM (g : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (U V : Matrix (Fin N) (Fin N) L) (k : Fin N) : Fin (N + 2) → L :=
  ∑ l, U k l • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid l) + ∑ l, V k l • g (mid l)

section
variable {g : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {g₀ U V : Matrix (Fin N) (Fin N) L} {b : Fin N → L}

/- English proof (translation)
Simplify using `[rowM, Finset.sum_apply, Matrix.one_apply, hg10, mid_ne_zero]`.
-/
theorem rowM_zero (hg10 : ∀ i, g (mid i) 0 = 0) (k : Fin N) : rowM g U V k 0 = 0 := by
  simp [rowM, Finset.sum_apply, Matrix.one_apply, hg10, mid_ne_zero]

/- English proof (translation)
Simplify using `[rowM, Finset.sum_apply, Matrix.one_apply, hg11, mid_injective.eq_iff, Matrix.mul_apply]`.
-/
theorem rowM_mid (hg11 : ∀ i j, g (mid i) (mid j) = g₀ i j) (k j : Fin N) :
    rowM g U V k (mid j) = (U + V * g₀) k j := by
  simp [rowM, Finset.sum_apply, Matrix.one_apply, hg11, mid_injective.eq_iff, Matrix.mul_apply]

/- English proof (translation)
Simplify using `[rowM, Finset.sum_apply, Matrix.one_apply, hg12, mid_ne_last, Matrix.mulVec, dotProduct]`.
-/
theorem rowM_last (hg12 : ∀ i, g (mid i) (Fin.last (N + 1)) = (g₀ *ᵥ b) i) (k : Fin N) :
    rowM g U V k (Fin.last (N + 1)) = (V *ᵥ (g₀ *ᵥ b)) k := by
  simp [rowM, Finset.sum_apply, Matrix.one_apply, hg12, mid_ne_last, Matrix.mulVec, dotProduct]

/- English proof (translation)
Simplify using `[Finset.sum_apply, rowM_zero hg10]`.
-/
theorem comb_zero (hg10 : ∀ i, g (mid i) 0 = 0) (A : Matrix (Fin N) (Fin N) L) (i : Fin N) :
    (∑ k, A i k • rowM g U V k) 0 = 0 := by
  simp [Finset.sum_apply, rowM_zero hg10]

/- English proof (translation)
Simplify using `[Finset.sum_apply, rowM_mid hg11, Matrix.mul_apply]`.
-/
theorem comb_mid (hg11 : ∀ i j, g (mid i) (mid j) = g₀ i j) (A : Matrix (Fin N) (Fin N) L) (i j : Fin N) :
    (∑ k, A i k • rowM g U V k) (mid j) = (A * (U + V * g₀)) i j := by
  simp [Finset.sum_apply, rowM_mid hg11, Matrix.mul_apply]

/- English proof (translation)
Simplify using `[Finset.sum_apply, rowM_last hg12, Matrix.mulVec, dotProduct]`.
-/
theorem comb_last (hg12 : ∀ i, g (mid i) (Fin.last (N + 1)) = (g₀ *ᵥ b) i) (A : Matrix (Fin N) (Fin N) L) (i : Fin N) :
    (∑ k, A i k • rowM g U V k) (Fin.last (N + 1)) = (A *ᵥ (V *ᵥ (g₀ *ᵥ b))) i := by
  simp [Finset.sum_apply, rowM_last hg12, Matrix.mulVec, dotProduct]
end

def rowsP (a : ℤ) (g : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (U V : Matrix (Fin N) (Fin N) L) (y : L) :
    Matrix (Fin (N + 2)) (Fin (N + 2)) L := fun i =>
  Fin.cases (motive := fun _ => Fin (N + 2) → L)
    (if 0 ≤ a then (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 else g 0)
    (Fin.lastCases (motive := fun _ => Fin (N + 2) → L)
      (y • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1))) (rowM g U V)) i

section
variable (a : ℤ) (g : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (U V : Matrix (Fin N) (Fin N) L) (y : L)

/- English proof (translation)
Rewrite using `[rowsP, Fin.cases_zero]`.
-/
theorem rowsP_zero : rowsP a g U V y 0 = if 0 ≤ a then (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 else g 0 := by
  rw [rowsP, Fin.cases_zero]

/- English proof (translation)
Rewrite using `[rowsP, mid, Fin.cases_succ, Fin.lastCases_castSucc]`.
-/
theorem rowsP_mid (k : Fin N) : rowsP a g U V y (mid k) = rowM g U V k := by
  rw [rowsP, mid, Fin.cases_succ, Fin.lastCases_castSucc]

/- English proof (translation)
Rewrite using `[rowsP, ← Fin.succ_last, Fin.cases_succ, Fin.lastCases_last]`.
-/
theorem rowsP_last :
    rowsP a g U V y (Fin.last (N + 1)) = y • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) := by
  rw [rowsP, ← Fin.succ_last, Fin.cases_succ, Fin.lastCases_last]
end

/- English proof (translation)
Rewrite using `[Matrix.det_succ_column_zero, Fin.sum_univ_succ]`. Establish `h1 : ∀ i : Fin (N + 1), rowsP a g U V y i.succ 0 = 0` using `fun i => by`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => rw [Fin.succ_last, rowsP_last]`. Simplify using `[Matrix.one_apply]`.

Consider the case `cast k => exact (rowsP_mid a g U V y k).symm ▸ rowM_zero hg10 k`. Simplify using `only [h1, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]`. Rewrite using `[mul_assoc]`. Use `congr 1`. Rewrite using `[Matrix.det_succ_row _ (Fin.last N), Fin.sum_univ_castSucc]`.

Establish `h2 : ∀ j : Fin N, rowsP a g U V y (Fin.last N).succ j.castSucc.succ = 0` using `fun j => by`. Rewrite using `[Fin.succ_last, rowsP_last]`. Simplify using `[Matrix.one_apply, ← mid.eq_def]`. Introduce `h`. Conclude with `absurd h.symm (mid_ne_last j)`.

Simplify using `only [Matrix.submatrix_apply, h2, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last]`. Establish `h3 : ((rowsP a g U V y).submatrix Fin.succ Fin.succ).submatrix Fin.castSucc Fin.castSucc = U + V * g₀`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply]`. Conclude with `(rowsP_mid a g U V y i) ▸ rowM_mid hg11 i j`.

Rewrite using `[h3, Fin.succ_last, rowsP_last]`. Simplify using `[Matrix.one_apply]`. Put the polynomial expressions in normal form.
-/
theorem det_rowsP {a : ℤ} {g : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {g₀ U V : Matrix (Fin N) (Fin N) L} {y : L}
    (hg10 : ∀ i, g (mid i) 0 = 0) (hg11 : ∀ i j, g (mid i) (mid j) = g₀ i j) :
    (rowsP a g U V y).det = rowsP a g U V y 0 0 * (U + V * g₀).det * y := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h1 : ∀ i : Fin (N + 1), rowsP a g U V y i.succ 0 = 0 := fun i => by
    induction i using Fin.lastCases with
    | last => rw [Fin.succ_last, rowsP_last]; simp [Matrix.one_apply]
    | cast k => exact (rowsP_mid a g U V y k).symm ▸ rowM_zero hg10 k
  simp only [h1, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul,
    Fin.succAbove_zero]
  rw [mul_assoc]
  congr 1
  rw [Matrix.det_succ_row _ (Fin.last N), Fin.sum_univ_castSucc]
  have h2 : ∀ j : Fin N, rowsP a g U V y (Fin.last N).succ j.castSucc.succ = 0 := fun j => by
    rw [Fin.succ_last, rowsP_last]; simp [Matrix.one_apply, ← mid.eq_def]; intro h; exact absurd h.symm (mid_ne_last j)
  simp only [Matrix.submatrix_apply, h2, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last]
  have h3 : ((rowsP a g U V y).submatrix Fin.succ Fin.succ).submatrix Fin.castSucc Fin.castSucc = U + V * g₀ := by
    ext i j
    simp only [Matrix.submatrix_apply]
    exact (rowsP_mid a g U V y i) ▸ rowM_mid hg11 i j
  rw [h3, Fin.succ_last, rowsP_last]
  simp [Matrix.one_apply]
  ring_nf

def vecOf (x₀ : L) (xm : Fin N → L) (xl : L) : Fin (N + 2) → L := fun i =>
  Fin.cases (motive := fun _ => L) x₀ (Fin.lastCases (motive := fun _ => L) xl xm) i

/- English proof (translation)
Rewrite using `[vecOf, Fin.cases_zero]`.
-/
@[simp] theorem vecOf_zero (x₀ : L) (xm : Fin N → L) (xl : L) : vecOf x₀ xm xl 0 = x₀ := by
  rw [vecOf, Fin.cases_zero]
/- English proof (translation)
Rewrite using `[vecOf, mid, Fin.cases_succ, Fin.lastCases_castSucc]`.
-/
@[simp] theorem vecOf_mid (x₀ : L) (xm : Fin N → L) (xl : L) (k : Fin N) : vecOf x₀ xm xl (mid k) = xm k := by
  rw [vecOf, mid, Fin.cases_succ, Fin.lastCases_castSucc]
/- English proof (translation)
Rewrite using `[vecOf, ← Fin.succ_last, Fin.cases_succ, Fin.lastCases_last]`.
-/
@[simp] theorem vecOf_last (x₀ : L) (xm : Fin N → L) (xl : L) : vecOf x₀ xm xl (Fin.last (N + 1)) = xl := by
  rw [vecOf, ← Fin.succ_last, Fin.cases_succ, Fin.lastCases_last]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Break down `idx_cases j with rfl | ⟨k, rfl⟩ | rfl` into its components or cases. Use `exacts [h0, hm k, hl]`.
-/
theorem vec_ext {f f' : Fin (N + 2) → L} (h0 : f 0 = f' 0) (hm : ∀ j, f (mid j) = f' (mid j))
    (hl : f (Fin.last (N + 1)) = f' (Fin.last (N + 1))) : f = f' := by
  funext j
  rcases idx_cases j with rfl | ⟨k, rfl⟩ | rfl
  exacts [h0, hm k, hl]

/- English proof (translation)
The claim follows from `S.smul_mem ⟨x, hx⟩ hw`.
-/
theorem smem {n : ℕ} {S : Submodule (intL L) (Fin n → L)} {x : L} {w : Fin n → L} (hx : x ∈ intL L) (hw : w ∈ S) :
    x • w ∈ S := S.smul_mem ⟨x, hx⟩ hw

/- English proof (translation)
The claim follows from `Submodule.sum_mem _ fun i _ => smem (hx i) (hw i)`.
-/
theorem sum_smem {n : ℕ} {ι : Type} [Fintype ι] {S : Submodule (intL L) (Fin n → L)} {x : ι → L}
    {w : ι → Fin n → L} (hx : ∀ i, x i ∈ intL L) (hw : ∀ i, w i ∈ S) : ∑ i, x i • w i ∈ S :=
  Submodule.sum_mem _ fun i _ => smem (hx i) (hw i)

/- English proof (translation)
Use `show Valued.v (x / y) ≤ 1`. Rewrite using `[map_div₀]`. Conclude with `div_le_one_of_le₀ h zero_le'`.
-/
theorem div_mem_int {x y : L} (h : Valued.v x ≤ Valued.v y) : x / y ∈ intL L := by
  show Valued.v (x / y) ≤ 1
  rw [map_div₀]
  exact div_le_one_of_le₀ h zero_le'

/- English proof (translation)
Rewrite using `[map_zpow₀, hϖ, ← WithZero.exp_zsmul]`. Simplify using the standard rewrite rules.
-/
theorem v_zpow {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) : Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp

/- English proof (translation)
Rewrite using `[← zpow_natCast, v_zpow hϖ]`.
-/
theorem v_pow {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℕ) : Valued.v (ϖ ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [← zpow_natCast, v_zpow hϖ]

/- English proof (translation)
Use `show Valued.v (ϖ ^ k) ≤ 1`. Rewrite using `[v_pow hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem pow_mem_int {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℕ) : ϖ ^ k ∈ intL L := by
  show Valued.v (ϖ ^ k) ≤ 1
  rw [v_pow hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega

/- English proof (translation)
The claim follows from `last_ne_zero.symm`.
-/
theorem zero_ne_last : (0 : Fin (N + 2)) ≠ Fin.last (N + 1) := last_ne_zero.symm

/- English proof (translation)
The claim follows from `(mid_ne_zero j).symm`.
-/
theorem zero_ne_mid (j : Fin N) : (0 : Fin (N + 2)) ≠ mid j := (mid_ne_zero j).symm

/- English proof (translation)
The claim follows from `(mid_ne_last j).symm`.
-/
theorem last_ne_mid (j : Fin N) : Fin.last (N + 1) ≠ mid j := (mid_ne_last j).symm

section
variable {g : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {g₀ U V C : Matrix (Fin N) (Fin N) L} {b : Fin N → L}

/- English proof (translation)
Use `vec_ext ?_ (fun j => ?_) ?_` and prove the remaining obligations. Rewrite using `[comb_zero hg10]`. Simplify using `[Matrix.one_apply, mid_ne_zero]`. Rewrite using `[comb_mid hg11, hCM]`. Simplify using `[Matrix.one_apply, mid_injective.eq_iff, mid_ne_last, last_ne_mid]`.

Rewrite using `[comb_last hg12]`. Simplify using `[Matrix.one_apply, mid_ne_last, Matrix.mulVec_mulVec, Matrix.mul_assoc]`.
-/
theorem comb_C (hg10 : ∀ i, g (mid i) 0 = 0) (hg11 : ∀ i j, g (mid i) (mid j) = g₀ i j)
    (hg12 : ∀ i, g (mid i) (Fin.last (N + 1)) = (g₀ *ᵥ b) i) (hCM : C * (U + V * g₀) = 1) (i : Fin N) :
    ∑ k, C i k • rowM g U V k = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) +
      ((C * V * g₀) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) := by
  refine vec_ext ?_ (fun j => ?_) ?_
  · rw [comb_zero hg10]; simp [Matrix.one_apply, mid_ne_zero]
  · rw [comb_mid hg11, hCM]; simp [Matrix.one_apply, mid_injective.eq_iff, mid_ne_last, last_ne_mid]
  · rw [comb_last hg12]; simp [Matrix.one_apply, mid_ne_last, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/- English proof (translation)
Establish `hCU : g₀ * C * U = g₀ - g₀ * C * V * g₀`. Rewrite using `[eq_sub_iff_add_eq, Matrix.mul_assoc g₀ C U, Matrix.mul_assoc (g₀ * C) V, Matrix.mul_assoc g₀ C, ← Matrix.mul_add, ← Matrix.mul_add, hCM, Matrix.mul_one]`. Use `vec_ext ?_ (fun j => ?_) ?_` and prove the remaining obligations. Rewrite using `[comb_zero hg10]`. Simplify using `[Matrix.one_apply, hg10]`.

Rewrite using `[comb_mid hg11, Matrix.mul_assoc, hCM]`. Simplify using `[Matrix.one_apply, mid_ne_last, last_ne_mid, hg11]`. Rewrite using `[comb_last hg12, Pi.sub_apply, hg12, hCU, Matrix.sub_mulVec]`. Simplify using `[Matrix.one_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]`.
-/
theorem comb_gC (hg10 : ∀ i, g (mid i) 0 = 0) (hg11 : ∀ i j, g (mid i) (mid j) = g₀ i j)
    (hg12 : ∀ i, g (mid i) (Fin.last (N + 1)) = (g₀ *ᵥ b) i) (hCM : C * (U + V * g₀) = 1) (i : Fin N) :
    ∑ k, (g₀ * C) i k • rowM g U V k = g (mid i) -
      ((g₀ * C * U) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) := by
  have hCU : g₀ * C * U = g₀ - g₀ * C * V * g₀ := by
    rw [eq_sub_iff_add_eq, Matrix.mul_assoc g₀ C U, Matrix.mul_assoc (g₀ * C) V, Matrix.mul_assoc g₀ C, ← Matrix.mul_add,
      ← Matrix.mul_add, hCM, Matrix.mul_one]
  refine vec_ext ?_ (fun j => ?_) ?_
  · rw [comb_zero hg10]; simp [Matrix.one_apply, hg10]
  · rw [comb_mid hg11, Matrix.mul_assoc, hCM]; simp [Matrix.one_apply, mid_ne_last, last_ne_mid, hg11]
  · rw [comb_last hg12, Pi.sub_apply, hg12, hCU, Matrix.sub_mulVec]
    simp [Matrix.one_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]
end

/- English proof (translation)
Establish `h1 : (r ᵥ* C) ᵥ* (U + V * g₀) = r` using `by rw [Matrix.vecMul_vecMul, hCM, Matrix.vecMul_one]`. Establish `h2 : (r ᵥ* C) ⬝ᵥ (V *ᵥ (g₀ *ᵥ b)) = r ⬝ᵥ ((C * V * g₀) *ᵥ b)`. Rewrite using `[← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Use `vec_ext ?_ (fun j => ?_) ?_` and prove the remaining obligations. Simplify using `only [Matrix.vecMul, dotProduct, sum_idx, vecOf_zero, vecOf_mid, vecOf_last, rowsP_mid, rowsP_last, rowM_zero hg10]`.

Simplify using `[Matrix.one_apply]`. Simplify using `only [Matrix.vecMul, dotProduct, sum_idx, vecOf_zero, vecOf_mid, vecOf_last, rowsP_mid, rowsP_last, rowM_mid hg11]`. Use `congrFun h1 j` as an intermediate fact. Simplify using `only [Matrix.vecMul, dotProduct] at this`. Simplify using `only [Pi.smul_apply, Matrix.one_apply, last_ne_mid, if_false, smul_eq_mul, mul_zero, add_zero, zero_mul, zero_add]`.

Rewrite using `[← this, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Simplify using `only [Matrix.vecMul, dotProduct, sum_idx, vecOf_zero, vecOf_mid, vecOf_last, rowsP_mid, rowsP_last, rowM_last hg12]`. Simplify using `only [dotProduct] at h2`. Simplify using `only [Pi.smul_apply, Matrix.one_apply, if_true, smul_eq_mul, mul_one, zero_mul, zero_add]`.

Establish `e3 : ∀ u : Fin N → L, ∑ x, (z * ∑ x_1, r x_1 * C x_1 x) * u x = z * ∑ i, (r ᵥ* C) i * u i` using `fun u => by`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by simp only [Matrix.vecMul, dotProduct]; ring`. Rewrite using `[e3, h2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rho_mul {a : ℤ} {g : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {g₀ U V C : Matrix (Fin N) (Fin N) L} {b r : Fin N → L}
    {c y z : L} (hg10 : ∀ i, g (mid i) 0 = 0) (hg11 : ∀ i j, g (mid i) (mid j) = g₀ i j)
    (hg12 : ∀ i, g (mid i) (Fin.last (N + 1)) = (g₀ *ᵥ b) i) (hCM : C * (U + V * g₀) = 1) (hy : y ≠ 0) :
    vecOf 0 (fun j => z * (r ᵥ* C) j) (z * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y) ᵥ* rowsP a g U V y =
      vecOf 0 (fun j => z * r j) (z * c) := by
  have h1 : (r ᵥ* C) ᵥ* (U + V * g₀) = r := by rw [Matrix.vecMul_vecMul, hCM, Matrix.vecMul_one]
  have h2 : (r ᵥ* C) ⬝ᵥ (V *ᵥ (g₀ *ᵥ b)) = r ⬝ᵥ ((C * V * g₀) *ᵥ b) := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine vec_ext ?_ (fun j => ?_) ?_
  · simp only [Matrix.vecMul, dotProduct, sum_idx, vecOf_zero, vecOf_mid, vecOf_last, rowsP_mid, rowsP_last,
      rowM_zero hg10]
    simp [Matrix.one_apply]
  · simp only [Matrix.vecMul, dotProduct, sum_idx, vecOf_zero, vecOf_mid, vecOf_last, rowsP_mid, rowsP_last,
      rowM_mid hg11]
    have := congrFun h1 j
    simp only [Matrix.vecMul, dotProduct] at this
    simp only [Pi.smul_apply, Matrix.one_apply, last_ne_mid, if_false, smul_eq_mul, mul_zero, add_zero, zero_mul,
      zero_add]
    rw [← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [Matrix.vecMul, dotProduct, sum_idx, vecOf_zero, vecOf_mid, vecOf_last, rowsP_mid, rowsP_last,
      rowM_last hg12]
    simp only [dotProduct] at h2
    simp only [Pi.smul_apply, Matrix.one_apply, if_true, smul_eq_mul, mul_one, zero_mul, zero_add]
    have e3 : ∀ u : Fin N → L, ∑ x, (z * ∑ x_1, r x_1 * C x_1 x) * u x = z * ∑ i, (r ᵥ* C) i * u i := fun u => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by simp only [Matrix.vecMul, dotProduct]; ring
    rw [e3, h2]
    field_simp
    ring

/- English proof (translation)
Introduce `L _ _ ϖ N a g g₀ U V C r b c y hϖ hfrac hg00 hg0m hg0l hg10 hg11 hg12 hgl0 hglm hgll hy1 hy2 hy3 hy4`. Take `⟨hU, hV, hC, hgC, hM⟩` from `hfrac`. Establish `hCM : C * (U + V * g₀) = 1` using `mul_eq_one_comm.1 hM`. Establish `hϖ0 : ϖ ≠ 0` using `fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm`. Establish `hvy : Valued.v y ≠ 0` using `fun h => by rw [h] at hy1; exact WithZero.exp_ne_zero (le_zero_iff.1 hy1)`.

Establish `hy0 : y ≠ 0` using `fun h => hvy (by rw [h, map_zero])`. Use `⟨rowsP a g U V y, vecOf 0 (fun j => ϖ ^ a.toNat * (r ᵥ* C) j) (ϖ ^ a.toNat * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y), ?_, vecOf_zero _ _ _, vecOf_mid _ _ _, vecOf_last _ _ _, ?_⟩` and prove the remaining obligations. Establish `hdet : Valued.v (U + V * g₀).det = (Valued.v C.det)⁻¹`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← map_mul, ← Matrix.det_mul, hM, Matrix.det_one, map_one]`.

Rewrite using `[det_rowsP hg10 hg11, map_mul, map_mul, hdet, rowsP_zero]`. Use `split_ifs with ha`. Rewrite using `[Int.toNat_of_nonpos (by omega)]; simp [Matrix.one_apply]`. Rewrite using `[hg00, v_zpow hϖ, Int.toNat_of_nonneg (by omega)]`. Rewrite using `[rho_mul hg10 hg11 hg12 hCM hy0]`.

Establish `hvy1 : 1 ≤ Valued.v y` using `le_trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega) hy1`. Establish `eS : ∀ i, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i ∈ rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g` using `fun i => Submodule.mem_sup_left (row_mem_rowLat _ i)`. Establish `gS : ∀ i, g i ∈ rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g` using `fun i => Submodule.mem_sup_right (row_mem_rowLat g i)`. Establish `rS : ∀ k, rowM g U V k ∈ rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g` using `fun k => add_mem (sum_smem (hU k) fun l => eS _) (sum_smem (hV k) fun l => gS _)`. Establish `hgl : g (Fin.last (N + 1)) = ϖ ^ (-a) • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1))` using `vec_ext (by simp [hgl0, Matrix.one_apply]) (fun j => by simp [hglm, Matrix.one_apply, last_ne_mid]) (by simp [hgll, Matrix.one_apply])`.

Establish `hw : vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c) = if 0 ≤ a then g 0 - ϖ ^ a.toNat • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 else ϖ ^ (-a).toNat • g 0 - (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0` using `by split_ifs with ha`. Establish `hza : (ϖ ^ a.toNat : L) = ϖ ^ a` using `by rw [← zpow_natCast, Int.toNat_of_nonneg ha]`. Apply the tactic sequence `refine vec_ext ?_ (fun j => ?_) ?_ <;>`. Simplify using `[hza, hg00, hg0m, hg0l, Matrix.one_apply, mid_ne_zero, zero_ne_mid, zero_ne_last]`. Establish `h1 : a.toNat = 0` using `by omega`.

Establish `h2 : (ϖ ^ (-a).toNat : L) * ϖ ^ a = 1`. Rewrite using `[← zpow_natCast, Int.toNat_of_nonneg (by omega), _root_.zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hϖ0)]`. Apply the tactic sequence `refine vec_ext ?_ (fun j => ?_) ?_ <;>`. Simplify using `[h1, hg00, hg0m, hg0l, Matrix.one_apply, mid_ne_zero, zero_ne_mid, zero_ne_last, ← mul_assoc, h2]`. Apply `le_antisymm` to reduce the goal to its premises.

Establish `PS : ∀ i, rowsP a g U V y i ∈ rowLat (rowsP a g U V y) ⊔ Submodule.span (intL L) {vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c)}` using `fun i => Submodule.mem_sup_left (row_mem_rowLat _ i)`. Establish `wS : vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c) ∈ rowLat (rowsP a g U V y) ⊔ Submodule.span (intL L) {vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c)}` using `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Establish `mS : ∀ k, rowM g U V k ∈ rowLat (rowsP a g U V y) ⊔ Submodule.span (intL L) {vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c)}` using `fun k => rowsP_mid a g U V y k ▸ PS (mid k)`. Establish `lastS : ∀ x, Valued.v x ≤ Valued.v y → x • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) ∈ rowLat (rowsP a g U V y) ⊔ Submodule.span (intL L) {vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c)}` using `fun x hx => by`. Use `smem (div_mem_int hx) (PS (Fin.last (N + 1)))` as an intermediate fact.

Rewrite `this` using `[rowsP_last, smul_smul, div_mul_cancel₀ _ hy0]`. Then use the resulting hypothesis. Apply the tactic sequence `apply sup_le <;> rw [rowLat_le] <;> intro i <;> rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl`. Distinguish the cases in `ha : 0 ≤ a`. Use `PS 0` as an intermediate fact. Rewrite `this` using `[rowsP_zero, if_pos ha]`. Then use the resulting hypothesis.

Establish `h` using `hw`. Rewrite `h` using `[if_neg ha]`. Establish `hP0` using `PS 0`. Rewrite `hP0` using `[rowsP_zero, if_neg ha]`. Rewrite using `[show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 = ϖ ^ (-a).toNat • g 0 - vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c) by rw [h]; abel]`.

Conclude with `sub_mem (smem (pow_mem_int hϖ _) hP0) wS`. Rewrite using `[show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) = ∑ k, C i k • rowM g U V k - ((C * V * g₀) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) by`. Rewrite using `[comb_C hg10 hg11 hg12 hCM i]`. Use the proof step `abel]`. Conclude with `sub_mem (sum_smem (hC i) mS) (lastS _ (hy2 i))`.

Use `lastS 1 (by rw [map_one]; exact hvy1); rwa [one_smul] at this` as an intermediate fact. Distinguish the cases in `ha : 0 ≤ a`. Establish `h` using `hw`. Rewrite `h` using `[if_pos ha]`. Establish `hP0` using `PS 0`.

Rewrite `hP0` using `[rowsP_zero, if_pos ha]`. Rewrite using `[show g 0 = ϖ ^ a.toNat • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 + vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c) by rw [h]; abel]`. Conclude with `add_mem (smem (pow_mem_int hϖ _) hP0) wS`. Use `PS 0` as an intermediate fact. Rewrite `this` using `[rowsP_zero, if_neg ha]`. Then use the resulting hypothesis.

Rewrite using `[show g (mid i) = ∑ k, (g₀ * C) i k • rowM g U V k + ((g₀ * C * U) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) by`. Rewrite using `[comb_gC hg10 hg11 hg12 hCM i]`. Use the proof step `abel]`. Conclude with `add_mem (sum_smem (hgC i) mS) (lastS _ (hy3 i))`. Rewrite using `[hgl]`.

Use `lastS _ (le_trans ?_ hy1)` and prove the remaining obligations. Rewrite using `[v_zpow hϖ, neg_neg, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Apply `sup_le` to reduce the goal to its premises. Rewrite using `[rowLat_le]`.

Introduce `i`. Break down `idx_cases i with rfl | ⟨k, rfl⟩ | rfl` into its components or cases. Rewrite using `[rowsP_zero]`. Use `split_ifs exacts [eS 0, gS 0]`. Rewrite using `[rowsP_mid]`.

Conclude with `rS k`. Rewrite using `[rowsP_last]`. Establish `key : ∀ x : L, x • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) ∈ rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g → Valued.v y = Valued.v x → y • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) ∈ rowLat (1 : Matrix (Fin (N + 2)) (Fin (N …` using `fun x hx hv => by`. Establish `hx0 : x ≠ 0` using `fun h => hvy (by rw [hv, h, map_zero])`. Rewrite using `[show y • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) = (y / x) • x • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) by`.

Rewrite using `[smul_smul, div_mul_cancel₀ _ hx0]]`. Conclude with `smem (div_mem_int hv.le) hx`. Break down `hy4 with h | ⟨i, h⟩ | ⟨i, h⟩` into its components or cases. Distinguish the cases in `ha : 0 ≤ a`. Use `key (ϖ ^ (-a)) (hgl ▸ gS _) ?_` and prove the remaining obligations.

Rewrite using `[h, v_zpow hϖ, neg_neg, Int.toNat_of_nonneg ha]`. Use `key 1 (by rw [one_smul]; exact eS _) ?_` and prove the remaining obligations. Rewrite using `[h, map_one, Int.toNat_eq_zero.2 (by omega)]; simp`. Use `key _ ?_ h` and prove the remaining obligations. Rewrite using `[show ((C * V * g₀) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) = ∑ k, C i k • rowM g U V k - (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) by`.

Rewrite using `[comb_C hg10 hg11 hg12 hCM i]`. Use the proof step `abel]`. Conclude with `sub_mem (sum_smem (hC i) rS) (eS _)`. Use `key _ ?_ h` and prove the remaining obligations. Rewrite using `[show ((g₀ * C * U) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) = g (mid i) - ∑ k, (g₀ * C) i k • rowM g U V k by`.

Rewrite using `[comb_gC hg10 hg11 hg12 hCM i]`. Use the proof step `abel]`. Conclude with `sub_mem (gS _) (sum_smem (hgC i) rS)`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hw] split_ifs with ha`. Conclude with `sub_mem (gS 0) (smem (pow_mem_int hϖ _) (eS 0))`.

Conclude with `sub_mem (smem (pow_mem_int hϖ _) (gS 0)) (eS 0)`.
-/
theorem spanEq_holds : SpanEq := by
  intro L _ _ ϖ N a g g₀ U V C r b c y hϖ hfrac hg00 hg0m hg0l hg10 hg11 hg12 hgl0 hglm hgll hy1 hy2 hy3 hy4
  obtain ⟨hU, hV, hC, hgC, hM⟩ := hfrac
  have hCM : C * (U + V * g₀) = 1 := mul_eq_one_comm.1 hM
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hvy : Valued.v y ≠ 0 := fun h => by rw [h] at hy1; exact WithZero.exp_ne_zero (le_zero_iff.1 hy1)
  have hy0 : y ≠ 0 := fun h => hvy (by rw [h, map_zero])
  refine ⟨rowsP a g U V y, vecOf 0 (fun j => ϖ ^ a.toNat * (r ᵥ* C) j)
    (ϖ ^ a.toNat * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y), ?_, vecOf_zero _ _ _, vecOf_mid _ _ _, vecOf_last _ _ _, ?_⟩
  · have hdet : Valued.v (U + V * g₀).det = (Valued.v C.det)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, ← Matrix.det_mul, hM, Matrix.det_one, map_one]
    rw [det_rowsP hg10 hg11, map_mul, map_mul, hdet, rowsP_zero]
    split_ifs with ha
    · rw [Int.toNat_of_nonpos (by omega)]; simp [Matrix.one_apply]
    · rw [hg00, v_zpow hϖ, Int.toNat_of_nonneg (by omega)]
  · rw [rho_mul hg10 hg11 hg12 hCM hy0]
    have hvy1 : 1 ≤ Valued.v y := le_trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega) hy1
    have eS : ∀ i, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i ∈
        rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g :=
      fun i => Submodule.mem_sup_left (row_mem_rowLat _ i)
    have gS : ∀ i, g i ∈ rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g :=
      fun i => Submodule.mem_sup_right (row_mem_rowLat g i)
    have rS : ∀ k, rowM g U V k ∈ rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g :=
      fun k => add_mem (sum_smem (hU k) fun l => eS _) (sum_smem (hV k) fun l => gS _)
    have hgl : g (Fin.last (N + 1)) = ϖ ^ (-a) • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) :=
      vec_ext (by simp [hgl0, Matrix.one_apply]) (fun j => by simp [hglm, Matrix.one_apply, last_ne_mid])
        (by simp [hgll, Matrix.one_apply])
    have hw : vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c) = if 0 ≤ a then
        g 0 - ϖ ^ a.toNat • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0
        else ϖ ^ (-a).toNat • g 0 - (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 := by
      split_ifs with ha
      · have hza : (ϖ ^ a.toNat : L) = ϖ ^ a := by rw [← zpow_natCast, Int.toNat_of_nonneg ha]
        refine vec_ext ?_ (fun j => ?_) ?_ <;>
          simp [hza, hg00, hg0m, hg0l, Matrix.one_apply, mid_ne_zero, zero_ne_mid, zero_ne_last]
      · have h1 : a.toNat = 0 := by omega
        have h2 : (ϖ ^ (-a).toNat : L) * ϖ ^ a = 1 := by
          rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), _root_.zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hϖ0)]
        refine vec_ext ?_ (fun j => ?_) ?_ <;>
          simp [h1, hg00, hg0m, hg0l, Matrix.one_apply, mid_ne_zero, zero_ne_mid, zero_ne_last, ← mul_assoc, h2]
    apply le_antisymm
    · have PS : ∀ i, rowsP a g U V y i ∈ rowLat (rowsP a g U V y) ⊔
          Submodule.span (intL L) {vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c)} :=
        fun i => Submodule.mem_sup_left (row_mem_rowLat _ i)
      have wS : vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c) ∈ rowLat (rowsP a g U V y) ⊔
          Submodule.span (intL L) {vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c)} :=
        Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      have mS : ∀ k, rowM g U V k ∈ rowLat (rowsP a g U V y) ⊔
          Submodule.span (intL L) {vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c)} :=
        fun k => rowsP_mid a g U V y k ▸ PS (mid k)
      have lastS : ∀ x, Valued.v x ≤ Valued.v y → x • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) ∈
          rowLat (rowsP a g U V y) ⊔
          Submodule.span (intL L) {vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c)} := fun x hx => by
        have := smem (div_mem_int hx) (PS (Fin.last (N + 1)))
        rwa [rowsP_last, smul_smul, div_mul_cancel₀ _ hy0] at this
      apply sup_le <;> rw [rowLat_le] <;> intro i <;> rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl
      · by_cases ha : 0 ≤ a
        · have := PS 0; rwa [rowsP_zero, if_pos ha] at this
        · have h := hw; rw [if_neg ha] at h
          have hP0 := PS 0; rw [rowsP_zero, if_neg ha] at hP0
          rw [show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 = ϖ ^ (-a).toNat • g 0 -
            vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c) by rw [h]; abel]
          exact sub_mem (smem (pow_mem_int hϖ _) hP0) wS
      · rw [show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) = ∑ k, C i k • rowM g U V k -
          ((C * V * g₀) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) by
          rw [comb_C hg10 hg11 hg12 hCM i]; abel]
        exact sub_mem (sum_smem (hC i) mS) (lastS _ (hy2 i))
      · have := lastS 1 (by rw [map_one]; exact hvy1); rwa [one_smul] at this
      · by_cases ha : 0 ≤ a
        · have h := hw; rw [if_pos ha] at h
          have hP0 := PS 0; rw [rowsP_zero, if_pos ha] at hP0
          rw [show g 0 = ϖ ^ a.toNat • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 +
            vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c) by rw [h]; abel]
          exact add_mem (smem (pow_mem_int hϖ _) hP0) wS
        · have := PS 0; rwa [rowsP_zero, if_neg ha] at this
      · rw [show g (mid i) = ∑ k, (g₀ * C) i k • rowM g U V k +
          ((g₀ * C * U) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) by
          rw [comb_gC hg10 hg11 hg12 hCM i]; abel]
        exact add_mem (sum_smem (hgC i) mS) (lastS _ (hy3 i))
      · rw [hgl]
        refine lastS _ (le_trans ?_ hy1)
        rw [v_zpow hϖ, neg_neg, WithZero.exp_le_exp]; omega
    · apply sup_le
      · rw [rowLat_le]; intro i; rcases idx_cases i with rfl | ⟨k, rfl⟩ | rfl
        · rw [rowsP_zero]; split_ifs
          exacts [eS 0, gS 0]
        · rw [rowsP_mid]; exact rS k
        · rw [rowsP_last]
          have key : ∀ x : L, x • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) ∈
              rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g → Valued.v y = Valued.v x →
              y • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) ∈
              rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g := fun x hx hv => by
            have hx0 : x ≠ 0 := fun h => hvy (by rw [hv, h, map_zero])
            rw [show y • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) =
              (y / x) • x • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) by
              rw [smul_smul, div_mul_cancel₀ _ hx0]]
            exact smem (div_mem_int hv.le) hx
          rcases hy4 with h | ⟨i, h⟩ | ⟨i, h⟩
          · by_cases ha : 0 ≤ a
            · refine key (ϖ ^ (-a)) (hgl ▸ gS _) ?_
              rw [h, v_zpow hϖ, neg_neg, Int.toNat_of_nonneg ha]
            · refine key 1 (by rw [one_smul]; exact eS _) ?_
              rw [h, map_one, Int.toNat_eq_zero.2 (by omega)]; simp
          · refine key _ ?_ h
            rw [show ((C * V * g₀) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) =
              ∑ k, C i k • rowM g U V k - (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) by
              rw [comb_C hg10 hg11 hg12 hCM i]; abel]
            exact sub_mem (sum_smem (hC i) rS) (eS _)
          · refine key _ ?_ h
            rw [show ((g₀ * C * U) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) =
              g (mid i) - ∑ k, (g₀ * C) i k • rowM g U V k by
              rw [comb_gC hg10 hg11 hg12 hCM i]; abel]
            exact sub_mem (gS _) (sum_smem (hgC i) rS)
      · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hw]
        split_ifs with ha
        · exact sub_mem (gS 0) (smem (pow_mem_int hϖ _) (eS 0))
        · exact sub_mem (smem (pow_mem_int hϖ _) (gS 0)) (eS 0)

end GlobalTheory.InertZeta.RowSpan
