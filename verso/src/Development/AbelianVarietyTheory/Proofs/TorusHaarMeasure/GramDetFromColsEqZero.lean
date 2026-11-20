import Mathlib

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

namespace GramSubmodular

variable {m α β γ : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/- English proof (translation)
The claim follows from `(Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self U).det_nonneg).1`.
-/
lemma gram_det_re_nonneg (U : Matrix m α ℂ) : 0 ≤ (Uᴴ * U).det.re :=
  (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self U).det_nonneg).1

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
/- English proof (translation)
Rewrite using `[conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]`.
-/
lemma gram_fromCols (U : Matrix m α ℂ) (V : Matrix m β ℂ) :
    (fromCols U V)ᴴ * fromCols U V = fromBlocks (Uᴴ * U) (Uᴴ * V) (Vᴴ * U) (Vᴴ * V) := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]

end GramSubmodular

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
/- English proof (translation)
Establish `h` using `Complex.le_def.mp (posSemidef_conjTranspose_mul_self X).det_nonneg`. Conclude with `⟨by simpa using h.1, by simpa using h.2.symm⟩`.
-/
private lemma gram_det_re_nonneg_and_im_eq_zero (X : Matrix m α ℂ) : 0 ≤ (Xᴴ * X).det.re ∧ (Xᴴ * X).det.im = 0 := by
  have h := Complex.le_def.mp (posSemidef_conjTranspose_mul_self X).det_nonneg
  exact ⟨by simpa using h.1, by simpa using h.2.symm⟩

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
/- English proof (translation)
Rewrite using `[conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]`.
-/
private lemma gram_fromCols_eq_fromBlocks (X : Matrix m α ℂ) (N : Matrix m n ℂ) :
    (fromCols X N)ᴴ * fromCols X N = fromBlocks (Xᴴ * X) (Xᴴ * N) (Nᴴ * X) (Nᴴ * N) := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
/- English proof (translation)
Establish `hG : (Xᴴ * X)⁻¹ᴴ = (Xᴴ * X)⁻¹`. Rewrite using `[conjTranspose_nonsing_inv, conjTranspose_mul, conjTranspose_conjTranspose]`. Establish `hGG : (Xᴴ * X)⁻¹ * (Xᴴ * X) = 1` using `nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)`. Establish `hQ : X * (Xᴴ * X)⁻¹ * Xᴴ * (X * (Xᴴ * X)⁻¹ * Xᴴ) = X * (Xᴴ * X)⁻¹ * Xᴴ`. Rewrite using `[show X * (Xᴴ * X)⁻¹ * Xᴴ * (X * (Xᴴ * X)⁻¹ * Xᴴ) = X * ((Xᴴ * X)⁻¹ * (Xᴴ * X)) * (Xᴴ * X)⁻¹ * Xᴴ by simp only [Matrix.mul_assoc], hGG, Matrix.mul_one]`.

Establish `hP : (1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * (1 - X * (Xᴴ * X)⁻¹ * Xᴴ) = 1 - X * (Xᴴ * X)⁻¹ * Xᴴ`. Rewrite using `[sub_mul, mul_sub, mul_sub, hQ]`. Simplify using `only [Matrix.one_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Establish `hPh : (1 - X * (Xᴴ * X)⁻¹ * Xᴴ)ᴴ = 1 - X * (Xᴴ * X)⁻¹ * Xᴴ`.

Rewrite using `[conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, Matrix.mul_assoc]`. Rewrite using `[conjTranspose_mul, hPh, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ N, hP]`. Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]`.
-/
private lemma gram_projection_residual_eq [DecidableEq m] (X : Matrix m α ℂ) (N : Matrix m n ℂ)
    (h : (Xᴴ * X).det ≠ 0) :
    ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * N)ᴴ * ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * N) =
      Nᴴ * N - Nᴴ * X * (Xᴴ * X)⁻¹ * (Xᴴ * N) := by
  have hG : (Xᴴ * X)⁻¹ᴴ = (Xᴴ * X)⁻¹ := by
    rw [conjTranspose_nonsing_inv, conjTranspose_mul, conjTranspose_conjTranspose]
  have hGG : (Xᴴ * X)⁻¹ * (Xᴴ * X) = 1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)
  have hQ : X * (Xᴴ * X)⁻¹ * Xᴴ * (X * (Xᴴ * X)⁻¹ * Xᴴ) = X * (Xᴴ * X)⁻¹ * Xᴴ := by
    rw [show X * (Xᴴ * X)⁻¹ * Xᴴ * (X * (Xᴴ * X)⁻¹ * Xᴴ) =
      X * ((Xᴴ * X)⁻¹ * (Xᴴ * X)) * (Xᴴ * X)⁻¹ * Xᴴ by simp only [Matrix.mul_assoc], hGG,
      Matrix.mul_one]
  have hP : (1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * (1 - X * (Xᴴ * X)⁻¹ * Xᴴ) =
      1 - X * (Xᴴ * X)⁻¹ * Xᴴ := by
    rw [sub_mul, mul_sub, mul_sub, hQ]
    simp only [Matrix.one_mul, Matrix.mul_one]
    abel
  have hPh : (1 - X * (Xᴴ * X)⁻¹ * Xᴴ)ᴴ = 1 - X * (Xᴴ * X)⁻¹ * Xᴴ := by
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, hG, Matrix.mul_assoc]
  rw [conjTranspose_mul, hPh, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ N, hP]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
/- English proof (translation)
Use `haveI := invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr h)`. Rewrite using `[gram_fromCols_eq_fromBlocks, det_fromBlocks₁₁, invOf_eq_nonsing_inv, gram_projection_residual_eq X N h]`.
-/
private lemma gram_det_fromCols_eq_mul_residual [DecidableEq m] (X : Matrix m α ℂ) (N : Matrix m n ℂ)
    (h : (Xᴴ * X).det ≠ 0) :
    ((fromCols X N)ᴴ * fromCols X N).det = (Xᴴ * X).det *
      (((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * N)ᴴ * ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * N)).det := by
  haveI := invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr h)
  rw [gram_fromCols_eq_fromBlocks, det_fromBlocks₁₁, invOf_eq_nonsing_inv, gram_projection_residual_eq X N h]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
/- English proof (translation)
Simplify using `[Complex.mul_re, hz]`.
-/
private lemma re_mul_of_im_eq_zero {z w : ℂ} (hz : z.im = 0) : (z * w).re = z.re * w.re := by
  simp [Complex.mul_re, hz]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
/- English proof (translation)
Take `⟨v, hv0, hv⟩` from `exists_mulVec_eq_zero_iff.mpr h`. Establish `hXv : X *ᵥ v = 0` using `(conjTranspose_mul_self_mulVec_eq_zero X v).mp hv`. Use `exists_mulVec_eq_zero_iff.mp ⟨Sum.elim v 0, fun hw => hv0 ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Simplify using `using congrFun hw (Sum.inl a)`.

Rewrite using `[conjTranspose_mul_self_mulVec_eq_zero, fromCols_mulVec]`. Simplify using `[Function.comp_def, hXv]`. Conclude with `N.mulVec_zero`.
-/
private lemma gram_det_fromCols_eq_zero_of_gram_det_eq_zero (X : Matrix m α ℂ) (N : Matrix m n ℂ)
    (h : (Xᴴ * X).det = 0) : ((fromCols X N)ᴴ * fromCols X N).det = 0 := by
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr h
  have hXv : X *ᵥ v = 0 := (conjTranspose_mul_self_mulVec_eq_zero X v).mp hv
  refine exists_mulVec_eq_zero_iff.mp ⟨Sum.elim v 0, fun hw => hv0 ?_, ?_⟩
  · funext a
    simpa using congrFun hw (Sum.inl a)
  · rw [conjTranspose_mul_self_mulVec_eq_zero, fromCols_mulVec]
    simp [Function.comp_def, hXv]
    exact N.mulVec_zero

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
/- English proof (translation)
Distinguish the cases in `h : (Yᴴ * Y).det = 0`. Rewrite using `[gram_det_fromCols_eq_zero_of_gram_det_eq_zero Y Z h, h]`. Simplify using the standard rewrite rules. Rewrite using `[gram_det_fromCols_eq_mul_residual Y Z h, re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero Y).2]`. Use `mul_le_mul_of_nonneg_left ?_ (gram_det_re_nonneg_and_im_eq_zero Y).1` and prove the remaining obligations.

Establish `hQ : ((Yᴴ * Z)ᴴ * (Yᴴ * Y)⁻¹ * (Yᴴ * Z)).PosSemidef` using `(posSemidef_conjTranspose_mul_self Y).inv.conjTranspose_mul_mul_same _`. Establish `hmono'` using `(hmono γ _ _ (posSemidef_conjTranspose_mul_self ((1 - Y * (Yᴴ * Y)⁻¹ * Yᴴ) * Z)) hQ).2.1`. Use `hmono'.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[gram_projection_residual_eq Y Z h, conjTranspose_mul, conjTranspose_conjTranspose, sub_add_cancel]`.
-/
private lemma gram_det_fromCols_le_mul
    (hmono : ∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0))
    (Y : Matrix m β ℂ) (Z : Matrix m γ ℂ) :
    ((fromCols Y Z)ᴴ * fromCols Y Z).det.re ≤ (Yᴴ * Y).det.re * (Zᴴ * Z).det.re := by
  classical
  by_cases h : (Yᴴ * Y).det = 0
  · rw [gram_det_fromCols_eq_zero_of_gram_det_eq_zero Y Z h, h]
    simp
  · rw [gram_det_fromCols_eq_mul_residual Y Z h, re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero Y).2]
    refine mul_le_mul_of_nonneg_left ?_ (gram_det_re_nonneg_and_im_eq_zero Y).1
    have hQ : ((Yᴴ * Z)ᴴ * (Yᴴ * Y)⁻¹ * (Yᴴ * Z)).PosSemidef :=
      (posSemidef_conjTranspose_mul_self Y).inv.conjTranspose_mul_mul_same _
    have hmono' := (hmono γ _ _ (posSemidef_conjTranspose_mul_self
      ((1 - Y * (Yᴴ * Y)⁻¹ * Yᴴ) * Z)) hQ).2.1
    refine hmono'.trans (le_of_eq ?_)
    rw [gram_projection_residual_eq Y Z h, conjTranspose_mul, conjTranspose_conjTranspose, sub_add_cancel]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
/- English proof (translation)
Distinguish the cases in `h : (Xᴴ * X).det = 0`. Rewrite using `[h]`. Simplify using `using mul_nonneg (gram_det_re_nonneg_and_im_eq_zero (fromCols X Y)).1 (gram_det_re_nonneg_and_im_eq_zero (fromCols X Z)).1`. Rewrite using `[gram_det_fromCols_eq_mul_residual X _ h, gram_det_fromCols_eq_mul_residual X Y h, gram_det_fromCols_eq_mul_residual X Z h, mul_fromCols, re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero X).2, re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero X).2, re_mul_of_im_eq_ze …`. Establish `hF` using `gram_det_fromCols_le_mul hmono ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * Y) ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * Z)`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hF (mul_self_nonneg (Xᴴ * X).det.re)]`.
-/
private lemma gram_det_koteljanskii_inequality
    (hmono : ∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0))
    (X : Matrix m α ℂ) (Y : Matrix m β ℂ) (Z : Matrix m γ ℂ) :
    (Xᴴ * X).det.re * ((fromCols X (fromCols Y Z))ᴴ * fromCols X (fromCols Y Z)).det.re ≤
      ((fromCols X Y)ᴴ * fromCols X Y).det.re * ((fromCols X Z)ᴴ * fromCols X Z).det.re := by
  classical
  by_cases h : (Xᴴ * X).det = 0
  · rw [h]
    simpa using mul_nonneg (gram_det_re_nonneg_and_im_eq_zero (fromCols X Y)).1 (gram_det_re_nonneg_and_im_eq_zero (fromCols X Z)).1
  · rw [gram_det_fromCols_eq_mul_residual X _ h, gram_det_fromCols_eq_mul_residual X Y h, gram_det_fromCols_eq_mul_residual X Z h, mul_fromCols,
      re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero X).2, re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero X).2,
      re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero X).2]
    have hF := gram_det_fromCols_le_mul hmono ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * Y)
      ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * Z)
    nlinarith [mul_le_mul_of_nonneg_left hF (mul_self_nonneg (Xᴴ * X).det.re)]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in

/- English proof (translation)
Introduce `hmono m α β γ _ _ _ _ _ _ _ M`. Establish `key` using `gram_det_koteljanskii_inequality hmono (M.submatrix id Sum.inl) (M.submatrix id (Sum.inr ∘ Sum.inl)) (M.submatrix id (Sum.inr ∘ Sum.inr))`. Establish `hM : fromCols (M.submatrix id Sum.inl) (fromCols (M.submatrix id (Sum.inr ∘ Sum.inl)) (M.submatrix id (Sum.inr ∘ Sum.inr))) = M`. Apply the tactic sequence `ext x (a | b | c) <;> rfl`. Establish `hXY : fromCols (M.submatrix id Sum.inl) (M.submatrix id (Sum.inr ∘ Sum.inl)) = M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)`.

Apply the tactic sequence `ext x (a | b) <;> rfl`. Establish `hXZ : fromCols (M.submatrix id Sum.inl) (M.submatrix id (Sum.inr ∘ Sum.inr)) = M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)`. Apply the tactic sequence `ext x (a | c) <;> rfl`. Rewrite `key` using `[hM, hXY, hXZ]`. Then use the resulting hypothesis.
-/
theorem _root_.GlobalTheory.gram_det_submodular :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0)) → (∀ (m α β γ : Type) [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (M : Matrix m (α ⊕ β ⊕ γ) ℂ), (((M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))).det.re) * (((M)ᴴ * (M)).det.re) ≤ (((M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))).det.re) * (((M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))).det.re)) := by
  intro hmono m α β γ _ _ _ _ _ _ _ M
  have key := gram_det_koteljanskii_inequality hmono (M.submatrix id Sum.inl)
    (M.submatrix id (Sum.inr ∘ Sum.inl)) (M.submatrix id (Sum.inr ∘ Sum.inr))
  have hM : fromCols (M.submatrix id Sum.inl)
      (fromCols (M.submatrix id (Sum.inr ∘ Sum.inl)) (M.submatrix id (Sum.inr ∘ Sum.inr))) = M := by
    ext x (a | b | c) <;> rfl
  have hXY : fromCols (M.submatrix id Sum.inl) (M.submatrix id (Sum.inr ∘ Sum.inl)) =
      M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ) := by
    ext x (a | b) <;> rfl
  have hXZ : fromCols (M.submatrix id Sum.inl) (M.submatrix id (Sum.inr ∘ Sum.inr)) =
      M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ) := by
    ext x (a | c) <;> rfl
  rwa [hM, hXY, hXZ] at key

end GlobalTheory
