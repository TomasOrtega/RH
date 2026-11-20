import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LogSqLeTangentAddSq
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.LogSqVar

variable {ι : Type} [Fintype ι] [DecidableEq ι]

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Establish `h1` using `congrArg (fun M : Matrix ι ι ℂ => Complex.re (M i i)) h`. Simplify using `only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply_eq, Complex.one_re, Complex.re_sum] at h1`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_apply]`.

Simplify using `[Complex.mul_re]`.
-/
private lemma sum_normSq_apply_right_eq_one_of_mul_conjTranspose (W : Matrix ι ι ℂ) (h : W * Wᴴ = 1) (i : ι) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h1 := congrArg (fun M : Matrix ι ι ℂ => Complex.re (M i i)) h
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply_eq, Complex.one_re, Complex.re_sum] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_apply]
  simp [Complex.mul_re]

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Establish `h1` using `sum_normSq_apply_right_eq_one_of_mul_conjTranspose Wᴴ (by rw [conjTranspose_conjTranspose]; exact h) j`. Simplify `h1` using `[conjTranspose_apply, Complex.normSq_conj]`.
-/
private lemma sum_normSq_apply_left_eq_one_of_conjTranspose_mul (W : Matrix ι ι ℂ) (h : Wᴴ * W = 1) (j : ι) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have h1 := sum_normSq_apply_right_eq_one_of_mul_conjTranspose Wᴴ (by rw [conjTranspose_conjTranspose]; exact h) j
  simpa [conjTranspose_apply, Complex.normSq_conj] using h1

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Establish `h1 : Complex.normSq (V k j) ≤ 1`. Rewrite using `[← sum_normSq_apply_left_eq_one_of_conjTranspose_mul V hV j]`. Conclude with `Finset.single_le_sum (f := fun i => Complex.normSq (V i j)) (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ k)`. Rewrite `h1` using `[Complex.normSq_eq_norm_sq]`. Use polynomial arithmetic with `[norm_nonneg (V k j)]`.
-/
private lemma norm_apply_le_one_of_conjTranspose_mul_eq_one (V : Matrix ι ι ℂ) (hV : Vᴴ * V = 1) (k j : ι) : ‖V k j‖ ≤ 1 := by
  have h1 : Complex.normSq (V k j) ≤ 1 := by
    rw [← sum_normSq_apply_left_eq_one_of_conjTranspose_mul V hV j]
    exact Finset.single_le_sum (f := fun i => Complex.normSq (V i j))
      (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ k)
  rw [Complex.normSq_eq_norm_sq] at h1
  nlinarith [norm_nonneg (V k j)]

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Simplify using `only [Matrix.mul_apply, conjTranspose_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `(mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)).trans_eq (Finset.sum_mul _ _ _)`.

Use `_ ≤ ∑ l : ι, ∑ k : ι, δ := by`. Use `Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_star]`. Establish `h1` using `norm_apply_le_one_of_conjTranspose_mul_eq_one V hV k j`. Establish `h2` using `norm_apply_le_one_of_conjTranspose_mul_eq_one V hV l j`.

Establish `h3` using `hY k l`. Establish `h4` using `norm_nonneg (Y k l)`. Establish `h5` using `norm_nonneg (V k j)`. Establish `h6` using `norm_nonneg (V l j)`. Combine the equalities or inequalities in the displayed calculation.

Use `_ = (Fintype.card ι : ℝ) * Fintype.card ι * δ := by`. Simplify using `[Finset.sum_const, Finset.card_univ]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma norm_conj_diag_apply_le (V Y : Matrix ι ι ℂ) (hV : Vᴴ * V = 1) (δ : ℝ)
    (hY : ∀ i j, ‖Y i j‖ ≤ δ) (j : ι) :
    ‖(Vᴴ * Y * V) j j‖ ≤ (Fintype.card ι : ℝ) * Fintype.card ι * δ := by
  simp only [Matrix.mul_apply, conjTranspose_apply]
  calc ‖∑ l, (∑ k, star (V k j) * Y k l) * V l j‖
      ≤ ∑ l, ∑ k, ‖star (V k j) * Y k l‖ * ‖V l j‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)).trans_eq
          (Finset.sum_mul _ _ _)
    _ ≤ ∑ l : ι, ∑ k : ι, δ := by
        refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_star]
        have h1 := norm_apply_le_one_of_conjTranspose_mul_eq_one V hV k j
        have h2 := norm_apply_le_one_of_conjTranspose_mul_eq_one V hV l j
        have h3 := hY k l
        have h4 := norm_nonneg (Y k l)
        have h5 := norm_nonneg (V k j)
        have h6 := norm_nonneg (V l j)
        calc ‖V k j‖ * ‖Y k l‖ * ‖V l j‖ ≤ 1 * ‖Y k l‖ * 1 := by gcongr
          _ ≤ δ := by linarith
    _ = (Fintype.card ι : ℝ) * Fintype.card ι * δ := by
        simp [Finset.sum_const, Finset.card_univ]; ring

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Establish `hV' : Vᴴ * V = 1` using `mul_eq_one_comm.mp hV`. Establish `hW : (Uᴴ * V)ᴴ * (Uᴴ * V) = 1`. Rewrite using `[conjTranspose_mul, conjTranspose_conjTranspose, show Vᴴ * U * (Uᴴ * V) = Vᴴ * (U * Uᴴ) * V by simp only [Matrix.mul_assoc], hU, Matrix.mul_one, hV']`. Establish `hdiag : Vᴴ * (V * diagonal (fun j => (y j : ℂ)) * Vᴴ) * V = diagonal (fun j => (y j : ℂ))`. Rewrite using `[show Vᴴ * (V * diagonal (fun j => (y j : ℂ)) * Vᴴ) * V = (Vᴴ * V) * diagonal (fun j => (y j : ℂ)) * (Vᴴ * V) by simp only [Matrix.mul_assoc], hV', Matrix.one_mul, Matrix.mul_one]`.

Establish `hsplit : Vᴴ * (V * diagonal (fun j => (y j : ℂ)) * Vᴴ) * V = (Uᴴ * V)ᴴ * diagonal (fun i => (x i : ℂ)) * (Uᴴ * V) + Vᴴ * Y * V`. Rewrite using `[← hB, Matrix.mul_add, Matrix.add_mul, conjTranspose_mul, conjTranspose_conjTranspose]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite `hsplit` using `[hdiag]`. Establish `hj` using `congrArg (fun M : Matrix ι ι ℂ => Complex.re (M j j)) hsplit`.

Simplify using `only [diagonal_apply_eq, Complex.ofReal_re, Matrix.add_apply, Complex.add_re] at hj`. Establish `hA : Complex.re (((Uᴴ * V)ᴴ * diagonal (fun i => (x i : ℂ)) * (Uᴴ * V)) j j) = ∑ i, x i * Complex.normSq ((Uᴴ * V) i j)`. Generalize the expression as in `Uᴴ * V = W`. Establish `hd : Wᴴ * diagonal (fun i => (x i : ℂ)) = Matrix.of fun a b => Wᴴ a b * (x b : ℂ)`. Use extensionality with `a b`.

Simplify using `[Matrix.mul_diagonal]`. Rewrite using `[hd]`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, conjTranspose_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_apply]`.

Simplify using `[Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlow : m ≤ ∑ i, x i * Complex.normSq ((Uᴴ * V) i j)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.mul_sum, sum_normSq_apply_left_eq_one_of_conjTranspose_mul _ hW j, mul_one]`.

Use `_ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx i) (Complex.normSq_nonneg _)`. Establish `hsmall` using `norm_conj_diag_apply_le V Y hV' δ hY j`. Establish `hre` using `Complex.abs_re_le_norm ((Vᴴ * Y * V) j j)`. Establish `hre'` using `neg_abs_le ((Vᴴ * Y * V) j j).re`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma le_eigenvalue_of_add (U V Y : Matrix ι ι ℂ) (x y : ι → ℝ) (m δ : ℝ)
    (hU : U * Uᴴ = 1) (hV : V * Vᴴ = 1) (hx : ∀ i, m ≤ x i) (hY : ∀ i j, ‖Y i j‖ ≤ δ)
    (hB : U * diagonal (fun i => (x i : ℂ)) * Uᴴ + Y = V * diagonal (fun j => (y j : ℂ)) * Vᴴ)
    (j : ι) : m - (Fintype.card ι : ℝ) * Fintype.card ι * δ ≤ y j := by
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  have hW : (Uᴴ * V)ᴴ * (Uᴴ * V) = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose,
      show Vᴴ * U * (Uᴴ * V) = Vᴴ * (U * Uᴴ) * V by simp only [Matrix.mul_assoc], hU,
      Matrix.mul_one, hV']
  have hdiag : Vᴴ * (V * diagonal (fun j => (y j : ℂ)) * Vᴴ) * V = diagonal (fun j => (y j : ℂ)) := by
    rw [show Vᴴ * (V * diagonal (fun j => (y j : ℂ)) * Vᴴ) * V
        = (Vᴴ * V) * diagonal (fun j => (y j : ℂ)) * (Vᴴ * V) by simp only [Matrix.mul_assoc], hV',
      Matrix.one_mul, Matrix.mul_one]
  have hsplit : Vᴴ * (V * diagonal (fun j => (y j : ℂ)) * Vᴴ) * V
      = (Uᴴ * V)ᴴ * diagonal (fun i => (x i : ℂ)) * (Uᴴ * V) + Vᴴ * Y * V := by
    rw [← hB, Matrix.mul_add, Matrix.add_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [hdiag] at hsplit
  have hj := congrArg (fun M : Matrix ι ι ℂ => Complex.re (M j j)) hsplit
  simp only [diagonal_apply_eq, Complex.ofReal_re, Matrix.add_apply, Complex.add_re] at hj
  have hA : Complex.re (((Uᴴ * V)ᴴ * diagonal (fun i => (x i : ℂ)) * (Uᴴ * V)) j j)
      = ∑ i, x i * Complex.normSq ((Uᴴ * V) i j) := by
    generalize Uᴴ * V = W
    have hd : Wᴴ * diagonal (fun i => (x i : ℂ)) = Matrix.of fun a b => Wᴴ a b * (x b : ℂ) := by
      ext a b; simp [Matrix.mul_diagonal]
    rw [hd]
    simp only [Matrix.mul_apply, Matrix.of_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_apply]
    simp [Complex.mul_re]
    ring
  have hlow : m ≤ ∑ i, x i * Complex.normSq ((Uᴴ * V) i j) := by
    calc m = ∑ i, m * Complex.normSq ((Uᴴ * V) i j) := by
          rw [← Finset.mul_sum, sum_normSq_apply_left_eq_one_of_conjTranspose_mul _ hW j, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hx i) (Complex.normSq_nonneg _)
  have hsmall := norm_conj_diag_apply_le V Y hV' δ hY j
  have hre := Complex.abs_re_le_norm ((Vᴴ * Y * V) j j)
  have hre' := neg_abs_le ((Vᴴ * Y * V) j j).re
  linarith

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Establish `: U * diagonal (fun i => (a i : ℂ)) * Uᴴ * (U * diagonal (fun i => (b i : ℂ)) * Uᴴ) = U * (diagonal (fun i => (a i : ℂ)) * (Uᴴ * U) * diagonal (fun i => (b i : ℂ))) * Uᴴ`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[this, hU, Matrix.mul_one, diagonal_mul_diagonal]`. Simplify using the standard rewrite rules.
-/
private lemma conj_real_diagonal_mul_conj_real_diagonal (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (a b : ι → ℝ) :
    U * diagonal (fun i => (a i : ℂ)) * Uᴴ * (U * diagonal (fun i => (b i : ℂ)) * Uᴴ)
      = U * diagonal (fun i => ((a i * b i : ℝ) : ℂ)) * Uᴴ := by
  have : U * diagonal (fun i => (a i : ℂ)) * Uᴴ * (U * diagonal (fun i => (b i : ℂ)) * Uᴴ)
      = U * (diagonal (fun i => (a i : ℂ)) * (Uᴴ * U) * diagonal (fun i => (b i : ℂ))) * Uᴴ := by
    simp only [Matrix.mul_assoc]
  rw [this, hU, Matrix.mul_one, diagonal_mul_diagonal]
  simp

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Establish `h : U * diagonal (fun i => (a i : ℂ)) * Uᴴ * (V * diagonal (fun j => (b j : ℂ)) * Vᴴ) = U * (diagonal (fun i => (a i : ℂ)) * (Uᴴ * V) * diagonal (fun j => (b j : ℂ)) * Vᴴ)`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[h, Matrix.trace_mul_comm]`. Establish `h2 : diagonal (fun i => (a i : ℂ)) * (Uᴴ * V) * diagonal (fun j => (b j : ℂ)) * Vᴴ * U = diagonal (fun i => (a i : ℂ)) * (Uᴴ * V) * diagonal (fun j => (b j : ℂ)) * (Uᴴ * V)ᴴ`. Simplify using `[conjTranspose_mul, Matrix.mul_assoc]`.

Rewrite using `[h2]`. Generalize the expression as in `Uᴴ * V = W`. Establish `h3 : diagonal (fun i => (a i : ℂ)) * W * diagonal (fun j => (b j : ℂ)) = Matrix.of fun i j => (a i : ℂ) * W i j * b j`. Use extensionality with `i j`. Simplify using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`.

Rewrite using `[h3]`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, conjTranspose_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h4 : (W i j) * star (W i j) = (Complex.normSq (W i j) : ℂ)`. Rewrite using `[Complex.normSq_eq_conj_mul_self, mul_comm]`.

Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma re_trace_conj_diagonal_mul (U V : Matrix ι ι ℂ) (a b : ι → ℝ) :
    Complex.re (Matrix.trace (U * diagonal (fun i => (a i : ℂ)) * Uᴴ * (V * diagonal (fun j => (b j : ℂ)) * Vᴴ)))
      = ∑ i, ∑ j, a i * b j * Complex.normSq ((Uᴴ * V) i j) := by
  have h : U * diagonal (fun i => (a i : ℂ)) * Uᴴ * (V * diagonal (fun j => (b j : ℂ)) * Vᴴ)
      = U * (diagonal (fun i => (a i : ℂ)) * (Uᴴ * V) * diagonal (fun j => (b j : ℂ)) * Vᴴ) := by
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm]
  have h2 : diagonal (fun i => (a i : ℂ)) * (Uᴴ * V) * diagonal (fun j => (b j : ℂ)) * Vᴴ * U
      = diagonal (fun i => (a i : ℂ)) * (Uᴴ * V) * diagonal (fun j => (b j : ℂ)) * (Uᴴ * V)ᴴ := by
    simp [conjTranspose_mul, Matrix.mul_assoc]
  rw [h2]
  generalize Uᴴ * V = W
  have h3 : diagonal (fun i => (a i : ℂ)) * W * diagonal (fun j => (b j : ℂ))
      = Matrix.of fun i j => (a i : ℂ) * W i j * b j := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [h3]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h4 : (W i j) * star (W i j) = (Complex.normSq (W i j) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]; rfl
  calc ((a i : ℂ) * W i j * b j * star (W i j)).re
      = ((a i * b j : ℝ) * (W i j * star (W i j)) : ℂ).re := by push_cast; ring_nf
    _ = _ := by rw [h4, ← Complex.ofReal_mul, Complex.ofReal_re]

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Complex.normSq_eq_norm_sq, Complex.normSq_apply]`. Simplify using `[Complex.mul_re]`.
-/
private lemma sum_norm_sq_eq_re_trace_mul_conjTranspose (Y : Matrix ι ι ℂ) :
    ∑ i, ∑ j, ‖Y i j‖ ^ (2 : ℕ) = Complex.re (Matrix.trace (Y * Yᴴ)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.mul_re]

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Establish `h : (star fun i => (a i : ℂ)) = fun i => (a i : ℂ)` using `funext fun i => by simp`. Simplify using `[conjTranspose_mul, Matrix.mul_assoc, diagonal_conjTranspose, h]`.
-/
private lemma conjTranspose_unitary_conj_real_diagonal (U : Matrix ι ι ℂ) (a : ι → ℝ) :
    (U * diagonal (fun i => (a i : ℂ)) * Uᴴ)ᴴ = U * diagonal (fun i => (a i : ℂ)) * Uᴴ := by
  have h : (star fun i => (a i : ℂ)) = fun i => (a i : ℂ) := funext fun i => by simp
  simp [conjTranspose_mul, Matrix.mul_assoc, diagonal_conjTranspose, h]

open Matrix in
/- English proof (translation)
Introduce and unpack `⟨U, d, hU, hH, hA⟩`. Take `⟨x, hx⟩ : ∃ x : ι → ℝ, x = fun i => Real.exp (d i)` from `⟨_, rfl⟩`. Establish `hA' : A = U * diagonal (fun i => (x i : ℂ)) * Uᴴ` using `by subst hx; exact hA`. Establish `hxpos : ∀ i, 0 < x i` using `fun i => by rw [hx]; exact Real.exp_pos _`. Establish `hlogx : ∀ i, Real.log (x i) = d i` using `fun i => by rw [hx]; exact Real.log_exp _`.

Use `set m := Real.exp (-∑ i, |d i|) with hmdef`. Establish `hm : 0 < m` using `Real.exp_pos _`. Establish `hmx : ∀ i, m ≤ x i` using `fun i => by`. Rewrite using `[hx]`. Use `Real.exp_le_exp.mpr ?_` and prove the remaining obligations.

Establish `h1` using `Finset.single_le_sum (f := fun i => |d i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)`. Establish `h2` using `neg_abs_le (d i)`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨C, hC0, hg⟩` from `_root_.GlobalTheory.ClassFin.log_sq_le_tangent_add_sq (m / 2) (by positivity)`. Use `set n : ℝ := (Fintype.card ι : ℝ) with hndef`.

Establish `hn : 0 ≤ n * n` using `mul_self_nonneg n`. Use `⟨C, (m / 2) / (n * n + 1), by positivity, ?_⟩` and prove the remaining obligations. Introduce and unpack `Y H' hY ⟨V, e, hV, hH', hB⟩`. Take `⟨y, hy⟩ : ∃ y : ι → ℝ, y = fun j => Real.exp (e j)` from `⟨_, rfl⟩`. Establish `hB' : A + Y = V * diagonal (fun j => (y j : ℂ)) * Vᴴ` using `by subst hy; exact hB`.

Establish `hlogy : ∀ j, Real.log (y j) = e j` using `fun j => by rw [hy]; exact Real.log_exp _`. Establish `hU' : Uᴴ * U = 1` using `mul_eq_one_comm.mp hU`. Establish `hV' : Vᴴ * V = 1` using `mul_eq_one_comm.mp hV`. Establish `hylow : ∀ j, m / 2 ≤ y j`. Introduce `j`.

Establish `h1` using `le_eigenvalue_of_add U V Y x y m _ hU hV hmx hY (by rw [← hA']; exact hB') j`. Establish `h2 : n * n * ((m / 2) / (n * n + 1)) ≤ m / 2`. Rewrite using `[mul_div_assoc', div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite `h1` using `[← hndef]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `honeU : U * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Uᴴ = 1`. Simplify using `[hU]`. Establish `honeV : V * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Vᴴ = 1`. Simplify using `[hV]`.

Establish `T1 : Complex.re (Matrix.trace (H' * H')) = ∑ i, ∑ j, 1 * (e j * e j) * Complex.normSq ((Uᴴ * V) i j)`. Rewrite using `[hH', conj_real_diagonal_mul_conj_real_diagonal V hV' e e, show V * diagonal (fun i => ((e i * e i : ℝ) : ℂ)) * Vᴴ = U * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Uᴴ * (V * diagonal (fun i => ((e i * e i : ℝ) : ℂ)) * Vᴴ) by rw [honeU, Matrix.one_mul], re_trace_conj_diagonal_mul]`. Establish `T2 : Complex.re (Matrix.trace (H * H)) = ∑ i, ∑ j, (d i * d i) * 1 * Complex.normSq ((Uᴴ * V) i j)`. Rewrite using `[hH, conj_real_diagonal_mul_conj_real_diagonal U hU' d d, show U * diagonal (fun i => ((d i * d i : ℝ) : ℂ)) * Uᴴ = U * diagonal (fun i => ((d i * d i : ℝ) : ℂ)) * Uᴴ * (V * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Vᴴ) by rw [honeV, Matrix.mul_one], re_trace_conj_diagonal_mul]`. Establish `hAinv : A⁻¹ = U * diagonal (fun i => ((x i)⁻¹ : ℂ)) * Uᴴ`.

Establish `h : U * diagonal (fun i => ((x i)⁻¹ : ℂ)) * Uᴴ = U * diagonal (fun i => (((x i)⁻¹ : ℝ) : ℂ)) * Uᴴ` using `by simp`. Rewrite using `[h]`. Use `Matrix.inv_eq_right_inv ?_` and prove the remaining obligations. Rewrite using `[hA', conj_real_diagonal_mul_conj_real_diagonal U hU', show (fun i => ((x i * (x i)⁻¹ : ℝ) : ℂ)) = fun _ => ((1 : ℝ) : ℂ) from`. Use function extensionality and compare the values at `fun i => by rw [mul_inv_cancel₀ (hxpos i).ne'], honeU]`.

Establish `hYeq : Y = V * diagonal (fun j => (y j : ℂ)) * Vᴴ - U * diagonal (fun i => (x i : ℂ)) * Uᴴ`. Rewrite using `[← hB', hA', add_sub_cancel_left]`. Establish `hHA : H * A⁻¹ = U * diagonal (fun i => ((d i * (x i)⁻¹ : ℝ) : ℂ)) * Uᴴ`. Rewrite using `[hAinv, hH, ← conj_real_diagonal_mul_conj_real_diagonal U hU']`. Simplify using the standard rewrite rules.

Establish `T3 : Complex.re (Matrix.trace (H * A⁻¹ * Y)) = ∑ i, ∑ j, (d i * (x i)⁻¹) * y j * Complex.normSq ((Uᴴ * V) i j) - ∑ i, ∑ j, d i * 1 * Complex.normSq ((Uᴴ * V) i j)`. Rewrite using `[hHA, hYeq, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, re_trace_conj_diagonal_mul, conj_real_diagonal_mul_conj_real_diagonal U hU', show (fun i => ((d i * (x i)⁻¹ * x i : ℝ) : ℂ)) = fun i => (d i : ℂ) from`. Use function extensionality and compare the values at `fun i => by rw [inv_mul_cancel_right₀ (hxpos i).ne'],`. Use `show U * diagonal (fun i => (d i : ℂ)) * Uᴴ = U * diagonal (fun i => (d i : ℂ)) * Uᴴ * (V * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Vᴴ) by rw [honeV, Matrix.mul_one],`. Use the proof step `re_trace_conj_diagonal_mul]`.

Establish `T4 : ∑ i : ι, ∑ j : ι, ‖Y i j‖ ^ (2 : ℕ) = ∑ i, ∑ j, 1 * (y j * y j) * Complex.normSq ((Uᴴ * V) i j) - ∑ i, ∑ j, x i * y j * Complex.normSq ((Uᴴ * V) i j) - ∑ i, ∑ j, x i * y j * Complex.normSq ((Uᴴ * V) i j) + ∑ i, ∑ j, (x i * x i) * 1 * Complex.normSq ((Uᴴ * V) i j)`. Rewrite using `[sum_norm_sq_eq_re_trace_mul_conjTranspose, hYeq, conjTranspose_sub, conjTranspose_unitary_conj_real_diagonal, conjTranspose_unitary_conj_real_diagonal, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, Complex.sub_re, Complex.s …`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[T1, T2, T3, T4]`. Establish `hpt : ∀ i j, 1 * (e j * e j) * Complex.normSq ((Uᴴ * V) i j) ≤ (d i * d i) * 1 * Complex.normSq ((Uᴴ * V) i j) + 2 * ((d i * (x i)⁻¹) * y j * Complex.normSq ((Uᴴ * V) i j) - d i * 1 * Complex.normSq ((Uᴴ * V) i j)) + C * (1 * (y j * y j) * Complex.normSq ((Uᴴ * V) i j) - x i * y …`.

Introduce `i j`. Establish `hb` using `hg (x i) (y j) ((div_le_self hm.le one_le_two).trans (hmx i)) (hylow j)`. Rewrite `hb` using `[hlogx, hlogy]`. Establish `hw` using `Complex.normSq_nonneg ((Uᴴ * V) i j)`. Establish `hxne` using `(hxpos i).ne'`.

Establish `key : (d i * d i) * 1 * Complex.normSq ((Uᴴ * V) i j) + 2 * ((d i * (x i)⁻¹) * y j * Complex.normSq ((Uᴴ * V) i j) - d i * 1 * Complex.normSq ((Uᴴ * V) i j)) + C * (1 * (y j * y j) * Complex.normSq ((Uᴴ * V) i j) - x i * y j * Complex.normSq ((Uᴴ * V) i j) - x i * y j * Complex.n …`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use polynomial arithmetic with `[mul_nonneg hw (sub_nonneg.mpr hb)]`. Simplify using `only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j`.
-/
theorem _root_.GlobalTheory.ClassFin.LogSqVar.first_variation (ι : Type) [Fintype ι] [DecidableEq ι]
    (H A : Matrix ι ι ℂ) :
    _root_.GlobalTheory.ClassFin.IsLog H A →
      ∃ (C : ℝ) (δ : ℝ), (0 : ℝ) < δ ∧
        ∀ (Y H' : Matrix ι ι ℂ), (∀ (i j : ι), ‖Y i j‖ ≤ δ) →
          _root_.GlobalTheory.ClassFin.IsLog H' (A + Y) →
            Complex.re (Matrix.trace (H' * H')) ≤
              Complex.re (Matrix.trace (H * H)) + (2 : ℝ) * Complex.re (Matrix.trace (H * A⁻¹ * Y)) +
                C * ∑ i : ι, ∑ j : ι, ‖Y i j‖ ^ (2 : ℕ) := by
  rintro ⟨U, d, hU, hH, hA⟩
  obtain ⟨x, hx⟩ : ∃ x : ι → ℝ, x = fun i => Real.exp (d i) := ⟨_, rfl⟩
  have hA' : A = U * diagonal (fun i => (x i : ℂ)) * Uᴴ := by subst hx; exact hA
  have hxpos : ∀ i, 0 < x i := fun i => by rw [hx]; exact Real.exp_pos _
  have hlogx : ∀ i, Real.log (x i) = d i := fun i => by rw [hx]; exact Real.log_exp _
  set m := Real.exp (-∑ i, |d i|) with hmdef
  have hm : 0 < m := Real.exp_pos _
  have hmx : ∀ i, m ≤ x i := fun i => by
    rw [hx]
    refine Real.exp_le_exp.mpr ?_
    have h1 := Finset.single_le_sum (f := fun i => |d i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
    have h2 := neg_abs_le (d i)
    linarith
  obtain ⟨C, hC0, hg⟩ := _root_.GlobalTheory.ClassFin.log_sq_le_tangent_add_sq (m / 2) (by positivity)
  set n : ℝ := (Fintype.card ι : ℝ) with hndef
  have hn : 0 ≤ n * n := mul_self_nonneg n
  refine ⟨C, (m / 2) / (n * n + 1), by positivity, ?_⟩
  rintro Y H' hY ⟨V, e, hV, hH', hB⟩
  obtain ⟨y, hy⟩ : ∃ y : ι → ℝ, y = fun j => Real.exp (e j) := ⟨_, rfl⟩
  have hB' : A + Y = V * diagonal (fun j => (y j : ℂ)) * Vᴴ := by subst hy; exact hB
  have hlogy : ∀ j, Real.log (y j) = e j := fun j => by rw [hy]; exact Real.log_exp _
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  have hylow : ∀ j, m / 2 ≤ y j := by
    intro j
    have h1 := le_eigenvalue_of_add U V Y x y m _ hU hV hmx hY (by rw [← hA']; exact hB') j
    have h2 : n * n * ((m / 2) / (n * n + 1)) ≤ m / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    rw [← hndef] at h1
    linarith
  have honeU : U * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Uᴴ = 1 := by
    simp [hU]
  have honeV : V * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Vᴴ = 1 := by
    simp [hV]

  have T1 : Complex.re (Matrix.trace (H' * H'))
      = ∑ i, ∑ j, 1 * (e j * e j) * Complex.normSq ((Uᴴ * V) i j) := by
    rw [hH', conj_real_diagonal_mul_conj_real_diagonal V hV' e e,
      show V * diagonal (fun i => ((e i * e i : ℝ) : ℂ)) * Vᴴ
        = U * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Uᴴ
          * (V * diagonal (fun i => ((e i * e i : ℝ) : ℂ)) * Vᴴ) by rw [honeU, Matrix.one_mul],
      re_trace_conj_diagonal_mul]
  have T2 : Complex.re (Matrix.trace (H * H))
      = ∑ i, ∑ j, (d i * d i) * 1 * Complex.normSq ((Uᴴ * V) i j) := by
    rw [hH, conj_real_diagonal_mul_conj_real_diagonal U hU' d d,
      show U * diagonal (fun i => ((d i * d i : ℝ) : ℂ)) * Uᴴ
        = U * diagonal (fun i => ((d i * d i : ℝ) : ℂ)) * Uᴴ
          * (V * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Vᴴ) by rw [honeV, Matrix.mul_one],
      re_trace_conj_diagonal_mul]
  have hAinv : A⁻¹ = U * diagonal (fun i => ((x i)⁻¹ : ℂ)) * Uᴴ := by
    have h : U * diagonal (fun i => ((x i)⁻¹ : ℂ)) * Uᴴ
        = U * diagonal (fun i => (((x i)⁻¹ : ℝ) : ℂ)) * Uᴴ := by simp
    rw [h]
    refine Matrix.inv_eq_right_inv ?_
    rw [hA', conj_real_diagonal_mul_conj_real_diagonal U hU',
      show (fun i => ((x i * (x i)⁻¹ : ℝ) : ℂ)) = fun _ => ((1 : ℝ) : ℂ) from
        funext fun i => by rw [mul_inv_cancel₀ (hxpos i).ne'], honeU]
  have hYeq : Y = V * diagonal (fun j => (y j : ℂ)) * Vᴴ - U * diagonal (fun i => (x i : ℂ)) * Uᴴ := by
    rw [← hB', hA', add_sub_cancel_left]
  have hHA : H * A⁻¹ = U * diagonal (fun i => ((d i * (x i)⁻¹ : ℝ) : ℂ)) * Uᴴ := by
    rw [hAinv, hH, ← conj_real_diagonal_mul_conj_real_diagonal U hU']
    simp
  have T3 : Complex.re (Matrix.trace (H * A⁻¹ * Y))
      = ∑ i, ∑ j, (d i * (x i)⁻¹) * y j * Complex.normSq ((Uᴴ * V) i j)
        - ∑ i, ∑ j, d i * 1 * Complex.normSq ((Uᴴ * V) i j) := by
    rw [hHA, hYeq, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, re_trace_conj_diagonal_mul,
      conj_real_diagonal_mul_conj_real_diagonal U hU',
      show (fun i => ((d i * (x i)⁻¹ * x i : ℝ) : ℂ)) = fun i => (d i : ℂ) from
        funext fun i => by rw [inv_mul_cancel_right₀ (hxpos i).ne'],
      show U * diagonal (fun i => (d i : ℂ)) * Uᴴ
        = U * diagonal (fun i => (d i : ℂ)) * Uᴴ
          * (V * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Vᴴ) by rw [honeV, Matrix.mul_one],
      re_trace_conj_diagonal_mul]
  have T4 : ∑ i : ι, ∑ j : ι, ‖Y i j‖ ^ (2 : ℕ)
      = ∑ i, ∑ j, 1 * (y j * y j) * Complex.normSq ((Uᴴ * V) i j)
        - ∑ i, ∑ j, x i * y j * Complex.normSq ((Uᴴ * V) i j)
        - ∑ i, ∑ j, x i * y j * Complex.normSq ((Uᴴ * V) i j)
        + ∑ i, ∑ j, (x i * x i) * 1 * Complex.normSq ((Uᴴ * V) i j) := by
    rw [sum_norm_sq_eq_re_trace_mul_conjTranspose, hYeq, conjTranspose_sub, conjTranspose_unitary_conj_real_diagonal,
      conjTranspose_unitary_conj_real_diagonal, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, Complex.sub_re, Complex.sub_re,
      Complex.sub_re, Matrix.trace_mul_comm (V * _ * Vᴴ) (U * _ * Uᴴ),
      conj_real_diagonal_mul_conj_real_diagonal V hV' y y, conj_real_diagonal_mul_conj_real_diagonal U hU' x x,
      show V * diagonal (fun i => ((y i * y i : ℝ) : ℂ)) * Vᴴ
        = U * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Uᴴ
          * (V * diagonal (fun i => ((y i * y i : ℝ) : ℂ)) * Vᴴ) by rw [honeU, Matrix.one_mul],
      show U * diagonal (fun i => ((x i * x i : ℝ) : ℂ)) * Uᴴ
        = U * diagonal (fun i => ((x i * x i : ℝ) : ℂ)) * Uᴴ
          * (V * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Vᴴ) by rw [honeV, Matrix.mul_one],
      re_trace_conj_diagonal_mul, re_trace_conj_diagonal_mul, re_trace_conj_diagonal_mul]
    ring
  rw [T1, T2, T3, T4]
  have hpt : ∀ i j, 1 * (e j * e j) * Complex.normSq ((Uᴴ * V) i j)
      ≤ (d i * d i) * 1 * Complex.normSq ((Uᴴ * V) i j)
        + 2 * ((d i * (x i)⁻¹) * y j * Complex.normSq ((Uᴴ * V) i j)
          - d i * 1 * Complex.normSq ((Uᴴ * V) i j))
        + C * (1 * (y j * y j) * Complex.normSq ((Uᴴ * V) i j)
          - x i * y j * Complex.normSq ((Uᴴ * V) i j)
          - x i * y j * Complex.normSq ((Uᴴ * V) i j)
          + (x i * x i) * 1 * Complex.normSq ((Uᴴ * V) i j)) := by
    intro i j
    have hb := hg (x i) (y j) ((div_le_self hm.le one_le_two).trans (hmx i)) (hylow j)
    rw [hlogx, hlogy] at hb
    have hw := Complex.normSq_nonneg ((Uᴴ * V) i j)
    have hxne := (hxpos i).ne'
    have key : (d i * d i) * 1 * Complex.normSq ((Uᴴ * V) i j)
        + 2 * ((d i * (x i)⁻¹) * y j * Complex.normSq ((Uᴴ * V) i j)
          - d i * 1 * Complex.normSq ((Uᴴ * V) i j))
        + C * (1 * (y j * y j) * Complex.normSq ((Uᴴ * V) i j)
          - x i * y j * Complex.normSq ((Uᴴ * V) i j)
          - x i * y j * Complex.normSq ((Uᴴ * V) i j)
          + (x i * x i) * 1 * Complex.normSq ((Uᴴ * V) i j))
        - 1 * (e j * e j) * Complex.normSq ((Uᴴ * V) i j)
        = Complex.normSq ((Uᴴ * V) i j)
          * (d i ^ 2 + 2 * d i / x i * (y j - x i) + C * (y j - x i) ^ 2 - e j ^ 2) := by
      field_simp
      ring
    nlinarith [mul_nonneg hw (sub_nonneg.mpr hb)]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j

end GlobalTheory.ClassFin.LogSqVar
