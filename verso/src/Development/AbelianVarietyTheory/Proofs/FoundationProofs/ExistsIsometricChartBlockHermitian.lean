import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc

noncomputable section
namespace GlobalTheory.CartanInt.HermChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

def herm {n : Type} (S : n → n → ℝ) : Matrix n n ℂ :=
  Matrix.of fun i j => (⟨(S i j + S j i) / 2, (S i j - S j i) / 2⟩ : ℂ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem herm_apply {n : Type} (S : n → n → ℝ) (i j : n) :
    herm S i j = (⟨(S i j + S j i) / 2, (S i j - S j i) / 2⟩ : ℂ) := rfl

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.conjTranspose_apply, herm_apply, herm_apply]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `only [Complex.star_def, Complex.conj_re]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Complex.star_def, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_conjTranspose {n : Type} (S : n → n → ℝ) : (herm S)ᴴ = herm S := by
  ext i j
  rw [Matrix.conjTranspose_apply, herm_apply, herm_apply]
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]; ring
  · simp only [Complex.star_def, Complex.conj_im]; ring

/- English proof (translation)
Establish `e : (fun x => herm (f x) i j) = fun x => (((f x i j + f x j i) / 2 : ℝ) : ℂ) + (((f x i j - f x j i) / 2 : ℝ) : ℂ) * Complex.I`. Use function extensionality and compare the values at `x`. Rewrite using `[herm_apply, Complex.mk_eq_add_mul_I]`. Rewrite using `[e]`. Establish `h1` using `hf i j`.

Establish `h2` using `hf j i`. Use `fun_prop`.
-/
theorem continuous_herm_entry {X n : Type} [TopologicalSpace X] {f : X → n → n → ℝ}
    (hf : ∀ i j, Continuous fun x => f x i j) (i j : n) : Continuous fun x => herm (f x) i j := by
  have e : (fun x => herm (f x) i j) = fun x => (((f x i j + f x j i) / 2 : ℝ) : ℂ) +
      (((f x i j - f x j i) / 2 : ℝ) : ℂ) * Complex.I := by
    funext x
    rw [herm_apply, Complex.mk_eq_add_mul_I]
  rw [e]
  have h1 := hf i j
  have h2 := hf j i
  fun_prop

/- English proof (translation)
Establish `h : ∀ i j, ‖herm S i j - herm T i j‖ ^ 2 = (S i j - T i j) ^ 2 / 2 + (S j i - T j i) ^ 2 / 2`. Introduce `i j`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply, herm_apply, herm_apply]`. Simplify using `only [Complex.sub_re, Complex.sub_im]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [h, Finset.sum_add_distrib]`. Rewrite using `[Finset.sum_comm (f := fun i j => (S j i - T j i) ^ 2 / 2), ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem sum_norm_sq_herm_sub {n : Type} [Fintype n] (S T : n → n → ℝ) :
    ∑ i, ∑ j, ‖herm S i j - herm T i j‖ ^ 2 = ∑ i, ∑ j, (S i j - T i j) ^ 2 := by
  have h : ∀ i j, ‖herm S i j - herm T i j‖ ^ 2 =
      (S i j - T i j) ^ 2 / 2 + (S j i - T j i) ^ 2 / 2 := by
    intro i j
    rw [Complex.sq_norm, Complex.normSq_apply, herm_apply, herm_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  simp only [h, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => (S j i - T j i) ^ 2 / 2), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `h1` using `congrArg Complex.re (hH i j)`. Establish `h2` using `congrArg Complex.im (hH i j)`. Simplify using `only [Complex.star_def, Complex.conj_re, Complex.conj_im] at h1 h2`. Rewrite using `[herm_apply]`. Apply `Complex.ext` to reduce the goal to its premises.

Use `show _ / (2 : ℝ) = _`. Combine the linear equalities and inequalities to obtain the conclusion. Use `show _ / (2 : ℝ) = _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem herm_re_add_im {n : Type} (H : n → n → ℂ) (hH : ∀ i j, star (H j i) = H i j) (i j : n) :
    herm (fun i j => (H i j).re + (H i j).im) i j = H i j := by
  have h1 := congrArg Complex.re (hH i j)
  have h2 := congrArg Complex.im (hH i j)
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at h1 h2
  rw [herm_apply]
  apply Complex.ext
  · show _ / (2 : ℝ) = _
    linarith
  · show _ / (2 : ℝ) = _
    linarith

/- English proof (translation)
Establish `h1 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im` using `by rw [Complex.sq_norm, Complex.normSq_apply]`. Establish `h2 : ‖z‖ ≤ 3.1416` using `hz.trans Real.pi_lt_d4.le`. Establish `h3 : ‖z‖ ^ 2 ≤ 3.1416 ^ 2` using `pow_le_pow_left₀ (norm_nonneg z) h2 2`. Use `abs_le_of_sq_le_sq' ?_ (by norm_num) |> abs_le.2` and prove the remaining obligations. Use polynomial arithmetic with `[sq_nonneg (z.re - z.im)]`.
-/
theorem abs_re_add_im_le {z : ℂ} (hz : ‖z‖ ≤ Real.pi) : |z.re + z.im| ≤ 89 / 20 := by
  have h1 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by rw [Complex.sq_norm, Complex.normSq_apply]
  have h2 : ‖z‖ ≤ 3.1416 := hz.trans Real.pi_lt_d4.le
  have h3 : ‖z‖ ^ 2 ≤ 3.1416 ^ 2 := pow_le_pow_left₀ (norm_nonneg z) h2 2
  refine abs_le_of_sq_le_sq' ?_ (by norm_num) |> abs_le.2
  nlinarith [sq_nonneg (z.re - z.im)]

/- English proof (translation)
Introduce `p q`. Use `⟨fun R => Matrix.fromBlocks (herm fun i j => R (Sum.inl (i, j))) 0 0 (herm fun i j => R (Sum.inr (i, j))), ?_, fun R => ⟨?_, isKC_fromBlocks _ _⟩, fun R R' => ?_, fun H hH hK hb => ?_⟩` and prove the remaining obligations. Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Apply the tactic sequence `exact continuous_herm_entry (f := fun (R : (Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) i j => R (Sum.inl (i, j))) (fun i j => continuous_apply _) a b`.

Conclude with `continuous_const`. Conclude with `continuous_const`. Apply the tactic sequence `exact continuous_herm_entry (f := fun (R : (Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) i j => R (Sum.inr (i, j))) (fun i j => continuous_apply _) a b`. Simplify using `only [Matrix.fromBlocks_conjTranspose, herm_conjTranspose, Matrix.conjTranspose_zero]`. Rewrite using `[Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type, ← sum_norm_sq_herm_sub (fun i j => R (Sum.inl (i, j))) (fun i j => R' (Sum.inl (i, j))), ← sum_norm_sq_herm_sub (fun i j => R (Sum.inr (i, j))) (fun i j => R' (Sum.inr (i, j)))]`.

Simplify using `[Fintype.sum_sum_type]`. Establish `hs : ∀ a b, star (H b a) = H a b` using `fun a b => by`. Rewrite using `[← Matrix.conjTranspose_apply, hH]`. Use `⟨Sum.elim (fun x => (H (Sum.inl x.1) (Sum.inl x.2)).re + (H (Sum.inl x.1) (Sum.inl x.2)).im) (fun x => (H (Sum.inr x.1) (Sum.inr x.2)).re + (H (Sum.inr x.1) (Sum.inr x.2)).im), ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`.

Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Conclude with `herm_re_add_im (fun i j => H (Sum.inl i) (Sum.inl j)) (fun i j => hs _ _) a b`. Conclude with `(hK _ _ (by simp [sameBlock])).symm`. Conclude with `(hK _ _ (by simp [sameBlock])).symm`. Conclude with `herm_re_add_im (fun i j => H (Sum.inr i) (Sum.inr j)) (fun i j => hs _ _) a b`.

Introduce and unpack `(x | x)`. Conclude with `abs_re_add_im_le (hb _ _)`. Conclude with `abs_re_add_im_le (hb _ _)`.
-/
theorem exists_chart : ∀ (p q : ℕ), ∃ Φ : ((Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) → Mat p q,
    Continuous Φ ∧ (∀ R, (Φ R)ᴴ = Φ R ∧ IsKC (Φ R)) ∧
    (∀ R R', ∑ a, ∑ b, ‖(Φ R - Φ R') a b‖ ^ 2 = ∑ i, (R i - R' i) ^ 2) ∧
    ∀ H : Mat p q, Hᴴ = H → IsKC H → (∀ a b, ‖H a b‖ ≤ Real.pi) →
      ∃ R, Φ R = H ∧ ∀ i, |R i| ≤ 89 / 20 := by
  intro p q
  refine ⟨fun R => Matrix.fromBlocks (herm fun i j => R (Sum.inl (i, j))) 0 0
    (herm fun i j => R (Sum.inr (i, j))), ?_, fun R => ⟨?_, isKC_fromBlocks _ _⟩, fun R R' => ?_,
    fun H hH hK hb => ?_⟩
  · refine continuous_matrix fun a b => ?_
    rcases a with a | a <;> rcases b with b | b
    · exact continuous_herm_entry (f := fun (R : (Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) i j =>
        R (Sum.inl (i, j))) (fun i j => continuous_apply _) a b
    · exact continuous_const
    · exact continuous_const
    · exact continuous_herm_entry (f := fun (R : (Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) i j =>
        R (Sum.inr (i, j))) (fun i j => continuous_apply _) a b
  · simp only [Matrix.fromBlocks_conjTranspose, herm_conjTranspose, Matrix.conjTranspose_zero]
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type,
      ← sum_norm_sq_herm_sub (fun i j => R (Sum.inl (i, j))) (fun i j => R' (Sum.inl (i, j))),
      ← sum_norm_sq_herm_sub (fun i j => R (Sum.inr (i, j))) (fun i j => R' (Sum.inr (i, j)))]
    simp [Fintype.sum_sum_type]
  · have hs : ∀ a b, star (H b a) = H a b := fun a b => by
      rw [← Matrix.conjTranspose_apply, hH]
    refine ⟨Sum.elim (fun x => (H (Sum.inl x.1) (Sum.inl x.2)).re + (H (Sum.inl x.1) (Sum.inl x.2)).im)
      (fun x => (H (Sum.inr x.1) (Sum.inr x.2)).re + (H (Sum.inr x.1) (Sum.inr x.2)).im), ?_, ?_⟩
    · ext a b
      rcases a with a | a <;> rcases b with b | b
      · exact herm_re_add_im (fun i j => H (Sum.inl i) (Sum.inl j)) (fun i j => hs _ _) a b
      · exact (hK _ _ (by simp [sameBlock])).symm
      · exact (hK _ _ (by simp [sameBlock])).symm
      · exact herm_re_add_im (fun i j => H (Sum.inr i) (Sum.inr j)) (fun i j => hs _ _) a b
    · rintro (x | x)
      · exact abs_re_add_im_le (hb _ _)
      · exact abs_re_add_im_le (hb _ _)

end GlobalTheory.CartanInt.HermChart
