import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColDerApply

noncomputable section

open MvPolynomial

namespace GlobalTheory.ColLie

open GlobalTheory.MinorFrame

variable {ι : Type} [DecidableEq ι]

/- English proof (translation)
Use `open scoped Matrix.Norms.Operator in`. Establish `h2` using `((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0 (hasDerivAt_exp_smul_const (𝕂 := ℝ) S 0)`. Rewrite `h2` using `[zero_smul, NormedSpace.exp_zero, one_mul]`. Simplify using `only [Complex.coe_smul]`. Conclude with `h2`.
-/
theorem hasDerivAt_exp_ofReal_smul_entry {a : ℕ} (S : Matrix (Fin a) (Fin a) ℂ) (i j : Fin a) :
    HasDerivAt (fun h : ℝ => NormedSpace.exp ((h : ℂ) • S) i j) (S i j) 0 := by
  open scoped Matrix.Norms.Operator in
  have h2 := ((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) S 0)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  simp only [Complex.coe_smul]
  exact h2

/- English proof (translation)
Simplify using `only [colDer_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[pderiv_mul]`. Simplify using `only [smul_eq_C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem colDer_mul_X {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (R : Pol ι d a) (v : Var ι d a) :
    colDer τ S (R * X v) = colDer τ S R * X v + R * colDer τ S (X v) := by
  simp only [colDer_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [pderiv_mul]
  simp only [smul_eq_C_mul]
  ring

/- English proof (translation)
Simplify using `only [coeff_mul_X']`. Use `split_ifs`. Conclude with `hA _`. Conclude with `hasDerivAt_const _ _`.
-/
theorem hasDerivAt_coeff_mul_X {σ : Type} {A : ℝ → MvPolynomial σ ℂ} {B : MvPolynomial σ ℂ}
    (hA : ∀ m, HasDerivAt (fun h => coeff m (A h)) (coeff m B) 0) (w : σ) (m : σ →₀ ℕ) :
    HasDerivAt (fun h => coeff m (A h * X w)) (coeff m (B * X w)) 0 := by
  classical
  simp only [coeff_mul_X']
  split_ifs
  · exact hA _
  · exact hasDerivAt_const _ _

/- English proof (translation)
Establish `hone : ∀ P : Pol ι d a, colSub (g 0) P = P`. Establish `: (colSub (g 0) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `y`. Rewrite using `[h0]`.

Simplify using `only [colSub, aeval_X, Pi.one_apply, AlgHom.id_apply]`. Rewrite using `[Finset.sum_eq_single y.2.2]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Matrix.one_apply_ne hj]`.

Simplify using the standard rewrite rules. Introduce `P`. Rewrite using `[this, AlgHom.id_apply]`. Proceed by induction on `R using MvPolynomial.induction_on generalizing m with`. Consider the case `C c`.

Establish `h1 : colDer τ S (C c : Pol ι d a) = 0` using `by simp [colDer_apply]`. Simplify using `only [h1, algHom_C, coeff_zero]`. Conclude with `hasDerivAt_const _ _`. Consider the case `add P Q hP hQ`. Simplify using `only [map_add, coeff_add]`.

Conclude with `(hP m).add (hQ m)`. Consider the case `mul_X P v hP`. Establish `e1 : ∀ h, coeff m (colSub (g h) (P * X v)) = ∑ k, g h v.1 k v.2.2 * coeff m (colSub (g h) P * X (v.1, v.2.1, k))`. Introduce `h`. Rewrite using `[map_mul]`.

Use `conv_lhs => rw [show colSub (g h) (X v : Pol ι d a) = ∑ k, C (g h v.1 k v.2.2) * X (v.1, v.2.1, k) by`. Simplify using `[colSub]]`. Rewrite using `[Finset.mul_sum, coeff_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, coeff_C_mul]`.

Simplify using `only [e1]`. Establish `hd` using `HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hg v.1 k v.2.2).fun_mul (hasDerivAt_coeff_mul_X hP (v.1, v.2.1, k) m)`. Use `hd.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[colDer_mul_X, coeff_add, Finset.sum_add_distrib, add_comm]`. Use `congr 1`.

Rewrite using `[h0, Finset.sum_eq_single v.2.2]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Matrix.one_apply_ne hj]`. Simplify using the standard rewrite rules.

Rewrite using `[colDer_X, hone]`. Distinguish the cases in `hv : v.1 = τ`. Substitute `hv` using the available equality. Simplify using `only [if_true, Finset.mul_sum, coeff_sum, mul_smul_comm, coeff_smul, smul_eq_mul]`. Simplify using `[hv]`.
-/
theorem hasDerivAt_coeff_colSub_of_curve [Fintype ι] {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ)
    (g : ℝ → ι → Matrix (Fin a) (Fin a) ℂ) (h0 : g 0 = 1)
    (hg : ∀ σ i j, HasDerivAt (fun h => g h σ i j) (if σ = τ then S i j else 0) 0)
    (R : Pol ι d a) (m : Var ι d a →₀ ℕ) :
    HasDerivAt (fun h : ℝ => coeff m (colSub (g h) R)) (coeff m (colDer τ S R)) 0 := by
  have hone : ∀ P : Pol ι d a, colSub (g 0) P = P := by
    have : (colSub (g 0) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _ := by
      apply MvPolynomial.algHom_ext
      intro y
      rw [h0]
      simp only [colSub, aeval_X, Pi.one_apply, AlgHom.id_apply]
      rw [Finset.sum_eq_single y.2.2]
      · simp
      · intro j _ hj
        simp [Matrix.one_apply_ne hj]
      · simp
    intro P
    rw [this, AlgHom.id_apply]
  induction R using MvPolynomial.induction_on generalizing m with
  | C c =>
    have h1 : colDer τ S (C c : Pol ι d a) = 0 := by simp [colDer_apply]
    simp only [h1, algHom_C, coeff_zero]
    exact hasDerivAt_const _ _
  | add P Q hP hQ =>
    simp only [map_add, coeff_add]
    exact (hP m).add (hQ m)
  | mul_X P v hP =>
    have e1 : ∀ h, coeff m (colSub (g h) (P * X v)) =
        ∑ k, g h v.1 k v.2.2 * coeff m (colSub (g h) P * X (v.1, v.2.1, k)) := by
      intro h
      rw [map_mul]
      conv_lhs => rw [show colSub (g h) (X v : Pol ι d a) = ∑ k, C (g h v.1 k v.2.2) * X (v.1, v.2.1, k) by
        simp [colSub]]
      rw [Finset.mul_sum, coeff_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_left_comm, coeff_C_mul]
    simp only [e1]
    have hd := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hg v.1 k v.2.2).fun_mul (hasDerivAt_coeff_mul_X hP (v.1, v.2.1, k) m)
    refine hd.congr_deriv ?_
    rw [colDer_mul_X, coeff_add, Finset.sum_add_distrib, add_comm]
    congr 1
    · rw [h0, Finset.sum_eq_single v.2.2]
      · simp
      · intro j _ hj
        simp [Matrix.one_apply_ne hj]
      · simp
    · rw [colDer_X, hone]
      by_cases hv : v.1 = τ
      · subst hv
        simp only [if_true, Finset.mul_sum, coeff_sum, mul_smul_comm, coeff_smul, smul_eq_mul]
      · simp [hv]

/- English proof (translation)
Use `hasDerivAt_coeff_colSub_of_curve τ S (fun h => atPl τ (NormedSpace.exp ((h : ℂ) • S))) ?_ ?_ R m` and prove the remaining obligations. Simplify using `only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, atPl]`. Conclude with `Function.update_eq_self τ 1`. Introduce `σ i j`. Distinguish the cases in `h : σ = τ`.

Substitute `h` using the available equality. Simplify using `only [atPl, Function.update_self, if_true]`. Apply the tactic sequence `exact hasDerivAt_exp_ofReal_smul_entry S i j`. Simplify using `only [atPl, Function.update_of_ne h, if_neg h]`. Conclude with `hasDerivAt_const _ _`.
-/
theorem hasDerivAt_coeff_colSub_exp {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι)
    (S : Matrix (Fin a) (Fin a) ℂ) (R : Pol ι d a) (m : Var ι d a →₀ ℕ) :
    HasDerivAt (fun h : ℝ => coeff m (colSub (atPl τ (NormedSpace.exp ((h : ℂ) • S))) R))
      (coeff m (colDer τ S R)) 0 := by
  refine hasDerivAt_coeff_colSub_of_curve τ S (fun h => atPl τ (NormedSpace.exp ((h : ℂ) • S))) ?_ ?_ R m
  · simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, atPl]
    exact Function.update_eq_self τ 1
  · intro σ i j
    by_cases h : σ = τ
    · subst h
      simp only [atPl, Function.update_self, if_true]
      exact hasDerivAt_exp_ofReal_smul_entry S i j
    · simp only [atPl, Function.update_of_ne h, if_neg h]
      exact hasDerivAt_const _ _

end GlobalTheory.ColLie

end
