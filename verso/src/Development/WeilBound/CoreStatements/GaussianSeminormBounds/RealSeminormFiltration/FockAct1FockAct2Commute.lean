import Mathlib
import Formalism.PeriodIntegrals.JointBlockShapes.JointShape

noncomputable section

open MvPolynomial FockH1Action

namespace PositivityTheory.KReal

section Abstract

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Ring E] [Algebra ℂ E]

def quadT (R L : ι → E) (A : Matrix ι ι ℂ) : E := ∑ i, ∑ j, A i j • (R i * L j)

def quartT (R L : ι → E) (A B : Matrix ι ι ℂ) : E :=
  ∑ i, ∑ j, ∑ k, ∑ l, (A i j * B k l) • (R i * R k * (L j * L l))

/- English proof (translation)
Unfold `quartT`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Fintype.sum_prod_type]`. Use `_ = ∑ y : ι × ι, ∑ x : ι × ι, (B y.1 y.2 * A x.1 x.2) • (R y.1 * R x.1 * (L y.2 * L x.2)) := by`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm (A x.1 x.2), hR x.1, hL x.2]`. Use `_ = _ := by simp only [Fintype.sum_prod_type]`.
-/
theorem quartT_comm (R L : ι → E) (hR : ∀ a b, R a * R b = R b * R a)
    (hL : ∀ a b, L a * L b = L b * L a) (A B : Matrix ι ι ℂ) :
    quartT R L A B = quartT R L B A := by
  unfold quartT
  calc ∑ i, ∑ j, ∑ k, ∑ l, (A i j * B k l) • (R i * R k * (L j * L l))
      = ∑ x : ι × ι, ∑ y : ι × ι,
          (A x.1 x.2 * B y.1 y.2) • (R x.1 * R y.1 * (L x.2 * L y.2)) := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ y : ι × ι, ∑ x : ι × ι,
          (B y.1 y.2 * A x.1 x.2) • (R y.1 * R x.1 * (L y.2 * L x.2)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
        rw [mul_comm (A x.1 x.2), hR x.1, hL x.2]
    _ = _ := by simp only [Fintype.sum_prod_type]

/- English proof (translation)
Establish `key : ∀ i j k l, (A i j • (R i * L j)) * (B k l • (R k * L l)) = (A i j * B k l) • (R i * R k * (L j * L l)) + if j = k then (A i j * B k l) • (R i * L l) else 0`. Introduce `i j k l`. Establish `h1 : R i * L j * (R k * L l) = R i * (L j * R k) * L l` using `by simp only [mul_assoc]`. Rewrite using `[smul_mul_smul_comm, h1, hLR]`. Use `split_ifs with h`.

Simplify using `only [mul_add, add_mul, mul_one, smul_add, mul_assoc]`. Simplify using `only [add_zero, mul_assoc]`. Establish `h2 : quadT R L (A * B) = ∑ i, ∑ j, ∑ k, ∑ l, if j = k then (A i j * B k l) • (R i * L l) else 0`. Unfold `quadT`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Rewrite using `[h2]`. Unfold `quadT quartT`. Rewrite using `[Finset.sum_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun l _ => key i j k l`.
-/
theorem quadT_mul (R L : ι → E)
    (hLR : ∀ a b, L a * R b = R b * L a + if a = b then 1 else 0) (A B : Matrix ι ι ℂ) :
    quadT R L A * quadT R L B = quartT R L A B + quadT R L (A * B) := by
  have key : ∀ i j k l, (A i j • (R i * L j)) * (B k l • (R k * L l)) =
      (A i j * B k l) • (R i * R k * (L j * L l)) +
        if j = k then (A i j * B k l) • (R i * L l) else 0 := by
    intro i j k l
    have h1 : R i * L j * (R k * L l) = R i * (L j * R k) * L l := by simp only [mul_assoc]
    rw [smul_mul_smul_comm, h1, hLR]
    split_ifs with h
    · simp only [mul_add, add_mul, mul_one, smul_add, mul_assoc]
    · simp only [add_zero, mul_assoc]
  have h2 : quadT R L (A * B) =
      ∑ i, ∑ j, ∑ k, ∑ l, if j = k then (A i j * B k l) • (R i * L l) else 0 := by
    unfold quadT
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp
  rw [h2]
  unfold quadT quartT
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => key i j k l

/- English proof (translation)
Rewrite using `[quadT_mul R L hLR, quadT_mul R L hLR, h, quartT_comm R L hR hL]`.
-/
theorem quadT_commute (R L : ι → E) (hR : ∀ a b, R a * R b = R b * R a)
    (hL : ∀ a b, L a * L b = L b * L a)
    (hLR : ∀ a b, L a * R b = R b * L a + if a = b then 1 else 0) (A B : Matrix ι ι ℂ)
    (h : A * B = B * A) : quadT R L A * quadT R L B = quadT R L B * quadT R L A := by
  rw [quadT_mul R L hLR, quadT_mul R L hLR, h, quartT_comm R L hR hL]

end Abstract

section Fock

variable {σ : Type*} [DecidableEq σ]

/- English proof (translation)
Use `LinearMap.ext fun P => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pderiv a (pderiv b P) = pderiv b (pderiv a P)`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C c => simp`. Consider the case `add P Q hP hQ => simp [hP, hQ]`.

Consider the case `mul_X P n hP`. Simplify using `only [Derivation.leibniz, smul_eq_mul, map_add, hP, pderiv_X, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp <;> ring`.
-/
theorem pd_pd (a b : σ) :
    ((pderiv a).toLinearMap * (pderiv b).toLinearMap : Module.End ℂ (MvPolynomial σ ℂ)) =
      (pderiv b).toLinearMap * (pderiv a).toLinearMap := by
  refine LinearMap.ext fun P => ?_
  change pderiv a (pderiv b P) = pderiv b (pderiv a P)
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P n hP =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hP, pderiv_X, Pi.single_apply]
    split_ifs <;> simp <;> ring

/- English proof (translation)
Use `LinearMap.ext fun P => ?_` and prove the remaining obligations. Simplify using `[mul_left_comm]`.
-/
theorem mx_mx (a b : σ) :
    (LinearMap.mulLeft ℂ (X a) * LinearMap.mulLeft ℂ (X b) : Module.End ℂ (MvPolynomial σ ℂ)) =
      LinearMap.mulLeft ℂ (X b) * LinearMap.mulLeft ℂ (X a) := by
  refine LinearMap.ext fun P => ?_
  simp [mul_left_comm]

/- English proof (translation)
Use `LinearMap.ext fun P => ?_` and prove the remaining obligations. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `[Derivation.leibniz]`. Simplify using `[Derivation.leibniz, h, pderiv_X_of_ne (Ne.symm h)]`.
-/
theorem pd_mx (a b : σ) :
    ((pderiv a).toLinearMap * LinearMap.mulLeft ℂ (X b) : Module.End ℂ (MvPolynomial σ ℂ)) =
      LinearMap.mulLeft ℂ (X b) * (pderiv a).toLinearMap + if a = b then 1 else 0 := by
  refine LinearMap.ext fun P => ?_
  by_cases h : a = b
  · subst h
    simp [Derivation.leibniz]
  · simp [Derivation.leibniz, h, pderiv_X_of_ne (Ne.symm h)]

end Fock

section Lines

variable {p q r s : ℕ}

/- English proof (translation)
Unfold `raiB`. Apply the tactic sequence `by_cases ha : linePos a = true <;> by_cases hb : linePos b = true`. Simplify using `only [ha, hb, if_true]`. Conclude with `mx_mx a b`. Establish `hne : b ≠ a` using `fun h => hb (h ▸ ha)`.

Rewrite using `[if_pos ha, if_neg hb, mul_neg, neg_mul, pd_mx, if_neg hne, add_zero]`. Establish `hne : a ≠ b` using `fun h => ha (h ▸ hb)`. Rewrite using `[if_neg ha, if_pos hb, mul_neg, neg_mul, pd_mx, if_neg hne, add_zero]`. Rewrite using `[if_neg ha, if_neg hb, neg_mul_neg, neg_mul_neg, pd_pd]`.
-/
theorem rai_rai (a b : Ln p q r s) : raiB a * raiB b = raiB b * raiB a := by
  unfold raiB
  by_cases ha : linePos a = true <;> by_cases hb : linePos b = true
  · simp only [ha, hb, if_true]; exact mx_mx a b
  · have hne : b ≠ a := fun h => hb (h ▸ ha)
    rw [if_pos ha, if_neg hb, mul_neg, neg_mul, pd_mx, if_neg hne, add_zero]
  · have hne : a ≠ b := fun h => ha (h ▸ hb)
    rw [if_neg ha, if_pos hb, mul_neg, neg_mul, pd_mx, if_neg hne, add_zero]
  · rw [if_neg ha, if_neg hb, neg_mul_neg, neg_mul_neg, pd_pd]

/- English proof (translation)
Unfold `lowB`. Apply the tactic sequence `by_cases ha : linePos a = true <;> by_cases hb : linePos b = true`. Rewrite using `[if_pos ha, if_pos hb, pd_pd]`. Establish `hne : a ≠ b` using `fun h => hb (h ▸ ha)`. Rewrite using `[if_pos ha, if_neg hb, pd_mx, if_neg hne, add_zero]`.

Establish `hne : b ≠ a` using `fun h => ha (h ▸ hb)`. Rewrite using `[if_neg ha, if_pos hb, pd_mx, if_neg hne, add_zero]`. Rewrite using `[if_neg ha, if_neg hb, mx_mx]`.
-/
theorem low_low (a b : Ln p q r s) : lowB a * lowB b = lowB b * lowB a := by
  unfold lowB
  by_cases ha : linePos a = true <;> by_cases hb : linePos b = true
  · rw [if_pos ha, if_pos hb, pd_pd]
  · have hne : a ≠ b := fun h => hb (h ▸ ha)
    rw [if_pos ha, if_neg hb, pd_mx, if_neg hne, add_zero]
  · have hne : b ≠ a := fun h => ha (h ▸ hb)
    rw [if_neg ha, if_pos hb, pd_mx, if_neg hne, add_zero]
  · rw [if_neg ha, if_neg hb, mx_mx]

/- English proof (translation)
Unfold `lowB raiB`. Apply the tactic sequence `by_cases ha : linePos a = true <;> by_cases hb : linePos b = true`. Rewrite using `[if_pos ha, if_pos hb, pd_mx]`. Establish `hne : a ≠ b` using `fun h => hb (h ▸ ha)`. Rewrite using `[if_pos ha, if_neg hb, mul_neg, neg_mul, pd_pd, if_neg hne, add_zero]`.

Establish `hne : a ≠ b` using `fun h => ha (h ▸ hb)`. Rewrite using `[if_neg ha, if_pos hb, mx_mx, if_neg hne, add_zero]`. Rewrite using `[if_neg ha, if_neg hb, mul_neg, neg_mul, pd_mx]`. Distinguish the cases in `h : a = b`. Rewrite using `[if_pos h, if_pos h.symm]`.

Normalize the expressions using the abelian group laws. Rewrite using `[if_neg h, if_neg (Ne.symm h)]`. Normalize the expressions using the abelian group laws.
-/
theorem low_rai (a b : Ln p q r s) :
    lowB a * raiB b = raiB b * lowB a + if a = b then 1 else 0 := by
  unfold lowB raiB
  by_cases ha : linePos a = true <;> by_cases hb : linePos b = true
  · rw [if_pos ha, if_pos hb, pd_mx]
  · have hne : a ≠ b := fun h => hb (h ▸ ha)
    rw [if_pos ha, if_neg hb, mul_neg, neg_mul, pd_pd, if_neg hne, add_zero]
  · have hne : a ≠ b := fun h => ha (h ▸ hb)
    rw [if_neg ha, if_pos hb, mx_mx, if_neg hne, add_zero]
  · rw [if_neg ha, if_neg hb, mul_neg, neg_mul, pd_mx]
    by_cases h : a = b
    · rw [if_pos h, if_pos h.symm]; abel
    · rw [if_neg h, if_neg (Ne.symm h)]; abel

/- English proof (translation)
Unfold `omAct quadT omE`. Simplify using `only [LinearMap.sum_apply, LinearMap.smulRight_apply, Matrix.entryLinearMap_apply, smul_add, Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_smul, smul_smul]`.
-/
theorem omAct_eq (A : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s A = quadT raiB lowB A + (∑ l, A l l * (1 / 2 : ℂ)) • 1 := by
  unfold omAct quadT omE
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Matrix.entryLinearMap_apply,
    smul_add, Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_smul, smul_smul]

/- English proof (translation)
Establish `hc` using `quadT_commute raiB lowB rai_rai low_low low_rai A B h`. Rewrite using `[omAct_eq, omAct_eq]`. Simplify using `only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hc, smul_add, smul_smul]`. Rewrite using `[mul_comm (∑ l, A l l * (1 / 2 : ℂ))]`. Normalize the expressions using the abelian group laws.
-/
theorem omAct_commute (A B : Matrix (Ln p q r s) (Ln p q r s) ℂ) (h : A * B = B * A) :
    omAct p q r s A * omAct p q r s B = omAct p q r s B * omAct p q r s A := by
  have hc := quadT_commute raiB lowB rai_rai low_low low_rai A B h
  rw [omAct_eq, omAct_eq]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hc, smul_add, smul_smul]
  rw [mul_comm (∑ l, A l l * (1 / 2 : ℂ))]
  abel

end Lines

/- English proof (translation)
Use `omAct_commute (Matrix.kroneckerMap (· * ·) Z 1) (Matrix.kroneckerMap (· * ·) 1 W) ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]`. Simplify using the standard rewrite rules.
-/
theorem fockAct1_fockAct2_commute {p q r s : ℕ} (Z : Mat p q) (W : Mat r s) :
    fockAct1 p q r s Z * fockAct2 p q r s W = fockAct2 p q r s W * fockAct1 p q r s Z := by
  refine omAct_commute (Matrix.kroneckerMap (· * ·) Z 1) (Matrix.kroneckerMap (· * ·) 1 W) ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

end PositivityTheory.KReal

end
