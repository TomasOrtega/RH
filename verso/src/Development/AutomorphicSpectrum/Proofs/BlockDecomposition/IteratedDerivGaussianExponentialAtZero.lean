import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData

noncomputable section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.DilFam

variable {m n : ℕ}

def pt (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) : Fin m × Fin n × Bool → ℂ :=
  fun k => (if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1) * Complex.exp (z * X k.2.1)

def Fam (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (P : PositivityTheory.Rg.Sw.PX m n) (z : ℂ) : ℂ :=
  Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * MvPolynomial.eval (pt X v z) P *
    Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))

/- English proof (translation)
Establish `h : HasDerivAt (fun w : ℂ => w * (X k.2.1 : ℂ)) (X k.2.1 : ℂ) z`. Simplify using `using (hasDerivAt_id z).mul_const (X k.2.1 : ℂ)`. Use `((h.cexp).const_mul (if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1)).congr_deriv ?_` and prove the remaining obligations. Rewrite using `[show GlobalTheory.CompanionTheory.DilFam.pt X v z k = (if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1) * Complex.exp (z * X k.2.1) from rfl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_pt (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) (k : Fin m × Fin n × Bool) :
    HasDerivAt (fun w => pt X v w k) ((X k.2.1 : ℂ) * pt X v z k) z := by
  have h : HasDerivAt (fun w : ℂ => w * (X k.2.1 : ℂ)) (X k.2.1 : ℂ) z := by
    simpa using (hasDerivAt_id z).mul_const (X k.2.1 : ℂ)
  refine ((h.cexp).const_mul (if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1)).congr_deriv ?_
  rw [show GlobalTheory.CompanionTheory.DilFam.pt X v z k =
      (if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1) * Complex.exp (z * X k.2.1) from rfl]
  ring

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on`. Use `next a =>`. Simplify using `only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, mul_zero, Finset.sum_const_zero]`. Conclude with `hasDerivAt_const z a`. Use `next p q hp hq =>`.

Simplify using `only [map_add, mul_add, Finset.sum_add_distrib]`. Conclude with `hp.add hq`. Use `next p i hp =>`. Establish `hX : ∀ k, MvPolynomial.eval (x z) (MvPolynomial.pderiv k (MvPolynomial.X i : MvPolynomial σ ℂ)) = if k = i then 1 else 0`. Introduce `k`.

Distinguish the cases in `h : k = i`. Substitute `h` using the available equality. Simplify using `[MvPolynomial.pderiv_X_self]`. Rewrite using `[MvPolynomial.pderiv_X_of_ne (Ne.symm h), map_zero, if_neg h]`. Establish `hf : (fun w => MvPolynomial.eval (x w) (p * MvPolynomial.X i)) = fun w => MvPolynomial.eval (x w) p * x w i`.

Use function extensionality and compare the values at `w`. Simplify using `only [map_mul, MvPolynomial.eval_X]`. Rewrite using `[hf]`. Use `(hp.mul (hx i)).congr_deriv ?_` and prove the remaining obligations. Use `symm`.

Establish `hs : ∀ k, x' k * MvPolynomial.eval (x z) (MvPolynomial.pderiv k (p * MvPolynomial.X i)) = x' k * MvPolynomial.eval (x z) (MvPolynomial.pderiv k p) * x z i + (if k = i then x' k else 0) * MvPolynomial.eval (x z) p`. Introduce `k`. Rewrite using `[MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, MvPolynomial.eval_X, hX k]`. Apply the tactic sequence `split_ifs <;> ring`. Rewrite using `[Finset.sum_congr rfl (fun k _ => hs k), Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]`.

Simplify using `only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_eval {σ : Type*} [Fintype σ] (x : ℂ → σ → ℂ) (x' : σ → ℂ) (z : ℂ)
    (hx : ∀ k, HasDerivAt (fun w => x w k) (x' k) z) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun w => MvPolynomial.eval (x w) P)
      (∑ k, x' k * MvPolynomial.eval (x z) (MvPolynomial.pderiv k P)) z := by
  classical
  induction P using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, mul_zero, Finset.sum_const_zero]
    exact hasDerivAt_const z a
  next p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    exact hp.add hq
  next p i hp =>
    have hX : ∀ k, MvPolynomial.eval (x z) (MvPolynomial.pderiv k (MvPolynomial.X i : MvPolynomial σ ℂ)) =
        if k = i then 1 else 0 := by
      intro k
      by_cases h : k = i
      · subst h
        simp [MvPolynomial.pderiv_X_self]
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm h), map_zero, if_neg h]
    have hf : (fun w => MvPolynomial.eval (x w) (p * MvPolynomial.X i)) =
        fun w => MvPolynomial.eval (x w) p * x w i := by
      funext w
      simp only [map_mul, MvPolynomial.eval_X]
    rw [hf]
    refine (hp.mul (hx i)).congr_deriv ?_
    symm
    have hs : ∀ k, x' k * MvPolynomial.eval (x z) (MvPolynomial.pderiv k (p * MvPolynomial.X i)) =
        x' k * MvPolynomial.eval (x z) (MvPolynomial.pderiv k p) * x z i +
          (if k = i then x' k else 0) * MvPolynomial.eval (x z) p := by
      intro k
      rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, MvPolynomial.eval_X, hX k]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun k _ => hs k), Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring

/- English proof (translation)
Use `show v a j * Complex.exp (z * ((X j : ℝ) : ℂ)) * (star (v a j) * Complex.exp (z * ((X j : ℝ) : ℂ))) = _`. Rewrite using `[show (2 * z * ((X j : ℝ) : ℂ)) = z * X j + z * X j by ring, Complex.exp_add]`. Rewrite using `[show ((‖v a j‖ ^ 2 : ℝ) : ℂ) = v a j * star (v a j) by`. Rewrite using `[Complex.star_def, Complex.mul_conj']`. Use the proof step `norm_cast]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pt_mul (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) (a : Fin m) (j : Fin n) :
    pt X v z (a, j, false) * pt X v z (a, j, true) =
      Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ) := by
  show v a j * Complex.exp (z * ((X j : ℝ) : ℂ)) * (star (v a j) * Complex.exp (z * ((X j : ℝ) : ℂ))) = _
  rw [show (2 * z * ((X j : ℝ) : ℂ)) = z * X j + z * X j by ring, Complex.exp_add]
  rw [show ((‖v a j‖ ^ 2 : ℝ) : ℂ) = v a j * star (v a j) by
    rw [Complex.star_def, Complex.mul_conj']; norm_cast]
  ring

/- English proof (translation)
Simplify using `only [Fintype.sum_prod_type, Fintype.sum_bool]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_pt (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) (f : Fin m × Fin n × Bool → ℂ) :
    ∑ k, (X k.2.1 : ℂ) * pt X v z k * f k =
      ∑ j, (X j : ℂ) * ∑ a, (pt X v z (a, j, false) * f (a, j, false) +
        pt X v z (a, j, true) * f (a, j, true)) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/- English proof (translation)
Establish `hA : MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (PositivityTheory.Rg.Sw.dil (m` using `m) (2 * Real.pi) X P) = ∑ j, (X j : ℂ) * ((m : ℂ) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P + ∑ a, (GlobalTheory.CompanionTheory.DilFam.pt X v z (a, j, false) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (MvPolynomial.pderiv (a, j, …`. Simplify using `only [PositivityTheory.Rg.Sw.dil, Finset.sum_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply, Derivation.coeFn_coe, map_sum, map_add, map_sub, MvPolynomial.smul_eval, map …`. Rewrite using `[hA, GlobalTheory.CompanionTheory.DilFam.sum_pt X v z (fun k => MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (MvPolynomial.pderiv k P))]`. Simplify using `only [GlobalTheory.CompanionTheory.DilFam.pt_mul]`. Establish `h1 : (m : ℂ) * (∑ j, (X j : ℂ)) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P = ∑ j, (X j : ℂ) * ((m : ℂ) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P)`.

Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Establish `h3 : (-(4 * Real.pi : ℂ)) * (∑ a, ∑ j, (X j : ℂ) * (Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P = ∑ j, (X j : ℂ) * -(∑ a, 2 * ((2 * Real.pi : ℝ) : ℂ) * (Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : …`. Rewrite using `[Finset.sum_comm, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_dil (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) (P : PositivityTheory.Rg.Sw.PX m n) :
    MvPolynomial.eval (pt X v z) (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) =
      (m : ℂ) * (∑ j, (X j : ℂ)) * MvPolynomial.eval (pt X v z) P +
      (∑ k, (X k.2.1 : ℂ) * pt X v z k * MvPolynomial.eval (pt X v z) (MvPolynomial.pderiv k P)) +
      (-(4 * Real.pi : ℂ)) * (∑ a, ∑ j, (X j : ℂ) * (Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))) *
        MvPolynomial.eval (pt X v z) P := by
  have hA : MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) =
      ∑ j, (X j : ℂ) * ((m : ℂ) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P +
        ∑ a, (GlobalTheory.CompanionTheory.DilFam.pt X v z (a, j, false) *
            MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (MvPolynomial.pderiv (a, j, false) P) +
          GlobalTheory.CompanionTheory.DilFam.pt X v z (a, j, true) *
            MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (MvPolynomial.pderiv (a, j, true) P) -
          2 * ((2 * Real.pi : ℝ) : ℂ) * (GlobalTheory.CompanionTheory.DilFam.pt X v z (a, j, false) *
            GlobalTheory.CompanionTheory.DilFam.pt X v z (a, j, true) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P))) := by
    simp only [PositivityTheory.Rg.Sw.dil, Finset.sum_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, LinearMap.id_apply, Derivation.coeFn_coe, map_sum, map_add, map_sub,
      MvPolynomial.smul_eval, map_mul, MvPolynomial.eval_X]
  rw [hA, GlobalTheory.CompanionTheory.DilFam.sum_pt X v z
    (fun k => MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (MvPolynomial.pderiv k P))]
  simp only [GlobalTheory.CompanionTheory.DilFam.pt_mul]
  have h1 : (m : ℂ) * (∑ j, (X j : ℂ)) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P =
      ∑ j, (X j : ℂ) * ((m : ℂ) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : (-(4 * Real.pi : ℂ)) * (∑ a, ∑ j, (X j : ℂ) * (Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))) *
        MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P =
      ∑ j, (X j : ℂ) * -(∑ a, 2 * ((2 * Real.pi : ℝ) : ℂ) *
        (Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) P)) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    push_cast
    ring
  rw [h1, h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_sub_distrib]
  ring

/- English proof (translation)
Establish `hin : HasDerivAt (fun w : ℂ => -(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * w * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * (2 * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) z`. Apply `HasDerivAt.const_mul` to reduce the goal to its premises. Apply `HasDerivAt.fun_sum` to reduce the goal to its premises. Introduce `a _`. Apply `HasDerivAt.fun_sum` to reduce the goal to its premises.

Introduce `j _`. Apply `HasDerivAt.mul_const` to reduce the goal to its premises. Establish `h : HasDerivAt (fun w : ℂ => 2 * w * (X j : ℂ)) (2 * X j) z`. Simplify using `using ((hasDerivAt_id z).const_mul (2 : ℂ)).mul_const (X j : ℂ)`. Conclude with `h.cexp`.

Use `hin.cexp using 1` and compare the differences between its conclusion and the goal. Use `congr 1`. Simplify using `only [Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_gauss (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * w * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))
      (Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) *
        ((-(4 * Real.pi : ℂ)) * ∑ a, ∑ j, (X j : ℂ) * (Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) z := by
  have hin : HasDerivAt
      (fun w : ℂ => -(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * w * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))
      (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * (2 * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) z := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro a _
    apply HasDerivAt.fun_sum
    intro j _
    apply HasDerivAt.mul_const
    have h : HasDerivAt (fun w : ℂ => 2 * w * (X j : ℂ)) (2 * X j) z := by
      simpa using ((hasDerivAt_id z).const_mul (2 : ℂ)).mul_const (X j : ℂ)
    exact h.cexp
  convert hin.cexp using 1
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `he : HasDerivAt (fun w : ℂ => Complex.exp ((m : ℂ) * w * ∑ j, (X j : ℂ))) (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * ((m : ℂ) * ∑ j, (X j : ℂ))) z`. Establish `h : HasDerivAt (fun w : ℂ => (m : ℂ) * w * ∑ j, (X j : ℂ)) ((m : ℂ) * ∑ j, (X j : ℂ)) z`. Simplify using `using ((hasDerivAt_id z).const_mul (m : ℂ)).mul_const (∑ j, (X j : ℂ))`. Conclude with `h.cexp`. Establish `hp` using `GlobalTheory.CompanionTheory.DilFam.hasDerivAt_eval (GlobalTheory.CompanionTheory.DilFam.pt X v) (fun k => (X k.2.1 : ℂ) * GlobalTheory.CompanionTheory.DilFam.pt X v z k) z (GlobalTheory.CompanionTheory.DilFam.hasDerivAt_pt X v z) P`.

Establish `hg` using `GlobalTheory.CompanionTheory.DilFam.hasDerivAt_gauss X v z`. Establish `h` using `(he.mul hp).mul hg`. Use `h.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[show GlobalTheory.CompanionTheory.DilFam.Fam X v (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) z = Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) * Co …`. Simplify using `only [Pi.mul_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_Fam (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (P : PositivityTheory.Rg.Sw.PX m n) (z : ℂ) :
    HasDerivAt (Fam X v P) (Fam X v (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) z) z := by
  have he : HasDerivAt (fun w : ℂ => Complex.exp ((m : ℂ) * w * ∑ j, (X j : ℂ)))
      (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * ((m : ℂ) * ∑ j, (X j : ℂ))) z := by
    have h : HasDerivAt (fun w : ℂ => (m : ℂ) * w * ∑ j, (X j : ℂ)) ((m : ℂ) * ∑ j, (X j : ℂ)) z := by
      simpa using ((hasDerivAt_id z).const_mul (m : ℂ)).mul_const (∑ j, (X j : ℂ))
    exact h.cexp
  have hp := GlobalTheory.CompanionTheory.DilFam.hasDerivAt_eval (GlobalTheory.CompanionTheory.DilFam.pt X v)
    (fun k => (X k.2.1 : ℂ) * GlobalTheory.CompanionTheory.DilFam.pt X v z k) z (GlobalTheory.CompanionTheory.DilFam.hasDerivAt_pt X v z) P
  have hg := GlobalTheory.CompanionTheory.DilFam.hasDerivAt_gauss X v z
  have h := (he.mul hp).mul hg
  refine h.congr_deriv ?_
  rw [show GlobalTheory.CompanionTheory.DilFam.Fam X v (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) z =
      Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) *
        MvPolynomial.eval (GlobalTheory.CompanionTheory.DilFam.pt X v z) (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) *
        Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) from rfl,
    GlobalTheory.CompanionTheory.DilFam.eval_dil]
  simp only [Pi.mul_apply]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [GlobalTheory.CompanionTheory.DilFam.Fam, map_one, mul_one]`.
-/
theorem Fam_one (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) :
    Fam X v 1 = fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) *
      Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))) := by
  funext z
  simp only [GlobalTheory.CompanionTheory.DilFam.Fam, map_one, mul_one]

/- English proof (translation)
Establish `hD : GlobalTheory.CompanionTheory.DilFam.pt X v 0 = fun k => if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1`. Use function extensionality and compare the values at `k`. Simplify using `only [GlobalTheory.CompanionTheory.DilFam.pt, zero_mul, Complex.exp_zero, mul_one]`. Simplify using `only [GlobalTheory.CompanionTheory.DilFam.Fam, PositivityTheory.Rg.Sw.evX, PositivityTheory.Rg.Sw.gs, hD, mul_zero, zero_mul, Complex.exp_zero, one_mul]`. Use `congr 1`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Fam_zero (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (P : PositivityTheory.Rg.Sw.PX m n) :
    Fam X v P 0 = PositivityTheory.Rg.Sw.evX P v * PositivityTheory.Rg.Sw.gs (2 * Real.pi) v := by
  have hD : GlobalTheory.CompanionTheory.DilFam.pt X v 0 = fun k => if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1 := by
    funext k
    simp only [GlobalTheory.CompanionTheory.DilFam.pt, zero_mul, Complex.exp_zero, mul_one]
  simp only [GlobalTheory.CompanionTheory.DilFam.Fam, PositivityTheory.Rg.Sw.evX, PositivityTheory.Rg.Sw.gs, hD, mul_zero,
    zero_mul, Complex.exp_zero, one_mul]
  congr 1
  congr 1
  push_cast
  ring

/- English proof (translation)
Proceed by induction on `r generalizing P with`. Consider the case `zero => rw [iteratedDeriv_zero, pow_zero, Module.End.one_apply]`. Consider the case `succ r ih`. Establish `hd : deriv (GlobalTheory.CompanionTheory.DilFam.Fam X v P) = GlobalTheory.CompanionTheory.DilFam.Fam X v (PositivityTheory.Rg.Sw.dil (m` using `m) (2 * Real.pi) X P) := by`. Use function extensionality and compare the values at `z`.

Conclude with `(GlobalTheory.CompanionTheory.DilFam.hasDerivAt_Fam X v P z).deriv`. Rewrite using `[iteratedDeriv_succ', hd, ih, pow_succ, Module.End.mul_apply]`.
-/
theorem iteratedDeriv_Fam (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (r : ℕ) (P : PositivityTheory.Rg.Sw.PX m n) :
    iteratedDeriv r (Fam X v P) = Fam X v ((PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X ^ r) P) := by
  induction r generalizing P with
  | zero => rw [iteratedDeriv_zero, pow_zero, Module.End.one_apply]
  | succ r ih =>
    have hd : deriv (GlobalTheory.CompanionTheory.DilFam.Fam X v P) =
        GlobalTheory.CompanionTheory.DilFam.Fam X v (PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X P) := by
      funext z
      exact (GlobalTheory.CompanionTheory.DilFam.hasDerivAt_Fam X v P z).deriv
    rw [iteratedDeriv_succ', hd, ih, pow_succ, Module.End.mul_apply]

/- English proof (translation)
Introduce `m n X v`. Rewrite using `[← GlobalTheory.CompanionTheory.DilFam.Fam_one X v]`. Use `⟨fun z => (GlobalTheory.CompanionTheory.DilFam.hasDerivAt_Fam X v 1 z).differentiableAt, fun r => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.CompanionTheory.DilFam.iteratedDeriv_Fam, GlobalTheory.CompanionTheory.DilFam.Fam_zero]`.
-/
theorem main : ∀ (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ), Differentiable ℂ (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = PositivityTheory.Rg.Sw.evX ((PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X ^ r) 1) v * PositivityTheory.Rg.Sw.gs (2 * Real.pi) v := by
  intro m n X v
  rw [← GlobalTheory.CompanionTheory.DilFam.Fam_one X v]
  refine ⟨fun z => (GlobalTheory.CompanionTheory.DilFam.hasDerivAt_Fam X v 1 z).differentiableAt, fun r => ?_⟩
  rw [GlobalTheory.CompanionTheory.DilFam.iteratedDeriv_Fam, GlobalTheory.CompanionTheory.DilFam.Fam_zero]

end GlobalTheory.CompanionTheory.DilFam
