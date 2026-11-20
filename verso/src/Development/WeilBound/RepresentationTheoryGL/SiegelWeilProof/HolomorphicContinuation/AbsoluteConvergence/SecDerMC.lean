import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMB
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HasDerivAtPhi

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

/- English proof (translation)
Unfold `aE`. Rewrite using `[Complex.coe_smul]`.
-/
theorem aE_eq (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H σ = NormedSpace.exp (σ • H) := by
  unfold aE; rw [Complex.coe_smul]

/- English proof (translation)
Simplify using `only [aE_eq]`. Use `open scoped Matrix.Norms.Operator in`. Conclude with `((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt s (hasDerivAt_exp_smul_const (𝕂 := ℝ) H s)`.
-/
theorem hasDerivAt_aE_entry (H : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun σ : ℝ => aE H σ i j) ((aE H s * H) i j) s := by
  simp only [aE_eq]
  open scoped Matrix.Norms.Operator in
  exact ((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt s
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) H s)

/- English proof (translation)
Use function extensionality and compare the values at `a j`. Simplify using `only [mulR, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem mulR_mul (A B : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    mulR B (mulR A y) = mulR (A * B) y := by
  funext a j
  simp only [mulR, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/- English proof (translation)
Use function extensionality and compare the values at `a j`. Simplify using `[mulR, Matrix.one_apply]`.
-/
theorem mulR_one (y : Fin m → Fin n → ℂ) : mulR (1 : Matrix (Fin n) (Fin n) ℂ) y = y := by
  funext a j
  simp [mulR, Matrix.one_apply]

/- English proof (translation)
Apply the tactic sequence `have h : HasDerivAt (fun σ : ℝ => ∑ i, y a i * aE H σ i j) (∑ i, y a i * (aE H s * H) i j) s := HasDerivAt.fun_sum fun i _ => (hasDerivAt_aE_entry H s i j).const_mul (y a i)`. Establish `e : ∑ i, y a i * (aE H s * H) i j = mulR H (mulR (aE H s) y) a j`. Rewrite using `[mulR_mul]`. Both sides reduce to the same expression. Conclude with `e ▸ h`.
-/
theorem hasDerivAt_mulR (H : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) (s : ℝ) (a : Fin m) (j : Fin n) :
    HasDerivAt (fun σ : ℝ => mulR (aE H σ) y a j) (mulR H (mulR (aE H s) y) a j) s := by
  have h : HasDerivAt (fun σ : ℝ => ∑ i, y a i * aE H σ i j) (∑ i, y a i * (aE H s * H) i j) s :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_aE_entry H s i j).const_mul (y a i)
  have e : ∑ i, y a i * (aE H s * H) i j = mulR H (mulR (aE H s) y) a j := by
    rw [mulR_mul]; rfl
  exact e ▸ h

/- English proof (translation)
Break down `k with ⟨a, j, b⟩` into its components or cases. Consider the cases of `b`. Conclude with `hasDerivAt_mulR H y s a j`. Conclude with `(hasDerivAt_mulR H y s a j).star`.
-/
theorem hasDerivAt_ept (H : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) (s : ℝ) (k : Fin m × Fin n × Bool) :
    HasDerivAt (fun σ : ℝ => ept (mulR (aE H σ) y) k) (ept (mulR H (mulR (aE H s) y)) k) s := by
  rcases k with ⟨a, j, b⟩
  cases b
  · exact hasDerivAt_mulR H y s a j
  · exact (hasDerivAt_mulR H y s a j).star

/- English proof (translation)
Simplify using `only [eulH, evX_eq, map_sum, map_add, map_mul, eval_X, eval_C]`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_bool]`. Simplify using `only [ept, mulR, if_true, Bool.false_eq_true, if_false, star_sum, star_mul']`.

Put the polynomial expressions in normal form.
-/
theorem evX_eulH (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (z : Fin m → Fin n → ℂ) :
    evX (eulH H R) z = ∑ k, MvPolynomial.eval (ept z) (pderiv k R) * ept (mulR H z) k := by
  simp only [eulH, evX_eq, map_sum, map_add, map_mul, eval_X, eval_C]
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [ept, mulR, if_true, Bool.false_eq_true, if_false, star_sum, star_mul']
  ring_nf

def trHQ (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) : PX m n :=
  ∑ i, ∑ j, MvPolynomial.C (H i j) * (Qb ε true j i + Qb ε false j i)

/- English proof (translation)
Simplify using `only [Qb, evX_eq, map_add, map_sum, map_mul, eval_X, ept, if_true, Bool.false_eq_true, if_false]`. Use `Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => ε x = true) (fun x => star (z x i) * z x j) using 3` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem evX_Qb_add (ε : Fin m → Bool) (z : Fin m → Fin n → ℂ) (i j : Fin n) :
    evX (Qb ε true i j + Qb ε false i j) z = ∑ a, star (z a i) * z a j := by
  simp only [Qb, evX_eq, map_add, map_sum, map_mul, eval_X, ept, if_true, Bool.false_eq_true, if_false]
  convert Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => ε x = true) (fun x => star (z x i) * z x j) using 3
  ext x; simp

/- English proof (translation)
Establish `e : evX (trHQ ε H) z = ∑ i, ∑ j, H i j * evX (Qb ε true j i + Qb ε false j i) z`. Simplify using `only [trHQ, evX_eq, map_sum, map_mul, eval_C]`. Rewrite using `[e]`. Simplify using `only [evX_Qb_add, mulR, Finset.mul_sum]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem evX_trHQ (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (z : Fin m → Fin n → ℂ) :
    evX (trHQ ε H) z = ∑ a, ∑ j, star (z a j) * mulR H z a j := by
  have e : evX (trHQ ε H) z = ∑ i, ∑ j, H i j * evX (Qb ε true j i + Qb ε false j i) z := by
    simp only [trHQ, evX_eq, map_sum, map_mul, eval_C]
  rw [e]
  simp only [evX_Qb_add, mulR, Finset.mul_sum]
  calc ∑ i, ∑ j, ∑ a, H i j * (star (z a j) * z a i) = ∑ j, ∑ i, ∑ a, H i j * (star (z a j) * z a i) :=
        Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ i, H i j * (star (z a j) * z a i) := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ i, H i j * (star (z a j) * z a i) := Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ i, star (z a j) * (z a i * H i j) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Establish `hij : ∀ i j, star (H i j) = H j i` using `fun i j => by`. Use `congrFun (congrFun hH j) i` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_apply]`. Establish `hconj : star (evX (trHQ ε H) z) = evX (trHQ ε H) z`. Rewrite using `[evX_trHQ]`.

Simplify using `only [mulR, star_sum, star_mul', star_star, Finset.mul_sum, hij]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `congrArg Complex.im hconj` as an intermediate fact. Simplify using `only [Complex.star_def, Complex.conj_im] at this`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem trHQ_real (ε : Fin m → Bool) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (z : Fin m → Fin n → ℂ) :
    (evX (trHQ ε H) z).im = 0 := by
  have hij : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using this
  have hconj : star (evX (trHQ ε H) z) = evX (trHQ ε H) z := by
    rw [evX_trHQ]
    simp only [mulR, star_sum, star_mul', star_star, Finset.mul_sum, hij]
    refine Finset.sum_congr rfl fun a _ => ?_
    calc ∑ j, ∑ i, z a j * (star (z a i) * H j i) = ∑ i, ∑ j, z a j * (star (z a i) * H j i) := Finset.sum_comm
      _ = ∑ i, ∑ j, star (z a i) * (z a j * H j i) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have := congrArg Complex.im hconj
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

/- English proof (translation)
Establish `hre : HasDerivAt (fun σ => (w σ).re) w'.re s` using `Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hw`. Establish `him : HasDerivAt (fun σ => (w σ).im) w'.im s` using `Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hw`. Establish `h` using `(hre.pow 2).add (him.pow 2)`. Establish `e : ∀ σ, (w σ).re ^ 2 + (w σ).im ^ 2 = ‖w σ‖ ^ 2` using `fun σ => by`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`.

Expand and normalize the polynomial expressions, which then agree. Use `(h.congr_of_eventuallyEq (Eventually.of_forall fun σ => (e σ).symm)).congr_deriv ?_` and prove the remaining obligations. Simplify using `only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_normSq (w : ℝ → ℂ) (w' : ℂ) (s : ℝ) (hw : HasDerivAt w w' s) :
    HasDerivAt (fun σ => ‖w σ‖ ^ 2) (2 * (star (w s) * w').re) s := by
  have hre : HasDerivAt (fun σ => (w σ).re) w'.re s := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hw
  have him : HasDerivAt (fun σ => (w σ).im) w'.im s := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hw
  have h := (hre.pow 2).add (him.pow 2)
  have e : ∀ σ, (w σ).re ^ 2 + (w σ).im ^ 2 = ‖w σ‖ ^ 2 := fun σ => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun σ => (e σ).symm)).congr_deriv ?_
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

/- English proof (translation)
Establish `hS : HasDerivAt (fun σ => ∑ a, ∑ j, ‖mulR (aE H σ) y a j‖ ^ 2) (∑ a, ∑ j, 2 * (star (mulR (aE H s) y a j) * mulR H (mulR (aE H s) y) a j).re) s` using `HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun j _ => hasDerivAt_normSq _ _ s (hasDerivAt_mulR H y s a j)`. Establish `hg` using `(((hS.const_mul c).ofReal_comp).neg).cexp`. Use `set T := evX (trHQ ε H) (mulR (aE H s) y) with hTdef`. Establish `h0 : T.im = 0` using `trHQ_real ε hH _`. Establish `hsum : (∑ a, ∑ j, 2 * (star (mulR (aE H s) y a j) * mulR H (mulR (aE H s) y) a j).re) = 2 * T.re`.

Rewrite using `[hTdef, evX_trHQ]`. Simplify using `only [Complex.re_sum, Finset.mul_sum]`. Establish `hT' : ((T.re : ℝ) : ℂ) = T` using `Complex.ext (by simp) (by simp [h0])`. Unfold `gs`. Use `hg.congr_deriv ?_` and prove the remaining obligations.

Simplify using `only [Pi.neg_apply]`. Rewrite using `[hsum]`. Use `push_cast`. Rewrite using `[hT']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_gsE (c : ℝ) (ε : Fin m → Bool) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (y : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fun σ => gs c (mulR (aE H σ) y))
      (gs c (mulR (aE H s) y) * (-(2 * (c : ℂ)) * evX (trHQ ε H) (mulR (aE H s) y))) s := by
  have hS : HasDerivAt (fun σ => ∑ a, ∑ j, ‖mulR (aE H σ) y a j‖ ^ 2)
      (∑ a, ∑ j, 2 * (star (mulR (aE H s) y a j) * mulR H (mulR (aE H s) y) a j).re) s :=
    HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun j _ => hasDerivAt_normSq _ _ s (hasDerivAt_mulR H y s a j)
  have hg := (((hS.const_mul c).ofReal_comp).neg).cexp
  set T := evX (trHQ ε H) (mulR (aE H s) y) with hTdef
  have h0 : T.im = 0 := trHQ_real ε hH _
  have hsum : (∑ a, ∑ j, 2 * (star (mulR (aE H s) y a j) * mulR H (mulR (aE H s) y) a j).re) = 2 * T.re := by
    rw [hTdef, evX_trHQ]
    simp only [Complex.re_sum, Finset.mul_sum]
  have hT' : ((T.re : ℝ) : ℂ) = T := Complex.ext (by simp) (by simp [h0])
  unfold gs
  refine hg.congr_deriv ?_
  simp only [Pi.neg_apply]
  rw [hsum]
  push_cast
  rw [hT']
  ring

end PositivityTheory.Rg.Sw.AbsSt.SDM
