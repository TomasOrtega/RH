import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.MulCoordMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem arc_apply_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) (i : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) :
    _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i = if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im := rfl
/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq]`. Simplify using `only [Fintype.sum_prod_type, Fintype.sum_bool, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.arc_apply_k, if_true, Bool.false_eq_true, if_false, Real.norm_eq_abs, sq_abs]`. Use `Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_arc_sq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) :
    ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2 = ∑ w, ∑ a, ∑ j, ‖R.loc w X a j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.arc_apply_k, if_true, Bool.false_eq_true, if_false,
    Real.norm_eq_abs, sq_abs]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring
/- English proof (translation)
Rewrite using `[Complex.ofReal_exp, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.norm_arc_sq_k]`. Simplify using `only [gs]`. Rewrite using `[← Complex.exp_sum]`. Use `congr 1`. Use `push_cast`.

Rewrite using `[Finset.mul_sum, Finset.sum_neg_distrib]`.
-/
theorem gauss_eq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) :
    ((Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℝ) : ℂ) = ∏ w, gs (2 * Real.pi) (R.loc w X) := by
  rw [Complex.ofReal_exp, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.norm_arc_sq_k]
  simp only [gs]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_neg_distrib]
def lin_k (a : Fin d.m) (j : Fin d.n) (b : Bool) : PX d.m d.n :=
  if b then MvPolynomial.C (1 / 2) * (MvPolynomial.X (a, j, false) + MvPolynomial.X (a, j, true))
  else MvPolynomial.C (-Complex.I / 2) * (MvPolynomial.X (a, j, false) - MvPolynomial.X (a, j, true))
/- English proof (translation)
Consider the cases of `b`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k, evX, Bool.false_eq_true, if_false, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X, if_true]`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k, evX, if_true, Bool.false_eq_true, if_false, map_mul, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X]`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`.
-/
theorem evX_lin_k (a : Fin d.m) (j : Fin d.n) (b : Bool) (z : Fin d.m → Fin d.n → ℂ) :
    evX (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k (d := d) a j b) z = ((if b then (z a j).re else (z a j).im : ℝ) : ℂ) := by
  cases b
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k, evX, Bool.false_eq_true, if_false, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
      if_true]
    apply Complex.ext <;> simp <;> ring
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k, evX, if_true, Bool.false_eq_true, if_false, map_mul, map_add, MvPolynomial.eval_C,
      MvPolynomial.eval_X]
    apply Complex.ext <;> simp <;> ring
/- English proof (translation)
Simplify using `only [fP, evX, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fP_mul_k (P Q : PX d.m d.n) (u : Fin d.m → Fin d.n → ℂ) : fP (P * Q) u = evX P u * fP Q u := by
  simp only [fP, evX, map_mul]
  ring
/- English proof (translation)
Unfold `_root_.PositivityTheory.SiegelWeilFormula.RD_k.fock _root_.PositivityTheory.SiegelWeilFormula.RD_k.fockOn at hh ⊢`. Proceed by induction on `hh using Submodule.span_induction with`. Consider the case `mem h hmem`. Take `⟨P, g, hg, rfl⟩` from `hmem`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨Function.update P i.1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1), g, hg, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `X`. Establish `e1 : ∏ w ∈ Finset.univ, fP (Function.update P i.1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1) w) (R.loc w X) = fP (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1) (R.loc i.1 X) * ∏ w ∈ Finset …`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i.1), Function.update_self]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun w hw => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hw)]`. Establish `e2 : ∏ w ∈ Finset.univ, fP (P w) (R.loc w X) = fP (P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X)` using `(Finset.mul_prod_erase _ _ (Finset.mem_univ i.1)).symm`. Simplify using `only`. Rewrite using `[e1, e2, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.fP_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.evX_lin_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.arc_apply_k]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero`. Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `X`. Simplify using the standard rewrite rules.

Consider the case `add h₁ h₂ _ _ i₁ i₂`. Use `Submodule.add_mem _ i₁ i₂ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `X`. Simplify using `[mul_add]`. Consider the case `smul a h _ i₁`.

Use `Submodule.smul_mem _ a i₁ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `X`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_coord_mem_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (i : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) {h : Mx F E d.m d.n → ℂ} (hh : h ∈ R.fock) :
    (fun X => ((_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i : ℝ) : ℂ) * h X) ∈ R.fock := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.fock _root_.PositivityTheory.SiegelWeilFormula.RD_k.fockOn at hh ⊢
  induction hh using Submodule.span_induction with
  | mem h hmem =>
    obtain ⟨P, g, hg, rfl⟩ := hmem
    apply Submodule.subset_span
    refine ⟨Function.update P i.1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1), g, hg, ?_⟩
    funext X
    have e1 : ∏ w ∈ Finset.univ, fP (Function.update P i.1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1) w) (R.loc w X) =
        fP (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i.1), Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun w hw => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
    have e2 : ∏ w ∈ Finset.univ, fP (P w) (R.loc w X) =
        fP (P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i.1)).symm
    dsimp only
    rw [e1, e2, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.fP_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.evX_lin_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.arc_apply_k]
    ring
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext X
    simp
  | add h₁ h₂ _ _ i₁ i₂ =>
    convert Submodule.add_mem _ i₁ i₂ using 1
    funext X
    simp [mul_add]
  | smul a h _ i₁ =>
    convert Submodule.smul_mem _ a i₁ using 1
    funext X
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
/- English proof (translation)
Establish `base : (fun X => (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) ∈ R.fock`. Unfold `_root_.PositivityTheory.SiegelWeilFormula.RD_k.fock _root_.PositivityTheory.SiegelWeilFormula.RD_k.fockOn`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨fun _ => 1, g, hg, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `X`.

Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.gauss_eq_k]`. Simplify using `only [fP, evX, map_one, one_mul]`. Both sides reduce to the same expression. Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C a`.

Use `Submodule.smul_mem _ a base using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `X`. Simplify using `only [MvPolynomial.eval_C, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add p q hp hq`.

Use `Submodule.add_mem _ hp hq using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `X`. Simplify using `only [map_add, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p i hp`.

Use `_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.mul_coord_mem_k R i hp using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `X`. Simplify using `only [map_mul, MvPolynomial.eval_X]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem poly_mem_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Q : MvPolynomial (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℂ) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) :
    (fun X => MvPolynomial.eval (fun i => ((_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i : ℝ) : ℂ)) Q * (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) *
      g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) ∈ R.fock := by
  have base : (fun X => (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) ∈ R.fock := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.fock _root_.PositivityTheory.SiegelWeilFormula.RD_k.fockOn
    apply Submodule.subset_span
    refine ⟨fun _ => 1, g, hg, ?_⟩
    funext X
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.gauss_eq_k]
    simp only [fP, evX, map_one, one_mul]
    rfl
  induction Q using MvPolynomial.induction_on with
  | C a =>
    convert Submodule.smul_mem _ a base using 1
    funext X
    simp only [MvPolynomial.eval_C, Pi.smul_apply, smul_eq_mul]
    ring
  | add p q hp hq =>
    convert Submodule.add_mem _ hp hq using 1
    funext X
    simp only [map_add, Pi.add_apply]
    ring
  | mul_X p i hp =>
    convert _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.mul_coord_mem_k R i hp using 1
    funext X
    simp only [map_mul, MvPolynomial.eval_X]
    ring
end PositivityTheory.SiegelWeilFormula.KFP.OswGen
end
end
