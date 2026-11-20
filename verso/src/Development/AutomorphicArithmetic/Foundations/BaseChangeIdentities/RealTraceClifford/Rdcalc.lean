import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.HderEntry
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `n V _ _`. Use `⟨fun f f' e X => GlobalTheory.CompanionTheory.RCalc.Rd_congr X e, fun f hf => ⟨fun X => GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf, fun X Y g hg => GlobalTheory.CompanionTheory.RCalc.Rd_bracket X Y hf hg, fun h hh X g hg => ?_⟩⟩` and prove the remaining obligations. Establish `hdet : IsUnit h.det` using `isUnit_iff_ne_zero.2 hh`. Establish `hhg : h * g ∈ GLs n` using `by show (h * g).det ≠ 0`. Rewrite using `[Matrix.det_mul]`.

Conclude with `mul_ne_zero hh hg`. Establish `hgh : g * h ∈ GLs n` using `by show (g * h).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero hg hh`. Prove the components needed by the constructor for the conclusion.

Establish `hd` using `GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hf hhg`. Establish `hc : HasFDerivAt (fun y : Mat n => f (h * y)) ((fderiv ℝ f (h * g)).comp (GlobalTheory.CompanionTheory.RCalc.mulL h)) g` using `HasFDerivAt.comp (g := f) (f := fun y : Mat n => h * y) g hd.hasFDerivAt (GlobalTheory.CompanionTheory.RCalc.mulL h).hasFDerivAt`. Simplify using `only [Rd, hc.fderiv, ContinuousLinearMap.comp_apply, GlobalTheory.CompanionTheory.RCalc.mulL_apply, mul_assoc]`. Establish `hd` using `GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hf hgh`. Establish `hc : HasFDerivAt (fun y : Mat n => f (y * h)) ((fderiv ℝ f (g * h)).comp (GlobalTheory.CompanionTheory.RCalc.mulR h)) g` using `HasFDerivAt.comp (g := f) (f := fun y : Mat n => y * h) g hd.hasFDerivAt (GlobalTheory.CompanionTheory.RCalc.mulR h).hasFDerivAt`.

Establish `e : g * h * (h⁻¹ * X * h) = g * X * h`. Rewrite using `[Matrix.mul_assoc g h, ← Matrix.mul_assoc h, ← Matrix.mul_assoc h, Matrix.mul_nonsing_inv h hdet, Matrix.one_mul, Matrix.mul_assoc]`. Simplify using `only [Rd, hc.fderiv, ContinuousLinearMap.comp_apply, GlobalTheory.CompanionTheory.RCalc.mulR_apply, e]`.
-/
theorem UpperTheory.RealTr.rdcalc :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V],
      (∀ f f' : Mat n → V, Set.EqOn f f' (GLs n) → ∀ X, Set.EqOn (Rd X f) (Rd X f') (GLs n)) ∧
      ∀ f : Mat n → V, ContDiffOn ℝ ∞ f (GLs n) → (∀ X, ContDiffOn ℝ ∞ (Rd X f) (GLs n)) ∧
        (∀ X Y, ∀ g ∈ GLs n, Rd X (Rd Y f) g - Rd Y (Rd X f) g = Rd (X * Y - Y * X) f g) ∧
        ∀ h ∈ GLs n, ∀ X, ∀ g ∈ GLs n, Rd X (fun y => f (h * y)) g = Rd X f (h * g) ∧
          Rd X (fun y => f (y * h)) g = Rd (h⁻¹ * X * h) f (g * h) := by
  intro n V _ _
  refine ⟨fun f f' e X => GlobalTheory.CompanionTheory.RCalc.Rd_congr X e, fun f hf =>
    ⟨fun X => GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf, fun X Y g hg => GlobalTheory.CompanionTheory.RCalc.Rd_bracket X Y hf hg,
      fun h hh X g hg => ?_⟩⟩
  have hdet : IsUnit h.det := isUnit_iff_ne_zero.2 hh
  have hhg : h * g ∈ GLs n := by
    show (h * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hh hg
  have hgh : g * h ∈ GLs n := by
    show (g * h).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hg hh
  constructor
  · have hd := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hf hhg
    have hc : HasFDerivAt (fun y : Mat n => f (h * y))
        ((fderiv ℝ f (h * g)).comp (GlobalTheory.CompanionTheory.RCalc.mulL h)) g :=
      HasFDerivAt.comp (g := f) (f := fun y : Mat n => h * y) g hd.hasFDerivAt
        (GlobalTheory.CompanionTheory.RCalc.mulL h).hasFDerivAt
    simp only [Rd, hc.fderiv, ContinuousLinearMap.comp_apply, GlobalTheory.CompanionTheory.RCalc.mulL_apply, mul_assoc]
  · have hd := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hf hgh
    have hc : HasFDerivAt (fun y : Mat n => f (y * h))
        ((fderiv ℝ f (g * h)).comp (GlobalTheory.CompanionTheory.RCalc.mulR h)) g :=
      HasFDerivAt.comp (g := f) (f := fun y : Mat n => y * h) g hd.hasFDerivAt
        (GlobalTheory.CompanionTheory.RCalc.mulR h).hasFDerivAt
    have e : g * h * (h⁻¹ * X * h) = g * X * h := by
      rw [Matrix.mul_assoc g h, ← Matrix.mul_assoc h, ← Matrix.mul_assoc h, Matrix.mul_nonsing_inv h hdet,
        Matrix.one_mul, Matrix.mul_assoc]
    simp only [Rd, hc.fderiv, ContinuousLinearMap.comp_apply, GlobalTheory.CompanionTheory.RCalc.mulR_apply, e]
