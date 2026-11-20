import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.PointwiseKernelBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsAutIdemElementary

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Deep

/- English proof (translation)
Introduce `hD B d p q h hDS hsig hgap hh`. Take `⟨him, hre, hle, -⟩` from `GlobalTheory.rowsAut_idem_elementary B`. Establish `hrk : ∀ v, rkR (B.I.ε v) = min p q` using `fun v => by`. Rewrite using `[← (hsig v).1, ← (hsig v).2]`. Both sides reduce to the same expression.

Establish `hw : ∀ v, ‖B.w v‖ = 1` using `fun v => (hDS v).2.2.1.1`. Establish `hdec` using `fun v (g : UJ (B.I.ε v)) => hD B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) (hDS v).1 (hDS v).2.1 h (hgap v) (by rw [hrk v]; exact hh) (uMat g) g.2 (B.w v) (hDS v).2.2.1.2 (B.w v) (hDS v).2.2.1.2`. Establish `hd : 0 ≤ ∏ v, d v` using `Finset.prod_nonneg fun v _ => (hDS v).2.2.2.1.le`. Establish `key : ∀ (y : B.I.GA) (c : InfinitePlace B.I.F → ℝ), (∀ v, ‖⟪B.w v, B.σ v (uMat (y.1 v)) (B.w v)⟫_ℂ‖ ≤ c v) → ‖phe B d y‖ ≤ (∏ v, d v) * (B.e 1).re * ∏ v, c v`. Introduce `y c hc`.

Establish `h1 : ∏ v, ‖⟪B.w v, B.σ v (uMat (y.1 v)) (B.w v)⟫_ℂ‖ ≤ ∏ v, c v` using `Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => hc v`. Establish `h0 : 0 ≤ ∏ v, c v` using `(Finset.prod_nonneg fun v _ => norm_nonneg _).trans h1`. Unfold `phe ph`. Rewrite using `[norm_mul, norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_of_nonneg hd, mul_right_comm]`. Conclude with `mul_le_mul (mul_le_mul_of_nonneg_left (hle _) hd) h1 (Finset.prod_nonneg fun v _ => norm_nonneg _) (mul_nonneg hd hre)`.

Use `⟨fun _ y => key y _ fun v => ?_, fun y => ?_, ?_, him, hre, fun y hy => ?_, fun v g => ?_⟩` and prove the remaining obligations. Use `(hdec v (y.1 v)).1` as an intermediate fact. Rewrite `this` using `[hw, mul_one, mul_one, hrk]`. Conclude with `this`. Use `key y (fun _ => 1) fun v => by` as an intermediate fact.

Use `(norm_inner_le_norm _ _).trans ?_` and prove the remaining obligations. Rewrite using `[(hDS v).2.1.2.2.1.2.1 _ (y.1 v).2, hw, mul_one]`. Simplify using `using this`. Establish `h1 : ∀ v, ⟪B.w v, B.σ v (uMat ((1 : B.I.GA).1 v)) (B.w v)⟫_ℂ = 1` using `fun v => by`. Establish `e : uMat ((1 : B.I.GA).1 v) = 1` using `rfl`.

Rewrite using `[e, (hDS v).2.1.2.2.1.1.1]`. Simplify using `[inner_self_eq_norm_sq_to_K, hw]`. Unfold `phe ph`. Simplify using `only [h1, Finset.prod_const_one, star_one, mul_one]`. Both sides reduce to the same expression.

Conclude with `B.e_adm.2.2.2.2.1 _ (right_ne_zero_of_mul hy)`. Use `(hdec v g).2` as an intermediate fact. Rewrite `this` using `[hw, mul_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem ptBound_of_decGap : GlobalTheory.DSId.DecGap → GlobalTheory.Deep.PtBound := by
  intro hD B d p q h hDS hsig hgap hh
  obtain ⟨him, hre, hle, -⟩ := GlobalTheory.rowsAut_idem_elementary B
  have hrk : ∀ v, rkR (B.I.ε v) = min p q := fun v => by
    rw [← (hsig v).1, ← (hsig v).2]; rfl
  have hw : ∀ v, ‖B.w v‖ = 1 := fun v => (hDS v).2.2.1.1
  have hdec := fun v (g : UJ (B.I.ε v)) =>
    hD B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) (hDS v).1 (hDS v).2.1 h (hgap v)
      (by rw [hrk v]; exact hh) (uMat g) g.2 (B.w v) (hDS v).2.2.1.2 (B.w v) (hDS v).2.2.1.2
  have hd : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hDS v).2.2.2.1.le
  have key : ∀ (y : B.I.GA) (c : InfinitePlace B.I.F → ℝ),
      (∀ v, ‖⟪B.w v, B.σ v (uMat (y.1 v)) (B.w v)⟫_ℂ‖ ≤ c v) →
      ‖phe B d y‖ ≤ (∏ v, d v) * (B.e 1).re * ∏ v, c v := by
    intro y c hc
    have h1 : ∏ v, ‖⟪B.w v, B.σ v (uMat (y.1 v)) (B.w v)⟫_ℂ‖ ≤ ∏ v, c v :=
      Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => hc v
    have h0 : 0 ≤ ∏ v, c v := (Finset.prod_nonneg fun v _ => norm_nonneg _).trans h1
    unfold phe ph
    rw [norm_mul, norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_of_nonneg hd, mul_right_comm]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hle _) hd) h1
      (Finset.prod_nonneg fun v _ => norm_nonneg _) (mul_nonneg hd hre)
  refine ⟨fun _ y => key y _ fun v => ?_, fun y => ?_, ?_, him, hre, fun y hy => ?_, fun v g => ?_⟩
  · have := (hdec v (y.1 v)).1
    rw [hw, mul_one, mul_one, hrk] at this
    exact this
  · have := key y (fun _ => 1) fun v => by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [(hDS v).2.1.2.2.1.2.1 _ (y.1 v).2, hw, mul_one]
    simpa using this
  · have h1 : ∀ v, ⟪B.w v, B.σ v (uMat ((1 : B.I.GA).1 v)) (B.w v)⟫_ℂ = 1 := fun v => by
      have e : uMat ((1 : B.I.GA).1 v) = 1 := rfl
      rw [e, (hDS v).2.1.2.2.1.1.1]
      simp [inner_self_eq_norm_sq_to_K, hw]
    unfold phe ph
    simp only [h1, Finset.prod_const_one, star_one, mul_one]
    rfl
  · exact B.e_adm.2.2.2.2.1 _ (right_ne_zero_of_mul hy)
  · have := (hdec v g).2
    rwa [hw, mul_one, mul_one] at this

end GlobalTheory.Deep
