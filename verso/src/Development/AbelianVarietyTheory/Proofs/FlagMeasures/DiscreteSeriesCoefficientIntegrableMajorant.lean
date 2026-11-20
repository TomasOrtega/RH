import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantIntegrable

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec.PhMajProof

/- English proof (translation)
Break down `hyp with h0 | hlt` into its components or cases. Establish `key : (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) = fun g : UJ ε => decE (rkR ε) 0 (dOp (uMat g)) * Real.exp (s * dOp (uMat g))`. Use function extensionality and compare the values at `g`. Rewrite using `[GlobalTheory.Count.Majorant.dOp_eq_zero ε h0 g]`. Simplify using `[decE]`.

Rewrite using `[key]`. Conclude with `GlobalTheory.Count.Majorant.majorant_integrable n ε 0 s le_rfl (Or.inl h0)`. Establish `hh : 0 ≤ h`. Establish `: 0 ≤ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε)` using `mul_nonneg (by positivity) (add_nonneg hs (by positivity))`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `GlobalTheory.Count.Majorant.majorant_integrable n ε h s hh (Or.inr hlt)`.
-/
theorem local_integrable (n : ℕ) (ε : Fin n → Bool) (h s : ℝ) (hs : 0 ≤ s)
    (hyp : rkR ε = 0 ∨ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h) :
    Integrable (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) := by
  rcases hyp with h0 | hlt
  · have key : (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) =
        fun g : UJ ε => decE (rkR ε) 0 (dOp (uMat g)) * Real.exp (s * dOp (uMat g)) := by
      funext g
      rw [GlobalTheory.Count.Majorant.dOp_eq_zero ε h0 g]
      simp [decE]
    rw [key]
    exact GlobalTheory.Count.Majorant.majorant_integrable n ε 0 s le_rfl (Or.inl h0)
  · have hh : 0 ≤ h := by
      have : 0 ≤ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) :=
        mul_nonneg (by positivity) (add_nonneg hs (by positivity))
      linarith
    exact GlobalTheory.Count.Majorant.majorant_integrable n ε h s hh (Or.inr hlt)

/- English proof (translation)
Introduce `B d h hds hloc`. Establish `hd : ∀ v, 0 < d v` using `fun v => (hds v).2.2.2.1`. Establish `hdp : 0 ≤ ∏ v, d v` using `Finset.prod_nonneg fun v _ => (hd v).le`. Establish `hcont : ∀ v, Continuous fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v)`. Introduce `v`.

Establish `hon` using `(hds v).2.1.2.2.1.2.2 (B.w v)`. Use `hon.comp_continuous ?_ ?_` and prove the remaining obligations. Unfold `uMat`. Conclude with `(Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)`. Introduce `g`.

Conclude with `(g v).2`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `ph`. Conclude with `continuous_const.mul (continuous_star.comp (continuous_finsetProd _ fun v _ => continuous_const.inner (hcont v)))`. Introduce `g`.

Unfold `ph majPh`. Rewrite using `[norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_of_nonneg hdp]`. Conclude with `mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => hloc v (g v)) hdp`. Introduce `s hs hyp`. Establish `key : (fun g => majPh B d h g * Real.exp (s * dSum B.I g)) = fun g : B.I.Ginf => (∏ v, d v) * ∏ v, (decE (rkR (B.I.ε v)) h (dOp (uMat (g v))) * Real.exp (s * dOp (uMat (g v))))`.

Use function extensionality and compare the values at `g`. Unfold `majPh dSum`. Rewrite using `[Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Unfold `muInf`. Establish `hprod : Integrable (fun x : (∀ v, UJ (B.I.ε v)) => ∏ v, (decE (rkR (B.I.ε v)) h (dOp (uMat (x v))) * Real.exp (s * dOp (uMat (x v))))) (Measure.pi fun v => muG (B.I.ε v))` using `Integrable.fintype_prod_dep fun v => local_integrable B.I.n (B.I.ε v) h s hs (hyp v)`. Conclude with `hprod.const_mul _`.
-/
theorem phMaj : PhMaj := by
  intro B d h hds hloc
  have hd : ∀ v, 0 < d v := fun v => (hds v).2.2.2.1
  have hdp : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hd v).le
  have hcont : ∀ v, Continuous fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v) := by
    intro v
    have hon := (hds v).2.1.2.2.1.2.2 (B.w v)
    refine hon.comp_continuous ?_ ?_
    · unfold uMat
      exact (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)
    · intro g
      exact (g v).2
  refine ⟨?_, ?_, ?_⟩
  · unfold ph
    exact continuous_const.mul (continuous_star.comp
      (continuous_finsetProd _ fun v _ => continuous_const.inner (hcont v)))
  · intro g
    unfold ph majPh
    rw [norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_of_nonneg hdp]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => hloc v (g v)) hdp
  · intro s hs hyp
    have key : (fun g => majPh B d h g * Real.exp (s * dSum B.I g)) = fun g : B.I.Ginf =>
        (∏ v, d v) * ∏ v, (decE (rkR (B.I.ε v)) h (dOp (uMat (g v))) * Real.exp (s * dOp (uMat (g v)))) := by
      funext g
      unfold majPh dSum
      rw [Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]
      ring
    rw [key]
    unfold muInf
    have hprod : Integrable (fun x : (∀ v, UJ (B.I.ε v)) => ∏ v,
        (decE (rkR (B.I.ε v)) h (dOp (uMat (x v))) * Real.exp (s * dOp (uMat (x v)))))
        (Measure.pi fun v => muG (B.I.ε v)) :=
      Integrable.fintype_prod_dep fun v => local_integrable B.I.n (B.I.ε v) h s hs (hyp v)
    exact hprod.const_mul _

end GlobalTheory.Dec.PhMajProof
