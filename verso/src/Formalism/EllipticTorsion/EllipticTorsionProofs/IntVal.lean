import Formalism.EllipticTorsion.Statement

noncomputable section

namespace Formalism.ELL.IntegerValuedContinuity

/- English proof (translation)
Establish `h1 : Continuous (algebraMap ℚ_[p] K)`. Establish `: (⇑(algebraMap ℚ_[p] K)) = fun c => c • (1 : K)`. Use function extensionality and compare the values at `c`. Conclude with `Algebra.algebraMap_eq_smul_one c`. Rewrite using `[this]`.

Conclude with `continuous_id.smul continuous_const`. Establish `h2 : Continuous (fun b : ℤ_[p] => (b : ℚ_[p]))` using `continuous_subtype_val`. Conclude with `(P.continuous).comp (h1.comp h2)`.
-/
theorem continuous_eval {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K]
    [NormedAlgebra ℚ_[p] K] (P : Polynomial K) :
    Continuous fun b : ℤ_[p] => P.eval (algebraMap ℚ_[p] K (b : ℚ_[p])) := by
  have h1 : Continuous (algebraMap ℚ_[p] K) := by
    have : (⇑(algebraMap ℚ_[p] K)) = fun c => c • (1 : K) := by
      funext c; exact Algebra.algebraMap_eq_smul_one c
    rw [this]; exact continuous_id.smul continuous_const
  have h2 : Continuous (fun b : ℤ_[p] => (b : ℚ_[p])) := continuous_subtype_val
  exact (P.continuous).comp (h1.comp h2)

end Formalism.ELL.IntegerValuedContinuity

namespace Formalism.ELL

/- English proof (translation)
Introduce `p _ K _ _ P hP b`. Establish `hc` using `Formalism.ELL.IntegerValuedContinuity.continuous_eval (p := p) (K := K) P`. Establish `hclosed : IsClosed {b : ℤ_[p] | ‖P.eval (algebraMap ℚ_[p] K (b : ℚ_[p]))‖ ≤ 1}` using `isClosed_le (continuous_norm.comp hc) continuous_const`. Use `PadicInt.denseRange_natCast.induction_on b hclosed ?_` and prove the remaining obligations. Introduce `n`.

Use `show ‖P.eval (algebraMap ℚ_[p] K (((n : ℤ_[p])) : ℚ_[p]))‖ ≤ 1`. Establish `: algebraMap ℚ_[p] K (((n : ℤ_[p])) : ℚ_[p]) = (n : K)`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `hP n`.
-/
theorem integer_valued_padic_integers : IntValuedZp := by
  intro p _ K _ _ P hP b
  have hc := Formalism.ELL.IntegerValuedContinuity.continuous_eval (p := p) (K := K) P
  have hclosed : IsClosed {b : ℤ_[p] | ‖P.eval (algebraMap ℚ_[p] K (b : ℚ_[p]))‖ ≤ 1} :=
    isClosed_le (continuous_norm.comp hc) continuous_const
  refine PadicInt.denseRange_natCast.induction_on b hclosed ?_
  intro n
  show ‖P.eval (algebraMap ℚ_[p] K (((n : ℤ_[p])) : ℚ_[p]))‖ ≤ 1
  have : algebraMap ℚ_[p] K (((n : ℤ_[p])) : ℚ_[p]) = (n : K) := by
    simp
  rw [this]; exact hP n

end Formalism.ELL
