import Mathlib
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct

noncomputable section

namespace AdeleBaseChange

open SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
Use `open ValuativeRel in`. Establish `hint : IsIntegral 𝒪[v.adicCompletion K] y` using `isIntegral_of_mem_integer v w ((mem_valuationInteger_iff w y).2 hy)`. Establish `htr : IsIntegral 𝒪[v.adicCompletion K] (Algebra.trace (v.adicCompletion K) (w.adicCompletion L) y)` using `Algebra.isIntegral_trace hint`. Conclude with `(mem_valuationInteger_iff v _).1 ((Valuation.integer.integers (ValuativeRel.valuation (v.adicCompletion K))).mem_of_integral htr)`.
-/
theorem trace_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] {y : w.adicCompletion L}
    (hy : y ∈ w.adicCompletionIntegers L) :
    Algebra.trace (v.adicCompletion K) (w.adicCompletion L) y ∈ v.adicCompletionIntegers K := by
  open ValuativeRel in
  have hint : IsIntegral 𝒪[v.adicCompletion K] y :=
    isIntegral_of_mem_integer v w ((mem_valuationInteger_iff w y).2 hy)
  have htr : IsIntegral 𝒪[v.adicCompletion K]
      (Algebra.trace (v.adicCompletion K) (w.adicCompletion L) y) :=
    Algebra.isIntegral_trace hint
  exact (mem_valuationInteger_iff v _).1 ((Valuation.integer.integers
    (ValuativeRel.valuation (v.adicCompletion K))).mem_of_integral htr)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

abbrev traceDual : Basis ι K L :=
  (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b

/- English proof (translation)
Rewrite using `[mul_comm, ← Algebra.traceForm_apply]`. Conclude with `LinearMap.BilinForm.apply_dualBasis_left _ _ i j`.
-/
theorem trace_mul_traceDual (i j : ι) :
    Algebra.trace K L (b j * traceDual b i) = if j = i then 1 else 0 := by
  rw [mul_comm, ← Algebra.traceForm_apply]
  exact LinearMap.BilinForm.apply_dualBasis_left _ _ i j

def localCoord (v : HeightOneSpectrum (𝓞 K)) (i : ι) :
    CompletionsOver L v →ₗ[v.adicCompletion K] v.adicCompletion K :=
  ((Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i).comp
    (tensorEquiv L v).symm.toLinearEquiv.toLinearMap

omit [DecidableEq ι] in

/- English proof (translation)
Establish `h` using `(Algebra.TensorProduct.basis (v.adicCompletion K) b).sum_repr ((tensorEquiv L v).symm z)`. Establish `h2` using `congrArg (tensorEquiv L v) h`. Rewrite `h2` using `[AlgEquiv.apply_symm_apply, map_sum]`. Use `conv_rhs => rw [← h2]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[Algebra.TensorProduct.basis_apply, map_smul, tensorEquiv_one_tmul, Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem sum_localCoord (v : HeightOneSpectrum (𝓞 K)) (z : CompletionsOver L v) :
    ∑ i, algebraMap (v.adicCompletion K) (CompletionsOver L v) (localCoord b v i z) *
      algebraMap L (CompletionsOver L v) (b i) = z := by
  have h := (Algebra.TensorProduct.basis (v.adicCompletion K) b).sum_repr
    ((tensorEquiv L v).symm z)
  have h2 := congrArg (tensorEquiv L v) h
  rw [AlgEquiv.apply_symm_apply, map_sum] at h2
  conv_rhs => rw [← h2]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.TensorProduct.basis_apply, map_smul, tensorEquiv_one_tmul, Algebra.smul_def]
  rfl

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Establish `: (tensorEquiv L v).symm (algebraMap L (CompletionsOver L v) l) = 1 ⊗ₜ l`. Rewrite using `[AlgEquiv.symm_apply_eq, tensorEquiv_one_tmul]`. Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i ((tensorEquiv L v).symm (algebraMap L (CompletionsOver L v) l)) = _`. Rewrite using `[this, Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]`.
-/
theorem localCoord_algebraMap (v : HeightOneSpectrum (𝓞 K)) (i : ι) (l : L) :
    localCoord b v i (algebraMap L (CompletionsOver L v) l) =
      algebraMap K (v.adicCompletion K) (b.repr l i) := by
  have : (tensorEquiv L v).symm (algebraMap L (CompletionsOver L v) l) = 1 ⊗ₜ l := by
    rw [AlgEquiv.symm_apply_eq, tensorEquiv_one_tmul]
  change (Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i
    ((tensorEquiv L v).symm (algebraMap L (CompletionsOver L v) l)) = _
  rw [this, Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul, one_smul,
    Finsupp.mapRange_apply]

/- English proof (translation)
Establish `key : (Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i = (Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)).comp (LinearMap.mulRight (v.adicCompletion K) (1 ⊗ₜ traceDual b i))`. Use `(Algebra.TensorProduct.basis (v.adicCompletion K) b).ext fun j ↦ ?_` and prove the remaining obligations. Rewrite using `[Basis.coord_apply, Basis.repr_self, LinearMap.comp_apply, LinearMap.mulRight_apply, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul, trace_mul_traceDual, Finsupp.single_apply]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`. Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i ((tensorEquiv L v).symm z) = _`. Rewrite using `[key, LinearMap.comp_apply, LinearMap.mulRight_apply, ← Algebra.trace_eq_of_algEquiv (tensorEquiv L v), map_mul, AlgEquiv.apply_symm_apply, tensorEquiv_one_tmul, trace_pi]`. Both sides reduce to the same expression.
-/
theorem localCoord_eq_sum_trace (v : HeightOneSpectrum (𝓞 K)) (i : ι) (z : CompletionsOver L v) :
    localCoord b v i z = ∑ w : PlacesOver L v, Algebra.trace (v.adicCompletion K)
      (w.1.adicCompletion L) (z w * algebraMap L (w.1.adicCompletion L) (traceDual b i)) := by
  have key : (Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i =
      (Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)).comp
        (LinearMap.mulRight (v.adicCompletion K) (1 ⊗ₜ traceDual b i)) := by
    refine (Algebra.TensorProduct.basis (v.adicCompletion K) b).ext fun j ↦ ?_
    rw [Basis.coord_apply, Basis.repr_self, LinearMap.comp_apply, LinearMap.mulRight_apply,
      Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      trace_one_tmul, trace_mul_traceDual, Finsupp.single_apply]
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  change (Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i
    ((tensorEquiv L v).symm z) = _
  rw [key, LinearMap.comp_apply, LinearMap.mulRight_apply,
    ← Algebra.trace_eq_of_algEquiv (tensorEquiv L v), map_mul, AlgEquiv.apply_symm_apply,
    tensorEquiv_one_tmul, trace_pi]
  rfl

/- English proof (translation)
Rewrite using `[localCoord_eq_sum_trace]`. Conclude with `sum_mem fun w _ ↦ trace_mem_adicCompletionIntegers v w.1 (hz w)`.
-/
theorem localCoord_mem (v : HeightOneSpectrum (𝓞 K)) (i : ι) (z : CompletionsOver L v)
    (hz : ∀ w : PlacesOver L v,
      z w * algebraMap L (w.1.adicCompletion L) (traceDual b i) ∈ w.1.adicCompletionIntegers L) :
    localCoord b v i z ∈ v.adicCompletionIntegers K := by
  rw [localCoord_eq_sum_trace]
  exact sum_mem fun w _ ↦ trace_mem_adicCompletionIntegers v w.1 (hz w)

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
The claim follows from `IsModuleTopology.continuous_of_linearMap (localCoord b v i)`.
-/
theorem continuous_localCoord (v : HeightOneSpectrum (𝓞 K)) (i : ι) :
    Continuous (localCoord b v i) :=
  IsModuleTopology.continuous_of_linearMap (localCoord b v i)

end AdeleBaseChange

end

end GroundTheory.Global
