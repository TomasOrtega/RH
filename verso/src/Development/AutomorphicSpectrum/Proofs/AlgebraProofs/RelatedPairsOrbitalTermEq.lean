import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.ProjEig

open Module NumberField

section

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `h : ∀ l, Algebra.trace ℚ E (dualInt E k * integralBasis E l) = if l = k then 1 else 0`. Introduce `l`. Use `LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E) (traceForm_nondegenerate ℚ E) (integralBasis E) k l` as an intermediate fact. Rewrite `this` using `[Algebra.traceForm_apply]`. Unfold `dualInt`.

Use `this` and compare the differences between its conclusion and the goal. Use `conv_lhs => rw [← (integralBasis E).sum_repr x]`. Simplify using `only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, h]`. Simplify using the standard rewrite rules.
-/
theorem trace_dualInt_mul (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x : E) :
    Algebra.trace ℚ E (dualInt E k * x) = (integralBasis E).repr x k := by
  classical
  have h : ∀ l, Algebra.trace ℚ E (dualInt E k * integralBasis E l) = if l = k then 1 else 0 := by
    intro l
    have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E)
      (traceForm_nondegenerate ℚ E) (integralBasis E) k l
    rw [Algebra.traceForm_apply] at this
    unfold dualInt
    convert this
  conv_lhs => rw [← (integralBasis E).sum_repr x]
  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, h]
  simp

/- English proof (translation)
Establish `h` using `((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)).sum_repr ((a : E) * dualInt E l)`. Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm (a : E), mul_assoc, trace_dualInt_mul, integralBasis_apply]`. Establish `: (a : E) * algebraMap (𝓞 E) E (RingOfIntegers.basis E k) = algebraMap (𝓞 E) E (a * RingOfIntegers.basis E k)` using `by simp`.

Rewrite using `[this, integralBasis_repr_apply, Algebra.smul_def]`. Simplify using `[dualInt]`.
-/
theorem mul_dualInt_eq (a : 𝓞 E) (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (a : E) * dualInt E l =
      ∑ k, (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : E) *
        dualInt E k := by
  classical
  have h := ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
    (integralBasis E)).sum_repr ((a : E) * dualInt E l)
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm (a : E),
    mul_assoc, trace_dualInt_mul, integralBasis_apply]
  have : (a : E) * algebraMap (𝓞 E) E (RingOfIntegers.basis E k)
      = algebraMap (𝓞 E) E (a * RingOfIntegers.basis E k) := by simp
  rw [this, integralBasis_repr_apply, Algebra.smul_def]
  simp [dualInt]

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `(traceForm_nondegenerate ℚ E).1 _ fun y => ?_` and prove the remaining obligations. Rewrite using `[Algebra.traceForm_apply, sub_mul, map_sub, one_mul, Finset.sum_mul, map_sum, Algebra.trace_eq_matrix_trace (integralBasis E) y, sub_eq_zero, Matrix.trace]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, trace_dualInt_mul, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, integralBasis_apply, mul_comm y]`.
-/
theorem sum_dualInt_mul :
    ∑ k, dualInt E k * ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
  classical
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate ℚ E).1 _ fun y => ?_
  rw [Algebra.traceForm_apply, sub_mul, map_sub, one_mul, Finset.sum_mul, map_sum,
    Algebra.trace_eq_matrix_trace (integralBasis E) y, sub_eq_zero, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, trace_dualInt_mul, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    integralBasis_apply, mul_comm y]

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

/- English proof (translation)
Simplify using `[eigSp, Submodule.mem_iInf, sub_eq_zero]`.
-/
theorem mem_eigSp_iff_apply (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (x : V) :
    x ∈ eigSp ρ σ ↔ ∀ a : 𝓞 E, ρ a x = σ (a : E) • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

/- English proof (translation)
Unfold `eigProj`. Rewrite using `[Finset.mul_sum, Finset.smul_sum]`. Establish `h1 : ∀ k, ρ a * (σ (dualInt E k) • ρ (RingOfIntegers.basis E k)) = ∑ l, (σ (dualInt E k) * (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : K)) • ρ (RingOfIntegers.basis E l)`. Introduce `k`. Rewrite using `[mul_smul_comm, ← map_mul]`.

Use `conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E k)]`. Rewrite using `[map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, mul_smul, Int.cast_smul_eq_zsmul]`. Repeatedly rewrite using `[h1]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← map_mul, mul_dualInt_eq, map_sum, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul σ, map_intCast, mul_comm]`.
-/
theorem rho_mul_eigProj (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (a : 𝓞 E) :
    ρ a * eigProj ρ σ = σ (a : E) • eigProj ρ σ := by
  classical
  unfold eigProj
  rw [Finset.mul_sum, Finset.smul_sum]
  have h1 : ∀ k, ρ a * (σ (dualInt E k) • ρ (RingOfIntegers.basis E k)) =
      ∑ l, (σ (dualInt E k) *
        (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : K)) •
          ρ (RingOfIntegers.basis E l) := by
    intro k
    rw [mul_smul_comm, ← map_mul]
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E k)]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, mul_smul, Int.cast_smul_eq_zsmul]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul, ← map_mul, mul_dualInt_eq, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul σ, map_intCast, mul_comm]

/- English proof (translation)
Unfold `eigProj`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, smul_mul_assoc, ← map_mul, ← map_mul, mul_comm]`.
-/
theorem eigProj_mul_rho_comm (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (a : 𝓞 E) :
    eigProj ρ σ * ρ a = ρ a * eigProj ρ σ := by
  unfold eigProj
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← map_mul, ← map_mul, mul_comm]

end

/- English proof (translation)
Introduce `K _ _ V _ _ E _ _ ρ σ`. Use `⟨fun x => ?_, fun x hx => ?_, fun σ' hσ x hx => ?_, eigProj_mul_rho_comm ρ σ⟩` and prove the remaining obligations. Rewrite using `[mem_eigSp_iff_apply]`. Introduce `a`. Rewrite using `[← Module.End.mul_apply, rho_mul_eigProj, LinearMap.smul_apply]`.

Rewrite `hx` using `[mem_eigSp_iff_apply]`. Unfold `eigProj`. Rewrite using `[LinearMap.sum_apply]`. Repeatedly rewrite using `[LinearMap.smul_apply, hx, smul_smul, ← map_mul]`. Rewrite using `[← Finset.sum_smul, ← map_sum, sum_dualInt_mul, map_one, one_smul]`.

Rewrite `hx` using `[mem_eigSp_iff_apply]`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a : 𝓞 E, σ' (a : E) ≠ σ (a : E) := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hσ (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hcon))`.

Establish `h1 : eigProj ρ σ (ρ a x) = ρ a (eigProj ρ σ x)`. Rewrite using `[← Module.End.mul_apply, eigProj_mul_rho_comm, Module.End.mul_apply]`. Rewrite `h1` using `[← Module.End.mul_apply (ρ a), rho_mul_eigProj, LinearMap.smul_apply, hx, map_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero]`. Conclude with `h1.resolve_left (sub_ne_zero.mpr ha)`.
-/
theorem eigProj_spec : ∀ (K : Type) [Field K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V]
    (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K),
    (∀ x, eigProj ρ σ x ∈ eigSp ρ σ) ∧ (∀ x ∈ eigSp ρ σ, eigProj ρ σ x = x) ∧
    (∀ σ' : E →+* K, σ' ≠ σ → ∀ x ∈ eigSp ρ σ', eigProj ρ σ x = 0) ∧
    ∀ a : 𝓞 E, eigProj ρ σ * ρ a = ρ a * eigProj ρ σ := by
  intro K _ _ V _ _ E _ _ ρ σ
  refine ⟨fun x => ?_, fun x hx => ?_, fun σ' hσ x hx => ?_, eigProj_mul_rho_comm ρ σ⟩
  · rw [mem_eigSp_iff_apply]
    intro a
    rw [← Module.End.mul_apply, rho_mul_eigProj, LinearMap.smul_apply]
  · rw [mem_eigSp_iff_apply] at hx
    unfold eigProj
    rw [LinearMap.sum_apply]
    simp_rw [LinearMap.smul_apply, hx, smul_smul, ← map_mul]
    rw [← Finset.sum_smul, ← map_sum, sum_dualInt_mul, map_one, one_smul]
  · rw [mem_eigSp_iff_apply] at hx
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, σ' (a : E) ≠ σ (a : E) := by
      by_contra hcon
      push Not at hcon
      exact hσ (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hcon))
    have h1 : eigProj ρ σ (ρ a x) = ρ a (eigProj ρ σ x) := by
      rw [← Module.End.mul_apply, eigProj_mul_rho_comm, Module.End.mul_apply]
    rw [← Module.End.mul_apply (ρ a), rho_mul_eigProj, LinearMap.smul_apply, hx, map_smul,
      ← sub_eq_zero, ← sub_smul, smul_eq_zero] at h1
    exact h1.resolve_left (sub_ne_zero.mpr ha)

end GlobalTheory.CompanionTheory.Ar.HT.ProjEig
