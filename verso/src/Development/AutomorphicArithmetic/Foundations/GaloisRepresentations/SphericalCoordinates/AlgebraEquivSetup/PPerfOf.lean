import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Set `g : E →ₗ[ℚ] ℚ` to `(integralBasis E).constr ℚ (fun i => ((f (RingOfIntegers.basis E i) : ℤ) : ℚ))`. Establish `hg : ∀ y : 𝓞 E, g (y : E) = ((f y : ℤ) : ℚ)`. Establish `hext : ((g.restrictScalars ℤ).comp ((Algebra.linearMap (𝓞 E) E).restrictScalars ℤ)) = (Algebra.linearMap ℤ ℚ).comp f`. Use `(RingOfIntegers.basis E).ext fun i => ?_` and prove the remaining obligations. Simplify using `[g, ← integralBasis_apply]`.

Introduce `y`. Simplify using `using LinearMap.congr_fun hext y`. Establish `hnd : (Algebra.traceForm ℚ E).Nondegenerate` using `traceForm_nondegenerate ℚ E`. Use `⟨(LinearMap.BilinForm.toDual (Algebra.traceForm ℚ E) hnd).symm g, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[← Algebra.traceForm_apply, ← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]`.

Conclude with `hg y`.
-/
private theorem exists_trace_rep (E : Type) [Field E] [NumberField E] (f : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ z : E, ∀ y : 𝓞 E, Algebra.trace ℚ E (z * (y : E)) = ((f y : ℤ) : ℚ) := by
  let g : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ (fun i => ((f (RingOfIntegers.basis E i) : ℤ) : ℚ))
  have hg : ∀ y : 𝓞 E, g (y : E) = ((f y : ℤ) : ℚ) := by
    have hext : ((g.restrictScalars ℤ).comp ((Algebra.linearMap (𝓞 E) E).restrictScalars ℤ)) =
        (Algebra.linearMap ℤ ℚ).comp f := by
      refine (RingOfIntegers.basis E).ext fun i => ?_
      simp [g, ← integralBasis_apply]
    intro y
    simpa using LinearMap.congr_fun hext y
  have hnd : (Algebra.traceForm ℚ E).Nondegenerate := traceForm_nondegenerate ℚ E
  refine ⟨(LinearMap.BilinForm.toDual (Algebra.traceForm ℚ E) hnd).symm g, fun y => ?_⟩
  rw [← Algebra.traceForm_apply, ← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]
  exact hg y

/- English proof (translation)
Introduce `E _ _ _ A M hgen hc q hq`. Take `⟨_, e1, he1, hz⟩` from `hgen`. Take `⟨e2, he2, c', hc'⟩` from `hc`. Use `⟨e1 * e2, Nat.Coprime.mul (he1.coprime_dvd_right hq) (he2.coprime_dvd_right hq), ?_, ⟨c' * e1, ?_⟩⟩` and prove the remaining obligations. Introduce `f`.

Take `⟨z, hzf⟩` from `exists_trace_rep E f`. Establish `hzc : InCodiff z` using `fun y => ⟨f y, hzf y⟩`. Take `⟨x, hx⟩` from `hz z hzc`. Use `⟨(e2 : 𝓞 E) * x, fun y => ?_⟩` and prove the remaining obligations. Establish `h` using `A.trd_spec ((e2 : 𝓞 E) * x * y)`.

Establish `hmul : A.δ * ((((e2 : 𝓞 E) * x * y : 𝓞 E)) : E) = ((e1 * e2 : ℕ) : ℚ) • (z * (y : E))`. Rewrite using `[Algebra.smul_def, map_natCast]`. Use `push_cast`. Take the linear combination `(-((e2 : E) * (y : E))) * hx`. Establish `hq' : ((A.trd ((e2 : 𝓞 E) * x * y) : ℤ) : ℚ) = (((e1 * e2 : ℕ) : ℤ) : ℚ) * ((f y : ℤ) : ℚ)`.

Rewrite using `[h, hmul, map_smul, hzf, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `hq'` after adjusting the coercions. Rewrite using `[← mul_assoc, hc']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Gal.W2.Seed.pPerfOf :
    PerfOf := by
  intro E _ _ _ A M hgen hc q hq
  obtain ⟨_, e1, he1, hz⟩ := hgen
  obtain ⟨e2, he2, c', hc'⟩ := hc
  refine ⟨e1 * e2, Nat.Coprime.mul (he1.coprime_dvd_right hq) (he2.coprime_dvd_right hq), ?_, ⟨c' * e1, ?_⟩⟩
  · intro f
    obtain ⟨z, hzf⟩ := exists_trace_rep E f
    have hzc : InCodiff z := fun y => ⟨f y, hzf y⟩
    obtain ⟨x, hx⟩ := hz z hzc
    refine ⟨(e2 : 𝓞 E) * x, fun y => ?_⟩
    have h := A.trd_spec ((e2 : 𝓞 E) * x * y)
    have hmul : A.δ * ((((e2 : 𝓞 E) * x * y : 𝓞 E)) : E) = ((e1 * e2 : ℕ) : ℚ) • (z * (y : E)) := by
      rw [Algebra.smul_def, map_natCast]
      push_cast
      linear_combination (-((e2 : E) * (y : E))) * hx
    have hq' : ((A.trd ((e2 : 𝓞 E) * x * y) : ℤ) : ℚ) = (((e1 * e2 : ℕ) : ℤ) : ℚ) * ((f y : ℤ) : ℚ) := by
      rw [h, hmul, map_smul, hzf, smul_eq_mul]
      push_cast; ring
    exact_mod_cast hq'
  · rw [← mul_assoc, hc']
    push_cast
    ring
