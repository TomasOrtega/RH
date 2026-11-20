import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.KatoClassHeckeEulerFactorRelation

namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `t ht`. Establish `hb : ∀ i, IsIntegral ℤ (NumberField.integralBasis E i)`. Introduce `i`. Rewrite using `[NumberField.integralBasis_apply]`. Conclude with `(NumberField.RingOfIntegers.basis E i).isIntegral_coe`.

Establish `hx : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E)`. Rewrite using `[Submodule.mem_traceDual]`. Introduce `a ha`. Take `⟨y, rfl⟩` from `Submodule.mem_one.1 ha`. Take `⟨k, hk⟩` from `ht y`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.traceForm_apply]`. Rewrite using `[show algebraMap (𝓞 E) E y = (y : E) from rfl, hk]`. Simplify using the standard rewrite rules. Establish `h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E)` using `Submodule.mem_one.2 ⟨1, map_one _⟩`.

Establish `hI` using `isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (1 : Submodule (𝓞 E) E) hb h1 hx`. Rewrite `hI` using `[← NumberField.coe_discr, Algebra.smul_def, mul_one, map_intCast]`. Set `α : 𝓞 E` to `⟨_, hI⟩`. Establish `hα : (α : E) = (NumberField.discr E : E) * t` using `rfl`. Break down `Int.natAbs_eq (NumberField.discr E) with h | h` into its components or cases.

Use `⟨α, ?_⟩` and prove the remaining obligations. Establish `h' : ((NumberField.discr E : ℤ) : E) = (((NumberField.discr E).natAbs : ℤ) : E)` using `congrArg _ h`. Rewrite using `[hα, h', Int.cast_natCast]`. Use `⟨-α, ?_⟩` and prove the remaining obligations. Establish `h' : ((NumberField.discr E : ℤ) : E) = ((-((NumberField.discr E).natAbs : ℤ) : ℤ) : E)` using `congrArg _ h`.

Use `show -(α : E) = _`. Rewrite using `[hα, h', Int.cast_neg, Int.cast_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sDual : SDual E := by
  intro t ht
  have hb : ∀ i, IsIntegral ℤ (NumberField.integralBasis E i) := by
    intro i
    rw [NumberField.integralBasis_apply]
    exact (NumberField.RingOfIntegers.basis E i).isIntegral_coe
  have hx : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 ha
    obtain ⟨k, hk⟩ := ht y
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply]
    rw [show algebraMap (𝓞 E) E y = (y : E) from rfl, hk]
    simp
  have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have hI := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) hb h1 hx
  rw [← NumberField.coe_discr, Algebra.smul_def, mul_one, map_intCast] at hI
  let α : 𝓞 E := ⟨_, hI⟩
  have hα : (α : E) = (NumberField.discr E : E) * t := rfl
  rcases Int.natAbs_eq (NumberField.discr E) with h | h
  · refine ⟨α, ?_⟩
    have h' : ((NumberField.discr E : ℤ) : E) = (((NumberField.discr E).natAbs : ℤ) : E) :=
      congrArg _ h
    rw [hα, h', Int.cast_natCast]
  · refine ⟨-α, ?_⟩
    have h' : ((NumberField.discr E : ℤ) : E) = ((-((NumberField.discr E).natAbs : ℤ) : ℤ) : E) :=
      congrArg _ h
    show -(α : E) = _
    rw [hα, h', Int.cast_neg, Int.cast_natCast]
    ring

end UnipMove
