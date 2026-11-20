import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlockGLSupportedMemMirabolicSupported
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi

/- English proof (translation)
Establish `hcoe : embOf s (H.rt : E) = s H.rt` using `IsFractionRing.lift_algebraMap (intEmb_injective s) H.rt`. Establish `hw : (s H.rt) ^ 2 = -(H.d : ℂ)`. Establish `h` using `congrArg s H.rt_sq`. Simplify `h` using `[map_pow, map_neg, map_natCast]`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`.

Establish `hr0 : 0 < Real.sqrt H.d` using `Real.sqrt_pos.2 hd`. Establish `hrC : ((Real.sqrt H.d : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hr0.ne'`. Establish `hmC : (m : ℂ) ≠ 0` using `by exact_mod_cast hm`. Establish `hr2 : ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 = (H.d : ℂ)`. Establish `h` using `Real.sq_sqrt hd.le`.

Conclude with `h` after adjusting the coercions. Establish `hfac : (s H.rt - Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) * (s H.rt + Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) = 0`. Establish `: (s H.rt - Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) * (s H.rt + Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) = (s H.rt) ^ 2 - Complex.I ^ 2 * ((Real.sqrt H.d : ℝ) : ℂ) ^ 2` using `by ring`. Rewrite using `[this, hw, hr2, Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hval : embOf s (((m : E) * (H.rt : E))⁻¹) = ((m : ℂ) * s H.rt)⁻¹`. Rewrite using `[map_inv₀, map_mul, map_natCast, hcoe]`. Break down `mul_eq_zero.1 hfac with h | h` into its components or cases. Use `⟨-1, by norm_num, ?_⟩` and prove the remaining obligations. Establish `hw' : s H.rt = Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)` using `sub_eq_zero.1 h`.

Rewrite using `[hval, hw']`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Complex.I_sq]`. Evaluate the numerical expressions.

Use `⟨1, by norm_num, ?_⟩` and prove the remaining obligations. Establish `hw' : s H.rt = -(Complex.I * ((Real.sqrt H.d : ℝ) : ℂ))` using `eq_neg_of_add_eq_zero_left h`. Rewrite using `[hval, hw']`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[Complex.I_sq]`.
-/
theorem conj_inv_mul_rt (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (s : 𝓞 E →+* ℂ) (m : ℕ)
    (hm : m ≠ 0) : ∃ ε : ℝ, ε ^ 2 = 1 ∧ embOf s (((m : E) * (H.rt : E))⁻¹) =
      Complex.I * (((1 / ((m : ℝ) * Real.sqrt H.d)) * ε : ℝ) : ℂ) := by
  have hcoe : embOf s (H.rt : E) = s H.rt := IsFractionRing.lift_algebraMap (intEmb_injective s) H.rt
  have hw : (s H.rt) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg s H.rt_sq
    simpa [map_pow, map_neg, map_natCast] using h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hr0 : 0 < Real.sqrt H.d := Real.sqrt_pos.2 hd
  have hrC : ((Real.sqrt H.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hr2 : ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 = (H.d : ℂ) := by
    have h := Real.sq_sqrt hd.le
    exact_mod_cast h
  have hfac : (s H.rt - Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) *
      (s H.rt + Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) = 0 := by
    have : (s H.rt - Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) *
        (s H.rt + Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) =
        (s H.rt) ^ 2 - Complex.I ^ 2 * ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 := by ring
    rw [this, hw, hr2, Complex.I_sq]; ring
  have hval : embOf s (((m : E) * (H.rt : E))⁻¹) = ((m : ℂ) * s H.rt)⁻¹ := by
    rw [map_inv₀, map_mul, map_natCast, hcoe]
  rcases mul_eq_zero.1 hfac with h | h
  · refine ⟨-1, by norm_num, ?_⟩
    have hw' : s H.rt = Complex.I * ((Real.sqrt H.d : ℝ) : ℂ) := sub_eq_zero.1 h
    rw [hval, hw']
    push_cast
    field_simp
    rw [Complex.I_sq]
    norm_num
  · refine ⟨1, by norm_num, ?_⟩
    have hw' : s H.rt = -(Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) := eq_neg_of_add_eq_zero_left h
    rw [hval, hw']
    push_cast
    field_simp
    rw [Complex.I_sq]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi
