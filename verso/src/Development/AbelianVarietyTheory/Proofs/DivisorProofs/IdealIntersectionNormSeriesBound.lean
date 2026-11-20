import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.RegroupDenom

/- English proof (translation)
Use `show x ∈ ((A ⊓ B : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) ↔ _`. Rewrite using `[FractionalIdeal.coe_inf, Submodule.mem_inf]`. Both sides reduce to the same expression.
-/
theorem mem_inf_frac {K : Type} [Field K] [NumberField K]
    {A B : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} {x : K} :
    x ∈ A ⊓ B ↔ x ∈ A ∧ x ∈ B := by
  show x ∈ ((A ⊓ B : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) ↔ _
  rw [FractionalIdeal.coe_inf, Submodule.mem_inf]
  rfl

/- English proof (translation)
Introduce `K _ _ A B hA hB t g`. Establish `hJne : ∀ c : K, c ≠ 0 → B ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c⁻¹ * A ≠ 0`. Introduce `c hc`. Take `⟨x, hx0, hxI⟩` from `FractionalIdeal.exists_ne_zero_mem_isInteger hB`. Establish `h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c⁻¹ * A ≠ 0`.

Use `mul_ne_zero ?_ hA` and prove the remaining obligations. Simplify `hc` using `[FractionalIdeal.spanSingleton_eq_zero_iff]`. Take `⟨y, hy0, hyI⟩` from `FractionalIdeal.exists_ne_zero_mem_isInteger h2`. Introduce `hz`. Establish `hmem : algebraMap (𝓞 K) K x * algebraMap (𝓞 K) K y ∈ B ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c⁻¹ * A`.

Rewrite using `[mem_inf_frac]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[mul_comm, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ y hxI`. Rewrite using `[← Algebra.smul_def]`.

Conclude with `Submodule.smul_mem _ x hyI`. Rewrite `hmem` using `[hz, FractionalIdeal.mem_zero_iff]`. Simplify the hypotheses and the goal together. Establish `hcmem : ∀ c : K, c ≠ 0 → c ∈ A / (B ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c⁻¹ * A)`. Introduce `c hc`.

Rewrite using `[FractionalIdeal.mem_div_iff_of_ne_zero (hJne c hc)]`. Introduce `y hy`. Rewrite `hy` using `[mem_inf_frac]`. Take `⟨z, hz, rfl⟩` from `(FractionalIdeal.mem_singleton_mul).1 hy.2`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hc, one_mul]`.

Conclude with `hz`. Set `F : {c : K // c ≠ 0} → (Σ J : {J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K // J ≠ 0 ∧ J ≤ B}, {c : K // c ∈ A / (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)})` to `fun c => ⟨⟨_, hJne c.1 c.2, inf_le_left⟩, ⟨c.1, hcmem c.1 c.2⟩⟩`. Establish `hF : Function.Injective F`. Introduce `a b hab`. Use `congrArg (fun p : (Σ J : {J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K // J ≠ 0 ∧ J ≤ B}, {c : K // c ∈ A / (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)}) => (p.2 : K)) hab` as an intermediate fact.

Conclude with `Subtype.ext this`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.tsum_sigma']`. Use `congr 1`. Use function extensionality and compare the values at `J`.

Use `show ∑' b : {c : K // c ∈ A / (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)}, ENNReal.ofReal ((FractionalIdeal.absNorm (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) ^ (-t)) * g b = _`. Rewrite using `[ENNReal.tsum_mul_left]`.
-/
theorem tsum_regroup_by_denominator_le : ∀ (K : Type) [Field K] [NumberField K] (I₀ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), I₀ ≠ 0 → I ≠ 0 →
    ∀ (t : ℝ) (g : K → ENNReal),
    ∑' c : {c : K // c ≠ 0}, ENNReal.ofReal ((FractionalIdeal.absNorm
        (I ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (c : K)⁻¹ * I₀) : ℝ) ^ (-t)) * g c ≤
      ∑' J : {J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K // J ≠ 0 ∧ J ≤ I},
        ENNReal.ofReal ((FractionalIdeal.absNorm (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) ^ (-t)) *
          ∑' c : {c : K // c ∈ I₀ / (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)}, g c := by
  intro K _ _ A B hA hB t g
  classical
  have hJne : ∀ c : K, c ≠ 0 →
      B ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c⁻¹ * A ≠ 0 := by
    intro c hc
    obtain ⟨x, hx0, hxI⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hB
    have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c⁻¹ * A ≠ 0 := by
      refine mul_ne_zero ?_ hA
      simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hc
    obtain ⟨y, hy0, hyI⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger h2
    intro hz
    have hmem : algebraMap (𝓞 K) K x * algebraMap (𝓞 K) K y ∈
        B ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c⁻¹ * A := by
      rw [mem_inf_frac]
      constructor
      · rw [mul_comm, ← Algebra.smul_def]
        exact Submodule.smul_mem _ y hxI
      · rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ x hyI
    rw [hz, FractionalIdeal.mem_zero_iff] at hmem
    simp_all
  have hcmem : ∀ c : K, c ≠ 0 →
      c ∈ A / (B ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c⁻¹ * A) := by
    intro c hc
    rw [FractionalIdeal.mem_div_iff_of_ne_zero (hJne c hc)]
    intro y hy
    rw [mem_inf_frac] at hy
    obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_singleton_mul).1 hy.2
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    exact hz
  let F : {c : K // c ≠ 0} → (Σ J : {J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K // J ≠ 0 ∧ J ≤ B},
      {c : K // c ∈ A / (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)}) := fun c =>
    ⟨⟨_, hJne c.1 c.2, inf_le_left⟩, ⟨c.1, hcmem c.1 c.2⟩⟩
  have hF : Function.Injective F := by
    intro a b hab
    have := congrArg (fun p : (Σ J : {J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K // J ≠ 0 ∧ J ≤ B},
      {c : K // c ∈ A / (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)}) => (p.2 : K)) hab
    exact Subtype.ext this
  calc _ = ∑' c : {c : K // c ≠ 0}, (fun p : (Σ J : {J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K // J ≠ 0 ∧ J ≤ B},
      {c : K // c ∈ A / (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)}) =>
        ENNReal.ofReal ((FractionalIdeal.absNorm (p.1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) ^ (-t)) *
          g p.2) (F c) := rfl
    _ ≤ ∑' p : (Σ J : {J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K // J ≠ 0 ∧ J ≤ B},
      {c : K // c ∈ A / (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)}),
        ENNReal.ofReal ((FractionalIdeal.absNorm (p.1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) ^ (-t)) *
          g p.2 := ENNReal.tsum_comp_le_tsum_of_injective hF _
    _ = _ := by
      rw [ENNReal.tsum_sigma']
      congr 1
      funext J
      show ∑' b : {c : K // c ∈ A / (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)},
          ENNReal.ofReal ((FractionalIdeal.absNorm (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) ^ (-t)) *
            g b = _
      rw [ENNReal.tsum_mul_left]

end GlobalTheory.RegroupDenom
