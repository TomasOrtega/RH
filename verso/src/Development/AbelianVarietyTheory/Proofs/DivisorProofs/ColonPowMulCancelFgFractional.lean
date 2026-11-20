import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets
open NumberField

namespace GlobalTheory.ColonPowCancel

/- English proof (translation)
Set `I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K` to `⟨𝔟, FractionalIdeal.isFractional_of_fg hfg⟩`. Establish `hI : I ≠ 0`. Introduce `h`. Apply `h0` to reduce the goal to its premises. Establish `: (I : Submodule (𝓞 K) K) = ((0 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K)` using `by rw [h]`.

Rewrite `this` using `[FractionalIdeal.coe_zero]`. Conclude with `this`. Use `⟨((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K), ?_⟩` and prove the remaining obligations. Establish `h1 : I⁻¹ * I = 1` using `inv_mul_cancel₀ hI`. Establish `h2` using `congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K => (J : Submodule (𝓞 K) K)) h1`.

Simplify using `only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one] at h2`. Conclude with `h2`.
-/
theorem exists_inv {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K)
    (hfg : 𝔟.FG) (h0 : 𝔟 ≠ ⊥) : ∃ 𝔠 : Submodule (𝓞 K) K, 𝔠 * 𝔟 = 1 := by
  let I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    ⟨𝔟, FractionalIdeal.isFractional_of_fg hfg⟩
  have hI : I ≠ 0 := by
    intro h
    apply h0
    have : (I : Submodule (𝓞 K) K) = ((0 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) := by rw [h]
    rw [FractionalIdeal.coe_zero] at this
    exact this
  refine ⟨((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K), ?_⟩
  have h1 : I⁻¹ * I = 1 := inv_mul_cancel₀ hI
  have h2 := congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K => (J : Submodule (𝓞 K) K)) h1
  simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one] at h2
  exact h2

/- English proof (translation)
Rewrite using `[Submodule.mem_colon]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[Submodule.mul_le]`. Introduce `m hm a ha`.

Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hm`. Rewrite using `[smul_mul_assoc, ← Algebra.smul_def]`. Conclude with `N.smul_mem c (h a ha)`. Introduce `h a ha`. Rewrite using `[Algebra.smul_def]`.

Conclude with `h (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) ha)`.
-/
theorem mem_colon_iff {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    (N A : Submodule R K) (r : R) :
    r ∈ N.colon (A : Set K) ↔ Submodule.span R {algebraMap R K r} * A ≤ N := by
  rw [Submodule.mem_colon]
  constructor
  · intro h
    rw [Submodule.mul_le]
    intro m hm a ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
    rw [smul_mul_assoc, ← Algebra.smul_def]
    exact N.smul_mem c (h a ha)
  · intro h a ha
    rw [Algebra.smul_def]
    exact h (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) ha)

/- English proof (translation)
Take `⟨𝔠, hc⟩` from `exists_inv 𝔟 hfg h0`. Establish `hp : 𝔠 ^ p * 𝔟 ^ p = 1` using `by rw [← mul_pow, hc, one_pow]`. Use extensionality with `r`. Rewrite using `[mem_colon_iff, mem_colon_iff, mul_left_comm]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h' : 𝔠 ^ p * (𝔟 ^ p * (Submodule.span (𝓞 K) {algebraMap (𝓞 K) K r} * A)) ≤ 𝔠 ^ p * (𝔟 ^ p * N)` using `by gcongr`. Rewrite `h'` using `[← mul_assoc, ← mul_assoc (𝔠 ^ p), hp, one_mul, one_mul]`. Then use the resulting hypothesis. Introduce `h gcongr`.
-/
theorem colon_pow_mul_cancel {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K)
    (hfg : 𝔟.FG) (h0 : 𝔟 ≠ ⊥) (p : ℕ) (A N : Submodule (𝓞 K) K) :
    (𝔟 ^ p * N).colon ((𝔟 ^ p * A : Submodule (𝓞 K) K) : Set K) = N.colon (A : Set K) := by
  obtain ⟨𝔠, hc⟩ := exists_inv 𝔟 hfg h0
  have hp : 𝔠 ^ p * 𝔟 ^ p = 1 := by rw [← mul_pow, hc, one_pow]
  ext r
  rw [mem_colon_iff, mem_colon_iff, mul_left_comm]
  constructor
  · intro h
    have h' : 𝔠 ^ p * (𝔟 ^ p * (Submodule.span (𝓞 K) {algebraMap (𝓞 K) K r} * A))
        ≤ 𝔠 ^ p * (𝔟 ^ p * N) := by gcongr
    rwa [← mul_assoc, ← mul_assoc (𝔠 ^ p), hp, one_mul, one_mul] at h'
  · intro h
    gcongr

end GlobalTheory.ColonPowCancel
