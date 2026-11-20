import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasicOpenEqZeroOfMemIInfPowSmul

open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[isIntegrallyClosed_iff (FractionRing R)]`. Introduce `c hc`. Take `⟨s, hs⟩` from `hcond c hc`. It suffices to establish `hmem : Ideal.Quotient.mk (Ideal.span {x}) s = 0 by`. Rewrite `hmem` using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`.

Take `⟨w, rfl⟩` from `hmem`. Use `⟨w, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (algebraMap R (FractionRing R) x)` using `IsLocalization.map_units (FractionRing R) ⟨x, hx⟩`. Apply `hu.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[← hs, map_mul, mul_comm]`.

Establish `key` using `eq_zero_of_forall_associatedPrimes_exists_smul_eq_zero (A := R) (M := R ⧸ Ideal.span {x}) (x := Ideal.Quotient.mk (Ideal.span {x}) s)`. Apply `key` to reduce the goal to its premises. Introduce `P hP`. Use `haveI hPp : P.IsPrime := hP.isPrime`. Take `⟨hdom, hic⟩` from `hloc P hP`.

Set `RP` to `Localization.AtPrime P`. Set `K` to `FractionRing RP`. Establish `hreg : ∀ b ∈ nonZeroDivisors R, IsUnit (algebraMap R K b)`. Introduce `b hb`. Rewrite using `[IsScalarTower.algebraMap_apply R RP K]`.

Use `IsLocalization.map_units K (⟨algebraMap R RP b, ?_⟩ : nonZeroDivisors RP)` and prove the remaining obligations. Use `mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ?_` and prove the remaining obligations. Take `⟨t, ht⟩` from `(IsLocalization.map_eq_zero_iff P.primeCompl RP b).1 h0`. Establish `: (t : R) = 0` using `(mem_nonZeroDivisors_iff_right.1 hb) t ht`. Conclude with `t.2 (this ▸ P.zero_mem)`.

Set `φ : FractionRing R →+* K` to `IsLocalization.lift (M := nonZeroDivisors R) (g := algebraMap R K) fun b ↦ hreg b b.2`. Establish `hφ : ∀ r : R, φ (algebraMap R (FractionRing R) r) = algebraMap RP K (algebraMap R RP r)` using `fun r ↦ by`. Rewrite using `[IsLocalization.lift_eq, IsScalarTower.algebraMap_apply R RP K]`. Establish `hint : IsIntegral RP (φ c)`. Use `IsIntegral.map_of_comp_eq (algebraMap R RP) φ ?_ hc` and prove the remaining obligations.

Use extensionality with `r`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[hφ]`. Take `⟨u, hu⟩` from `(isIntegrallyClosed_iff K).1 hic hint`. Establish `hxu : algebraMap R RP x * u = algebraMap R RP s`.

Apply `IsFractionRing.injective RP K` to reduce the goal to its premises. Rewrite using `[map_mul, hu, ← hφ, ← hφ, hs, map_mul]`. Take `⟨⟨r, t⟩, hrt⟩` from `IsLocalization.surj P.primeCompl u`. Establish `h2 : algebraMap R RP (x * r) = algebraMap R RP (s * t)`. Simplify using `only at hrt`.

Rewrite using `[map_mul, map_mul, ← hxu, ← hrt]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨t', ht'⟩` from `(IsLocalization.eq_iff_exists P.primeCompl RP).1 h2`. Use `⟨t' * t, P.primeCompl.mul_mem t'.2 t.2, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`.

Use `⟨t' * r, ?_⟩` and prove the remaining obligations. Take the linear combination `ht'`.
-/
theorem isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes
    (R : Type) [CommRing R] [IsNoetherianRing R] (x : R) (hx : x ∈ nonZeroDivisors R)
    (hloc : ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
      ∃ _ : IsDomain (Localization.AtPrime P), IsIntegrallyClosed (Localization.AtPrime P))
    (hcond : ∀ c : FractionRing R, IsIntegral R c →
      ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) x * c) :
    IsIntegrallyClosed R := by
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro c hc
  obtain ⟨s, hs⟩ := hcond c hc

  suffices hmem : Ideal.Quotient.mk (Ideal.span {x}) s = 0 by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hmem
    obtain ⟨w, rfl⟩ := hmem
    refine ⟨w, ?_⟩
    have hu : IsUnit (algebraMap R (FractionRing R) x) :=
      IsLocalization.map_units (FractionRing R) ⟨x, hx⟩
    apply hu.mul_left_cancel
    rw [← hs, map_mul, mul_comm]
  have key := eq_zero_of_forall_associatedPrimes_exists_smul_eq_zero
    (A := R) (M := R ⧸ Ideal.span {x}) (x := Ideal.Quotient.mk (Ideal.span {x}) s)
  apply key
  intro P hP
  haveI hPp : P.IsPrime := hP.isPrime
  obtain ⟨hdom, hic⟩ := hloc P hP
  let RP := Localization.AtPrime P
  let K := FractionRing RP

  have hreg : ∀ b ∈ nonZeroDivisors R, IsUnit (algebraMap R K b) := by
    intro b hb
    rw [IsScalarTower.algebraMap_apply R RP K]
    refine IsLocalization.map_units K (⟨algebraMap R RP b, ?_⟩ : nonZeroDivisors RP)
    refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ?_
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl RP b).1 h0
    have : (t : R) = 0 := (mem_nonZeroDivisors_iff_right.1 hb) t ht
    exact t.2 (this ▸ P.zero_mem)
  let φ : FractionRing R →+* K :=
    IsLocalization.lift (M := nonZeroDivisors R) (g := algebraMap R K) fun b ↦ hreg b b.2
  have hφ : ∀ r : R, φ (algebraMap R (FractionRing R) r) = algebraMap RP K (algebraMap R RP r) :=
    fun r ↦ by
      rw [IsLocalization.lift_eq, IsScalarTower.algebraMap_apply R RP K]
  have hint : IsIntegral RP (φ c) := by
    refine IsIntegral.map_of_comp_eq (algebraMap R RP) φ ?_ hc
    ext r
    simp only [RingHom.comp_apply]
    rw [hφ]
  obtain ⟨u, hu⟩ := (isIntegrallyClosed_iff K).1 hic hint
  have hxu : algebraMap R RP x * u = algebraMap R RP s := by
    apply IsFractionRing.injective RP K
    rw [map_mul, hu, ← hφ, ← hφ, hs, map_mul]
  obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj P.primeCompl u
  have h2 : algebraMap R RP (x * r) = algebraMap R RP (s * t) := by
    simp only at hrt
    rw [map_mul, map_mul, ← hxu, ← hrt]
    ring
  obtain ⟨t', ht'⟩ := (IsLocalization.eq_iff_exists P.primeCompl RP).1 h2
  refine ⟨t' * t, P.primeCompl.mul_mem t'.2 t.2, ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton']
  refine ⟨t' * r, ?_⟩
  linear_combination ht'

end GlobalTheory
