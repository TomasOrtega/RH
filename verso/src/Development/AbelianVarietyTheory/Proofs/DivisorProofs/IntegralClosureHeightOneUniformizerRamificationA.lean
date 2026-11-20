import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

/- English proof (translation)
Set `L` to `Localization.AtPrime Q`. Use `haveI : IsDiscreteValuationRing L := isDiscreteValuationRing_of_height_eq_one Q hQ L`. Establish `hle : Q.primeCompl ≤ nonZeroDivisors B` using `Q.primeCompl_le_nonZeroDivisors`. Establish `hinj : Function.Injective (algebraMap B L)` using `IsLocalization.injective L hle`. Establish `hcomap : (IsLocalRing.maximalIdeal L).comap (algebraMap B L) = Q` using `IsLocalization.AtPrime.comap_maximalIdeal L Q`.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible L`. Take `⟨⟨s, r0⟩, hs⟩` from `IsLocalization.surj Q.primeCompl ϖ`. Simplify using `only at hs`. Establish `hu0 : IsUnit (algebraMap B L r0)` using `IsLocalization.map_units L r0`. Establish `hsirr : Irreducible (algebraMap B L s)`.

Rewrite using `[← hs]`. Conclude with `(irreducible_mul_isUnit hu0).mpr hϖ`. Establish `hmax` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hsirr`. Establish `hsQ : s ∈ Q`. Rewrite using `[← hcomap, Ideal.mem_comap, hmax]`.

Conclude with `Ideal.subset_span rfl`. Use `⟨s, ?_⟩` and prove the remaining obligations. Establish `hxL : algebraMap B L x ≠ 0`. Rewrite using `[Ne, ← map_zero (algebraMap B L)]`. Conclude with `fun h => hx0 (hinj h)`.

Take `⟨n, w, hw⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxL hsirr`. Establish `hxm : algebraMap B L x ∈ IsLocalRing.maximalIdeal L`. Rewrite using `[← Ideal.mem_comap, hcomap]`. Conclude with `hxQ`. Use `⟨n, ?_, hsQ, ?_, ?_⟩` and prove the remaining obligations.

Break down `Nat.eq_zero_or_pos n with h | h` into its components or cases. It suffices to derive a contradiction. Rewrite `hw` using `[h, pow_zero, mul_one]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp hxm (hw ▸ w.isUnit)`. Conclude with `h`.

Introduce `y hy`. Establish `hym : algebraMap B L y ∈ Ideal.span {algebraMap B L s}`. Rewrite using `[← hmax, ← Ideal.mem_comap, hcomap]`. Conclude with `hy`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.mp hym`.

Take `⟨⟨c, r⟩, hcr⟩` from `IsLocalization.surj Q.primeCompl z`. Simplify using `only at hcr`. Use `⟨c, r, r.2, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, ← hz, ← hcr]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨⟨a, r⟩, har⟩` from `IsLocalization.surj Q.primeCompl (w : L)`. Simplify using `only at har`. Establish `hau : IsUnit (algebraMap B L a)`. Rewrite using `[← har]`. Conclude with `w.isUnit.mul (IsLocalization.map_units L r)`.

Use `⟨a, r, ?_, r.2, hinj ?_⟩` and prove the remaining obligations. Introduce `haQ`. Establish `: algebraMap B L a ∈ IsLocalRing.maximalIdeal L`. Rewrite using `[← Ideal.mem_comap, hcomap]`. Conclude with `haQ`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).mp this hau`. Rewrite using `[map_mul, map_mul, map_pow, ← har, hw]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_localUniformizer_and_order {B : Type} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [IsIntegrallyClosed B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height = 1)
    (x : B) (hx0 : x ≠ 0) (hxQ : x ∈ Q) :
    ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧
      (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ r * x = a * s ^ e) := by
  let L := Localization.AtPrime Q
  haveI : IsDiscreteValuationRing L := isDiscreteValuationRing_of_height_eq_one Q hQ L
  have hle : Q.primeCompl ≤ nonZeroDivisors B := Q.primeCompl_le_nonZeroDivisors
  have hinj : Function.Injective (algebraMap B L) := IsLocalization.injective L hle
  have hcomap : (IsLocalRing.maximalIdeal L).comap (algebraMap B L) = Q :=
    IsLocalization.AtPrime.comap_maximalIdeal L Q
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible L
  obtain ⟨⟨s, r0⟩, hs⟩ := IsLocalization.surj Q.primeCompl ϖ
  simp only at hs
  have hu0 : IsUnit (algebraMap B L r0) := IsLocalization.map_units L r0
  have hsirr : Irreducible (algebraMap B L s) := by
    rw [← hs]; exact (irreducible_mul_isUnit hu0).mpr hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hsirr
  have hsQ : s ∈ Q := by
    rw [← hcomap, Ideal.mem_comap, hmax]; exact Ideal.subset_span rfl
  refine ⟨s, ?_⟩
  have hxL : algebraMap B L x ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap B L)]; exact fun h => hx0 (hinj h)
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxL hsirr
  have hxm : algebraMap B L x ∈ IsLocalRing.maximalIdeal L := by
    rw [← Ideal.mem_comap, hcomap]; exact hxQ
  refine ⟨n, ?_, hsQ, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hw
      exact (IsLocalRing.mem_maximalIdeal _).mp hxm (hw ▸ w.isUnit)
    · exact h
  · intro y hy
    have hym : algebraMap B L y ∈ Ideal.span {algebraMap B L s} := by
      rw [← hmax, ← Ideal.mem_comap, hcomap]; exact hy
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hym
    obtain ⟨⟨c, r⟩, hcr⟩ := IsLocalization.surj Q.primeCompl z
    simp only at hcr
    refine ⟨c, r, r.2, hinj ?_⟩
    rw [map_mul, map_mul, ← hz, ← hcr]; ring
  · obtain ⟨⟨a, r⟩, har⟩ := IsLocalization.surj Q.primeCompl (w : L)
    simp only at har
    have hau : IsUnit (algebraMap B L a) := by
      rw [← har]; exact w.isUnit.mul (IsLocalization.map_units L r)
    refine ⟨a, r, ?_, r.2, hinj ?_⟩
    · intro haQ
      have : algebraMap B L a ∈ IsLocalRing.maximalIdeal L := by
        rw [← Ideal.mem_comap, hcomap]; exact haQ
      exact (IsLocalRing.mem_maximalIdeal _).mp this hau
    · rw [map_mul, map_mul, map_pow, ← har, hw]; ring

/- English proof (translation)
Introduce `k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB p _ t ht hpt Q _ hQ hlie`. Establish `hN : IsNoetherianRing A`. Substitute `hA` using the available equality. Conclude with `isNoetherianRing_of_ringEquiv _ hu.aevalEquiv.toRingEquiv`. Establish `hI : IsIntegrallyClosed A`.

Substitute `hA` using the available equality. Establish `: IsIntegrallyClosed (MvPolynomial (Fin d) k)` using `UniqueFactorizationMonoid.instIsIntegrallyClosed`. Conclude with `IsIntegrallyClosed.of_equiv hu.aevalEquiv.toRingEquiv`. Establish `: CharZero F` using `charZero_of_injective_algebraMap (algebraMap k F).injective`. Substitute `hB` using the available equality.

Establish `hNB : IsNoetherianRing (integralClosure A K)` using `IsIntegralClosure.isNoetherianRing A F K _`. Establish `hIB : IsIntegrallyClosed (integralClosure A K)` using `integralClosure.isIntegrallyClosedOfFiniteExtension F`. Use `haveI : IsNoetherianRing ((integralClosure A K).restrictScalars k) := hNB`. Use `haveI : IsIntegrallyClosed ((integralClosure A K).restrictScalars k) := hIB`. Establish `hmem : algebraMap F K (t : F) ∈ (integralClosure A K).restrictScalars k`.

Rewrite using `[Subalgebra.mem_restrictScalars, mem_integralClosure_iff]`. Conclude with `isIntegral_algebraMap (x := t)`. Set `x : (integralClosure A K).restrictScalars k` to `⟨_, hmem⟩`. Establish `hxQ : x ∈ Q` using `(hlie t x rfl).mpr (hpt ▸ Ideal.subset_span rfl)`. Establish `hx0 : x ≠ 0`.

Introduce `h`. Establish `h' : algebraMap F K (t : F) = 0` using `congrArg Subtype.val h`. Rewrite `h'` using `[map_eq_zero_iff _ (algebraMap F K).injective, ZeroMemClass.coe_eq_zero]`. Conclude with `ht.ne_zero h'`. Take `⟨s, e, he, hs, hgen, a, r, ha, hr, hrx⟩` from `exists_localUniformizer_and_order Q hQ x hx0 hxQ`.

Use `⟨s, e, he, hs, hgen, a, r, ha, hr, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hrx` as an intermediate fact. Simplify using `using this`.
-/
theorem integralClosure_height_one_uniformizer_ramification :
    ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → ∀ t : A, Irreducible t → p = Ideal.span {t} → ∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧ (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB p _ t ht hpt Q _ hQ hlie
  have hN : IsNoetherianRing A := by
    subst hA
    exact isNoetherianRing_of_ringEquiv _ hu.aevalEquiv.toRingEquiv
  have hI : IsIntegrallyClosed A := by
    subst hA
    have : IsIntegrallyClosed (MvPolynomial (Fin d) k) :=
      UniqueFactorizationMonoid.instIsIntegrallyClosed
    exact IsIntegrallyClosed.of_equiv hu.aevalEquiv.toRingEquiv
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  subst hB
  have hNB : IsNoetherianRing (integralClosure A K) := IsIntegralClosure.isNoetherianRing A F K _
  have hIB : IsIntegrallyClosed (integralClosure A K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension F
  haveI : IsNoetherianRing ((integralClosure A K).restrictScalars k) := hNB
  haveI : IsIntegrallyClosed ((integralClosure A K).restrictScalars k) := hIB
  have hmem : algebraMap F K (t : F) ∈ (integralClosure A K).restrictScalars k := by
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (x := t)
  let x : (integralClosure A K).restrictScalars k := ⟨_, hmem⟩
  have hxQ : x ∈ Q := (hlie t x rfl).mpr (hpt ▸ Ideal.subset_span rfl)
  have hx0 : x ≠ 0 := by
    intro h
    have h' : algebraMap F K (t : F) = 0 := congrArg Subtype.val h
    rw [map_eq_zero_iff _ (algebraMap F K).injective, ZeroMemClass.coe_eq_zero] at h'
    exact ht.ne_zero h'
  obtain ⟨s, e, he, hs, hgen, a, r, ha, hr, hrx⟩ := exists_localUniformizer_and_order Q hQ x hx0 hxQ
  refine ⟨s, e, he, hs, hgen, a, r, ha, hr, ?_⟩
  have := congrArg Subtype.val hrx
  simpa using this

end GlobalTheory
