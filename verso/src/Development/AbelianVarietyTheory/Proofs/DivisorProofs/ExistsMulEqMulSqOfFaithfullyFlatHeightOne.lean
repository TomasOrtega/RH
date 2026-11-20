import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeig
open IsLocalRing

namespace GlobalTheory.Mum

/- English proof (translation)
Use `GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one O p h1` as an intermediate fact. Set `R` to `Localization.AtPrime p`. Establish `hinj : Function.Injective (algebraMap O R)` using `IsLocalization.injective R p.primeCompl_le_nonZeroDivisors`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Take `⟨⟨π, s⟩, hs⟩` from `IsLocalization.surj p.primeCompl ϖ`.

Establish `hsu : IsUnit (algebraMap O R s)` using `IsLocalization.map_units R s`. Establish `hπ : Irreducible (algebraMap O R π)`. Establish `e : algebraMap O R π = ϖ * algebraMap O R s` using `hs.symm`. Rewrite using `[e]`. Conclude with `(irreducible_mul_isUnit hsu).2 hϖ`.

Establish `hmax` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ`. Use `⟨π, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← IsLocalization.AtPrime.to_map_mem_maximal_iff R p π, hmax]`. Conclude with `Ideal.mem_span_singleton_self _`. Introduce and unpack `rfl`.

Conclude with `hπ.ne_zero (map_zero _)`. Introduce `y hy`. Rewrite `hy` using `[← IsLocalization.AtPrime.to_map_mem_maximal_iff R p y, hmax, Ideal.mem_span_singleton]`. Take `⟨z, hz⟩` from `hy`. Take `⟨⟨t, r⟩, hr⟩` from `IsLocalization.surj p.primeCompl z`.

Use `⟨r, r.2, t, hinj ?_⟩` and prove the remaining obligations. Establish `hr' : z * algebraMap O R r = algebraMap O R t` using `hr`. Rewrite using `[map_mul, map_mul, hz, ← hr']`. Expand and normalize the polynomial expressions, which then agree. Establish `hh' : algebraMap O R h ≠ 0` using `fun h0 => hh (hinj (by rw [h0, map_zero]))`.

Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hh' hπ`. Take `⟨⟨c, b⟩, hb⟩` from `IsLocalization.surj p.primeCompl (u : R)`. Establish `hb' : (u : R) * algebraMap O R b = algebraMap O R c` using `hb`. Use `⟨n, b, c, b.2, ?_, hinj ?_⟩` and prove the remaining obligations. Establish `hcu : IsUnit (algebraMap O R c)`.

Rewrite using `[← hb']`. Conclude with `u.isUnit.mul (IsLocalization.map_units R b)`. Conclude with `(IsLocalization.AtPrime.isUnit_to_map_iff R p c).1 hcu`. Rewrite using `[map_mul, map_mul, map_pow, hu, ← hb']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_uniformiser_mul_eq_mul_pow_of_height_eq_one (O : Type) [CommRing O] [IsDomain O]
    [IsNoetherianRing O] [IsIntegrallyClosed O] (p : Ideal O) [hp : p.IsPrime] (h1 : p.height = 1)
    (h : O) (hh : h ≠ 0) :
    ∃ π ∈ p, π ≠ 0 ∧ (∀ y ∈ p, ∃ s ∉ p, π ∣ s * y) ∧
      ∃ (n : ℕ) (b c : O), b ∉ p ∧ c ∉ p ∧ b * h = c * π ^ n := by
  have := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one O p h1
  let R := Localization.AtPrime p
  have hinj : Function.Injective (algebraMap O R) :=
    IsLocalization.injective R p.primeCompl_le_nonZeroDivisors
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨⟨π, s⟩, hs⟩ := IsLocalization.surj p.primeCompl ϖ
  have hsu : IsUnit (algebraMap O R s) := IsLocalization.map_units R s
  have hπ : Irreducible (algebraMap O R π) := by
    have e : algebraMap O R π = ϖ * algebraMap O R s := hs.symm
    rw [e]
    exact (irreducible_mul_isUnit hsu).2 hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff R p π, hmax]
    exact Ideal.mem_span_singleton_self _
  · rintro rfl
    exact hπ.ne_zero (map_zero _)
  · intro y hy
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff R p y, hmax, Ideal.mem_span_singleton] at hy
    obtain ⟨z, hz⟩ := hy
    obtain ⟨⟨t, r⟩, hr⟩ := IsLocalization.surj p.primeCompl z
    refine ⟨r, r.2, t, hinj ?_⟩
    have hr' : z * algebraMap O R r = algebraMap O R t := hr
    rw [map_mul, map_mul, hz, ← hr']
    ring
  · have hh' : algebraMap O R h ≠ 0 := fun h0 => hh (hinj (by rw [h0, map_zero]))
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hh' hπ
    obtain ⟨⟨c, b⟩, hb⟩ := IsLocalization.surj p.primeCompl (u : R)
    have hb' : (u : R) * algebraMap O R b = algebraMap O R c := hb
    refine ⟨n, b, c, b.2, ?_, hinj ?_⟩
    · have hcu : IsUnit (algebraMap O R c) := by
        rw [← hb']
        exact u.isUnit.mul (IsLocalization.map_units R b)
      exact (IsLocalization.AtPrime.isUnit_to_map_iff R p c).1 hcu
    · rw [map_mul, map_mul, map_pow, hu, ← hb']
      ring

/- English proof (translation)
Introduce `O C _ _ _ _ _ _ _ _ _ h hh hsq p hp h1 hP`. Take `⟨u, g, hg⟩` from `hsq`. Take `⟨π, hπp, hπ0, hgen, n, b, c, hb, hc, hbc⟩` from `exists_uniformiser_mul_eq_mul_pow_of_height_eq_one O p h1 h hh`. Set `P : Ideal C` to `Ideal.map (algebraMap O C) p`. Set `R` to `Localization.AtPrime P`.

Set `φ : O →+* R` to `(algebraMap C R).comp (algebraMap O C)`. Establish `hcomap : P.comap (algebraMap O C) = p` using `Ideal.comap_map_eq_self_of_faithfullyFlat p`. Establish `hinjR : Function.Injective (algebraMap C R)` using `IsLocalization.injective R P.primeCompl_le_nonZeroDivisors`. Establish `hinjC : Function.Injective (algebraMap O C)` using `FaithfulSMul.algebraMap_injective O C`. Establish `hinj : Function.Injective φ` using `hinjR.comp hinjC`.

Establish `hunit : ∀ s ∉ p, IsUnit (φ s)`. Introduce `s hs`. Use `(IsLocalization.AtPrime.isUnit_to_map_iff R P (algebraMap O C s)).2 ?_` and prove the remaining obligations. Introduce `hm`. Conclude with `hs (hcomap ▸ (Ideal.mem_comap.2 hm))`.

Establish `hπR : φ π ≠ 0` using `fun h0 => hπ0 (hinj (by rw [h0, map_zero]))`. Establish `hmax : maximalIdeal R = Ideal.span {φ π}`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]`. Introduce `y hy`.

Take `⟨s, hs, hd⟩` from `hgen y hy`. Rewrite using `[Ideal.mem_comap, Ideal.mem_span_singleton]`. Establish `hd' : φ π ∣ φ s * φ y` using `by rw [← map_mul]; exact map_dvd φ hd`. Conclude with `(hunit s hs).dvd_mul_left.1 hd'`. Rewrite using `[Ideal.span_singleton_le_iff_mem]`.

Conclude with `(IsLocalization.AtPrime.to_map_mem_maximal_iff R P (algebraMap O C π)).2 (Ideal.mem_map_of_mem _ hπp)`. Establish `hnf : ¬ IsField R`. Introduce `hf`. Rewrite `hf` using `[isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]`. Conclude with `hπR hf`.

Establish `hdvr : IsDiscreteValuationRing R` using `((IsDiscreteValuationRing.TFAE R hnf).out 4 0).1 (show (maximalIdeal R).IsPrincipal from ⟨⟨φ π, hmax⟩⟩)`. Establish `hirr : Irreducible (φ π)` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax`. Establish `hhR : φ h = algebraMap C R u * algebraMap C R g ^ 2` using `by show algebraMap C R (algebraMap O C h) = _`. Rewrite using `[hg, map_mul, map_pow]`. Establish `hg0 : algebraMap C R g ≠ 0`.

Introduce `h0`. Apply `hh` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hhR, h0, map_zero]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨m, v, hv⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hirr`. Establish `huR : IsUnit (algebraMap C R u)` using `u.isUnit.map _`. Establish `hnm : 2 * m = n`. Use `IsDiscreteValuationRing.unit_mul_pow_congr_pow hirr hirr ((hunit b hb).unit * huR.unit * v ^ 2) (hunit c hc).unit _ _ ?_` and prove the remaining obligations. Establish `e` using `congrArg φ hbc`.

Rewrite `e` using `[map_mul, map_mul, map_pow, hhR, hv]`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]`. Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨π ^ m, b, c, hb, hc, ?_⟩` and prove the remaining obligations.

Rewrite using `[hbc, ← hnm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime : ∀ (O C : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CommRing C] [IsDomain C] [IsNoetherianRing C] [Algebra O C] [Module.FaithfullyFlat O C] (h : O), h ≠ 0 → (∃ (u : Cˣ) (g : C), algebraMap O C h = u * g ^ 2) → ∀ p : Ideal O, p.IsPrime → p.height = 1 → (Ideal.map (algebraMap O C) p).IsPrime → ∃ a b c : O, b ∉ p ∧ c ∉ p ∧ b * h = c * a ^ 2 := by
  intro O C _ _ _ _ _ _ _ _ _ h hh hsq p hp h1 hP
  obtain ⟨u, g, hg⟩ := hsq
  obtain ⟨π, hπp, hπ0, hgen, n, b, c, hb, hc, hbc⟩ :=
    exists_uniformiser_mul_eq_mul_pow_of_height_eq_one O p h1 h hh
  let P : Ideal C := Ideal.map (algebraMap O C) p
  let R := Localization.AtPrime P
  let φ : O →+* R := (algebraMap C R).comp (algebraMap O C)
  have hcomap : P.comap (algebraMap O C) = p := Ideal.comap_map_eq_self_of_faithfullyFlat p
  have hinjR : Function.Injective (algebraMap C R) :=
    IsLocalization.injective R P.primeCompl_le_nonZeroDivisors
  have hinjC : Function.Injective (algebraMap O C) := FaithfulSMul.algebraMap_injective O C
  have hinj : Function.Injective φ := hinjR.comp hinjC
  have hunit : ∀ s ∉ p, IsUnit (φ s) := by
    intro s hs
    refine (IsLocalization.AtPrime.isUnit_to_map_iff R P (algebraMap O C s)).2 ?_
    intro hm
    exact hs (hcomap ▸ (Ideal.mem_comap.2 hm))
  have hπR : φ π ≠ 0 := fun h0 => hπ0 (hinj (by rw [h0, map_zero]))
  have hmax : maximalIdeal R = Ideal.span {φ π} := by
    apply le_antisymm
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro y hy
      obtain ⟨s, hs, hd⟩ := hgen y hy
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      have hd' : φ π ∣ φ s * φ y := by rw [← map_mul]; exact map_dvd φ hd
      exact (hunit s hs).dvd_mul_left.1 hd'
    · rw [Ideal.span_singleton_le_iff_mem]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R P (algebraMap O C π)).2
        (Ideal.mem_map_of_mem _ hπp)
  have hnf : ¬ IsField R := by
    intro hf
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot] at hf
    exact hπR hf
  have hdvr : IsDiscreteValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hnf).out 4 0).1 (show (maximalIdeal R).IsPrincipal from ⟨⟨φ π, hmax⟩⟩)
  have hirr : Irreducible (φ π) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  have hhR : φ h = algebraMap C R u * algebraMap C R g ^ 2 := by
    show algebraMap C R (algebraMap O C h) = _
    rw [hg, map_mul, map_pow]
  have hg0 : algebraMap C R g ≠ 0 := by
    intro h0
    apply hh
    apply hinj
    rw [hhR, h0, map_zero]
    ring
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hirr
  have huR : IsUnit (algebraMap C R u) := u.isUnit.map _
  have hnm : 2 * m = n := by
    refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hirr hirr
      ((hunit b hb).unit * huR.unit * v ^ 2) (hunit c hc).unit _ _ ?_
    have e := congrArg φ hbc
    rw [map_mul, map_mul, map_pow, hhR, hv] at e
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rw [← e]
    ring
  refine ⟨π ^ m, b, c, hb, hc, ?_⟩
  rw [hbc, ← hnm]
  ring

end GlobalTheory.Mum
