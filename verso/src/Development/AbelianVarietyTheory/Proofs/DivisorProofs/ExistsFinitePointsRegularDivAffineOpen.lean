import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePrimesDvdOfDvdMulLocalization
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory

/- English proof (translation)
Establish `hz : hA.fromSpec Q ∈ V`. Establish `h : hA.fromSpec Q ∈ Set.range hA.fromSpec` using `⟨Q, rfl⟩`. Rewrite `h` using `[hA.range_fromSpec]`. Conclude with `h`. Rewrite using `[unitAt_fnOf_iff hz]`.

Establish `h` using `hA.fromSpec_preimage_basicOpen r`. Express the relevant statement in the definitionally equal form `Q ∈ hA.fromSpec ⁻¹ᵁ X.basicOpen r ↔ _`. Rewrite using `[h]`. Conclude with `PrimeSpectrum.mem_basicOpen _ _`.
-/
theorem unitAt_fromSpec_fnOf_iff {X : Scheme.{0}} [IsIntegral X] {V : X.Opens} (hA : IsAffineOpen V)
    (hV : genericPoint X ∈ V) (Q : PrimeSpectrum Γ(X, V)) (r : Γ(X, V)) :
    UnitAt (hA.fromSpec Q) (fnOf V hV r) ↔ r ∉ Q.asIdeal := by
  have hz : hA.fromSpec Q ∈ V := by
    have h : hA.fromSpec Q ∈ Set.range hA.fromSpec := ⟨Q, rfl⟩
    rw [hA.range_fromSpec] at h
    exact h
  rw [unitAt_fnOf_iff hz]
  have h := hA.fromSpec_preimage_basicOpen r
  change Q ∈ hA.fromSpec ⁻¹ᵁ X.basicOpen r ↔ _
  rw [h]
  exact PrimeSpectrum.mem_basicOpen _ _

/- English proof (translation)
Introduce `X _ _ V hA hV a ha`. Establish `: Nonempty V` using `⟨⟨_, hV⟩⟩`. Establish `: IsNoetherianRing Γ(X, V)` using `IsLocallyNoetherian.component_noetherian ⟨V, hA⟩`. Establish `ha0 : a ≠ 0` using `fun h => ha (by rw [h, map_zero])`. Take `⟨S, hS, H⟩` from `exists_finite_primes_dvd_of_dvd_mul_localization Γ(X, V) a ha0`.

Use `⟨(fun Q : PrimeSpectrum Γ(X, V) => hA.fromSpec Q) '' S, hS.image _, ?_⟩` and prove the remaining obligations. Introduce and unpack `x hx _ _ ⟨τ, rfl⟩ hτ ⟨g, rfl⟩ ⟨c, hc⟩`. Use `set P : PrimeSpectrum Γ(X, V) := hA.primeIdealOf ⟨x, hx⟩ with hP`. Use `letI : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩`. Establish `hloc : IsLocalization.AtPrime (X.presheaf.stalk x) P.asIdeal` using `hA.isLocalization_stalk ⟨x, hx⟩`.

Establish `hgerm : ∀ r : Γ(X, V), algebraMap (X.presheaf.stalk x) X.functionField (algebraMap Γ(X, V) (X.presheaf.stalk x) r) = fnOf V hV r` using `fun r => algebraMap_germ hx r`. Set `e : Localization.AtPrime P.asIdeal ≃ₐ[Γ(X, V)] X.presheaf.stalk x` to `IsLocalization.algEquiv P.asIdeal.primeCompl _ _`. Establish `hd : algebraMap Γ(X, V) (X.presheaf.stalk x) a ∣ g * τ`. Use `⟨c, IsFractionRing.injective (X.presheaf.stalk x) X.functionField ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hgerm, hc, mul_div_cancel₀ _ ha]`.

Establish `key` using `H P (e.symm τ) (e.symm g) ?_ ?_`. Take `⟨d, hd⟩` from `map_dvd e key`. Rewrite `hd` using `[e.commutes, e.apply_symm_apply]`. Conclude with `⟨d, by rw [hd, map_mul, hgerm, mul_div_cancel_left₀ _ ha]⟩`. Introduce `Q hQ hQP hm`.

Establish `hsp : hA.fromSpec Q ⤳ x`. Establish `h` using `((PrimeSpectrum.le_iff_specializes Q P).1 hQP).map hA.fromSpec.continuous`. Rewrite `h` using `[hP, hA.fromSpec_primeIdealOf]`. Then use the resulting hypothesis. Establish `hu` using `hτ _ ⟨Q, hQ, rfl⟩ hsp`. Take `⟨⟨q, t⟩, hqt⟩` from `(IsLocalization.mem_map_algebraMap_iff P.asIdeal.primeCompl _).1 hm`.

Establish `h1` using `congrArg (fun y => algebraMap (X.presheaf.stalk x) X.functionField (e y)) hqt`. Simplify using `only [map_mul, e.commutes, e.apply_symm_apply, hgerm] at h1`. Establish `ht` using `(unitAt_fromSpec_fnOf_iff hA hV Q t).2 fun h => t.2 (hQP h)`. Establish `h2` using `hu.mul ht`. Rewrite `h2` using `[h1]`.

Conclude with `(unitAt_fromSpec_fnOf_iff hA hV Q q).1 h2 q.2`. Establish `h` using `map_dvd e.symm hd`. Rewrite `h` using `[e.symm.commutes, map_mul]`. Then use the resulting hypothesis.
-/
theorem exists_finite_points_regAt_div_of_affine :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (V : X.Opens), IsAffineOpen V → ∀ (hV : genericPoint X ∈ V) (a : Γ(X, V)), fnOf V hV a ≠ 0 → ∃ T : Set X, T.Finite ∧ ∀ x ∈ V, ∀ τ g : X.functionField, RegAt x τ → (∀ z ∈ T, z ⤳ x → UnitAt z τ) → RegAt x g → RegAt x (g * τ / fnOf V hV a) → RegAt x (g / fnOf V hV a) := by
  intro X _ _ V hA hV a ha
  have : Nonempty V := ⟨⟨_, hV⟩⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hA⟩
  have ha0 : a ≠ 0 := fun h => ha (by rw [h, map_zero])
  obtain ⟨S, hS, H⟩ := exists_finite_primes_dvd_of_dvd_mul_localization Γ(X, V) a ha0
  refine ⟨(fun Q : PrimeSpectrum Γ(X, V) => hA.fromSpec Q) '' S, hS.image _, ?_⟩
  rintro x hx _ _ ⟨τ, rfl⟩ hτ ⟨g, rfl⟩ ⟨c, hc⟩
  set P : PrimeSpectrum Γ(X, V) := hA.primeIdealOf ⟨x, hx⟩ with hP
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) P.asIdeal := hA.isLocalization_stalk ⟨x, hx⟩
  have hgerm : ∀ r : Γ(X, V), algebraMap (X.presheaf.stalk x) X.functionField
      (algebraMap Γ(X, V) (X.presheaf.stalk x) r) = fnOf V hV r := fun r => algebraMap_germ hx r
  let e : Localization.AtPrime P.asIdeal ≃ₐ[Γ(X, V)] X.presheaf.stalk x :=
    IsLocalization.algEquiv P.asIdeal.primeCompl _ _
  have hd : algebraMap Γ(X, V) (X.presheaf.stalk x) a ∣ g * τ := by
    refine ⟨c, IsFractionRing.injective (X.presheaf.stalk x) X.functionField ?_⟩
    rw [map_mul, map_mul, hgerm, hc, mul_div_cancel₀ _ ha]
  have key := H P (e.symm τ) (e.symm g) ?_ ?_
  · obtain ⟨d, hd⟩ := map_dvd e key
    rw [e.commutes, e.apply_symm_apply] at hd
    exact ⟨d, by rw [hd, map_mul, hgerm, mul_div_cancel_left₀ _ ha]⟩
  · intro Q hQ hQP hm
    have hsp : hA.fromSpec Q ⤳ x := by
      have h := ((PrimeSpectrum.le_iff_specializes Q P).1 hQP).map hA.fromSpec.continuous
      rwa [hP, hA.fromSpec_primeIdealOf] at h
    have hu := hτ _ ⟨Q, hQ, rfl⟩ hsp
    obtain ⟨⟨q, t⟩, hqt⟩ := (IsLocalization.mem_map_algebraMap_iff P.asIdeal.primeCompl _).1 hm
    have h1 := congrArg (fun y => algebraMap (X.presheaf.stalk x) X.functionField (e y)) hqt
    simp only [map_mul, e.commutes, e.apply_symm_apply, hgerm] at h1
    have ht := (unitAt_fromSpec_fnOf_iff hA hV Q t).2 fun h => t.2 (hQP h)
    have h2 := hu.mul ht
    rw [h1] at h2
    exact (unitAt_fromSpec_fnOf_iff hA hV Q q).1 h2 q.2
  · have h := map_dvd e.symm hd
    rwa [e.symm.commutes, map_mul] at h

end GlobalTheory
