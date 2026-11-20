import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ValLocal

/- English proof (translation)
Distinguish the cases in `hq : q = ⊥`. Conclude with `⟨b, a, by simpa [hq] using hb, Or.inl (mul_comm _ _)⟩`. Use `haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq (Localization.AtPrime q)`. Establish `hinj : Function.Injective (algebraMap A (Localization.AtPrime q))` using `IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors`. Establish `key : ∀ (u v : A) (z : Localization.AtPrime q), algebraMap A _ u * z = algebraMap A _ v → ∃ s r : A, s ∉ q ∧ s * v = r * u`.

Introduce `u v z hz`. Take `⟨⟨r, s⟩, hrs⟩` from `IsLocalization.surj q.primeCompl z`. Use `⟨s, r, s.2, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, ← hz, ← hrs]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨z, hz | hz⟩` from `ValuationRing.cond (algebraMap A (Localization.AtPrime q) a) (algebraMap A _ b)`. Take `⟨s, r, hs, h⟩` from `key a b z hz`. Conclude with `⟨s, r, hs, Or.inr h⟩`. Take `⟨s, r, hs, h⟩` from `key b a z hz`. Conclude with `⟨s, r, hs, Or.inl h⟩`.
-/
theorem exists_dvd_away {A : Type} [CommRing A] [IsDedekindDomain A] (q : Ideal A) [q.IsPrime] (a b : A) (hb : b ≠ 0) :
    ∃ s r : A, s ∉ q ∧ (s * a = r * b ∨ s * b = r * a) := by
  by_cases hq : q = ⊥
  · exact ⟨b, a, by simpa [hq] using hb, Or.inl (mul_comm _ _)⟩
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq (Localization.AtPrime q)
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
    IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors
  have key : ∀ (u v : A) (z : Localization.AtPrime q), algebraMap A _ u * z = algebraMap A _ v →
      ∃ s r : A, s ∉ q ∧ s * v = r * u := by
    intro u v z hz
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj q.primeCompl z
    refine ⟨s, r, s.2, hinj ?_⟩
    rw [map_mul, map_mul, ← hz, ← hrs]
    ring
  obtain ⟨z, hz | hz⟩ := ValuationRing.cond (algebraMap A (Localization.AtPrime q) a) (algebraMap A _ b)
  · obtain ⟨s, r, hs, h⟩ := key a b z hz
    exact ⟨s, r, hs, Or.inr h⟩
  · obtain ⟨s, r, hs, h⟩ := key b a z hz
    exact ⟨s, r, hs, Or.inl h⟩

/- English proof (translation)
Establish `hmem : ∀ y : 𝓞 F, (y : F) ∈ W` using `fun y => by`. Establish `h : IsIntegral W (y : F)` using `y.isIntegral_coe.tower_top`. Take `⟨z, hz⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral h`. Rewrite using `[← hz]`. Conclude with `z.2`.

Set `φ : 𝓞 F →+* W` to `(algebraMap (𝓞 F) F).codRestrict W.toSubring hmem`. Establish `hφ : ∀ y : 𝓞 F, ((φ y : W) : F) = (y : F)` using `fun _ => rfl`. Set `q : Ideal (𝓞 F)` to `(IsLocalRing.maximalIdeal W).comap φ`. Establish `hunit : ∀ s : 𝓞 F, s ∉ q → IsUnit (φ s)` using `fun s hs => by`. Assume the negation of the conclusion as `h`.

Conclude with `hs ((IsLocalRing.mem_maximalIdeal _).2 h)`. Take `⟨a, b, hb, hx⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) (x : F)`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hbF : (b : F) ≠ 0` using `by exact_mod_cast hb0`. Establish `hxb : (x : F) * b = a`.

Rewrite using `[← hx]`. Conclude with `div_mul_cancel₀ _ hbF`. Take `⟨s, r, hs, h | h⟩` from `exists_dvd_away q a b hb0`. Use `⟨φ r, φ s, r.isIntegral_coe, s.isIntegral_coe, hunit s hs, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `h' : (s : F) * a = r * b` using `by exact_mod_cast congrArg (fun y : 𝓞 F => (y : F)) h`.

Use `show (x : F) * s = r`. Apply `mul_right_cancel₀ hbF` to reduce the goal to its premises. Rewrite using `[← h', ← hxb]`. Expand and normalize the polynomial expressions, which then agree. Establish `h' : (s : F) * b = r * a` using `by exact_mod_cast congrArg (fun y : 𝓞 F => (y : F)) h`.

Establish `hxr : x * φ r = φ s`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (x : F) * r = s`. Apply `mul_right_cancel₀ hbF` to reduce the goal to its premises. Rewrite using `[h', ← hxb]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨φ s, φ r, s.isIntegral_coe, r.isIntegral_coe, isUnit_of_mul_isUnit_right (hxr ▸ hunit s hs), hxr⟩`.
-/
theorem exists_integral_frac {F : Type} [Field F] [NumberField F] (W : ValuationSubring F) (x : W) :
    ∃ a s : W, IsIntegral ℤ (a : F) ∧ IsIntegral ℤ (s : F) ∧ IsUnit s ∧ x * s = a := by
  have hmem : ∀ y : 𝓞 F, (y : F) ∈ W := fun y => by
    have h : IsIntegral W (y : F) := y.isIntegral_coe.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h
    rw [← hz]
    exact z.2
  let φ : 𝓞 F →+* W := (algebraMap (𝓞 F) F).codRestrict W.toSubring hmem
  have hφ : ∀ y : 𝓞 F, ((φ y : W) : F) = (y : F) := fun _ => rfl
  let q : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal W).comap φ
  have hunit : ∀ s : 𝓞 F, s ∉ q → IsUnit (φ s) := fun s hs => by
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (x : F)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : (b : F) ≠ 0 := by exact_mod_cast hb0
  have hxb : (x : F) * b = a := by
    rw [← hx]
    exact div_mul_cancel₀ _ hbF
  obtain ⟨s, r, hs, h | h⟩ := exists_dvd_away q a b hb0
  · refine ⟨φ r, φ s, r.isIntegral_coe, s.isIntegral_coe, hunit s hs, Subtype.ext ?_⟩
    have h' : (s : F) * a = r * b := by exact_mod_cast congrArg (fun y : 𝓞 F => (y : F)) h
    show (x : F) * s = r
    apply mul_right_cancel₀ hbF
    rw [← h', ← hxb]
    ring
  · have h' : (s : F) * b = r * a := by exact_mod_cast congrArg (fun y : 𝓞 F => (y : F)) h
    have hxr : x * φ r = φ s := by
      apply Subtype.ext
      show (x : F) * r = s
      apply mul_right_cancel₀ hbF
      rw [h', ← hxb]
      ring
    exact ⟨φ s, φ r, s.isIntegral_coe, r.isIntegral_coe,
      isUnit_of_mul_isUnit_right (hxr ▸ hunit s hs), hxr⟩

/- English proof (translation)
Introduce `E _ _ _ H l c O _ β hβ W b hb`. Use `haveI := c.fin`. Use `haveI : NumberField c.F := {}`. Use `letI : Algebra O W := b.toAlgebra`. Establish `hbv : ∀ o : O, ((b o : W) : c.F) = β o` using `fun o => by rw [← hb]; rfl`.

Establish `hinj : Function.Injective b` using `fun u v h => hβ.1 (by rw [← hbv, ← hbv, h])`. Set `S : Submonoid O` to `(IsUnit.submonoid W).comap b`. Use `haveI : IsLocalization S W := by`. Use `(isLocalization_iff S W).2 ⟨fun y => y.2, fun z => ?_, fun {u v} h => ⟨1, by rw [hinj h]⟩⟩` and prove the remaining obligations. Take `⟨a, s, ha, hs, hu, hz⟩` from `exists_integral_frac W z`.

Take `⟨a', ha'⟩` from `hβ.2 _ ha`. Take `⟨s', hs'⟩` from `hβ.2 _ hs`. Establish `e1 : b a' = a` using `Subtype.ext (by rw [hbv, ha'])`. Establish `e2 : b s' = s` using `Subtype.ext (by rw [hbv, hs'])`. Use `⟨⟨a', ⟨s', ?_⟩⟩, ?_⟩` and prove the remaining obligations.

Use `show IsUnit (b s')`. Rewrite using `[e2]` and apply the resulting hypothesis. Use `show z * b s' = b a'`. Rewrite using `[e1, e2, hz]`. Use `⟨IsPreimmersion.of_isLocalization (R := O) (S := W) S, ?_⟩` and prove the remaining obligations.

Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `(RingHom.flat_algebraMap_iff (R := O) (S := W)).2 (IsLocalization.flat W S)`.
-/
theorem preimmersion_flat :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), IsBaseRing β → ∀ (W : ValuationSubring c.F) (b : O →+* W), W.subtype.comp b = β → IsPreimmersion (spMap b) ∧ Flat (spMap b) := by
  intro E _ _ _ H l c O _ β hβ W b hb
  haveI := c.fin
  haveI : NumberField c.F := {}
  letI : Algebra O W := b.toAlgebra
  have hbv : ∀ o : O, ((b o : W) : c.F) = β o := fun o => by rw [← hb]; rfl
  have hinj : Function.Injective b := fun u v h => hβ.1 (by rw [← hbv, ← hbv, h])
  let S : Submonoid O := (IsUnit.submonoid W).comap b
  haveI : IsLocalization S W := by
    refine (isLocalization_iff S W).2 ⟨fun y => y.2, fun z => ?_, fun {u v} h => ⟨1, by rw [hinj h]⟩⟩
    obtain ⟨a, s, ha, hs, hu, hz⟩ := exists_integral_frac W z
    obtain ⟨a', ha'⟩ := hβ.2 _ ha
    obtain ⟨s', hs'⟩ := hβ.2 _ hs
    have e1 : b a' = a := Subtype.ext (by rw [hbv, ha'])
    have e2 : b s' = s := Subtype.ext (by rw [hbv, hs'])
    refine ⟨⟨a', ⟨s', ?_⟩⟩, ?_⟩
    · show IsUnit (b s')
      rwa [e2]
    · show z * b s' = b a'
      rw [e1, e2, hz]
  refine ⟨IsPreimmersion.of_isLocalization (R := O) (S := W) S, ?_⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact (RingHom.flat_algebraMap_iff (R := O) (S := W)).2 (IsLocalization.flat W S)

end GlobalTheory.ValLocal
