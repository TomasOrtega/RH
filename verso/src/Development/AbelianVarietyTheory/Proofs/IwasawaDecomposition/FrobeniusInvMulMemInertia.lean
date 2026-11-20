import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory

/- English proof (translation)
Introduce `E Ω _ _ _ _ v A hA τ τ' hτ hτ'`. Take `⟨hτD, hτF⟩` from `hτ`. Take `⟨hτ'D, hτ'F⟩` from `hτ'`. Use `haveI : v.asIdeal.IsMaximal := v.isMaximal`. Use `letI : Field (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.field _`.

Use `haveI : Finite (𝓞 E ⧸ v.asIdeal) := inferInstance`. Use `letI : Fintype (𝓞 E ⧸ v.asIdeal) := Fintype.ofFinite _`. Use `set p := ringChar (𝓞 E ⧸ v.asIdeal) with hpdef`. Use `haveI : CharP (𝓞 E ⧸ v.asIdeal) p := ringChar.charP _`. Take `⟨n, hp, hcard⟩` from `FiniteField.card (𝓞 E ⧸ v.asIdeal) p`.

Establish `hq : normV v = p ^ (n : ℕ)`. Simplify using `only [normV, Nat.card_eq_fintype_card, hcard]`. Establish `hpv : ((p : 𝓞 E)) ∈ v.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `CharP.cast_eq_zero _ p`.

Establish `hpA : A.valuation (p : Ω) < 1`. Use `(hA (p : 𝓞 E)).mpr hpv` as an intermediate fact. Simplify using `using this`. Establish `hpk : ((p : ℕ) : IsLocalRing.ResidueField A) = 0`. Rewrite using `[← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]`.

Simplify using `using hpA`. Use `haveI : CharP (IsLocalRing.ResidueField A) p := by`. Establish `h` using `CharP.ringChar_of_prime_eq_zero (R := IsLocalRing.ResidueField A) hp hpk`. Rewrite using `[← h]`. Conclude with `ringChar.charP _`.

Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `haveI : ExpChar (IsLocalRing.ResidueField A) p := ExpChar.prime hp`. Use `⟨(Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hτ'D) hτD, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hxA : x ∈ A` using `A.valuation_le_one_iff x |>.mp hx`. Use `set z := (τ'⁻¹ : G E Ω) (τ x) with hz`.

Establish `hzA : z ∈ A`. Rewrite using `[hz, apply_mem_iff_of_mem_Dec ((Dec (F := E) A).inv_mem hτ'D), apply_mem_iff_of_mem_Dec hτD]`. Conclude with `hxA`. Establish `hτ'z : τ' z = τ x` using `mul_inv_apply (τ x)`. Establish `h1` using `hτ'F z ((A.valuation_le_one_iff z).mpr hzA)`.

Rewrite `h1` using `[hτ'z]`. Establish `h2` using `hτF x hx`. Establish `h3 : A.valuation (z ^ normV v - x ^ normV v) < 1`. Establish `e : z ^ normV v - x ^ normV v = (τ x - x ^ normV v) - (τ x - z ^ normV v)` using `by ring`. Rewrite using `[e]`.

Conclude with `Valuation.map_sub_lt _ h2 h1`. Establish `hres : IsLocalRing.residue A ⟨z, hzA⟩ ^ (p ^ (n : ℕ)) = IsLocalRing.residue A ⟨x, hxA⟩ ^ (p ^ (n : ℕ))`. Rewrite using `[← sub_eq_zero, ← map_pow, ← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]`. Rewrite using `[← hq]`. Simplify using `using h3`.

Establish `hinj` using `iterateFrobenius_inj (IsLocalRing.ResidueField A) p (n : ℕ)`. Establish `heq : IsLocalRing.residue A ⟨z, hzA⟩ = IsLocalRing.residue A ⟨x, hxA⟩`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[iterateFrobenius_def, iterateFrobenius_def]`. Conclude with `hres`.

Establish `hzx : (⟨z, hzA⟩ - ⟨x, hxA⟩ : A) ∈ IsLocalRing.maximalIdeal A`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, heq, sub_self]`. Use `(ValuationSubring.valuation_lt_one_iff A _).mp hzx` as an intermediate fact. Establish `e2 : (τ'⁻¹ * τ) x = z` using `rfl`. Rewrite using `[e2]`.

Simplify using `using this`.
-/
theorem frob_inv_mul_mem_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ τ τ' : G E Ω, IsFrob (F := E) A (normV v) τ →
    IsFrob (F := E) A (normV v) τ' → τ'⁻¹ * τ ∈ Ine (F := E) A := by
  intro E Ω _ _ _ _ v A hA τ τ' hτ hτ'
  obtain ⟨hτD, hτF⟩ := hτ
  obtain ⟨hτ'D, hτ'F⟩ := hτ'

  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ v.asIdeal) := inferInstance
  letI : Fintype (𝓞 E ⧸ v.asIdeal) := Fintype.ofFinite _
  set p := ringChar (𝓞 E ⧸ v.asIdeal) with hpdef
  haveI : CharP (𝓞 E ⧸ v.asIdeal) p := ringChar.charP _
  obtain ⟨n, hp, hcard⟩ := FiniteField.card (𝓞 E ⧸ v.asIdeal) p
  have hq : normV v = p ^ (n : ℕ) := by
    simp only [normV, Nat.card_eq_fintype_card, hcard]

  have hpv : ((p : 𝓞 E)) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  have hpA : A.valuation (p : Ω) < 1 := by
    have := (hA (p : 𝓞 E)).mpr hpv
    simpa using this

  have hpk : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    simpa using hpA
  haveI : CharP (IsLocalRing.ResidueField A) p := by
    have h := CharP.ringChar_of_prime_eq_zero (R := IsLocalRing.ResidueField A) hp hpk
    rw [← h]; exact ringChar.charP _
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : ExpChar (IsLocalRing.ResidueField A) p := ExpChar.prime hp
  refine ⟨(Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hτ'D) hτD, fun x hx => ?_⟩
  have hxA : x ∈ A := A.valuation_le_one_iff x |>.mp hx
  set z := (τ'⁻¹ : G E Ω) (τ x) with hz
  have hzA : z ∈ A := by
    rw [hz, apply_mem_iff_of_mem_Dec ((Dec (F := E) A).inv_mem hτ'D), apply_mem_iff_of_mem_Dec hτD]
    exact hxA
  have hτ'z : τ' z = τ x := mul_inv_apply (τ x)
  have h1 := hτ'F z ((A.valuation_le_one_iff z).mpr hzA)
  rw [hτ'z] at h1
  have h2 := hτF x hx
  have h3 : A.valuation (z ^ normV v - x ^ normV v) < 1 := by
    have e : z ^ normV v - x ^ normV v = (τ x - x ^ normV v) - (τ x - z ^ normV v) := by ring
    rw [e]; exact Valuation.map_sub_lt _ h2 h1

  have hres : IsLocalRing.residue A ⟨z, hzA⟩ ^ (p ^ (n : ℕ)) = IsLocalRing.residue A ⟨x, hxA⟩ ^ (p ^ (n : ℕ)) := by
    rw [← sub_eq_zero, ← map_pow, ← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    rw [← hq]
    simpa using h3
  have hinj := iterateFrobenius_inj (IsLocalRing.ResidueField A) p (n : ℕ)
  have heq : IsLocalRing.residue A ⟨z, hzA⟩ = IsLocalRing.residue A ⟨x, hxA⟩ := by
    apply hinj
    rw [iterateFrobenius_def, iterateFrobenius_def]
    exact hres
  have hzx : (⟨z, hzA⟩ - ⟨x, hxA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, heq, sub_self]
  have := (ValuationSubring.valuation_lt_one_iff A _).mp hzx
  have e2 : (τ'⁻¹ * τ) x = z := rfl
  rw [e2]
  simpa using this

end GlobalTheory
