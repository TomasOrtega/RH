import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CoeffValuation

/- English proof (translation)
Establish `halg : IsAlgebraic ℤ x` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr (Algebra.IsAlgebraic.isAlgebraic x)`. Take `⟨m, hm, hint⟩` from `halg.exists_integral_multiple`. Establish `h1 : m • x ∈ W`. Establish `h : IsIntegral W (m • x)` using `hint.tower_top`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := W) (K := L)).mp h`.

Conclude with `hy ▸ y.2`. Establish `h2 : ((m.natAbs : ℕ) : L)⁻¹ ∈ W`. Use `h m.natAbs (Int.natAbs_ne_zero.mpr hm)` as an intermediate fact. Rewrite `this` using `[ValuationSubring.mem_nonunits_iff_or]`. Assume the negation of the conclusion as `hc`.

Conclude with `this (Or.inr hc)`. Establish `hm' : (m : L) ≠ 0` using `Int.cast_ne_zero.mpr hm`. Establish `h3 : (m : L)⁻¹ ∈ W`. Break down `Int.natAbs_eq m with e | e` into its components or cases. Rewrite using `[e, Int.cast_natCast]`.

Conclude with `h2`. Rewrite using `[e, Int.cast_neg, Int.cast_natCast, inv_neg]`. Conclude with `W.neg_mem _ h2`. Establish `: x = (m : L)⁻¹ * (m • x)`. Rewrite using `[zsmul_eq_mul, inv_mul_cancel_left₀ hm']`.

Rewrite using `[this]`. Conclude with `W.mul_mem _ _ h3 h1`.
-/
theorem mem_of_forall_natCast {L : Type} [Field L] [NumberField L] (W : ValuationSubring L)
    (h : ∀ n : ℕ, n ≠ 0 → (n : L) ∉ W.nonunits) (x : L) : x ∈ W := by
  have halg : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨m, hm, hint⟩ := halg.exists_integral_multiple
  have h1 : m • x ∈ W := by
    have h : IsIntegral W (m • x) := hint.tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := L)).mp h
    exact hy ▸ y.2
  have h2 : ((m.natAbs : ℕ) : L)⁻¹ ∈ W := by
    have := h m.natAbs (Int.natAbs_ne_zero.mpr hm)
    rw [ValuationSubring.mem_nonunits_iff_or] at this
    by_contra hc
    exact this (Or.inr hc)
  have hm' : (m : L) ≠ 0 := Int.cast_ne_zero.mpr hm
  have h3 : (m : L)⁻¹ ∈ W := by
    rcases Int.natAbs_eq m with e | e
    · rw [e, Int.cast_natCast]; exact h2
    · rw [e, Int.cast_neg, Int.cast_natCast, inv_neg]; exact W.neg_mem _ h2
  have : x = (m : L)⁻¹ * (m • x) := by
    rw [zsmul_eq_mul, inv_mul_cancel_left₀ hm']
  rw [this]
  exact W.mul_mem _ _ h3 h1

/- English proof (translation)
Distinguish the cases in `h : ∃ n : ℕ, n ≠ 0 ∧ (n : L) ∈ W.nonunits`. Take `⟨n, hn, hW⟩` from `h`. Use `(GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField W hn hW).1` as an intermediate fact. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible W`.

Use `⟨π, ?_⟩` and prove the remaining obligations. Use `(isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨_, k, rfl⟩`. Conclude with `IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective W L)).mpr (pow_ne_zero k hπ.ne_zero))`. Introduce `z`.

Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := W) z`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Take `⟨k, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ`. Use `⟨⟨a * (u⁻¹ : Wˣ), ⟨π ^ k, k, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Establish `hb1 : algebraMap W L (u * π ^ k) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective W L)).mpr hb0`.

Rewrite using `[div_mul_eq_mul_div, div_eq_iff hb1, ← map_mul, ← map_mul]`. Use `congr 1`. Rewrite using `[mul_assoc, Units.inv_mul_cancel_left]`. Introduce `a b hab`. Conclude with `⟨1, by rw [IsFractionRing.injective W L hab]⟩`.

Establish `hall : ∀ x : L, x ∈ W` using `mem_of_forall_natCast W fun n hn hW => h ⟨n, hn, hW⟩`. Establish `hbij : Function.Bijective (algebraMap W L)` using `⟨IsFractionRing.injective W L, fun x => ⟨⟨x, hall x⟩, rfl⟩⟩`. Establish `hF : IsField W` using `(RingEquiv.ofBijective _ hbij).toMulEquiv.isField (Field.toIsField L)`. Establish `: IsPrincipalIdealRing W` using `hF.isPrincipalIdealRing`. Conclude with `⟨inferInstance, 1, IsLocalization.away_of_isUnit_of_bijective L isUnit_one hbij⟩`.
-/
theorem dedekind_and_away {L : Type} [Field L] [NumberField L] (W : ValuationSubring L) :
    IsDedekindDomain W ∧ ∃ π : W, IsLocalization.Away π L := by
  by_cases h : ∃ n : ℕ, n ≠ 0 ∧ (n : L) ∈ W.nonunits
  · obtain ⟨n, hn, hW⟩ := h
    have := (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField W hn hW).1
    refine ⟨inferInstance, ?_⟩
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
    refine ⟨π, ?_⟩
    refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨_, k, rfl⟩
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective W L)).mpr (pow_ne_zero k hπ.ne_zero))
    · intro z
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) z
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
      refine ⟨⟨a * (u⁻¹ : Wˣ), ⟨π ^ k, k, rfl⟩⟩, ?_⟩
      have hb1 : algebraMap W L (u * π ^ k) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W L)).mpr hb0
      rw [div_mul_eq_mul_div, div_eq_iff hb1, ← map_mul, ← map_mul]
      congr 1
      rw [mul_assoc, Units.inv_mul_cancel_left]
    · intro a b hab
      exact ⟨1, by rw [IsFractionRing.injective W L hab]⟩
  · have hall : ∀ x : L, x ∈ W := mem_of_forall_natCast W fun n hn hW => h ⟨n, hn, hW⟩
    have hbij : Function.Bijective (algebraMap W L) :=
      ⟨IsFractionRing.injective W L, fun x => ⟨⟨x, hall x⟩, rfl⟩⟩
    have hF : IsField W := (RingEquiv.ofBijective _ hbij).toMulEquiv.isField (Field.toIsField L)
    have : IsPrincipalIdealRing W := hF.isPrincipalIdealRing
    exact ⟨inferInstance, 1, IsLocalization.away_of_isUnit_of_bijective L isUnit_one hbij⟩

/- English proof (translation)
Introduce `E _ _ _ H l c W`. Use `c.fin` as an intermediate fact. Establish `: NumberField c.F` using `NumberField.mk`. Take `⟨hD, π, hπ⟩` from `dedekind_and_away W`. Conclude with `⟨⟨⟨inferInstance, hD⟩, inferInstance, (inferInstance : IsFractionRing W c.F)⟩, IsOpenImmersion.of_isLocalization (S := c.F) π⟩`.
-/
theorem isDedFrac_and_isOpenImmersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (W : ValuationSubring c.F), GlobalTheory.Models.IsDedFrac W.subtype ∧ IsOpenImmersion (spMap W.subtype) := by
  intro E _ _ _ H l c W
  have := c.fin
  have : NumberField c.F := NumberField.mk
  obtain ⟨hD, π, hπ⟩ := dedekind_and_away W
  exact ⟨⟨⟨inferInstance, hD⟩, inferInstance, (inferInstance : IsFractionRing W c.F)⟩,
    IsOpenImmersion.of_isLocalization (S := c.F) π⟩

end GlobalTheory.CoeffValuation
