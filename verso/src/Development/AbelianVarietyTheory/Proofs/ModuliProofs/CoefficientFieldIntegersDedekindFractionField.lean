import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.SqrtNegDiscMemCoeffField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.CoeffRings

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k : ℕ, H.d + 1 = 4 * k` from `⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩`. Establish `hk' : (H.d : ℂ) + 1 = 4 * k` using `by exact_mod_cast hk`. Use `⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k : ℤ), by monicity!, ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]`. Simplify using `only [eq_intCast, Int.cast_natCast]`.

Take the linear combination `(1 / 4 : ℂ) * H.sqrt_neg_disc_sq - (1 / 4 : ℂ) * hk'`.
-/
theorem isIntegral_half (H : Host E) : IsIntegral ℤ ((1 + H.rt0) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, H.d + 1 = 4 * k := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have hk' : (H.d : ℂ) + 1 = 4 * k := by exact_mod_cast hk
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k : ℤ), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C]
  simp only [eq_intCast, Int.cast_natCast]
  linear_combination (1 / 4 : ℂ) * H.sqrt_neg_disc_sq - (1 / 4 : ℂ) * hk'

/- English proof (translation)
The claim follows from `(GlobalTheory.HostModel.isPrimitiveRoot_zeta hn).isIntegral hn`.
-/
theorem isIntegral_int_zeta {n : ℕ} (hn : 0 < n) : IsIntegral ℤ (zeta n) :=
  (GlobalTheory.HostModel.isPrimitiveRoot_zeta hn).isIntegral hn

/- English proof (translation)
Establish `h : IsIntegral W x` using `hx.tower_top`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := W) (K := L)).mp h`. Conclude with `hy ▸ y.2`.
-/
theorem mem_of_isIntegral {L : Type} [Field L] (W : ValuationSubring L) {x : L} (hx : IsIntegral ℤ x) : x ∈ W := by
  have h : IsIntegral W x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := L)).mp h
  exact hy ▸ y.2

/- English proof (translation)
Establish `hpV : (p : V) ∈ IsLocalRing.maximalIdeal V` using `ValuationSubring.coe_mem_nonunits_iff.mp (by simpa using hp)`. Take `⟨a, b, hab⟩ : IsCoprime (n : V) (p : V)` from `Nat.Coprime.cast h`. Assume the negation of the conclusion as `hn`. Establish `hnV : (n : V) ∈ IsLocalRing.maximalIdeal V` using `hn`. Establish `h1 : (1 : V) ∈ IsLocalRing.maximalIdeal V` using `hab ▸ add_mem (Ideal.mul_mem_left _ a hnV) (Ideal.mul_mem_left _ b hpV)`.

Conclude with `(IsLocalRing.maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).mpr h1)`.
-/
theorem isUnit_of_coprime {L : Type} [Field L] (V : ValuationSubring L) {p n : ℕ} (hp : (p : L) ∈ V.nonunits)
    (h : n.Coprime p) : IsUnit (n : V) := by
  have hpV : (p : V) ∈ IsLocalRing.maximalIdeal V :=
    ValuationSubring.coe_mem_nonunits_iff.mp (by simpa using hp)
  obtain ⟨a, b, hab⟩ : IsCoprime (n : V) (p : V) := Nat.Coprime.cast h
  by_contra hn
  have hnV : (n : V) ∈ IsLocalRing.maximalIdeal V := hn
  have h1 : (1 : V) ∈ IsLocalRing.maximalIdeal V :=
    hab ▸ add_mem (Ideal.mul_mem_left _ a hnV) (Ideal.mul_mem_left _ b hpV)
  exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `hd : H.d % 16 = 7` using `H.2`. Take `⟨k, hk⟩ : ∃ k : ℕ, 4 * k = H.d + 1` from `⟨(H.d + 1) / 4, by omega⟩`. Establish `hkC : (4 : ℂ) * k = H.d + 1` using `by exact_mod_cast hk`. Use `⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k : ℤ), by monicity!, ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_natCast, eq_intCast, Int.cast_natCast]`.

Take the linear combination `(1 / 4 : ℂ) * H.sqrt_neg_disc_sq + (1 / 4 : ℂ) * hkC`.
-/
private theorem isIntegral_one_add_rt0_div_two (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    IsIntegral ℤ ((1 + H.rt0) / 2) := by
  have hd : H.d % 16 = 7 := H.2
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 4 * k = H.d + 1 := ⟨(H.d + 1) / 4, by omega⟩
  have hkC : (4 : ℂ) * k = H.d + 1 := by exact_mod_cast hk
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k : ℤ), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_natCast, eq_intCast, Int.cast_natCast]
  linear_combination (1 / 4 : ℂ) * H.sqrt_neg_disc_sq + (1 / 4 : ℂ) * hkC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Set `e : R ≃+* g.range` to `RingEquiv.ofBijective g.rangeRestrict ⟨fun a b h => hg (congrArg Subtype.val h), g.rangeRestrict_surjective⟩`. Use `⟨e.symm.toRingHom.comp (Subring.inclusion hS), fun x => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Subtype.val (e.apply_symm_apply ⟨x, hS x.2⟩)`.
-/
private theorem exists_isInc_of_le_range {R : Type} [CommRing R] (g : R →+* ℂ)
    (hg : Function.Injective g) (S : Subring ℂ) (hS : S ≤ g.range) :
    ∃ b : S →+* R, _root_.GlobalTheory.Models.IsInc S.subtype g b := by
  let e : R ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict
    ⟨fun a b h => hg (congrArg Subtype.val h), g.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (Subring.inclusion hS), fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hS x.2⟩)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Rewrite `hpW` using `[ValuationSubring.mem_nonunits_iff]`. Establish `hle : ∀ m : ℤ, W.valuation (m : ℂ) ≤ 1` using `fun m => by`. Simplify using `using W.valuation_le_one (m : W)`. Establish `hn1 : W.valuation (n : ℂ) = 1`. Use `le_antisymm (by simpa using hle n) (not_lt.mp fun hlt => ?_)` and prove the remaining obligations.

Take `⟨u, v, huv⟩` from `Nat.isCoprime_iff_coprime.mpr hn`. Establish `huvC : (u : ℂ) * n + v * p = 1` using `by exact_mod_cast huv`. Establish `h1 : W.valuation ((u : ℂ) * n) < 1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hle u)) hlt`.

Establish `h2 : W.valuation ((v : ℂ) * p) < 1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hle v)) hpW`. Use `Valuation.map_add_lt _ h1 h2` as an intermediate fact. Rewrite `this` using `[huvC, map_one]`.

Conclude with `lt_irrefl _ this`. Conclude with `W.mem_of_valuation_le_one _ (by rw [map_inv₀, hn1, inv_one])`.
-/
private theorem natCast_inv_mem_of_coprime (W : ValuationSubring ℂ) {p n : ℕ}
    (hpW : (p : ℂ) ∈ W.nonunits) (hn : n.Coprime p) : (n : ℂ)⁻¹ ∈ W := by
  rw [ValuationSubring.mem_nonunits_iff] at hpW
  have hle : ∀ m : ℤ, W.valuation (m : ℂ) ≤ 1 := fun m => by
    simpa using W.valuation_le_one (m : W)
  have hn1 : W.valuation (n : ℂ) = 1 := by
    refine le_antisymm (by simpa using hle n) (not_lt.mp fun hlt => ?_)
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hn
    have huvC : (u : ℂ) * n + v * p = 1 := by exact_mod_cast huv
    have h1 : W.valuation ((u : ℂ) * n) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle u)) hlt
    have h2 : W.valuation ((v : ℂ) * p) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle v)) hpW
    have := Valuation.map_add_lt _ h1 h2
    rw [huvC, map_one] at this
    exact lt_irrefl _ this
  exact W.mem_of_valuation_le_one _ (by rw [map_inv₀, hn1, inv_one])

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `hV : IsIntegral V x` using `hx.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hV`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
private theorem mem_valuationSubring_of_isIntegral_moduli {K : Type} [Field K] (V : ValuationSubring K)
    {x : K} (hx : IsIntegral ℤ x) : x ∈ V := by
  have hV : IsIntegral V x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hV
  rw [← hy]
  exact y.2

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Set `f : 𝓞 K →+* V` to `(algebraMap (𝓞 K) K).codRestrict V.toSubring (fun x => mem_valuationSubring_of_isIntegral_moduli V (RingOfIntegers.isIntegral_coe x))`. Use `letI : Algebra (𝓞 K) V := f.toAlgebra`. Establish `hcoe : ∀ x : 𝓞 K, ((algebraMap (𝓞 K) V x : V) : K) = algebraMap (𝓞 K) K x` using `fun _ => rfl`. Set `P : Ideal (𝓞 K)` to `(IsLocalRing.maximalIdeal V).comap (algebraMap (𝓞 K) V)`. Establish `hM : P.primeCompl ≤ nonZeroDivisors (𝓞 K)`.

Introduce `s hs`. Use `mem_nonZeroDivisors_of_ne_zero ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hs P.zero_mem`. Establish `hpP : ((p : 𝓞 K)) ∈ P` using `by show algebraMap (𝓞 K) V p ∈ IsLocalRing.maximalIdeal V`.

Rewrite using `[map_natCast]`. Conclude with `hpV`. Establish `hP : P ≠ ⊥`. Introduce `h`. Establish `: ((p : 𝓞 K)) = 0` using `by simpa [h] using hpP`.

Conclude with `hp (by exact_mod_cast this)`. Establish `hinj : Function.Injective (algebraMap (𝓞 K) V)`. Introduce `a b h`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Use `congrArg Subtype.val h` as an intermediate fact.

Simplify `this` using `[hcoe]`. Use `haveI : IsLocalization P.primeCompl V := { map_units := by`. Introduce and unpack `⟨s, hs⟩`. Assume the negation of the conclusion as `h`. Conclude with `hs h`.

Use `surj := by`. Introduce `v`. Take `⟨a, b, hb, hab⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) (v : K)`. Establish `hb0 : algebraMap (𝓞 K) K b ≠ 0`. Introduce `h0`.

Conclude with `nonZeroDivisors.ne_zero hb (by exact_mod_cast (IsFractionRing.injective (𝓞 K) K) (h0.trans (map_zero _).symm))`. Set `Dp` to `Localization.AtPrime P`. Use `haveI : IsDiscreteValuationRing Dp := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hP Dp`. Establish `hDinj : Function.Injective (algebraMap (𝓞 K) Dp)` using `IsLocalization.injective Dp hM`. Take `⟨c, hc⟩` from `ValuationRing.cond (algebraMap (𝓞 K) Dp a) (algebraMap (𝓞 K) Dp b)`.

Take `⟨⟨x, s⟩, rfl⟩` from `IsLocalization.mk'_surjective P.primeCompl c`. Establish `hspec` using `IsLocalization.mk'_spec Dp x s`. Establish `key : ∀ u w : 𝓞 K, algebraMap (𝓞 K) Dp u * IsLocalization.mk' Dp x s = algebraMap (𝓞 K) Dp w → u * x = w * s`. Introduce `u w h`. Apply `hDinj` to reduce the goal to its premises.

Rewrite using `[map_mul, map_mul, ← h, ← hspec, _root_.mul_assoc]`. Break down `hc with hc | hc` into its components or cases. Establish `h1` using `key a b hc`. Distinguish the cases in `hx : x ∈ P`. It suffices to derive a contradiction.

Apply `s.2` to reduce the goal to its premises. Use `show algebraMap (𝓞 K) V s ∈ IsLocalRing.maximalIdeal V`. Establish `hsv : algebraMap (𝓞 K) V s = v * algebraMap (𝓞 K) V x`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show algebraMap (𝓞 K) K s = (v : K) * algebraMap (𝓞 K) K x`.

Rewrite using `[← hab, div_mul_eq_mul_div, eq_div_iff hb0]`. Rewrite using `[← map_mul, ← map_mul, h1, mul_comm]`. Rewrite using `[hsv]`. Conclude with `Ideal.mul_mem_left _ _ hx`. Use `⟨(s, ⟨x, hx⟩), ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show (v : K) * algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K s`. Rewrite using `[← hab, div_mul_eq_mul_div, div_eq_iff hb0, ← map_mul, ← map_mul, h1, mul_comm]`. Establish `h1` using `key b a hc`. Use `⟨(x, s), ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show (v : K) * algebraMap (𝓞 K) K s = algebraMap (𝓞 K) K x`. Rewrite using `[← hab, div_mul_eq_mul_div, div_eq_iff hb0, ← map_mul, ← map_mul, ← h1, mul_comm]`. Use `exists_of_eq := by`. Introduce `x y h`.

Conclude with `⟨1, by rw [hinj h]⟩ }`. Conclude with `IsLocalization.isDedekindDomain (𝓞 K) hM V`.
-/
private theorem isDedekindDomain_valuationSubring_of_not_isUnit_natCast {K : Type} [Field K] [NumberField K]
    (V : ValuationSubring K) (p : ℕ) (hp : p ≠ 0) (hpV : ¬ IsUnit (p : V)) :
    IsDedekindDomain V := by
  let f : 𝓞 K →+* V := (algebraMap (𝓞 K) K).codRestrict V.toSubring
    (fun x => mem_valuationSubring_of_isIntegral_moduli V (RingOfIntegers.isIntegral_coe x))
  letI : Algebra (𝓞 K) V := f.toAlgebra
  have hcoe : ∀ x : 𝓞 K, ((algebraMap (𝓞 K) V x : V) : K) = algebraMap (𝓞 K) K x := fun _ => rfl
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal V).comap (algebraMap (𝓞 K) V)
  have hM : P.primeCompl ≤ nonZeroDivisors (𝓞 K) := by
    intro s hs
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rintro rfl
    exact hs P.zero_mem
  have hpP : ((p : 𝓞 K)) ∈ P := by
    show algebraMap (𝓞 K) V p ∈ IsLocalRing.maximalIdeal V
    rw [map_natCast]
    exact hpV
  have hP : P ≠ ⊥ := by
    intro h
    have : ((p : 𝓞 K)) = 0 := by simpa [h] using hpP
    exact hp (by exact_mod_cast this)
  have hinj : Function.Injective (algebraMap (𝓞 K) V) := by
    intro a b h
    apply RingOfIntegers.coe_injective
    have := congrArg Subtype.val h
    simpa [hcoe] using this
  haveI : IsLocalization P.primeCompl V :=
    { map_units := by
        rintro ⟨s, hs⟩
        by_contra h
        exact hs h
      surj := by
        intro v
        obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (v : K)
        have hb0 : algebraMap (𝓞 K) K b ≠ 0 := by
          intro h0
          exact nonZeroDivisors.ne_zero hb
            (by exact_mod_cast (IsFractionRing.injective (𝓞 K) K) (h0.trans (map_zero _).symm))
        let Dp := Localization.AtPrime P
        haveI : IsDiscreteValuationRing Dp :=
          IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hP Dp
        have hDinj : Function.Injective (algebraMap (𝓞 K) Dp) := IsLocalization.injective Dp hM
        obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap (𝓞 K) Dp a) (algebraMap (𝓞 K) Dp b)
        obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
        have hspec := IsLocalization.mk'_spec Dp x s
        have key : ∀ u w : 𝓞 K,
            algebraMap (𝓞 K) Dp u * IsLocalization.mk' Dp x s = algebraMap (𝓞 K) Dp w →
            u * x = w * s := by
          intro u w h
          apply hDinj
          rw [map_mul, map_mul, ← h, ← hspec, _root_.mul_assoc]
        rcases hc with hc | hc
        · have h1 := key a b hc
          by_cases hx : x ∈ P
          · exfalso
            apply s.2
            show algebraMap (𝓞 K) V s ∈ IsLocalRing.maximalIdeal V
            have hsv : algebraMap (𝓞 K) V s = v * algebraMap (𝓞 K) V x := by
              apply Subtype.ext
              show algebraMap (𝓞 K) K s = (v : K) * algebraMap (𝓞 K) K x
              rw [← hab, div_mul_eq_mul_div, eq_div_iff hb0]
              rw [← map_mul, ← map_mul, h1, mul_comm]
            rw [hsv]
            exact Ideal.mul_mem_left _ _ hx
          · refine ⟨(s, ⟨x, hx⟩), ?_⟩
            apply Subtype.ext
            show (v : K) * algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K s
            rw [← hab, div_mul_eq_mul_div, div_eq_iff hb0, ← map_mul, ← map_mul, h1, mul_comm]
        · have h1 := key b a hc
          refine ⟨(x, s), ?_⟩
          apply Subtype.ext
          show (v : K) * algebraMap (𝓞 K) K s = algebraMap (𝓞 K) K x
          rw [← hab, div_mul_eq_mul_div, div_eq_iff hb0, ← map_mul, ← map_mul, ← h1, mul_comm]
      exists_of_eq := by
        intro x y h
        exact ⟨1, by rw [hinj h]⟩ }
  exact IsLocalization.isDedekindDomain (𝓞 K) hM V

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Introduce `E _ _ _ H l c`. Use `haveI : FiniteDimensional ℚ c.F := c.2`. Use `haveI : NumberField c.F := ⟨⟩`. Establish `hw : IsIntegral ℤ ((1 + H.rt0) / 2)` using `isIntegral_one_add_rt0_div_two H`. Establish `hnatF : ∀ n : ℕ, (n : ℂ) ∈ c.F` using `fun n => natCast_mem c.F n`.

Establish `hwF : (1 + H.rt0) / 2 ∈ c.F` using `div_mem (add_mem (one_mem _) (_root_.GlobalTheory.HostModel.sqrtNegDisc_mem_coeffField c)) (by simpa using hnatF 2)`. Establish `hintF : ∀ {x : ℂ} (hx : x ∈ c.F), IsIntegral ℤ x → IsIntegral ℤ (⟨x, hx⟩ : c.F)` using `fun hx h => (isIntegral_algHom_iff c.F.val.toRingHom.toIntAlgHom Subtype.val_injective).mp h`. Use `⟨?_, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Use `⟨⟨inferInstance, inferInstance⟩, inferInstance, ?_⟩` and prove the remaining obligations. Establish `h : IsFractionRing (𝓞 c.F) c.F` using `inferInstance`.

Conclude with `h`. Introduce `A hA`. Establish `hApos : 0 < A` using `Nat.pos_of_dvd_of_pos hA l.A_pos`. Establish `hzF : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A ∈ c.F`. Take `⟨k, hk⟩` from `_root_.GlobalTheory.LevelExist.zeta_eq_pow_of_dvd l.A_pos hA`.

Rewrite using `[hk]`. Conclude with `pow_mem (_root_.GlobalTheory.HostModel.zeta_A_mem_coeff c) k`. Establish `hz : IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A)` using `(_root_.GlobalTheory.HostModel.isPrimitiveRoot_zeta hApos).isIntegral hApos`. Use `exists_isInc_of_le_range _ (fun a b h => RingOfIntegers.coe_injective (Subtype.val_injective h)) _ ?_` and prove the remaining obligations. Unfold `_root_.GlobalTheory.Models.RZ`.

Rewrite using `[Subring.closure_le]`. Introduce `x hx`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx`. Break down `hx with rfl | rfl | rfl` into its components or cases. Conclude with `⟨⟨⟨_, hwF⟩, hintF hwF hw⟩, rfl⟩`.

Conclude with `⟨1, by simp⟩`. Conclude with `⟨⟨⟨_, hzF⟩, hintF hzF hz⟩, rfl⟩`. Introduce `p W hp hpW`. Establish `memV : ∀ x : c.F, x ∈ c.V W ↔ (x : ℂ) ∈ W` using `fun x => by`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.V`.

Conclude with `ValuationSubring.mem_comap`. Establish `hunit : ∀ n : ℕ, n.Coprime p → IsUnit (n : c.V W)`. Introduce `n hn`. Establish `hinvW` using `natCast_inv_mem_of_coprime W hpW hn`. Establish `hn0 : (n : ℂ) ≠ 0`.

Use `norm_cast`. Introduce and unpack `rfl`. Conclude with `hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hn)`. Establish `hnF : (n : ℂ)⁻¹ ∈ c.F` using `inv_mem (hnatF n)`. Use `IsUnit.of_mul_eq_one (a := (n : c.V W)) ⟨⟨_, hnF⟩, (memV _).mpr hinvW⟩ ?_` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hn0]`. Use `⟨?_, hunit, ?_⟩` and prove the remaining obligations. Establish `hpV : ¬ IsUnit (p : c.V W)`.

Introduce and unpack `hu`. Take `⟨b, hb⟩` from `hu.exists_right_inv`. Establish `hbC : (p : ℂ) * ((b : c.F) : ℂ) = 1`. Use `congrArg (fun y : c.V W => ((y : c.F) : ℂ)) hb` as an intermediate fact. Simplify using `using this`.

Rewrite `hpW` using `[ValuationSubring.mem_nonunits_iff]`. Establish `hbW : W.valuation ((b : c.F) : ℂ) ≤ 1` using `W.valuation_le_one ⟨_, (memV _).mp b.2⟩`. Use `lt_of_le_of_lt (mul_le_of_le_one_right' hbW) hpW` as an intermediate fact. Rewrite `this` using `[← map_mul, hbC, map_one]`. Conclude with `lt_irrefl _ this`.

Establish `hD` using `isDedekindDomain_valuationSubring_of_not_isUnit_natCast (c.V W) p hp.ne_zero hpV`. Use `⟨⟨inferInstance, hD⟩, ⟨fun a b h => by exact_mod_cast congrArg Subtype.val h⟩, ?_⟩` and prove the remaining obligations. Establish `h : IsFractionRing (c.V W) c.F` using `inferInstance`. Conclude with `h`. Introduce `S A hS hA hzF`.

Establish `hz : IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A)` using `(_root_.GlobalTheory.HostModel.isPrimitiveRoot_zeta hA).isIntegral hA`. Establish `hSF : (S : ℂ)⁻¹ ∈ c.F` using `inv_mem (hnatF S)`. Use `exists_isInc_of_le_range _ (fun a b h => Subtype.val_injective (Subtype.val_injective h)) _ ?_` and prove the remaining obligations. Unfold `_root_.GlobalTheory.Models.RZ`. Rewrite using `[Subring.closure_le]`.

Introduce `x hx`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx`. Break down `hx with rfl | rfl | rfl` into its components or cases. Conclude with `⟨⟨⟨_, hwF⟩, (memV _).mpr (mem_valuationSubring_of_isIntegral_moduli W hw)⟩, rfl⟩`. Conclude with `⟨⟨⟨_, hSF⟩, (memV _).mpr (natCast_inv_mem_of_coprime W hpW hS)⟩, rfl⟩`.

Conclude with `⟨⟨⟨_, hzF⟩, (memV _).mpr (mem_valuationSubring_of_isIntegral_moduli W hz)⟩, rfl⟩`.
-/
theorem _root_.GlobalTheory.CoeffRings.coeff_isDedFrac : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.GlobalTheory.Models.IsDedFrac (algebraMap (𝓞 c.F) c.F) ∧ Algebra.FiniteType ℤ (𝓞 c.F) ∧ (∀ A : ℕ, A ∣ l.A → ∃ b : _root_.GlobalTheory.Models.RZ H 1 A →+* 𝓞 c.F, _root_.GlobalTheory.Models.IsInc (_root_.GlobalTheory.Models.RZ H 1 A).subtype (c.F.val.toRingHom.comp (algebraMap (𝓞 c.F) c.F)) b) ∧ ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → _root_.GlobalTheory.Models.IsDedFrac (c.V W).subtype ∧ (∀ n : ℕ, n.Coprime p → IsUnit (n : c.V W)) ∧ ∀ S A : ℕ, S.Coprime p → 0 < A → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A ∈ c.F → ∃ b : _root_.GlobalTheory.Models.RZ H S A →+* c.V W, _root_.GlobalTheory.Models.IsInc (_root_.GlobalTheory.Models.RZ H S A).subtype (c.F.val.toRingHom.comp (c.V W).subtype) b := by
  intro E _ _ _ H l c
  haveI : FiniteDimensional ℚ c.F := c.2
  haveI : NumberField c.F := ⟨⟩
  have hw : IsIntegral ℤ ((1 + H.rt0) / 2) := isIntegral_one_add_rt0_div_two H
  have hnatF : ∀ n : ℕ, (n : ℂ) ∈ c.F := fun n => natCast_mem c.F n
  have hwF : (1 + H.rt0) / 2 ∈ c.F :=
    div_mem (add_mem (one_mem _) (_root_.GlobalTheory.HostModel.sqrtNegDisc_mem_coeffField c)) (by simpa using hnatF 2)
  have hintF : ∀ {x : ℂ} (hx : x ∈ c.F), IsIntegral ℤ x → IsIntegral ℤ (⟨x, hx⟩ : c.F) :=
    fun hx h => (isIntegral_algHom_iff c.F.val.toRingHom.toIntAlgHom Subtype.val_injective).mp h
  refine ⟨?_, inferInstance, ?_, ?_⟩
  · refine ⟨⟨inferInstance, inferInstance⟩, inferInstance, ?_⟩
    have h : IsFractionRing (𝓞 c.F) c.F := inferInstance
    exact h
  · intro A hA
    have hApos : 0 < A := Nat.pos_of_dvd_of_pos hA l.A_pos
    have hzF : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A ∈ c.F := by
      obtain ⟨k, hk⟩ := _root_.GlobalTheory.LevelExist.zeta_eq_pow_of_dvd l.A_pos hA
      rw [hk]
      exact pow_mem (_root_.GlobalTheory.HostModel.zeta_A_mem_coeff c) k
    have hz : IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A) := (_root_.GlobalTheory.HostModel.isPrimitiveRoot_zeta hApos).isIntegral hApos
    refine exists_isInc_of_le_range _
      (fun a b h => RingOfIntegers.coe_injective (Subtype.val_injective h)) _ ?_
    unfold _root_.GlobalTheory.Models.RZ
    rw [Subring.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨⟨⟨_, hwF⟩, hintF hwF hw⟩, rfl⟩
    · exact ⟨1, by simp⟩
    · exact ⟨⟨⟨_, hzF⟩, hintF hzF hz⟩, rfl⟩
  · intro p W hp hpW
    have memV : ∀ x : c.F, x ∈ c.V W ↔ (x : ℂ) ∈ W := fun x => by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.V
      exact ValuationSubring.mem_comap
    have hunit : ∀ n : ℕ, n.Coprime p → IsUnit (n : c.V W) := by
      intro n hn
      have hinvW := natCast_inv_mem_of_coprime W hpW hn
      have hn0 : (n : ℂ) ≠ 0 := by
        norm_cast
        rintro rfl
        exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hn)
      have hnF : (n : ℂ)⁻¹ ∈ c.F := inv_mem (hnatF n)
      refine IsUnit.of_mul_eq_one (a := (n : c.V W)) ⟨⟨_, hnF⟩, (memV _).mpr hinvW⟩ ?_
      apply Subtype.ext
      apply Subtype.ext
      simp [hn0]
    refine ⟨?_, hunit, ?_⟩
    · have hpV : ¬ IsUnit (p : c.V W) := by
        rintro hu
        obtain ⟨b, hb⟩ := hu.exists_right_inv
        have hbC : (p : ℂ) * ((b : c.F) : ℂ) = 1 := by
          have := congrArg (fun y : c.V W => ((y : c.F) : ℂ)) hb
          simpa using this
        rw [ValuationSubring.mem_nonunits_iff] at hpW
        have hbW : W.valuation ((b : c.F) : ℂ) ≤ 1 :=
          W.valuation_le_one ⟨_, (memV _).mp b.2⟩
        have := lt_of_le_of_lt (mul_le_of_le_one_right' hbW) hpW
        rw [← map_mul, hbC, map_one] at this
        exact lt_irrefl _ this
      have hD := isDedekindDomain_valuationSubring_of_not_isUnit_natCast (c.V W) p hp.ne_zero hpV
      refine ⟨⟨inferInstance, hD⟩, ⟨fun a b h => by exact_mod_cast congrArg Subtype.val h⟩, ?_⟩
      have h : IsFractionRing (c.V W) c.F := inferInstance
      exact h
    · intro S A hS hA hzF
      have hz : IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A) := (_root_.GlobalTheory.HostModel.isPrimitiveRoot_zeta hA).isIntegral hA
      have hSF : (S : ℂ)⁻¹ ∈ c.F := inv_mem (hnatF S)
      refine exists_isInc_of_le_range _
        (fun a b h => Subtype.val_injective (Subtype.val_injective h)) _ ?_
      unfold _root_.GlobalTheory.Models.RZ
      rw [Subring.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨⟨⟨_, hwF⟩, (memV _).mpr (mem_valuationSubring_of_isIntegral_moduli W hw)⟩, rfl⟩
      · exact ⟨⟨⟨_, hSF⟩, (memV _).mpr (natCast_inv_mem_of_coprime W hpW hS)⟩, rfl⟩
      · exact ⟨⟨⟨_, hzF⟩, (memV _).mpr (mem_valuationSubring_of_isIntegral_moduli W hz)⟩, rfl⟩

end GlobalTheory.CoeffRings
