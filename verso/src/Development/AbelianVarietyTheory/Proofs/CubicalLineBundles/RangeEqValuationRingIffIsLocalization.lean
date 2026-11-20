import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

/- English proof (translation)
Introduce `K _ _ p R _ _ _ _ _ _`. Establish `hinj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `htow : ∀ a : 𝓞 K, algebraMap R K (algebraMap (𝓞 K) R a) = algebraMap (𝓞 K) K a` using `fun a => (IsScalarTower.algebraMap_apply (𝓞 K) R K a).symm`. Establish `hone : ∀ s : p.asIdeal.primeCompl, p.valuation K (algebraMap (𝓞 K) K s) = 1` using `fun s => (p.valuation_eq_one_iff_notMem (K := K)).2 s.2`. Establish `hne : ∀ s : p.asIdeal.primeCompl, algebraMap (𝓞 K) K s ≠ 0`.

Introduce `s h`. Use `hone s` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `zero_ne_one this`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `(isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s`. Take `⟨r, hr⟩` from `(h (algebraMap (𝓞 K) K s)⁻¹).2 (by rw [map_inv₀, hone s, inv_one])`. Use `IsUnit.of_mul_eq_one r (hinj ?_)` and prove the remaining obligations.

Rewrite using `[map_mul, htow, hr, map_one, mul_inv_cancel₀ (hne s)]`. Introduce `z`. Take `⟨n, d, hnd⟩` from `p.exists_primeCompl_mul_eq_of_integer (algebraMap R K z) ((h _).1 ⟨z, rfl⟩)`. Use `⟨(n, d), hinj ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, htow, htow]`.

Conclude with `hnd`. Introduce `x y hxy`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `h2 : algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K y`. Rewrite using `[← htow, ← htow, hxy]`.

Rewrite using `[IsFractionRing.injective (𝓞 K) K h2]`. Introduce `h y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Take `⟨⟨n, d⟩, hnd⟩` from `IsLocalization.surj p.asIdeal.primeCompl z`.

Establish `h2` using `congrArg (fun t => p.valuation K (algebraMap R K t)) hnd`. Simplify using `only [map_mul, htow, hone] at h2`. Rewrite using `[(_root_.mul_one _).symm.trans h2]`. Conclude with `p.valuation_le_one n`. Introduce `hy`.

Take `⟨n, d, hnd⟩` from `p.exists_primeCompl_mul_eq_of_integer y hy`. Use `⟨IsLocalization.mk' R n d, ?_⟩` and prove the remaining obligations. Apply `mul_right_cancel₀ (hne d)` to reduce the goal to its premises. Rewrite using `[hnd, ← htow, ← htow, ← map_mul, IsLocalization.mk'_spec]`.
-/
theorem range_eq_valuationRing_iff_isLocalization :
    ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) (R : Type) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K] [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) R K], (∀ y : K, y ∈ Set.range (algebraMap R K) ↔ p.valuation K y ≤ 1) ↔ IsLocalization p.asIdeal.primeCompl R := by
  intro K _ _ p R _ _ _ _ _ _
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have htow : ∀ a : 𝓞 K, algebraMap R K (algebraMap (𝓞 K) R a) = algebraMap (𝓞 K) K a :=
    fun a => (IsScalarTower.algebraMap_apply (𝓞 K) R K a).symm
  have hone : ∀ s : p.asIdeal.primeCompl, p.valuation K (algebraMap (𝓞 K) K s) = 1 :=
    fun s => (p.valuation_eq_one_iff_notMem (K := K)).2 s.2
  have hne : ∀ s : p.asIdeal.primeCompl, algebraMap (𝓞 K) K s ≠ 0 := by
    intro s h
    have := hone s
    rw [h, map_zero] at this
    exact zero_ne_one this
  constructor
  · intro h
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · intro s
      obtain ⟨r, hr⟩ := (h (algebraMap (𝓞 K) K s)⁻¹).2 (by rw [map_inv₀, hone s, inv_one])
      refine IsUnit.of_mul_eq_one r (hinj ?_)
      rw [map_mul, htow, hr, map_one, mul_inv_cancel₀ (hne s)]
    · intro z
      obtain ⟨n, d, hnd⟩ := p.exists_primeCompl_mul_eq_of_integer (algebraMap R K z)
        ((h _).1 ⟨z, rfl⟩)
      refine ⟨(n, d), hinj ?_⟩
      rw [map_mul, htow, htow]
      exact hnd
    · intro x y hxy
      refine ⟨1, ?_⟩
      have h2 : algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K y := by
        rw [← htow, ← htow, hxy]
      rw [IsFractionRing.injective (𝓞 K) K h2]
  · intro h y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj p.asIdeal.primeCompl z
      have h2 := congrArg (fun t => p.valuation K (algebraMap R K t)) hnd
      simp only [map_mul, htow, hone] at h2
      rw [(_root_.mul_one _).symm.trans h2]
      exact p.valuation_le_one n
    · intro hy
      obtain ⟨n, d, hnd⟩ := p.exists_primeCompl_mul_eq_of_integer y hy
      refine ⟨IsLocalization.mk' R n d, ?_⟩
      apply mul_right_cancel₀ (hne d)
      rw [hnd, ← htow, ← htow, ← map_mul, IsLocalization.mk'_spec]

end GlobalTheory.LamF
