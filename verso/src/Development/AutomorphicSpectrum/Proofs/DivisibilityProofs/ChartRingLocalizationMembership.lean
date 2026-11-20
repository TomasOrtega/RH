import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsCompactUnitaryPointsAtPlaceFstMemCompact
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

/- English proof (translation)
Introduce `K _ _ ι _ Ω _ y A _ _ hA m _ O _ _ _ _ _ _ _ c hc t`. Establish `hconst : ∀ a : A, algebraMap A Ω a ∈ chartRing ℤ (segreVec y) c` using `hA c hc`. Establish `hmul : ∀ {a b : A}, a ∉ m → b ∉ m → a * b ∉ m` using `fun ha hb h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha hb`. Prove the components needed by the constructor for the conclusion. Introduce `ht`.

Proceed by induction on `ht using Algebra.adjoin_induction with`. Consider the case `mem a ha`. Use `⟨1, fun h => Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one m).2 h), ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, one_mul]`. Conclude with `Algebra.subset_adjoin ha`.

Consider the case `algebraMap o`. Take `⟨⟨a, s⟩, h⟩` from `IsLocalization.surj m.primeCompl o`. Use `⟨s, s.2, ?_⟩` and prove the remaining obligations. Establish `h' : algebraMap A Ω (s : A) * algebraMap O Ω o = algebraMap A Ω a`. Rewrite using `[IsScalarTower.algebraMap_apply A O Ω, IsScalarTower.algebraMap_apply A O Ω a, ← map_mul, mul_comm, h]`.

Rewrite using `[h']`. Conclude with `hconst a`. Consider the case `add a b _ _ ha hb`. Take `⟨s, hs, ha⟩` from `ha`. Take `⟨r, hr, hb⟩` from `hb`.

Use `⟨s * r, hmul hs hr, ?_⟩` and prove the remaining obligations. Establish `: algebraMap A Ω (s * r) * (a + b) = algebraMap A Ω r * (algebraMap A Ω s * a) + algebraMap A Ω s * (algebraMap A Ω r * b)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `add_mem (mul_mem (hconst r) ha) (mul_mem (hconst s) hb)`. Consider the case `mul a b _ _ ha hb`. Take `⟨s, hs, ha⟩` from `ha`. Take `⟨r, hr, hb⟩` from `hb`. Use `⟨s * r, hmul hs hr, ?_⟩` and prove the remaining obligations.

Establish `: algebraMap A Ω (s * r) * (a * b) = (algebraMap A Ω s * a) * (algebraMap A Ω r * b)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `mul_mem ha hb`.

Introduce and unpack `⟨s, hs, ht⟩`. Establish `hle : ∀ {a : Ω}, a ∈ chartRing ℤ (segreVec y) c → a ∈ chartRing O (segreVec y) c`. Introduce `a ha`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem a ha => exact Algebra.subset_adjoin ha`.

Consider the case `algebraMap n`. Establish `: algebraMap ℤ Ω n = algebraMap O Ω (n : O)` using `by simp`. Rewrite using `[this]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`.

Consider the case `mul a b _ _ ha hb => exact mul_mem ha hb`. Take `⟨u, hu⟩` from `IsLocalization.map_units O (⟨s, hs⟩ : m.primeCompl)`. Establish `hu' : (u : O) = algebraMap A O s` using `hu`. Establish `hinv : algebraMap O Ω ((u⁻¹ : Oˣ) : O) * algebraMap A Ω s = 1`. Rewrite using `[IsScalarTower.algebraMap_apply A O Ω, ← hu', ← map_mul, Units.inv_mul, map_one]`.

Establish `: t = algebraMap O Ω ((u⁻¹ : Oˣ) : O) * (algebraMap A Ω s * t)`. Rewrite using `[← mul_assoc, hinv, one_mul]`. Rewrite using `[this]`. Conclude with `mul_mem (Subalgebra.algebraMap_mem _ _) (hle ht)`.
-/
theorem GlobalTheory.CompanionTheory.Ar.Num.mem_chartRing_atPrime_iff : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, ι k), segreVec y c ≠ 0 → ∀ t : Ω, t ∈ chartRing O (segreVec y) c ↔ ∃ s : A, s ∉ m ∧ algebraMap A Ω s * t ∈ chartRing ℤ (segreVec y) c := by
  intro K _ _ ι _ Ω _ y A _ _ hA m _ O _ _ _ _ _ _ _ c hc t
  have hconst : ∀ a : A, algebraMap A Ω a ∈ chartRing ℤ (segreVec y) c := hA c hc
  have hmul : ∀ {a b : A}, a ∉ m → b ∉ m → a * b ∉ m := fun ha hb h =>
    (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha hb
  constructor
  · intro ht
    induction ht using Algebra.adjoin_induction with
    | mem a ha =>
      refine ⟨1, fun h => Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one m).2 h), ?_⟩
      rw [map_one, one_mul]
      exact Algebra.subset_adjoin ha
    | algebraMap o =>
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj m.primeCompl o
      refine ⟨s, s.2, ?_⟩
      have h' : algebraMap A Ω (s : A) * algebraMap O Ω o = algebraMap A Ω a := by
        rw [IsScalarTower.algebraMap_apply A O Ω, IsScalarTower.algebraMap_apply A O Ω a, ← map_mul,
          mul_comm, h]
      rw [h']
      exact hconst a
    | add a b _ _ ha hb =>
      obtain ⟨s, hs, ha⟩ := ha
      obtain ⟨r, hr, hb⟩ := hb
      refine ⟨s * r, hmul hs hr, ?_⟩
      have : algebraMap A Ω (s * r) * (a + b) =
          algebraMap A Ω r * (algebraMap A Ω s * a) + algebraMap A Ω s * (algebraMap A Ω r * b) := by
        rw [map_mul]; ring
      rw [this]
      exact add_mem (mul_mem (hconst r) ha) (mul_mem (hconst s) hb)
    | mul a b _ _ ha hb =>
      obtain ⟨s, hs, ha⟩ := ha
      obtain ⟨r, hr, hb⟩ := hb
      refine ⟨s * r, hmul hs hr, ?_⟩
      have : algebraMap A Ω (s * r) * (a * b) = (algebraMap A Ω s * a) * (algebraMap A Ω r * b) := by
        rw [map_mul]; ring
      rw [this]
      exact mul_mem ha hb
  · rintro ⟨s, hs, ht⟩
    have hle : ∀ {a : Ω}, a ∈ chartRing ℤ (segreVec y) c → a ∈ chartRing O (segreVec y) c := by
      intro a ha
      induction ha using Algebra.adjoin_induction with
      | mem a ha => exact Algebra.subset_adjoin ha
      | algebraMap n =>
        have : algebraMap ℤ Ω n = algebraMap O Ω (n : O) := by simp
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
      | add a b _ _ ha hb => exact add_mem ha hb
      | mul a b _ _ ha hb => exact mul_mem ha hb
    obtain ⟨u, hu⟩ := IsLocalization.map_units O (⟨s, hs⟩ : m.primeCompl)
    have hu' : (u : O) = algebraMap A O s := hu
    have hinv : algebraMap O Ω ((u⁻¹ : Oˣ) : O) * algebraMap A Ω s = 1 := by
      rw [IsScalarTower.algebraMap_apply A O Ω, ← hu', ← map_mul, Units.inv_mul, map_one]
    have : t = algebraMap O Ω ((u⁻¹ : Oˣ) : O) * (algebraMap A Ω s * t) := by
      rw [← mul_assoc, hinv, one_mul]
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) (hle ht)
