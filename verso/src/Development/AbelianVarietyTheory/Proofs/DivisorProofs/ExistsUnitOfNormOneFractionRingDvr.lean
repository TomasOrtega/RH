import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

/- English proof (translation)
Introduce `V _ _ _ C _ _ hC a ha`. Establish `key : ∀ x : V, ‖algebraMap (FractionRing V) C (algebraMap V _ x)‖ = 1 → IsUnit x`. Introduce `x hx`. Assume the negation of the conclusion as `hu`. Establish `hm : x ∈ IsLocalRing.maximalIdeal V` using `(IsLocalRing.mem_maximalIdeal x).2 hu`.

Use `hC.2 x hm` as an intermediate fact. Rewrite `this` using `[hx]`. Conclude with `lt_irrefl _ this`. Break down `ValuationRing.isInteger_or_isInteger V a with ⟨x, hx⟩ | ⟨x, hx⟩` into its components or cases. Establish `hu` using `key x (by rw [hx]; exact ha)`.

Conclude with `⟨hu.unit, by simp [hx]⟩`. Establish `hx' : ‖algebraMap (FractionRing V) C (algebraMap V _ x)‖ = 1`. Rewrite using `[hx, map_inv₀, norm_inv, ha, inv_one]`. Establish `hu` using `key x hx'`. Use `⟨hu.unit⁻¹, ?_⟩` and prove the remaining obligations.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at ha`. Establish `h1 : algebraMap V (FractionRing V) (↑hu.unit⁻¹ : V) * algebraMap V (FractionRing V) x = 1`. Rewrite using `[← map_mul]`.

Establish `: (↑hu.unit⁻¹ : V) * x = 1`. Use `hu.unit.inv_mul` as an intermediate fact. Simplify using `using this`. Rewrite using `[this, map_one]`. Rewrite `h1` using `[hx]`.

Clear denominators, using `at h1` for the nonvanishing conditions. Conclude with `h1.symm`.
-/
theorem GlobalTheory.KeyEven.fractionRing_norm_one_unit : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (C : Type) [NormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ a : FractionRing V, ‖algebraMap (FractionRing V) C a‖ = 1 → ∃ u : Vˣ, a = algebraMap V (FractionRing V) u := by
  intro V _ _ _ C _ _ hC a ha
  have key : ∀ x : V, ‖algebraMap (FractionRing V) C (algebraMap V _ x)‖ = 1 → IsUnit x := by
    intro x hx
    by_contra hu
    have hm : x ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal x).2 hu
    have := hC.2 x hm
    rw [hx] at this
    exact lt_irrefl _ this
  rcases ValuationRing.isInteger_or_isInteger V a with ⟨x, hx⟩ | ⟨x, hx⟩
  · have hu := key x (by rw [hx]; exact ha)
    exact ⟨hu.unit, by simp [hx]⟩
  · have hx' : ‖algebraMap (FractionRing V) C (algebraMap V _ x)‖ = 1 := by
      rw [hx, map_inv₀, norm_inv, ha, inv_one]
    have hu := key x hx'
    refine ⟨hu.unit⁻¹, ?_⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    have h1 : algebraMap V (FractionRing V) (↑hu.unit⁻¹ : V) * algebraMap V (FractionRing V) x = 1 := by
      rw [← map_mul]
      have : (↑hu.unit⁻¹ : V) * x = 1 := by
        have := hu.unit.inv_mul
        simpa using this
      rw [this, map_one]
    rw [hx] at h1
    field_simp at h1
    exact h1.symm
