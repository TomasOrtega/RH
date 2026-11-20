import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Supply the required witnesses or components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Clear the denominators using the available nonvanishing facts.

A detailed English derivation is pending.
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
