import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem inChart_unitAt_of_inFrameDomain : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segreCoord y) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f : Ω) (h : genPt ξ ⤳ centre z), CoordsAt ξ y z w → InFrameDomain y cc f w → InChart ξ (segreCoord y) cc ⟨centre z, h⟩ ∧ unitAt ξ ⟨centre z, h⟩ f := by
  intro X Ω _ ξ K _ J _ y hT z w cc f h hw hd
  have hu : ∀ k, IsUnit (w ⟨k, cc k⟩) := fun k => IsUnit.mk0 _ (hd.1 k)
  have hy : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => (hw.2 k (cc k) (hu k)).1
  have reg : ∀ {a : Ω} {r : ℂ}, ValAt ξ z a r → a ∈ regAt ξ ⟨centre z, h⟩ := by
    rintro a r ⟨_, s, hs, -⟩
    exact ⟨s, hs⟩
  refine ⟨⟨Finset.prod_ne_zero_iff.2 fun k _ => hy k, fun c' => ?_⟩, ?_⟩
  · choose r hr _ using fun k => (hw.2 k (cc k) (hu k)).2 (c' k)
    have hp : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, y ⟨k, c' k⟩ / y ⟨k, cc k⟩) (∏ k ∈ s, r k) := by
      classical
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using CxVal.one h
      | insert k s hk ih =>
        rw [Finset.prod_insert hk, Finset.prod_insert hk]
        exact CxVal.mul (hr k) ih
    have e : segreCoord y c' / segreCoord y cc = ∏ k, y ⟨k, c' k⟩ / y ⟨k, cc k⟩ := by
      simp only [segreCoord, Finset.prod_div_distrib]
    rw [e]
    exact reg (hp Finset.univ)
  · obtain ⟨v, hv, hv0⟩ := hd.2
    have hf : ValAt ξ z f v := (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w h hw f v).2 hv
    refine ⟨?_, reg hf, reg (CxVal.inv hf hv0)⟩
    obtain ⟨_, s, hs, hsv⟩ := hf
    have hs0 : (Scheme.stalkClosedPointTo z).hom s ≠ 0 := by rw [hsv]; exact hv0
    have := (CxVal.isUnit s hs0).map (genMap ξ ⟨centre z, h⟩)
    rw [hs] at this
    exact this.ne_zero

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
