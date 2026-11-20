import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ x : K,
      (∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → σ x = x) → x ∈ k₀ := by
  intro K _ _ k₀ hk₀ x hfix
  by_contra hx
  have htr : Transcendental k₀ x := by
    intro halg
    have hint : IsIntegral k₀ x := halg.isIntegral
    have hdeg : (minpoly k₀ x).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hint)
    obtain ⟨r, hr⟩ := minpoly.mem_range_of_degree_eq_one k₀ x hdeg
    apply hx
    rw [← hr]
    exact r.2
  obtain ⟨σ, hσk, hσx⟩ := GlobalTheory.FixedRoots.exists_ringEquiv_add_one k₀ x htr
  have h := hfix σ hσk
  rw [hσx] at h
  simp at h

end GlobalTheory
