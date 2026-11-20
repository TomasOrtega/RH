import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem closed_empty_of_universallyClosed_of_le_jacobson :
  ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), UniversallyClosed p → ∀ Z : Set X, IsClosed Z → (∀ x ∈ Z, ¬ I ≤ (p x).asIdeal) → Z = ∅ := by
  intro R _ I hI X p hp Z hZ hmiss
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hcl : IsClosed (p.base '' Z) := p.isClosedMap _ hZ
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (p x).isPrime.ne_top
  let q : Spec (CommRingCat.of R) := ⟨m, hm.isPrime⟩
  have hq : q ∈ closure {p.base x} := (PrimeSpectrum.le_iff_mem_closure _ _).mp hle
  have hq' : q ∈ p.base '' Z :=
    closure_minimal (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem p.base hx)) hcl hq
  obtain ⟨y, hy, hyq⟩ := hq'
  apply hmiss y hy
  have hmy : (p y).asIdeal = m := by
    show (p.base y).asIdeal = m
    rw [hyq]
  rw [hmy]
  refine hI.trans ?_
  exact sInf_le ⟨bot_le, hm⟩

end GlobalTheory
