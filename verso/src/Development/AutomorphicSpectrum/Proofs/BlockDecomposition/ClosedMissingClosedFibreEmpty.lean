import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.ClosedFibre

/- English proof (translation)
Introduce `R _ I hI X hX Z hZ h`. Use `haveI := hI`. Use `haveI := hX`. Assume the negation of the conclusion as `hne`. Take `⟨x, hx⟩` from `Set.nonempty_iff_ne_empty.mpr hne`.

Establish `hcl : IsClosed (X.hom.base '' Z)` using `X.hom.isClosedMap _ hZ`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal (X.hom.base x).asIdeal (X.hom.base x).isPrime.ne_top`. Set `q : PrimeSpectrum R` to `⟨m, hm.isPrime⟩`. Establish `hsp : (X.hom.base x) ⤳ q` using `(PrimeSpectrum.le_iff_specializes _ _).mp hle`. Establish `hq : q ∈ X.hom.base '' Z` using `hsp.mem_closed hcl ⟨x, hx, rfl⟩`.

Take `⟨y, hy, hyq⟩` from `hq`. Apply `h y hy` to reduce the goal to its premises. Rewrite using `[hyq]`. Conclude with `(IsAdicComplete.le_jacobson_bot (I := I)).trans (sInf_le ⟨bot_le, hm⟩)`.
-/
theorem closed_missing_closedFibre_empty : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R →
  ∀ (X : Over (Spec (CommRingCat.of R))), UniversallyClosed X.hom →
  ∀ Z : Set X.left, IsClosed Z → (∀ x ∈ Z, ¬ (I ≤ (X.hom.base x).asIdeal)) → Z = ∅ := by
  intro R _ I hI X hX Z hZ h
  haveI := hI
  haveI := hX
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hcl : IsClosed (X.hom.base '' Z) := X.hom.isClosedMap _ hZ
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (X.hom.base x).asIdeal (X.hom.base x).isPrime.ne_top
  let q : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  have hsp : (X.hom.base x) ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have hq : q ∈ X.hom.base '' Z := hsp.mem_closed hcl ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyq⟩ := hq
  apply h y hy
  rw [hyq]
  exact (IsAdicComplete.le_jacobson_bot (I := I)).trans (sInf_le ⟨bot_le, hm⟩)

end GlobalTheory.CompanionTheory.ClosedFibre
