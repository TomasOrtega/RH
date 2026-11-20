import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

/- English proof (translation)
Extract witnesses or component facts from the available result. Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem vb_basis_of_isField {R : Type} [CommRing R] (hR : IsField R) {M : Type} [AddCommGroup M] [Module R M]
    (g : ℕ) (h : VB R M g) : Nonempty (Module.Basis (Fin g) R M) := by
  obtain ⟨hfin, -, hrank⟩ := h
  haveI : Module.Free R M := by
    letI := hR.toField
    exact Module.Free.of_divisionRing R M
  haveI : Nontrivial R := ⟨hR.exists_pair_ne⟩
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  have hg : Module.finrank R M = g := by
    have hp := hrank p
    rw [Module.rankAtStalk_eq_finrank_of_free] at hp
    exact hp
  exact ⟨Module.finBasisOfFinrankEq R M hg⟩

end GlobalTheory.CompanionTheory.HopfC
