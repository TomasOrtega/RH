import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

/- English proof (translation)
Take `⟨hfin, -, hrank⟩` from `h`. Use `haveI : Module.Free R M := by`. Use `letI := hR.toField`. Conclude with `Module.Free.of_divisionRing R M`. Use `haveI : Nontrivial R := ⟨hR.exists_pair_ne⟩`.

Take `⟨p⟩ : Nonempty (PrimeSpectrum R)` from `inferInstance`. Establish `hg : Module.finrank R M = g`. Establish `hp` using `hrank p`. Rewrite `hp` using `[Module.rankAtStalk_eq_finrank_of_free]`. Conclude with `hp`.

Conclude with `⟨Module.finBasisOfFinrankEq R M hg⟩`.
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
