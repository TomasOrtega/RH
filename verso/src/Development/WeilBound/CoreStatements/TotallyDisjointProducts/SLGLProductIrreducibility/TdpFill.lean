import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyDisjointProductIrreducibleOfPolynomialRin

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.Hypotheses₂.totallyDisjointProductIrreducible_of_parts`.
-/
theorem PositivityTheory.SlGl.totallyDisjointProductIrreducible_of_parts :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.SegmentRepresentation →
      GlobalTheory.Published.GrothendieckRingPolynomial → GlobalTheory.Published.TotallyDisjointProductIrreducible :=
  GlobalTheory.CompanionTheory.Hypotheses₂.totallyDisjointProductIrreducible_of_parts
