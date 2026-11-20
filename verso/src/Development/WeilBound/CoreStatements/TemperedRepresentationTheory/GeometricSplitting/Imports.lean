import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetOfInducedFiltration

/- English proof (translation)
Introduce `k _ _ _ _` and use `GlobalTheory.CompanionTheory.GeoAssembly.jacquetOfInducedFiltration k`.
-/
theorem PositivityTheory.Geo.geometricLemmaFiltration : GlobalTheory.Published.GeometricLemmaFiltration :=
  fun k _ _ _ _ => GlobalTheory.CompanionTheory.GeoAssembly.jacquetOfInducedFiltration k
