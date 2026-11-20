import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideMore

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GlobalTheory.FourClauses.irreducibleAdmissibleGL : GlobalTheory.Published.IrreducibleAdmissibleGL :=
  GlobalTheory.FourClauses.adm GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
