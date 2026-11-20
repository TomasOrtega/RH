import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankSectionsPrincipalPolarisationEqOne

namespace GlobalTheory.AbLaw

/- English proof (translation)
The claim follows from `finrank_sections_principal_polarisation_eq_one`.
-/
theorem principalPolarisation_unique_section : GlobalTheory.Published.principalPolarisationOneSection :=
  finrank_sections_principal_polarisation_eq_one

end GlobalTheory.AbLaw
