import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtConclOfIsoOf
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvFamNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSubfieldModel

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.PTN

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem ptConclAt_all_of (hfs : PtfsHyp) (hL : LocHyp) :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω],
      PTConclAt F Ω := by
  intro F Ω _ _ _ _ _
  obtain ⟨K, hK, hC, e, E, h⟩ := GlobalTheory.CompanionTheory.FieldModel.exists_subfield_model F Ω
  exact ptConcl_of_iso_of hL F Ω K (AlgebraicClosure ℚ) e E h (hfs K)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Supply the required witnesses or components.
-/
theorem poitouTateNormalised_of (hfs : PtfsHyp) (hL : LocHyp) (hvan : VanishAll) :
    PoitouTateNormalised := by
  intro F Ω _ _ _ _ _ l _ r hl hr ζ hζ
  obtain ⟨inv, hinv⟩ := GlobalTheory.CompanionTheory.PoitouTateInv.exists_invFam_normalised F Ω l r hr ζ hζ
  refine ⟨inv, hinv, ?_⟩
  intro S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  have h := ptConclAt_all_of hfs hL F Ω l r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M ρ hρ
  exact ⟨h.1, h.2, hvan F Ω l r hl hr S hS M ρ hρ⟩

end PositivityTheory.PTN
