import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedGaloisHomsBoundedClassNumberOfArtinRec
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnramifiedGaloisHomsBoundedClassNumberOfArtinRec.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.unramifiedGaloisHoms_bounded_classNumber_of_artinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → ReciprocityTheory.ChartRestriction.T2.VhE := by
  first | exact @GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity | exact GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity | (intros; apply GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity <;> assumption)
