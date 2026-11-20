import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepsCuspidalStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltTer

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GaloisFromAdm.main_alt_alt_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FMainAltAltAltTer.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.galoisRepsCusp_of_adm2 : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → GlobalTheory.BlockComplement.GaloisRepsCusp D := by
  first | exact @_root_.GlobalTheory.GaloisFromAdm.main_alt_alt_alt | exact _root_.GlobalTheory.GaloisFromAdm.main_alt_alt_alt | (intros; apply _root_.GlobalTheory.GaloisFromAdm.main_alt_alt_alt <;> assumption)
end
