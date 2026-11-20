import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalIdealSt

namespace PositivityTheory.Stage1.PM

/- English proof (translation)
The claim follows from `CompanionTheory.FamInh.globalArtin`.
-/
theorem globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity :=
  CompanionTheory.FamInh.globalArtin

/- English proof (translation)
The claim follows from `GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt CompanionTheory.FamInh.globalArtin`.
-/
theorem rayClassFieldSt : GlobalTheory.Published.RayClassFieldSt :=
  GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt CompanionTheory.FamInh.globalArtin

/- English proof (translation)
The claim follows from `GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter CompanionTheory.FamInh.globalArtin`.
-/
theorem heckeLAdicCharacter : GlobalTheory.Published.HeckeLAdicCharacter :=
  GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter CompanionTheory.FamInh.globalArtin

end PositivityTheory.Stage1.PM
