import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero

open PositivityTheory.Rg.Rsw

namespace GlobalTheory.CompanionTheory.HeckeEtaExist

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem heckeEta : HeckeEta :=
  GlobalTheory.RawLift.exists_hecke_resEta

end GlobalTheory.CompanionTheory.HeckeEtaExist
