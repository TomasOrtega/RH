import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceLinear
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HodgeSub.corr_add_smul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHodgeCorrespondenceLinear.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.hodge_correspondence_linear : ∀ {T : Scheme.{0}} (A : Over T) [GrpObj A] (V : T.Opens) (hV : IsAffineOpen V)
    (s s' : Γ(GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, V)) (c c' : primDR (onAff A hV)) (r : Γ(T, V)),
    GlobalTheory.HodgeSub.Corr A hV s c → GlobalTheory.HodgeSub.Corr A hV s' c' → GlobalTheory.HodgeSub.Corr A hV (s + s') (c + c') ∧ GlobalTheory.HodgeSub.Corr A hV (r • s) (r • c) := by
  first | exact @GlobalTheory.HodgeSub.corr_add_smul | exact GlobalTheory.HodgeSub.corr_add_smul | (intros; apply GlobalTheory.HodgeSub.corr_add_smul <;> assumption)
