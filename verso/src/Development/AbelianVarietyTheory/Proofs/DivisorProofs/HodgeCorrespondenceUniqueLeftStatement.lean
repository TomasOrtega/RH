import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceUniqueLeft
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HodgeSubInj.eq_of_corr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHodgeCorrespondenceUniqueLeft.lean&line=93#L93)
-/
theorem _root_.GlobalTheory.T.hodge_correspondence_unique_left : GlobalTheory.CovTop.Hypotheses2 → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (V : T.Opens) (hV : IsAffineOpen V) (s s' : Γ(GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, V)) (c : primDR (onAff A hV)),
      GlobalTheory.HodgeSub.Corr A hV s c → GlobalTheory.HodgeSub.Corr A hV s' c → s = s' := by
  first | exact @GlobalTheory.HodgeSubInj.eq_of_corr | exact GlobalTheory.HodgeSubInj.eq_of_corr | (intros; apply GlobalTheory.HodgeSubInj.eq_of_corr <;> assumption)
