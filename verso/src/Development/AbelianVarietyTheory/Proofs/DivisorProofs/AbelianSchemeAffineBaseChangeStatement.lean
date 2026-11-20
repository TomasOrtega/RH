import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeAffineBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianSchemeAffineBaseChange.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.abelian_scheme_affine_base_change : ∀ {T : Scheme.{0}} (A : Over T) [GrpObj A] (V V' : T.Opens) (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (h : V' ≤ V),
    letI := resAlg h
    ∃ (φ : (onAff A hV').left ⟶ (onAff A hV).left)
      (_ : IsGrpPullback (onAff A hV') (onAff A hV) (spMap (algebraMap Γ(T, V) Γ(T, V'))) φ),
      φ ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec := by
  first | exact @GlobalTheory.HodgeSub.exists_proj | exact GlobalTheory.HodgeSub.exists_proj | (intros; apply GlobalTheory.HodgeSub.exists_proj <;> assumption)
