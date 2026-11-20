import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingLineBundleInvMixOneZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCechNonvanishingLineBundleInvMixOneZero.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.cechNonvanishing_lineBundleInvMix_one_zero : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left), L.IsLB → ∀ j : ℕ, NV A L j → NV A (mix A L 1 0) j := by
  first | exact @GlobalTheory.AmpleGen.nv_mix_one_zero | exact GlobalTheory.AmpleGen.nv_mix_one_zero | (intros; apply GlobalTheory.AmpleGen.nv_mix_one_zero <;> assumption)
