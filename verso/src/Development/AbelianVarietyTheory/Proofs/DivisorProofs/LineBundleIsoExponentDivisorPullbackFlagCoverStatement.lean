import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoExponentDivisorPullbackFlagCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLineBundleIsoExponentDivisorPullbackFlagCover.lean&line=184#L184)
-/
theorem _root_.GlobalTheory.T.lineBundleIso_exponentDivisor_pullback_flagCover : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)) (g : C.Y.X ⟶ X.YY), g ≫ X.π = C.π ≫ GlobalTheory.Toroidal.genι Y → (∀ (K : Type) [Field K] (p : Sp K ⟶ C.Y.X), GlobalTheory.VarFlag.Rel X.F C (p ≫ g) p) → ∀ ex : Ix Dw → ℤ, ex none = 0 → LBIso (C.Y.lb (C.LEx ex)) ((X.LL ex).pull g) := by
  first | exact @GlobalTheory.VarFlag.lbIso_LL_pull | exact GlobalTheory.VarFlag.lbIso_LL_pull | (intros; apply GlobalTheory.VarFlag.lbIso_LL_pull <;> assumption)
