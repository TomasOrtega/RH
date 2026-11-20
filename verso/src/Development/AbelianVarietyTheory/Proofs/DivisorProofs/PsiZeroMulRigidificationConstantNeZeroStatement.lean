import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiZeroMulRigidificationConstantNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Poinc.IntTerm.psi_zero_rig_const` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPsiZeroMulRigidificationConstantNeZero.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.psi_zero_mul_rigidification_constant_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), ∃ c₀ : FractionRing V, c₀ ≠ 0 ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = GlobalTheory.UT.cst (FractionRing V) z c₀ := by
  first | exact @GlobalTheory.Poinc.IntTerm.psi_zero_rig_const | exact GlobalTheory.Poinc.IntTerm.psi_zero_rig_const | (intros; apply GlobalTheory.Poinc.IntTerm.psi_zero_rig_const <;> assumption)
