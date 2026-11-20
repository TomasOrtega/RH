import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex
import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KeyIsoNormal.val_iff_and_nrm_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FThetaLawProofs%2FNormalFormsEqOfKeyDataIsoComplex.lean&line=208#L208)
-/
theorem _root_.GlobalTheory.T.normalForms_eq_of_keyDataIso_complex : ∀ x x' : KeyIn ℂ, KeyPB x' x (RingHom.id ℂ) → (∀ t, Val x t ↔ Val x' t) ∧ ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), Nrm x τ a b ↔ Nrm x' τ a b := by
  first | exact @GlobalTheory.KeyIsoNormal.val_iff_and_nrm_iff | exact GlobalTheory.KeyIsoNormal.val_iff_and_nrm_iff | (intros; apply GlobalTheory.KeyIsoNormal.val_iff_and_nrm_iff <;> assumption)
