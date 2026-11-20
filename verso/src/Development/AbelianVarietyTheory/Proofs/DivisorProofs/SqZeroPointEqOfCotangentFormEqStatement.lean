import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSqZeroPointEqOfCotangentFormEq.lean&line=175#L175)
-/
theorem _root_.GlobalTheory.T.sqZeroPoint_eq_of_cotangentForm_eq : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A], (GlobalTheory.LieVB.omega A).IsQuasicoherent → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (z z' : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O M ≫ z' = η[A]), (∀ w, Phi z h w = Phi z' h' w) → z = z') := by
  first | exact @GlobalTheory.SqZeroPt.eq_of_Phi_eq | exact GlobalTheory.SqZeroPt.eq_of_Phi_eq | (intros; apply GlobalTheory.SqZeroPt.eq_of_Phi_eq <;> assumption)
