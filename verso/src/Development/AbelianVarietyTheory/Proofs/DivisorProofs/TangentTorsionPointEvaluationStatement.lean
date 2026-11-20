import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTorsionPointEvaluation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpOverFstComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
open GlobalTheory.SqZeroPt
open scoped GlobalTheory.SqZeroPt
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.OpenOmega

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OpenOmega.snd_pt_tanTors` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTangentTorsionPointEvaluation.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.tangent_torsion_point_evaluation : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (GG : PDivGroup p R) (θ : TorsionMap G GG) (n : ℕ) (hs : PtSurj θ n), SpecProp θ n hs → ∀ (x : Pdiv.LieG G) (h : zeroSec R R ≫ x.1 = η[G]) (w : Wmod G) (a : GG.A n), dUnit R a = cnθ θ n hs w → (θ.pt n _ (tanTors p n x) a).snd = Ideal.Quotient.mk _ (Phi x.1 h w) := by
  first | exact @GlobalTheory.OpenOmega.snd_pt_tanTors | exact GlobalTheory.OpenOmega.snd_pt_tanTors | (intros; apply GlobalTheory.OpenOmega.snd_pt_tanTors <;> assumption)
