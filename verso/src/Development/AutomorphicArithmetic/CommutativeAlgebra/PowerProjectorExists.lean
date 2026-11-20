import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowerOfAbelianSchemeProjective
import Development.AutomorphicArithmetic.CommutativeAlgebra.IteratedFiberPowerZeroIsIsoAndSuccIsPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open UpperTheory.Gal.Int.Geo

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem relDim_pow {S : Scheme.{0}} (A : Over S) (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) (k : ℕ) :
    SmoothOfRelativeDimension (k * g) (GlobalTheory.KS.pow A k).hom := by
  induction k with
  | zero =>
    obtain ⟨h0, -⟩ := UpperTheory.iteratedFiberPower_zero_isIso_and_succ_isPullback A
    simp only [zero_mul]
    infer_instance
  | succ m ih =>
    obtain ⟨-, hs⟩ := UpperTheory.iteratedFiberPower_zero_isIso_and_succ_isPullback A
    obtain ⟨u, v, hpb, hcomp⟩ := hs m
    have hu : SmoothOfRelativeDimension g u :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback hpb.flip hg
    rw [← hcomp, Nat.succ_mul, Nat.add_comm]
    infer_instance

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.power_projector_exists :
    PowProj := by
  intro q _ D R _ _ b N _ _ X s o k
  letI := o.grp
  haveI := o.comm
  have hT := GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle q D R b N X s o
  refine ⟨fun hs => GlobalTheory.KS.isProjOver_pow R X s hs o.A o.ab _ hT.2 o.ample k, ?_⟩
  intro d hd
  haveI := relDim_pow o.A D.g hT.1 k
  exact ⟨k * D.g + d, inferInstance⟩
