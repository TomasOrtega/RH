import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowerOfAbelianSchemeProjective
import Development.AutomorphicArithmetic.CommutativeAlgebra.IteratedFiberPowerZeroIsIsoAndSuccIsPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open UpperTheory.Gal.Int.Geo

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Take `⟨h0, -⟩` from `UpperTheory.iteratedFiberPower_zero_isIso_and_succ_isPullback A`. Simplify using `only [zero_mul]`. Use `infer_instance`.

Consider the case `succ m ih`. Take `⟨-, hs⟩` from `UpperTheory.iteratedFiberPower_zero_isIso_and_succ_isPullback A`. Take `⟨u, v, hpb, hcomp⟩` from `hs m`. Establish `hu : SmoothOfRelativeDimension g u` using `(smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback hpb.flip hg`. Rewrite using `[← hcomp, Nat.succ_mul, Nat.add_comm]`.

Use `infer_instance`.
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
Introduce `q _ D R _ _ b N _ _ X s o k`. Use `letI := o.grp`. Use `haveI := o.comm`. Establish `hT` using `GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle q D R b N X s o`. Use `⟨fun hs => GlobalTheory.KS.isProjOver_pow R X s hs o.A o.ab _ hT.2 o.ample k, ?_⟩` and prove the remaining obligations.

Introduce `d hd`. Use `haveI := relDim_pow o.A D.g hT.1 k`. Conclude with `⟨k * D.g + d, inferInstance⟩`.
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
