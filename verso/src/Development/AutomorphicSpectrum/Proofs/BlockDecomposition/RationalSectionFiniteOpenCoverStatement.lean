import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionFiniteOpenCover
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRationalSectionFiniteOpenCover.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.rational_section_finite_open_cover : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    [CompactSpace (GlobalTheory.CxPts q σ)] {L : LB X} (ψ : GlobalTheory.Weight q σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r),
    ∃ (N : ℕ) (W : Fin N → X.Opens) (b : Fin N → L.ι) (a d : ∀ l, Γ(X, W l)),
      (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) ∧ (∀ l, W l ≤ L.U (b l)) ∧
      (∀ l, ∃ h : genericPoint X ∈ W l, fnOf (W l) h (d l) ≠ 0) ∧
      ∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ offSupp q σ (divOfRatSec ψ.isLB hr) → ev q σ (W l) (d l) y ≠ 0 →
        GlobalTheory.Cartier.logNorm ψ r y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchRep.logNorm_finite_rep | exact GlobalTheory.CompanionTheory.MixZ.ArchRep.logNorm_finite_rep | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchRep.logNorm_finite_rep <;> assumption)
