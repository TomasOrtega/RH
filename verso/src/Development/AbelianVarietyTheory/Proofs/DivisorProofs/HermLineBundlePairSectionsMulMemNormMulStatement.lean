import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHermLineBundlePairSectionsMulMemNormMul.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b a' b' : ℤ) (f g : X.functionField), f ∈ P.H a b → g ∈ P.H a' b' → f * g ∈ P.H (a + a') (b + b') ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (a + a') (b + b') σ y (f * g) = P.nu a b σ y f * P.nu a' b' σ y g := by
  first | exact @GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul | exact GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul | (intros; apply GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul <;> assumption)
