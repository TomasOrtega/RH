import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowMemSectionsOfMulPowMem
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDivPowMemSectionsOfMulPowMem.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.div_pow_mem_sections_of_mul_pow_mem : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ) (u : X.functionField), u ∈ P.H N m → u * t ^ N / s ^ m ∈ P.H 0 (b * N) → u / s ^ m ∈ P.H N 0 := by
  first | exact @GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow | exact GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow | (intros; apply GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow <;> assumption)
