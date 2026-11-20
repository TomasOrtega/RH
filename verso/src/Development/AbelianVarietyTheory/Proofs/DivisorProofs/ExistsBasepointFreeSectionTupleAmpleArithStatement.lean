import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasepointFreeSectionTupleAmpleArith
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HSAmp.NoethGens.exists_gens` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsBasepointFreeSectionTupleAmpleArith.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.exists_basepointFreeSectionTuple_ample_arith : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∃ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x := by
  first | exact @GlobalTheory.HSAmp.NoethGens.exists_gens | exact GlobalTheory.HSAmp.NoethGens.exists_gens | (intros; apply GlobalTheory.HSAmp.NoethGens.exists_gens <;> assumption)
