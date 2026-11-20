import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.SplitOrbit.orbitSplit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FUnitNormVectorsOneOrbitSelfDualLatticeSplit.lean&line=218#L218)
-/
theorem _root_.GlobalTheory.T.unitNormVectors_one_orbit_selfDualLattice_split : ∀ D : D7, GlobalTheory.FinPl.OrbitSplit D := by
  first | exact @GlobalTheory.FinPl.SplitOrbit.orbitSplit | exact GlobalTheory.FinPl.SplitOrbit.orbitSplit | (intros; apply GlobalTheory.FinPl.SplitOrbit.orbitSplit <;> assumption)
