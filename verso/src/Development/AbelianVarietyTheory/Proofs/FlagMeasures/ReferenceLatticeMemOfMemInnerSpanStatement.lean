import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReferenceLatticeMemOfMemInnerSpan
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DegCnt.NF.ref_mem_of_mem_Wn` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FReferenceLatticeMemOfMemInnerSpan.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.referenceLattice_mem_of_mem_innerSpan : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : GlobalTheory.DegCnt.NF H r) (L : Submodule (𝓞 K) V), N.F.z ∈ L → ∀ v ∈ N.Ref L, v ∈ N.Wn → v ∈ L := by
  first | exact @GlobalTheory.DegCnt.NF.ref_mem_of_mem_Wn | exact GlobalTheory.DegCnt.NF.ref_mem_of_mem_Wn | (intros; apply GlobalTheory.DegCnt.NF.ref_mem_of_mem_Wn <;> assumption)
