import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBlockCongruenceLevelSubgroupIffStabilizerEntr
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemBlockCongruenceLevelSubgroupIffStabilizerEntr.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.mem_blockCongruenceLevelSubgroup_iff_stabilizer_entries : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) (h : GA D d), h ∈ blockLev D 𝔪 d a ↔ h ∈ intG D d ∧ ∀ i j : Fin d, j.1 < a → a ≤ i.1 → ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪 := by
  first | exact @GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff | exact GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff | (intros; apply GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff <;> assumption)
