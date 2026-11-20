import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRigExtMapRelFrobLeRangeRigOfOmega
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDivGroup.ker_rigExtMap_relFrob_le_range_rigOfOmega` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKerRigExtMapRelFrobLeRangeRigOfOmega.lean&line=94#L94)
-/
theorem _root_.GlobalTheory.T.ker_rigExtMap_relFrob_le_range_rigOfOmega' : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), LinearMap.ker (rigExtMap (relFrob h G)) ≤ LinearMap.range (frobTwist h G).rigOfOmega := by
  first | exact @GlobalTheory.PDivGroup.ker_rigExtMap_relFrob_le_range_rigOfOmega | exact GlobalTheory.PDivGroup.ker_rigExtMap_relFrob_le_range_rigOfOmega | (intros; apply GlobalTheory.PDivGroup.ker_rigExtMap_relFrob_le_range_rigOfOmega <;> assumption)
