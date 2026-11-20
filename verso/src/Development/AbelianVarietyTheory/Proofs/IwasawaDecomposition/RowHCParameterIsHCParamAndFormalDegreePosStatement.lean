import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePos
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FRowHCParameterIsHCParamAndFormalDegreePos.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.rowHCParameter_isHCParam_and_formalDegree_pos : ∀ (R : Ranks) (P : HCParam R), Formalism.QuantumDeterminants.IsHCParam (lamSH R P) ∧ 0 < trueDsig R P := by
  first | exact @GlobalTheory.Mem.Vol.lamSH_isHCParam_and_trueDsig_pos | exact GlobalTheory.Mem.Vol.lamSH_isHCParam_and_trueDsig_pos | (intros; apply GlobalTheory.Mem.Vol.lamSH_isHCParam_and_trueDsig_pos <;> assumption)
