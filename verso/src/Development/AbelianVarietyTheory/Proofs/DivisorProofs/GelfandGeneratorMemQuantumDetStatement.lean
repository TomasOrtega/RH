import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandGeneratorMemQuantumDet
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CapelliGelfand.gelfA_mem_adjoin_qdet` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGelfandGeneratorMemQuantumDet.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.gelfand_generator_mem_quantum_det : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X →
    ∀ k : ℕ, GlobalTheory.SmoothForms.gelfA X k ∈ Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet X)) := by
  first | exact @GlobalTheory.CapelliGelfand.gelfA_mem_adjoin_qdet | exact GlobalTheory.CapelliGelfand.gelfA_mem_adjoin_qdet | (intros; apply GlobalTheory.CapelliGelfand.gelfA_mem_adjoin_qdet <;> assumption)
