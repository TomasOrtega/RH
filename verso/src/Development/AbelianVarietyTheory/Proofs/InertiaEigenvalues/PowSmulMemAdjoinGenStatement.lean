import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemAdjoinGen
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPowSmulMemAdjoinGen.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.exists_pow_smul_mem_adjoin_gen_of_separable : ∀ (K : UQ) (B : InvAlg K) (a : K.O), B.P.Separable → K.Small a → ∃ N : ℕ, ∀ r : B.A, IsIntegral K.O r → (al K a ^ N) • r ∈ Algebra.adjoin K.O {B.g} := by
  first | exact @GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen | exact GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen | (intros; apply GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen <;> assumption)
