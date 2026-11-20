import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VariableMatrixDetPolyPowMulMemDualWeyl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrameRead.detPol_pow_mul_mem_dualWeyl` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVariableMatrixDetPolyPowMulMemDualWeyl.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.variableMatrixDetPoly_pow_mul_mem_dualWeyl : ∀ (R : Type) [CommRing R] (n k : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R), f ∈ dualWeyl R n n ν → detPol R n ^ k * f ∈ dualWeyl R n n fun a => ν a + k := by
  first | exact @GlobalTheory.FrameRead.detPol_pow_mul_mem_dualWeyl | exact GlobalTheory.FrameRead.detPol_pow_mul_mem_dualWeyl | (intros; apply GlobalTheory.FrameRead.detPol_pow_mul_mem_dualWeyl <;> assumption)
