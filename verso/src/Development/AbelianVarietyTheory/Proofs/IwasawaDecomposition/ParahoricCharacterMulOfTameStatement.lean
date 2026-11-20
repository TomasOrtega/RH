import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricCharacterMulOfTame
import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnrM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsNrm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.LamMul.lamJ_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FParahoricCharacterMulOfTame.lean&line=160#L160)
-/
theorem _root_.GlobalTheory.T.parahoricCharacter_mul_of_tame : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (δ : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) (P.adicCompletion L)), k ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → k' ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → lamJ δ (k * k') = lamJ δ k * lamJ δ k' := by
  first | exact @GlobalTheory.Mem.LamMul.lamJ_mul | exact GlobalTheory.Mem.LamMul.lamJ_mul | (intros; apply GlobalTheory.Mem.LamMul.lamJ_mul <;> assumption)
