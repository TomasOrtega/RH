import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharExistsNeOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StdPsiNontrivial.exists_ne_one_of_isStd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStandardAdelicCharExistsNeOne.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.standard_adelic_char_exists_ne_one : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ s : AF F, ψ s ≠ 1 := by
  first | exact @GlobalTheory.StdPsiNontrivial.exists_ne_one_of_isStd | exact GlobalTheory.StdPsiNontrivial.exists_ne_one_of_isStd | (intros; apply GlobalTheory.StdPsiNontrivial.exists_ne_one_of_isStd <;> assumption)
