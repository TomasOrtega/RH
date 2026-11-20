import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsPassGenerators
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FPlusHatsPassGenerators.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.T.Ahat_mul_and_R0_mul_mem_nfSpan_hats : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ b ∈ bset d, ∀ y : ℂ, d.L.Ahat y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0 y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators | exact GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators | (intros; apply GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators <;> assumption)
