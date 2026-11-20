import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersMemNormalFormProductSpan
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FHatLettersMemNormalFormProductSpan.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.hatLetters_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1 := by
  first | exact @GlobalTheory.HatNF.hats_mem_nfSpan | exact GlobalTheory.HatNF.hats_mem_nfSpan | (intros; apply GlobalTheory.HatNF.hats_mem_nfSpan <;> assumption)
