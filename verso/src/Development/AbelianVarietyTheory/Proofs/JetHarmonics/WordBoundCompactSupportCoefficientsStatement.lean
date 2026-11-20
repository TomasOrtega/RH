import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundCompactSupportCoefficients
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HatNF.wordBound_cptCoef` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FWordBoundCompactSupportCoefficients.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.wordBound_compactSupportCoefficients : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), KB.CutWord P p.l0 w → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ KB.CptCoef p.T.base f) := by
  first | exact @GlobalTheory.HatNF.wordBound_cptCoef | exact GlobalTheory.HatNF.wordBound_cptCoef | (intros; apply GlobalTheory.HatNF.wordBound_cptCoef <;> assumption)
