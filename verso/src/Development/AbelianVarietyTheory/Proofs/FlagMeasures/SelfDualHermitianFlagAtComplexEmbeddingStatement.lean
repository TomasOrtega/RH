import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianFlagAtComplexEmbedding
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocDual.locDual` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FSelfDualHermitianFlagAtComplexEmbedding.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.selfDual_hermitianFlag_at_complex_embedding : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n m : ℕ) (J : Matrix (Fin n) (Fin n) E) (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool) (F : ℕ → Submodule (𝓞 E) (Fin n → E)), (∀ x, φ (star x) = starRingEnd ℂ (φ x)) → IsUnit P → Pᴴ * J.map φ * P = Formalism.REAL.Jm ε → IsDualFlag J F m → Submodule.span E (F m : Set (Fin n → E)) = ⊤ → IsDualFlag (Formalism.REAL.Jm ε) (locFlag φ P F) m ∧ locFlag φ P F m = ⊤ := by
  first | exact @GlobalTheory.LocDual.locDual | exact GlobalTheory.LocDual.locDual | (intros; apply GlobalTheory.LocDual.locDual <;> assumption)
