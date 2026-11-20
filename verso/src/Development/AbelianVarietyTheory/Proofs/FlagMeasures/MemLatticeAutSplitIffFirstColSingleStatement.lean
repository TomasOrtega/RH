import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLatticeAutSplitIffFirstColSingle
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OrbitTerm.mem_autGL_split_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMemLatticeAutSplitIffFirstColSingle.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.mem_latticeAut_split_iff_firstCol_single : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → ∀ x : MatInf E (k + 1), (∀ w a, x w a 0 = if a = 0 then 1 else 0) → (x ∈ autGL E (k + 1) Λ ↔ (fun w a b => x w a.succ b.succ) ∈ autGL E k Λ' ∧ ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ ∀ w b, x w 0 b.succ = w.embedding (τ b)) := by
  first | exact @GlobalTheory.OrbitTerm.mem_autGL_split_iff | exact GlobalTheory.OrbitTerm.mem_autGL_split_iff | (intros; apply GlobalTheory.OrbitTerm.mem_autGL_split_iff <;> assumption)
