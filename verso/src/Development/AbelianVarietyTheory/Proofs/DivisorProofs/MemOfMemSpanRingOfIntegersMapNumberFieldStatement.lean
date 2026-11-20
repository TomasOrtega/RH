import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfMemSpanRingOfIntegersMapNumberField
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemOfMemSpanRingOfIntegersMapNumberField.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.mem_of_mem_span_ringOfIntegers_map_numberField : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ)
    (N : Submodule (𝓞 K) (Fin n → K)) (w : Fin n → K),
    (fun i => j (w i)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin n → K) i => j (c i)) '' (N : Set (Fin n → K))) → w ∈ N := by
  first | exact @GlobalTheory.FlatDescent.mem_of_mem_span_map | exact GlobalTheory.FlatDescent.mem_of_mem_span_map | (intros; apply GlobalTheory.FlatDescent.mem_of_mem_span_map <;> assumption)
