import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreMore
open NumberField

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span`. Consider the case `exact _root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span`. Consider the case `(apply _root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span ..)`.
-/
theorem exists_ringOfIntegers_smul_mem_of_mem_span {K : Type} [Field K] [NumberField K] {r : ℕ}
    (E : Submodule (𝓞 K) (Fin r → K)) {v : Fin r → K}
    (hv : v ∈ Submodule.span K (E : Set (Fin r → K))) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ E := by
  first
  | exact @_root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span
  | exact _root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span
  | (apply _root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span ..)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Conclude with `(Submodule.mem_inf.mp hx).2`. Introduce `v hv`.

Establish `hv' : v ∈ Submodule.span K (E : Set (Fin r → K))` using `by rw [hE]; trivial`. Take `⟨d, hd, hdv⟩` from `exists_ringOfIntegers_smul_mem_of_mem_span E hv'`. Establish `hdK : (algebraMap (𝓞 K) K d) ≠ 0`. Rewrite using `[ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]` and apply the resulting hypothesis. Establish `hmem : d • v ∈ (E ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin r → K))`.

Use `Submodule.mem_inf.mpr ⟨hdv, ?_⟩` and prove the remaining obligations. Use `show d • v ∈ V`. Rewrite using `[← algebraMap_smul K d]`. Conclude with `V.smul_mem _ hv`. Establish `key : v = (algebraMap (𝓞 K) K d)⁻¹ • (d • v)`.

Rewrite using `[← algebraMap_smul K d, smul_smul, inv_mul_cancel₀ hdK, one_smul]`. Rewrite using `[key]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem span_inf_eq_of_span_eq_top (K : Type) [Field K] [NumberField K] (r : ℕ)
    (E : Submodule (𝓞 K) (Fin r → K)) (V : Submodule K (Fin r → K))
    (hE : Submodule.span K (E : Set (Fin r → K)) = ⊤) :
    Submodule.span K ((E ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin r → K)) :
      Set (Fin r → K)) = V := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.mp hx).2
  · intro v hv
    have hv' : v ∈ Submodule.span K (E : Set (Fin r → K)) := by rw [hE]; trivial
    obtain ⟨d, hd, hdv⟩ := exists_ringOfIntegers_smul_mem_of_mem_span E hv'
    have hdK : (algebraMap (𝓞 K) K d) ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
    have hmem : d • v ∈ (E ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin r → K)) := by
      refine Submodule.mem_inf.mpr ⟨hdv, ?_⟩
      show d • v ∈ V
      rw [← algebraMap_smul K d]
      exact V.smul_mem _ hv
    have key : v = (algebraMap (𝓞 K) K d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul K d, smul_smul, inv_mul_cancel₀ hdK, one_smul]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/- English proof (translation)
Introduce `K _ _ r E V hE` and use `span_inf_eq_of_span_eq_top K r E V hE`.
-/
theorem span_cut : ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (E : Submodule (𝓞 K) (Fin r → K)) (V : Submodule K (Fin r → K)), Submodule.span K (E : Set (Fin r → K)) = ⊤ → Submodule.span K ((E ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin r → K)) : Set (Fin r → K)) = V :=
  fun K _ _ r E V hE => span_inf_eq_of_span_eq_top K r E V hE

end GlobalTheory
