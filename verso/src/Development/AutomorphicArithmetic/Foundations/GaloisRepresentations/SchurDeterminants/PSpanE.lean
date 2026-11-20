import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
private theorem one_mem_eSpan (K : Type) [CommRing K] (n : ℕ) :
    (1 : MvPolynomial (Fin n) K) ∈ eSpan K n 0 := by
  unfold eSpan
  exact Submodule.subset_span ⟨Fin.elim0, by simp⟩

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
private theorem esymm_mem_eSpan (K : Type) [CommRing K] (n : ℕ) (i : Fin n) :
    esymm (Fin n) K ((i : ℕ) + 1) ∈ eSpan K n 1 := by
  unfold eSpan
  exact Submodule.subset_span ⟨fun _ => i.succ, by simp⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem exists_mem_eSpan (h : ESpanMul) (K : Type) [CommRing K] (n : ℕ)
    (q : MvPolynomial (Fin n) K) :
    ∃ k, aeval (fun i : Fin n => esymm (Fin n) K ((i : ℕ) + 1)) q ∈ eSpan K n k := by
  obtain ⟨hmono, hmul⟩ := h K n
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_⟩
    rw [aeval_C, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ a (one_mem_eSpan K n)
  | add p q hp hq =>
    obtain ⟨k, hk⟩ := hp
    obtain ⟨l, hl⟩ := hq
    refine ⟨max k l, ?_⟩
    rw [map_add]
    exact Submodule.add_mem _ (hmono _ _ (le_max_left k l) hk) (hmono _ _ (le_max_right k l) hl)
  | mul_X p i hp =>
    obtain ⟨k, hk⟩ := hp
    refine ⟨k + 1, ?_⟩
    rw [map_mul, aeval_X]
    exact hmul _ _ _ _ hk (esymm_mem_eSpan K n i)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem spanE_of : ESpanMul → SpanE := by
  intro h K _ n P hP
  obtain ⟨q, hq⟩ := esymmAlgHom_fin_surjective K (le_refl n) ⟨P, (mem_symmetricSubalgebra P).2 hP⟩
  have hq' : aeval (fun i : Fin n => esymm (Fin n) K ((i : ℕ) + 1)) q = P := by
    have := congrArg Subtype.val hq
    rwa [esymmAlgHom_apply] at this
  obtain ⟨k₀, hk₀⟩ := exists_mem_eSpan h K n q
  refine ⟨k₀, fun k hk => ?_⟩
  have hmem := (h K n).1 _ _ hk hk₀
  rw [hq'] at hmem
  unfold eSpan at hmem
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  exact ⟨w, hw.symm⟩

end UpperTheory.Gal.Schur
