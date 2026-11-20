import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalLengthSum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFibreRelDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivCycleMinimal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeLocalLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleSupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

open Classical in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem SemilocalLength.proof (h1 : SemilocalLengthSum.Statement.{u})
    (h2 : FibreRelDim.Statement.{u}) (h3 : DivCycleMinimal.Statement.{u})
    (h4 : ConeLocalLength.Statement.{u}) : SemilocalLength.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn c a h ha hh haP W hW hWn hPW hhW M hM1 hM0 α hα
  have := hP'.isPrime
  obtain ⟨d, hd⟩ := exists_relDegFn (F := F) j (ι' := ι')
  obtain ⟨β, hβ⟩ := exists_fibreLift j P' W α
  obtain ⟨hfin, hlen⟩ := h1 F K K' j ι' P' hP' n hP'n hPn c a h ha hh haP W hW hWn hPW hhW d
    (fun W' hW' _ => hd W' hW') α hα β hβ
  have key : ∀ W' ∈ hfin.toFinset.filter (fun W' => (rename (blockIncl j ι') a) ∈ W'), ∃ hW' : IsMultiProjPrime W',
      haveI := hW'.isPrime
      Ring.ord (degZeroLoc P' {W'}) (β W') = multAt (P' ⊔ Ideal.span {(rename (blockIncl j ι') a)}) W' ∧
        multAt (P' ⊔ Ideal.span {(rename (blockIncl j ι') a)}) W' ≠ ⊤ ∧
        divCycle P' (rename (blockIncl j ι') a) W' = ((multAt (P' ⊔ Ideal.span {(rename (blockIncl j ι') a)}) W').toNat : ℤ) ∧ M W' = d W' := by
    intro W' hT
    obtain ⟨hWf, haW'⟩ := Finset.mem_filter.mp hT
    have hWf' := hfin.mem_toFinset.mp hWf
    obtain ⟨hW'p, hPW', hcW'⟩ := id hWf'
    have := hW'p.isPrime
    have hmin := h3 F K' ι' P' hP'.isPrime n hP'n (rename (blockIncl j ι') a) haP W' hW'p.isPrime
      (h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW W' hWf')
      (sup_le hPW' ((Ideal.span_singleton_le_iff_mem _).mpr haW'))
    have hcone := h4 F K' ι' P' hP' W' hW'p hPW' (Function.extend j c 0) (rename (blockIncl j ι') a)
      (rename (blockIncl j ι') h) (isMultiHomog_rename j ι' ha) (isMultiHomog_rename j ι' hh)
      (fun hm => hhW (by rw [← hcW']; exact hm)) (β W')
      (by rw [hβ W' hWf', hα, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap])
    refine ⟨hW'p, hcone.symm, hmin.2, ?_, by rw [hM1 W' hW'p hcW', hd W' hW'p]⟩
    unfold divCycle
    rw [dif_pos ⟨hmin.1, hW'p.relevant⟩]
  refine ⟨∑ W' ∈ hfin.toFinset.filter (fun W' => (rename (blockIncl j ι') a) ∈ W'),
    (Ring.ord (degZeroLoc P' {W'}) (β W')).toNat * d W', ?_, ?_⟩
  · rw [hlen, Nat.cast_sum]
    refine Finset.sum_congr rfl fun W' hT => ?_
    obtain ⟨hW'p, hord, hfin', -, -⟩ := key W' hT
    rw [Nat.cast_mul, ENat.natCast_toNat (hord ▸ hfin')]
  · unfold cycEval
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset.filter (fun W' => (rename (blockIncl j ι') a) ∈ W')) _ ?_,
      Nat.cast_sum]
    · refine Finset.sum_congr rfl fun W' hT => ?_
      obtain ⟨hW'p, hord, -, hdiv, hMd⟩ := key W' hT
      rw [hdiv, hMd, hord]
      push_cast
      ring
    · intro W' hW'
      have hdc : divCycle P' (rename (blockIncl j ι') a) W' ≠ 0 := left_ne_zero_of_mul (Function.mem_support.mp hW')
      have hMW : M W' ≠ 0 := right_ne_zero_of_mul (Function.mem_support.mp hW')
      obtain ⟨hWp, -⟩ := DivCycleSupport.proof F K' ι' P' hP' n hP'n (Function.extend j c 0) (rename (blockIncl j ι') a)
        (isMultiHomog_rename j ι' ha) haP W' hdc
      have hmin : W' ∈ (P' ⊔ Ideal.span {(rename (blockIncl j ι') a)}).minimalPrimes := by
        by_contra hn
        exact hdc (by unfold divCycle; rw [dif_neg (fun hc => hn hc.1)])
      have hc : contractPrime j W' = W := by
        by_contra hne
        exact hMW (hM0 W' hne)
      exact Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr ⟨hWp, le_sup_left.trans hmin.1.2, hc⟩,
        hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
