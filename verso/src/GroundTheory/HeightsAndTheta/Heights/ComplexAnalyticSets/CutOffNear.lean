import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Set Topology MvPolynomial ComplexSets
open scoped ContDiff Manifold

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_cutoff_near {n : ℕ} {S U : Set (Fin n → ℂ)} (hS : IsClosed S) (hU : IsOpen U)
    (hSU : S ⊆ U) :
    ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ U ∧
      ∃ V : Set (Fin n → ℂ), IsOpen V ∧ S ⊆ V ∧ ∀ x ∈ V, χ x = 1 := by
  obtain ⟨V, hV, hSV, hVU⟩ := normal_exists_closure_subset hS hU hSU
  obtain ⟨f, hf1, hf0, hf⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ, Fin n → ℂ) (n := ⊤) hS (t := closure V) (hSV.trans (interior_maximal subset_closure hV))
  refine ⟨f, f.contMDiff.contDiff, hf, ?_, ?_⟩
  · refine (closure_minimal (fun x hx => ?_) isClosed_closure).trans hVU
    by_contra h
    exact hx (hf0 x h)
  · obtain ⟨W, hW, hSW, hWf⟩ := mem_nhdsSet_iff_exists.1 hf1
    exact ⟨W, hW, hSW, fun x hx => hWf hx⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_cutoff_near_zeroSet {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hIU : zeroSet I ⊆ U) :
    ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ U ∧
      ∃ V : Set (Fin n → ℂ), IsOpen V ∧ zeroSet I ⊆ V ∧ ∀ x ∈ V, χ x = 1 := by
  refine exists_cutoff_near ?_ hU hIU
  have : zeroSet I = ⋂ q ∈ I, {x : Fin n → ℂ | eval x q = 0} := by
    ext x
    simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

end GroundTheory.Heights₂.Heights
