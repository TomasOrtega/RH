import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type*} [DecidableEq K] {ι : K → Type*}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eval_eq_zero_of_block_zero {m : K → ℕ} (hm : ∀ k, 1 ≤ m k) {f : MvPolynomial (Σ k, ι k) ℂ}
    (hf : IsWeightedHomogeneous (blockWeight ι) f m) {x : (Σ k, ι k) → ℂ} {k : K}
    (hx : ∀ i, x ⟨k, i⟩ = 0) : eval x f = 0 := by
  classical
  rw [MvPolynomial.eval_eq]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw := hf (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨v, hv, hvk⟩ : ∃ v ∈ d.support, v.1 = k := by
    by_contra hno
    push Not at hno
    have h0 : (Finsupp.weight (blockWeight ι) d) k = 0 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun v hv => ?_
      simp [blockWeight, hno v hv]
    have := hm k
    rw [hw] at h0
    omega
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hv ?_)
  obtain ⟨k', i⟩ := v
  subst hvk
  rw [hx i]
  exact zero_pow (Finsupp.mem_support_iff.mp hv)

variable [Fintype K] [∀ k, Fintype (ι k)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem mem_radical_iff_offBlocks (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) {m : K → ℕ} (hm : ∀ k, 1 ≤ m k)
    {f : MvPolynomial (Σ k, ι k) ℂ} (hf : IsWeightedHomogeneous (blockWeight ι) f m) :
    f ∈ I.radical ↔ f ∈ vanishingIdeal ℂ (zeroLocus ℂ I ∩ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ) I]
  constructor
  · exact fun h => vanishingIdeal_anti_mono Set.inter_subset_left h
  · intro h x hx
    by_cases hU : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0
    · exact h x ⟨hx, hU⟩
    · push Not at hU
      obtain ⟨k, hk⟩ := hU
      exact eval_eq_zero_of_block_zero hm hf hk

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Establish an intermediate fact. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finrank_gradedPiece_eq {P₁ P₂ : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (m : K → ℕ)
    (h : ∀ f ∈ weightedHomogeneousSubmodule ℂ (blockWeight ι) m, f ∈ P₁ ↔ f ∈ P₂) :
    Module.finrank ℂ (gradedPiece P₁ m) = Module.finrank ℂ (gradedPiece P₂ m) := by
  set W := weightedHomogeneousSubmodule ℂ (blockWeight ι) m
  let f₁ := (Ideal.Quotient.mkₐ ℂ P₁).toLinearMap ∘ₗ W.subtype
  let f₂ := (Ideal.Quotient.mkₐ ℂ P₂).toLinearMap ∘ₗ W.subtype
  have hr₁ : LinearMap.range f₁ = gradedPiece P₁ m := by
    simp only [f₁, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hr₂ : LinearMap.range f₂ = gradedPiece P₂ m := by
    simp only [f₂, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hk : LinearMap.ker f₁ = LinearMap.ker f₂ := by
    ext ⟨x, hx⟩
    simp only [LinearMap.mem_ker, f₁, f₂, LinearMap.comp_apply, Submodule.subtype_apply,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact h x hx
  rw [← hr₁, ← hr₂]
  exact ((f₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans
    f₂.quotKerEquivRange).finrank_eq

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem hilbFn_radical_eq_offBlocks (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) {m : K → ℤ} (hm : ∀ k, 1 ≤ m k) :
    hilbFn I.radical m = hilbFn (vanishingIdeal ℂ (zeroLocus ℂ I ∩ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})) m := by
  unfold hilbFn
  have h0 : ∀ k, 0 ≤ m k := fun k => le_trans zero_le_one (hm k)
  rw [if_pos h0, if_pos h0]
  congr 1
  refine finrank_gradedPiece_eq _ fun f hf => mem_radical_iff_offBlocks I (m := fun k => (m k).toNat) (fun k => ?_) ?_
  · have := hm k
    omega
  · rwa [mem_weightedHomogeneousSubmodule] at hf

omit [DecidableEq K] [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem foldr_diffStep_eventuallyEq {h₁ h₂ : (K → ℤ) → ℤ} (h : h₁ =ᶠ[atTop] h₂) (l : List (K → ℤ)) :
    l.foldr diffStep h₁ =ᶠ[atTop] l.foldr diffStep h₂ := by
  induction l with
  | nil => exact h
  | cons b l ih =>
    have ht : Tendsto (fun m : K → ℤ => m - b) atTop atTop := by
      exact (tendsto_atTop_add_const_right atTop (-b) tendsto_id).congr fun m => by simp [sub_eq_add_neg]
    filter_upwards [ih, ht.eventually ih] with m hm hmb
    simp only [List.foldr_cons, diffStep, hm, hmb]

omit [DecidableEq K] [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eventualValue_congr {f g : (K → ℤ) → ℤ} (h : f =ᶠ[atTop] g) : eventualValue f = eventualValue g := by
  unfold eventualValue
  have hiff : (∃ c, ∀ᶠ m in atTop, f m = c) ↔ ∃ c, ∀ᶠ m in atTop, g m = c :=
    ⟨fun ⟨c, hc⟩ => ⟨c, (h.and hc).mono fun _ hm => hm.1.symm.trans hm.2⟩,
      fun ⟨c, hc⟩ => ⟨c, (h.and hc).mono fun _ hm => hm.1.trans hm.2⟩⟩
  by_cases hf : ∃ c, ∀ᶠ m in atTop, f m = c
  · rw [dif_pos hf, dif_pos (hiff.mp hf)]
    obtain ⟨m, hm⟩ := (hf.choose_spec.and ((hiff.mp hf).choose_spec.and h)).exists
    exact hm.1.symm.trans (hm.2.2.trans hm.2.1)
  · rw [dif_neg hf, dif_neg (mt hiff.mpr hf)]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem intNum_radical_eq_offBlocks (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) {n : ℕ} (bs : Fin n → K → ℤ) :
    intNum ℂ I.radical bs =
      intNum ℂ (vanishingIdeal ℂ (zeroLocus ℂ I ∩ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})) bs := by
  unfold intNum mixedDiff
  refine eventualValue_congr (foldr_diffStep_eventuallyEq ?_ _)
  filter_upwards [eventually_ge_atTop (1 : K → ℤ)] with m hm
  exact hilbFn_radical_eq_offBlocks I fun k => hm k

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
