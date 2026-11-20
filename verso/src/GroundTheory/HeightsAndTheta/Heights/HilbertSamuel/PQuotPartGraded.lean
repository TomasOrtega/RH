import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsQuotPartGraded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace QuotPartGraded

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in

def blockWeight (ι : K → Type) : (Σ k, ι k) → (K → ℤ) := fun x => Pi.single x.1 1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem blockWeight_apply (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) d k = ∑ i, (d ⟨k, i⟩ : ℤ) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun i c => c • blockWeight ι i) (by intro i; simp),
    Finset.sum_apply, Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]

/- English proof (translation)
Replace the relevant objects with their definitions. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem isMultiHomog_iff (p : MRingOver S ι) (a : K → ℕ) :
    IsMultiHomog p a ↔ IsWeightedHomogeneous (blockWeight ι) p (fun k => (a k : ℤ)) := by
  unfold IsMultiHomog
  constructor
  · intro h d hd
    funext k
    rw [blockWeight_apply]
    have := h d (mem_support_iff.2 hd) k
    exact_mod_cast this
  · intro h m hm k
    have := congrFun (h (mem_support_iff.1 hm)) k
    rw [blockWeight_apply] at this
    exact_mod_cast this

/- English proof (translation)
Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Check the signs of the components of the expression.
-/
theorem nonneg_of_isWeightedHomogeneous {p : MRingOver S ι} {c : K → ℤ}
    (hp : IsWeightedHomogeneous (blockWeight ι) p c) (h0 : p ≠ 0) : ∀ k, 0 ≤ c k := by
  obtain ⟨d, hd⟩ := ne_zero_iff.1 h0
  intro k
  rw [← hp hd, blockWeight_apply]
  positivity

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem span_eq (c : K → ℤ) :
    Submodule.span S {p : MRingOver S ι | (∀ k, 0 ≤ c k) ∧ IsMultiHomog p (fun k => (c k).toNat)} =
      weightedHomogeneousSubmodule S (blockWeight ι) c := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro p ⟨hc, hp⟩
    rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule]
    have h' := (isMultiHomog_iff p _).1 hp
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rwa [hcc] at h'
  · intro p hp
    by_cases h0 : p = 0
    · rw [h0]; exact Submodule.zero_mem _
    · apply Submodule.subset_span
      have hc := nonneg_of_isWeightedHomogeneous hp h0
      refine ⟨hc, (isMultiHomog_iff p _).2 ?_⟩
      have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
      rw [hcc]
      exact hp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem quotPart_eq (V : Ideal (MRingOver S ι)) (c : K → ℤ) :
    KH.quotPart S V c =
      (weightedHomogeneousSubmodule S (blockWeight ι) c).map (Ideal.Quotient.mkₐ S V).toLinearMap := by
  rw [KH.quotPart, ← span_eq, Submodule.map_span]
  rfl

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem isHomogeneous {V : Ideal (MRingOver S ι)} (hV : IsMultiHomogIdeal V) :
    V.IsHomogeneous (weightedHomogeneousSubmodule S (blockWeight ι)) := by
  obtain ⟨T, hT, rfl⟩ := hV
  apply Ideal.homogeneous_span
  intro f hf
  obtain ⟨a, ha⟩ := hT f hf
  exact ⟨fun k => (a k : ℤ), (isMultiHomog_iff f a).1 ha⟩

end QuotPartGraded

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Supply the required witnesses or components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem QuotPartGraded.proof : QuotPartGraded.Statement := by
  intro S _ K _ ι _ V hV
  have hq := QuotPartGraded.quotPart_eq (S := S) (ι := ι) V
  refine ⟨?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨?_, ?_⟩
    · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro s v hv hsum
      have hlift : ∀ c, ∃ p : MRingOver S ι, c ∈ s →
          (p ∈ weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι) c ∧
            Ideal.Quotient.mk V p = v c) := by
        intro c
        by_cases hc : c ∈ s
        · have h1 := hv c hc
          rw [hq] at h1
          obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.1 h1
          exact ⟨y, fun _ => ⟨hy, hyv⟩⟩
        · exact ⟨0, fun h => absurd h hc⟩
      choose p hp using hlift
      have hsumV : ∑ c ∈ s, p c ∈ V := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hsum]
        exact Finset.sum_congr rfl fun c hc => (hp c hc).2
      intro c hc
      have hcomp := weightedHomogeneousComponent_mem_of_mem S (QuotPartGraded.blockWeight ι)
        (QuotPartGraded.isHomogeneous hV) hsumV c
      rw [map_sum, Finset.sum_eq_single c] at hcomp
      · rw [← (hp c hc).2, Ideal.Quotient.eq_zero_iff_mem]
        rwa [weightedHomogeneousComponent_eq_self (hp c hc).1] at hcomp
      · intro d hd hdc
        exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne c (hp d hd).1 (Ne.symm hdc)
      · intro h
        exact absurd hc h
    · have htop := (DirectSum.Decomposition.isInternal
        (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι))).submodule_iSup_eq_top
      rw [show KH.quotPart S V = fun c => (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι) c).map
          (Ideal.Quotient.mkₐ S V).toLinearMap from funext hq]
      rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]
      exact Ideal.Quotient.mkₐ_surjective S V
  · intro a c p m hp hm
    rw [hq] at hm ⊢
    obtain ⟨q, hq', rfl⟩ := Submodule.mem_map.1 hm
    refine Submodule.mem_map.2 ⟨p * q, ?_, ?_⟩
    · have := ((QuotPartGraded.isMultiHomog_iff p a).1 hp).mul hq'
      rw [mem_weightedHomogeneousSubmodule, add_comm]
      exact this
    · simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
      rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
