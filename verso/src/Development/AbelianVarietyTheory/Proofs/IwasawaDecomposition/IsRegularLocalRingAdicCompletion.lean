import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe

open IsLocalRing

namespace GlobalTheory.RegularCompletion

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem isRegularLocalRing_adicCompletion :
    ∀ (T : Type) [CommRing T] [IsRegularLocalRing T],
      IsRegularLocalRing (AdicCompletion (maximalIdeal T) T) := by
  intro T _ _
  haveI : IsNoetherianRing (AdicCompletion (maximalIdeal T) T) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion T (maximalIdeal T)
  set S := AdicCompletion (maximalIdeal T) T

  obtain ⟨s, hcard, hs⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal T).fg_of_isNoetherianRing
  set xs := s.toList
  have hofl : Ideal.ofList xs = maximalIdeal T := by
    rw [← hs]; unfold Ideal.ofList; congr 1; ext x; simp [xs]
  have hlen : xs.length = (maximalIdeal T).spanFinrank := by simp [xs, hcard]
  have hreg : RingTheory.Sequence.IsRegular T xs := GlobalTheory.isRegular_of_length_eq_spanFinrank hofl hlen
  have hmem : ∀ r ∈ xs.map (algebraMap T S), r ∈ maximalIdeal S := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ (hofl ▸ Ideal.subset_span hx)
  have hregS : RingTheory.Sequence.IsRegular S (xs.map (algebraMap T S)) :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
      (hreg.toIsWeaklyRegular.of_flat)
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hregS
  have hnt : Nontrivial (S ⧸ Ideal.ofList (xs.map (algebraMap T S))) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro htop
    apply hregS.2
    simp [htop]
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [AdicCompletion.spanFinrank_maximalIdeal_eq, ← hdim]
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Ideal.ofList (xs.map (algebraMap T S))) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [List.length_map, hlen]
  calc ((Submodule.spanFinrank (maximalIdeal T) : ℕ) : WithBot ℕ∞)
      = 0 + ((Submodule.spanFinrank (maximalIdeal T) : ℕ) : WithBot ℕ∞) := (zero_add _).symm
    _ ≤ _ := add_le_add_left h0 _

end GlobalTheory.RegularCompletion
