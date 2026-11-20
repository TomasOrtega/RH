import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe

open IsLocalRing

namespace GlobalTheory.RegularCompletion

/- English proof (translation)
Introduce `T _ _`. Use `haveI : IsNoetherianRing (AdicCompletion (maximalIdeal T) T) := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion T (maximalIdeal T)`. Use `set S := AdicCompletion (maximalIdeal T) T`. Take `⟨s, hcard, hs⟩` from `Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal T).fg_of_isNoetherianRing`. Use `set xs := s.toList`.

Establish `hofl : Ideal.ofList xs = maximalIdeal T`. Rewrite using `[← hs]`. Unfold `Ideal.ofList`. Use `congr 1`. Use extensionality with `x`.

Simplify using `[xs]`. Establish `hlen : xs.length = (maximalIdeal T).spanFinrank` using `by simp [xs, hcard]`. Establish `hreg : RingTheory.Sequence.IsRegular T xs` using `GlobalTheory.isRegular_of_length_eq_spanFinrank hofl hlen`. Establish `hmem : ∀ r ∈ xs.map (algebraMap T S), r ∈ maximalIdeal S`. Introduce `r hr`.

Take `⟨x, hx, rfl⟩` from `List.mem_map.mp hr`. Rewrite using `[AdicCompletion.maximalIdeal_eq_map]`. Conclude with `Ideal.mem_map_of_mem _ (hofl ▸ Ideal.subset_span hx)`. Establish `hregS : RingTheory.Sequence.IsRegular S (xs.map (algebraMap T S))` using `(IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr (hreg.toIsWeaklyRegular.of_flat)`. Establish `hdim` using `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hregS`.

Establish `hnt : Nontrivial (S ⧸ Ideal.ofList (xs.map (algebraMap T S)))`. Rewrite using `[Ideal.Quotient.nontrivial_iff]`. Introduce `htop`. Apply `hregS.2` to reduce the goal to its premises. Simplify using `[htop]`.

Use `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_` and prove the remaining obligations. Rewrite using `[AdicCompletion.spanFinrank_maximalIdeal_eq, ← hdim]`. Establish `h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Ideal.ofList (xs.map (algebraMap T S)))` using `ringKrullDim_nonneg_of_nontrivial`. Rewrite using `[List.length_map, hlen]`. Combine the equalities or inequalities in the displayed calculation.
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
