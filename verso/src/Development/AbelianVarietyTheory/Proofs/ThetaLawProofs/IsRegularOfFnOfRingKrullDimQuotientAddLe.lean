import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe

namespace GlobalTheory

/- English proof (translation)
Introduce `A _ _ d r f hd hm hq`. Establish `he : Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f)`. Unfold `Ideal.ofList`. Use `congr 1`. Use extensionality with `x`.

Simplify using `[List.mem_ofFn]`. Use `isRegular_of_isCM_of_ringKrullDim_quotient_add_length_le (isCM_of_isRegularLocalRing A) (fun y hy => ?_) ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `List.mem_ofFn.mp hy`. Conclude with `hm i`. Rewrite using `[he, List.length_ofFn, hd]`.

Conclude with `hq`.
-/
theorem isRegular_ofFn_of_ringKrullDim_quotient_add_le :
    ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (d r : ℕ) (f : Fin r → A),
      ringKrullDim A = d → (∀ i, f i ∈ IsLocalRing.maximalIdeal A) →
      ringKrullDim (A ⧸ Ideal.span (Set.range f)) + r ≤ d →
      RingTheory.Sequence.IsRegular A (List.ofFn f) := by
  intro A _ _ d r f hd hm hq
  have he : Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
    unfold Ideal.ofList
    congr 1
    ext x
    simp [List.mem_ofFn]
  refine isRegular_of_isCM_of_ringKrullDim_quotient_add_length_le
    (isCM_of_isRegularLocalRing A) (fun y hy => ?_) ?_
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact hm i
  · rw [he, List.length_ofFn, hd]
    exact hq

end GlobalTheory
