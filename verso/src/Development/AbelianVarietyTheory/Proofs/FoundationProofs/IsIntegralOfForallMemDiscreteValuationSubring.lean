import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `S K _ _ _ _ _ _ t ht`. Assume the negation of the conclusion as `hn`. Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`. Conclude with `hn isIntegral_zero`.

Establish `: Algebra.EssFiniteType S K` using `.of_isLocalization K (nonZeroDivisors S)`. Establish `hic : IsIntegrallyClosedIn (integralClosure S K).toSubring K` using `inferInstanceAs (IsIntegrallyClosedIn (integralClosure S K) K)`. Take `⟨W, hW, htW⟩` from `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn (R := (integralClosure S K).toSubring) (x := t) hn`. Establish `hinv : t⁻¹ ∈ W.nonunits` using `W.inv_mem_nonunits_iff.mpr (Or.inr htW)`. Take `⟨V, h1, h2, -, h3⟩` from `exists_discreteValuationSubring_of_valuationSubring (R := S) W (fun r => hW ((integralClosure S K).algebraMap_mem r)) Set.finite_empty (Set.finite_singleton t⁻¹) (by simp) (by simpa using hinv) ⟨_, rfl, inv_ne_zero ht0⟩`.

Conclude with `(V.inv_mem_nonunits_iff.mp (h3 _ rfl)).resolve_left ht0 (ht V h1 h2)`.
-/
theorem isIntegral_of_forall_mem_discreteValuationSubring : ∀ (S K : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field K] [Algebra S K] [IsFractionRing S K] (t : K), (∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ s : S, algebraMap S K s ∈ V) → t ∈ V) → IsIntegral S t := by
  intro S K _ _ _ _ _ _ t ht
  by_contra hn
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hn isIntegral_zero
  have : Algebra.EssFiniteType S K := .of_isLocalization K (nonZeroDivisors S)
  have hic : IsIntegrallyClosedIn (integralClosure S K).toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure S K) K)
  obtain ⟨W, hW, htW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure S K).toSubring) (x := t) hn
  have hinv : t⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr htW)
  obtain ⟨V, h1, h2, -, h3⟩ := exists_discreteValuationSubring_of_valuationSubring (R := S) W
    (fun r => hW ((integralClosure S K).algebraMap_mem r))
    Set.finite_empty (Set.finite_singleton t⁻¹) (by simp) (by simpa using hinv)
    ⟨_, rfl, inv_ne_zero ht0⟩
  exact (V.inv_mem_nonunits_iff.mp (h3 _ rfl)).resolve_left ht0 (ht V h1 h2)

end GlobalTheory
