import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin

open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `O H K _ _ _ _ _ _ _ _ _ hred`. Establish `: IsReduced (K ⊗[O] H)` using `hred`. Establish `hcard : Nat.card (H →ₐ[O] K) = Module.finrank O H` using `natCard_algHom_eq_finrank_of_isReduced_baseChange O H K`. Establish `hfin : Finite (H →ₐ[O] K)`. Distinguish the cases in `h0 : Module.finrank O H = 0`.

Establish `: IsEmpty (H →ₐ[O] K)`. Use `⟨fun f => ?_⟩` and prove the remaining obligations. Establish `hι : IsEmpty (Module.Free.ChooseBasisIndex O H)`. Rewrite using `[← Fintype.card_eq_zero_iff, ← Module.finrank_eq_card_chooseBasisIndex]`. Conclude with `h0`.

Establish `h10 : (1 : H) = 0` using `(Module.Free.chooseBasis O H).repr.injective (Subsingleton.elim _ _)`. Establish `h1` using `congrArg f h10`. Rewrite `h1` using `[map_one, map_zero]`. Conclude with `one_ne_zero h1`. Use `infer_instance`.

Conclude with `Nat.finite_of_card_ne_zero (hcard ▸ h0)`. Use `⟨hfin, hcard, fun h => ?_⟩` and prove the remaining obligations. Set `_` to `Fintype.ofFinite (H →ₐ[O] K)`. Rewrite using `[finsum_eq_sum_of_fintype]`. Conclude with `algebraMap_trace_eq_sum_algHom_of_card (R := O) (S := H) (L := K) (by rw [← Nat.card_eq_fintype_card, hcard]) (P := fun g => g) (fun _ _ e => e) h`.
-/
theorem finite_card_trace_algHom_of_isReduced_baseChange :
    ∀ (O H K : Type) [CommRing O] [Nontrivial O] [CommRing H] [Algebra O H] [Module.Free O H]
      [Module.Finite O H] [Field K] [IsAlgClosed K] [Algebra O K], IsReduced (K ⊗[O] H) →
      Finite (H →ₐ[O] K) ∧ Nat.card (H →ₐ[O] K) = Module.finrank O H ∧
        ∀ h : H, algebraMap O K (Algebra.trace O H h) = ∑ᶠ ga : H →ₐ[O] K, ga h := by
  intro O H K _ _ _ _ _ _ _ _ _ hred
  have : IsReduced (K ⊗[O] H) := hred
  have hcard : Nat.card (H →ₐ[O] K) = Module.finrank O H :=
    natCard_algHom_eq_finrank_of_isReduced_baseChange O H K
  have hfin : Finite (H →ₐ[O] K) := by
    by_cases h0 : Module.finrank O H = 0
    · have : IsEmpty (H →ₐ[O] K) := by
        refine ⟨fun f => ?_⟩
        have hι : IsEmpty (Module.Free.ChooseBasisIndex O H) := by
          rw [← Fintype.card_eq_zero_iff, ← Module.finrank_eq_card_chooseBasisIndex]
          exact h0
        have h10 : (1 : H) = 0 :=
          (Module.Free.chooseBasis O H).repr.injective (Subsingleton.elim _ _)
        have h1 := congrArg f h10
        rw [map_one, map_zero] at h1
        exact one_ne_zero h1
      infer_instance
    · exact Nat.finite_of_card_ne_zero (hcard ▸ h0)
  refine ⟨hfin, hcard, fun h => ?_⟩
  let _ := Fintype.ofFinite (H →ₐ[O] K)
  rw [finsum_eq_sum_of_fintype]
  exact algebraMap_trace_eq_sum_algHom_of_card (R := O) (S := H) (L := K)
    (by rw [← Nat.card_eq_fintype_card, hcard]) (P := fun g => g) (fun _ _ e => e) h

end GlobalTheory
