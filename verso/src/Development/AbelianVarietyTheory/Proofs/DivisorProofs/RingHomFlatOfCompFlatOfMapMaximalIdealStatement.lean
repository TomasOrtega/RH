import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFlatOfCompFlatOfMapMaximalIdeal
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRingHomFlatOfCompFlatOfMapMaximalIdeal.lean&line=164#L164)
-/
theorem _root_.GlobalTheory.T.flat_of_flat_comp_of_map_maximalIdeal_eq : ∀ (O R' E : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [IsNoetherianRing E] (φ' : O →+* R') (b : R' →+* E), φ'.Flat → (maximalIdeal O).map φ' = maximalIdeal R' → IsLocalHom b → (b.comp φ').Flat → b.Flat := by
  first | exact @GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal | exact GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal | (intros; apply GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal <;> assumption)
