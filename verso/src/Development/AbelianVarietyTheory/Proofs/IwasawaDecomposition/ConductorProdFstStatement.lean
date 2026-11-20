import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorProdFst
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.conductor_prod_fst` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FConductorProdFst.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_mul_fst_eq_of_integral_of_conductor : ∀ (R S' S : Type) [CommRing R] [CommRing S'] [CommRing S] (e : S ≃+* R × S') (d : S), (∀ c : FractionRing S, IsIntegral S c → ∃ s : S, algebraMap S (FractionRing S) s = algebraMap S (FractionRing S) d * c) → ∀ c : FractionRing R, IsIntegral R c → ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) (e d).1 * c := by
  first | exact @GlobalTheory.conductor_prod_fst | exact GlobalTheory.conductor_prod_fst | (intros; apply GlobalTheory.conductor_prod_fst <;> assumption)
