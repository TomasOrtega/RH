import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedIdealMapMaximal
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FReducedIdealMapMaximal.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.reduced_ideal_map_maximal : ∀ {B R : Type} [CommRing B] [CommRing R] (ψ : B →+* R), ψ.Finite → ψ.FormallyUnramified → ∀ (Q : Ideal R) [Q.IsPrime] (J : Ideal B), J ≤ Q.comap ψ → IsReduced (B ⧸ J) → (∀ P : Ideal B, P.IsPrime → J ≤ P → P ≤ Q.comap ψ → P = Q.comap ψ) → J.map ((algebraMap R (Localization.AtPrime Q)).comp ψ) = maximalIdeal (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.map_eq_maximalIdeal_of_reduced_minimal | exact GlobalTheory.map_eq_maximalIdeal_of_reduced_minimal | (intros; apply GlobalTheory.map_eq_maximalIdeal_of_reduced_minimal <;> assumption)
