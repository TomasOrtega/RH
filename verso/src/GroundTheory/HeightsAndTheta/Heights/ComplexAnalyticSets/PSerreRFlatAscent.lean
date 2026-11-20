import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreRFlatAscent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSerreRFlatAscentLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

/- English proof (translation)
Introduce `A B _ _ _ hA hB hflat k hRA hfib P _ hdim`. Establish `: IsNoetherianRing A` using `hA`. Establish `: IsNoetherianRing B` using `hB`. Establish `: Module.Flat A B` using `hflat`. Set `` to `Localization.AtPrime.algebraOfLiesOver (P.under A) P`.

Establish `: IsLocalHom (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P))` using `Localization.isLocalHom_localRingHom _ _ _ Ideal.LiesOver.over`. Use `isLocalRing_closedFibre (R := Localization.AtPrime (P.under A)) (S := Localization.AtPrime P)` as an intermediate fact. Set `e` to `Ideal.quotEquivOfEq (map_maximalIdeal_localization_eq (A := A) P).symm`. Establish `hsum` using `ringKrullDim_eq_add_ringKrullDim_closedFibre (R := Localization.AtPrime (P.under A)) (S := Localization.AtPrime P)`. Establish `h0A : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime (P.under A))` using `ringKrullDim_nonneg_of_nontrivial`.

Establish `h0F : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime P ⧸ (maximalIdeal (Localization.AtPrime (P.under A))).map (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P)))` using `ringKrullDim_nonneg_of_nontrivial`. Rewrite `hdim` using `[hsum]`. Establish `hAk` using `(le_add_of_nonneg_right h0F).trans hdim`. Establish `hFk` using `(le_add_of_nonneg_left h0A).trans hdim`. Establish `hF : IsRegularLocalRing (primeFibreLocalRing A P)` using `hfib P (by rw [ringKrullDim_eq_of_ringEquiv e]; exact hFk)`.

Conclude with `isRegularLocalRing_of_flat_of_closedFibre (hRA (P.under A) hAk) (hF.of_ringEquiv e)`.
-/
theorem SerreRFlatAscent.proof : SerreRFlatAscent.Statement := by
  intro A B _ _ _ hA hB hflat k hRA hfib P _ hdim
  have : IsNoetherianRing A := hA
  have : IsNoetherianRing B := hB
  have : Module.Flat A B := hflat
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  have : IsLocalHom (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P)) :=
    Localization.isLocalHom_localRingHom _ _ _ Ideal.LiesOver.over
  have := isLocalRing_closedFibre (R := Localization.AtPrime (P.under A)) (S := Localization.AtPrime P)
  let e := Ideal.quotEquivOfEq (map_maximalIdeal_localization_eq (A := A) P).symm
  have hsum := ringKrullDim_eq_add_ringKrullDim_closedFibre (R := Localization.AtPrime (P.under A))
    (S := Localization.AtPrime P)
  have h0A : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime (P.under A)) :=
    ringKrullDim_nonneg_of_nontrivial
  have h0F : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime P ⧸
      (maximalIdeal (Localization.AtPrime (P.under A))).map
        (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P))) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [hsum] at hdim
  have hAk := (le_add_of_nonneg_right h0F).trans hdim
  have hFk := (le_add_of_nonneg_left h0A).trans hdim
  have hF : IsRegularLocalRing (primeFibreLocalRing A P) :=
    hfib P (by rw [ringKrullDim_eq_of_ringEquiv e]; exact hFk)
  exact isRegularLocalRing_of_flat_of_closedFibre (hRA (P.under A) hAk) (hF.of_ringEquiv e)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
