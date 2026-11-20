import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

open IsLocalRing

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.CA.g_dimcpl :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
      ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by
  intro R _ _ _
  haveI := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion R (maximalIdeal R)
  have hm := AdicCompletion.maximalIdeal_eq_map (R := R)
  haveI : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal.isMaximal R).eq_of_le Ideal.IsPrime.ne_top'
      (Ideal.map_le_iff_le_comap.mp hm.ge)⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R)
    (maximalIdeal (AdicCompletion (maximalIdeal R) R))
  rw [← hm, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h]
