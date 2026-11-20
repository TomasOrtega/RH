import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.AdmFin

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

/- English proof (translation)
Introduce `R _ M _ _ _ _ _ _`. Use `haveI : IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R) := by`. Use `letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)`. Use `infer_instance`. Use `⟨tateH1FinitenessAtPlacesOver (IsLocalRing.maximalIdeal R), fun hfin k => ?_⟩` and prove the remaining obligations.

Use `haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) := hfin`. Use `haveI : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M`. Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[pow_zero, Ideal.one_eq_top, Submodule.top_smul]`.

Use `infer_instance`. Consider the case `succ n ih`. Rewrite using `[pow_succ', Submodule.mul_smul]`. Conclude with `Submodule.finite_quotient_smul _ (IsNoetherian.noetherian _)`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordAdm_maximalIdeal_and_finite_quotients :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Module.Finite R M], OrdAdm M (IsLocalRing.maximalIdeal R) ∧ (Finite (IsLocalRing.ResidueField R) → ∀ k : ℕ, Finite (M ⧸ (IsLocalRing.maximalIdeal R ^ k • ⊤ : Submodule R M))) := by
  intro R _ M _ _ _ _ _ _
  haveI : IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R) := by
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    infer_instance
  refine ⟨tateH1FinitenessAtPlacesOver (IsLocalRing.maximalIdeal R), fun hfin k => ?_⟩
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) := hfin
  haveI : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  induction k with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    infer_instance
  | succ n ih =>
    rw [pow_succ', Submodule.mul_smul]
    exact Submodule.finite_quotient_smul _ (IsNoetherian.noetherian _)
