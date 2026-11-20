import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Introduce `F _ _ n e I f u hI hf hu`. Establish `hne : specFirst f u ≠ 0` using `h₄ F n e I f u hI hf hu`. Use `⟨hne, fun q hq => ?_⟩` and prove the remaining obligations. Establish `hqp : Prime q` using `hq.prime`. Take `⟨t, ht⟩` from `h₃ F n e I f q hI hf hqp`.

Establish `htI : linForm t ∉ I`. Introduce `h`. Establish `hmem` using `h₂ F n e I I f t hf le_rfl h`. Rewrite `hmem` using `[h₁ F n e I f hI hf, Ideal.mem_bot]`. Conclude with `ht (hmem ▸ dvd_zero q)`.

Set `p : Ideal (MvPolynomial (Fin e × Fin n) F)` to `Ideal.span {q}`. Establish `hpp : p.IsPrime` using `(Ideal.span_singleton_prime hqp.ne_zero).mpr hqp`. Establish `htp : specFirst f t ∉ p`. Rewrite using `[Ideal.mem_span_singleton]`. Conclude with `ht`.

Establish `: IsDiscreteValuationRing (Localization.AtPrime p)` using `h₅ _ q p hqp rfl`. Establish `hem` using `h₆ _ q (specFirst f u) p hqp rfl hne`. Establish `: Module.Finite (Localization.AtPrime p) (ChartLoc I t e p)` using `h₇ F n e I f t p hI hf htp`. Take `⟨_, hinj, -⟩` from `h₈ F n e I f t p hI hf htI`. Establish `: Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p)`.

Rewrite using `[Module.isTorsionFree_iff_algebraMap_injective]`. Conclude with `hinj`. Establish `: Module.Free (Localization.AtPrime p) (ChartLoc I t e p)` using `Module.free_of_finite_type_torsion_free'`. Establish `hnorm` using `h₉ F n e I f t p hI hf (Or.inr ⟨q, hqp, rfl⟩) htp u`. Establish `hunit : IsUnit (algebraMap _ (Localization.AtPrime p) (specFirst f t))` using `IsLocalization.map_units (Localization.AtPrime p) (⟨specFirst f t, htp⟩ : p.primeCompl)`.

Establish `hinjO : Function.Injective (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p))` using `IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors`. Establish `hdet : LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p) (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))) ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Apply `hinjO` to reduce the goal to its premises.

Rewrite using `[hnorm, h0, mul_zero, map_zero]`. Establish `hlen` using `h₁₁ (Localization.AtPrime p) (ChartLoc I t e p) _ hdet`. Rewrite using `[hem, hnorm, Ring.ord_mul_of_isUnit_left hunit, ← hlen]`. Conclude with `h₁₀ F n e I f t u q p hI hf hu hqp rfl ht`.
-/
theorem SectionOrder.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartChoice.Statement) (h₄ : SpecFirstNe.Statement) (h₅ : LocalizationPrimeDVR.Statement)
    (h₆ : EmultiplicityOrd.Statement) (h₇ : ChartFinite.Statement) (h₈ : ChartLocDomain.Statement)
    (h₉ : ChartNorm.Statement) (h₁₀ : ChartLength.Statement) (h₁₁ : LengthQuotientDet.Statement) :
    SectionOrder.Statement := by
  intro F _ _ n e I f u hI hf hu
  have hne : specFirst f u ≠ 0 := h₄ F n e I f u hI hf hu
  refine ⟨hne, fun q hq => ?_⟩
  have hqp : Prime q := hq.prime
  obtain ⟨t, ht⟩ := h₃ F n e I f q hI hf hqp

  have htI : linForm t ∉ I := by
    intro h
    have hmem := h₂ F n e I I f t hf le_rfl h
    rw [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem
    exact ht (hmem ▸ dvd_zero q)
  let p : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q}
  have hpp : p.IsPrime := (Ideal.span_singleton_prime hqp.ne_zero).mpr hqp
  have htp : specFirst f t ∉ p := by
    rw [Ideal.mem_span_singleton]
    exact ht
  have : IsDiscreteValuationRing (Localization.AtPrime p) := h₅ _ q p hqp rfl
  have hem := h₆ _ q (specFirst f u) p hqp rfl hne
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₇ F n e I f t p hI hf htp
  obtain ⟨_, hinj, -⟩ := h₈ F n e I f t p hI hf htI
  have : Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hinj
  have : Module.Free (Localization.AtPrime p) (ChartLoc I t e p) :=
    Module.free_of_finite_type_torsion_free'
  have hnorm := h₉ F n e I f t p hI hf (Or.inr ⟨q, hqp, rfl⟩) htp u
  have hunit : IsUnit (algebraMap _ (Localization.AtPrime p) (specFirst f t)) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨specFirst f t, htp⟩ : p.primeCompl)
  have hinjO : Function.Injective
      (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) :=
    IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
  have hdet : LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
      (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))) ≠ 0 := by
    intro h0
    apply hne
    apply hinjO
    rw [hnorm, h0, mul_zero, map_zero]
  have hlen := h₁₁ (Localization.AtPrime p) (ChartLoc I t e p) _ hdet
  rw [hem, hnorm, Ring.ord_mul_of_isUnit_left hunit, ← hlen]
  exact h₁₀ F n e I f t u q p hI hf hu hqp rfl ht

end

end GroundTheory.Heights₂.Heights
