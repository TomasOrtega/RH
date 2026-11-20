import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacter

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.Annihilator

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem ext_lemma {x y : AF F} (h1 : fstA F x = fstA F y) (h2 : sndA F x = sndA F y) :
    x = y :=
  Prod.ext h1 h2

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem mul_pairA_zero (x : AF F) (z : Ainf F) :
    x * pairA F z 0 = pairA F (fstA F x * z) 0 := by
  apply ext_lemma
  · rw [map_mul]
    rfl
  · rw [map_mul]
    show sndA F x * 0 = 0
    exact mul_zero _

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
private theorem mul_pairA_singleV (x : AF F) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    x * pairA F 0 (singleV F v t) = pairA F 0 (singleV F v (sndA F x v * t)) := by
  apply ext_lemma
  · rw [map_mul]
    show fstA F x * 0 = 0
    exact mul_zero _
  · rw [map_mul]
    show sndA F x * singleV F v t = singleV F v (sndA F x v * t)
    unfold singleV
    classical
    exact (RestrictedProduct.mul_single _ v t (sndA F x)).symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_zero_of_forall [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : AF F)
    (hx : ∀ y, ψ (x * y) = 1) : x = 0 := by
  obtain ⟨hloc, -, hinf⟩ := GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ
  apply ext_lemma
  ·
    have h0 : fstA F x = 0 := hinf _ fun y => by
      have h := hx (pairA F y 0)
      rw [mul_pairA_zero] at h
      exact h
    rw [h0, map_zero]
  ·
    have key : ∀ v, sndA F x v = 0 := by
      intro v
      by_contra hne
      obtain ⟨s, hs⟩ := hloc v
      apply hs
      have h := hx (pairA F 0 (singleV F v ((sndA F x v)⁻¹ * s)))
      rw [mul_pairA_singleV, mul_inv_cancel_left₀ hne] at h
      exact h
    rw [map_zero]
    exact DFunLike.ext _ _ fun v => (key v).trans rfl

/- English proof (translation)
Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_eq_of_forall [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : AF F)
    (hx : ∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) : ∃ ξ : F, x = algebraMap F (AF F) ξ := by
  by_cases htriv : ∀ y, ψ (x * y) = 1
  · exact ⟨0, by rw [map_zero]; exact eq_zero_of_forall hψ x htriv⟩
  · push_neg at htriv
    obtain ⟨hc, hn, -, -⟩ := id hψ

    have hχ : IsCharAF F (ψ.compAddMonoidHom (AddMonoidHom.mulLeft x)) := by
      unfold IsCharAF
      exact ⟨hc.comp (continuous_const.mul continuous_id), fun y => hn _, hx, htriv⟩
    obtain ⟨a, -, ha⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F ψ _ hψ hχ
    refine ⟨a, sub_eq_zero.mp (eq_zero_of_forall hψ _ fun y => ?_)⟩
    have h1 : ψ (x * y) = ψ (algebraMap F (AF F) a * y) := ha y
    rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, h1, ← AddChar.map_add_eq_mul,
      add_neg_cancel, AddChar.map_zero_eq_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem self_annihilator : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → (∀ x : AF F, (∀ y, ψ (x * y) = 1) → x = 0) ∧ ∀ x : AF F, (∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) → ∃ ξ : F, x = algebraMap F (AF F) ξ := by
  intro F _ _ hF ψ hψ
  haveI := hF
  exact ⟨fun x hx => eq_zero_of_forall hψ x hx, fun x hx => exists_eq_of_forall hψ x hx⟩

end GlobalTheory.SWQ.Annihilator
