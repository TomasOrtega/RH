import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.AtFormAdmOneOfSteps
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtomicFormOneReduction

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section
set_option maxHeartbeats 3200000

namespace Formalism.FourierDecayAlt.P

namespace UnipotentHaarMeasurability
open Formalism.FourierDecayAlt.ThreeDimData

namespace GC

/- English proof (translation)
Introduce `hSch hBC hNI hBB hSh hKF hZ hZD hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS`. Establish `hS'` using `hS`. Take `⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩` from `hS'`. Take `⟨hBC1, -, -, -⟩` from `hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS`. Take `⟨d, hd, hSd⟩` from `hSch k r ε lam H σ μG hlam hσ hG`.

Establish `hw0n : w0 ≠ 0`. Take `⟨P, -, hn1, -⟩` from `hw0`. Introduce `h0`. Rewrite `hn1` using `[h0, norm_zero]`. Conclude with `zero_ne_one hn1`.

Establish `hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d` using `fun x hx => DDSmoothness.fdeg_eq hd hSd hx`. Establish `hmu` using `DDSmoothness.muSof_facts hW hN`. Establish `hae` using `DDSmoothness.ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq`. Establish `hAs : ∀ v : H, IsAdm σ w0 v → v ∈ PI.UpqRep.smoothVecs (k` using `k) (r := r) σ := by`. Introduce `v hv`.

Break down `hv with hv | hv` into its components or cases. Conclude with `DDSmoothness.DD_smooth hIn.2.2.1 hlam hσ hw0 v hv`. Conclude with `hIn.2.2.1 k r ε lam H σ hlam hσ v hv`. Distinguish the cases in `hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0`. Take `⟨l, hl, hx1, hid⟩` from `hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz`.

Establish `hK` using `hKF hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS l hl hx1 hid`. Establish `hI : ∀ v : H, IsAdm σ w0 v → ∀ x ∈ PI.UpqRep.smoothVecs (k` using `k) (r := r) σ, be z c π σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x) := by`. Introduce `v hv x hx`. Break down `hv with hv | hv` into its components or cases. Conclude with `hid x hx v hv`.

Conclude with `hK v hv x hx`. Use `⟨l, hl, fun x hx v hv => ⟨hBC1 x hx v hv, hI v hv x hx⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx hx0 v hv`. Establish `hNv` using `(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v hv (l v)).1`. Rewrite `hNv` using `[hI v hv v (hAs v hv)]`.

Simplify using `only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv`. Rewrite `hNv` using `[hdeg w0 hw0n]`. Rewrite using `[hdeg x hx0]`. Use `DDSmoothness.l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)` and prove the remaining obligations. Rewrite using `[hI v hv _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x hx _ hg)]`.

Simplify using `only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]`. Use `push_neg at hnz`. Establish `h0` using `hZ hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz`. Establish `h0D` using `hZD hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz`. Use `⟨fun _ => 0, DDSmoothness.bessel_zero, fun x hx v hv => ⟨hBC1 x hx v hv, ?_⟩, fun x _ _ v _ => by simp⟩` and prove the remaining obligations.

Use `show be z c π σ μW μN x v = _`. Establish `hz0 : be z c π σ μW μN x v = 0`. Break down `hv with hv | hv` into its components or cases. Conclude with `h0D v hv x hx`. Conclude with `h0 v hv x hx`.

Rewrite using `[hz0]`. Use extensionality with `ξ`. Simplify using the standard rewrite rules.
-/
theorem smooth_admissible_form_one_side : CompanionTheory.D.Upq.BesselFunctionalConstruction.C.AtFormAdmOneOfSteps := by
  intro hSch hBC hNI hBB hSh hKF hZ hZD hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨hBC1, -, -, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hw0n : w0 ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    intro h0; rw [h0, norm_zero] at hn1; exact zero_ne_one hn1
  have hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d := fun x hx => DDSmoothness.fdeg_eq hd hSd hx
  have hmu := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  have hAs : ∀ v : H, IsAdm σ w0 v → v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    intro v hv
    rcases hv with hv | hv
    · exact DDSmoothness.DD_smooth hIn.2.2.1 hlam hσ hw0 v hv
    · exact hIn.2.2.1 k r ε lam H σ hlam hσ v hv
  by_cases hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0
  · obtain ⟨l, hl, hx1, hid⟩ := hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    have hK := hKF hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS l hl hx1 hid
    have hI : ∀ v : H, IsAdm σ w0 v → ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
        be z c π σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x) := by
      intro v hv x hx
      rcases hv with hv | hv
      · exact hid x hx v hv
      · exact hK v hv x hx
    refine ⟨l, hl, fun x hx v hv => ⟨hBC1 x hx v hv, hI v hv x hx⟩, ?_⟩
    intro x hx hx0 v hv
    have hNv := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v hv (l v)).1
    rw [hI v hv v (hAs v hv)] at hNv
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv
    rw [hdeg w0 hw0n] at hNv
    rw [hdeg x hx0]
    refine DDSmoothness.l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)
    rw [hI v hv _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x hx _ hg)]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  · push_neg at hnz
    have h0 := hZ hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    have h0D := hZD hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    refine ⟨fun _ => 0, DDSmoothness.bessel_zero, fun x hx v hv => ⟨hBC1 x hx v hv, ?_⟩,
      fun x _ _ v _ => by simp⟩
    show be z c π σ μW μN x v = _
    have hz0 : be z c π σ μW μN x v = 0 := by
      rcases hv with hv | hv
      · exact h0D v hv x hx
      · exact h0 v hv x hx
    rw [hz0]
    ext ξ; simp

end GC

end UnipotentHaarMeasurability

end Formalism.FourierDecayAlt.P

end
