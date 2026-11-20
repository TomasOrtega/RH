import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSummableMajorantRationalVectorsLocallyUnif

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

/- English proof (translation)
Introduce `F _ _ N _ ψ hF hψ Φ hΦ`. Take `⟨hc, ⟨K, hK, hKz⟩, hdec⟩` from `hΦ`. Take `⟨hψc, hψn, -, -⟩` from `hψ`. Use `haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`. Take `⟨k, hk⟩` from `GlobalTheory.SumMaj.summable_majorant F N hF K hK`.

Take `⟨C, hC⟩` from `hdec k`. Establish `hC0 : 0 ≤ C` using `le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k)) (hC 0)`. Establish `hterm : ∀ ξ : Fin N → F, Continuous fun w : VA F N => ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1)`. Introduce `ξ`. Use `Continuous.mul (hψc.comp ?_) (hc.comp (continuous_const.add continuous_fst))` and prove the remaining obligations.

Use `Continuous.add ?_ (continuous_const.mul ?_)` and prove the remaining obligations. Conclude with `continuous_finset_sum _ fun i _ => continuous_const.mul ((continuous_apply i).comp continuous_snd)`. Conclude with `continuous_finset_sum _ fun i _ => ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)`. Establish `heq : thV ψ Φ = fun w : VA F N => ∑' ξ : Fin N → F, ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1)`. Use function extensionality and compare the values at `w`.

Simplify using `only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]`. Both sides reduce to the same expression. Rewrite using `[heq]`. Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Take `⟨ω, hωc, hωn⟩` from `exists_compact_mem_nhds x`.

Take `⟨c, hcs, hc0, hcb⟩` from `hk (Prod.fst '' ω) (hωc.image continuous_fst)`. Establish `hon : ContinuousOn (fun w : VA F N => ∑' ξ : Fin N → F, ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1)) ω`. Use `continuousOn_tsum (fun ξ => (hterm ξ).continuousOn) (hcs.mul_left C) fun ξ w hw => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, hψn, one_mul]`. Distinguish the cases in `hmem : fin (rat ξ + w.1) ∈ K`.

Establish `h1` using `hcb ξ w.1 ⟨w, hw, rfl⟩ hmem`. Establish `h2` using `hC (rat ξ + w.1)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hKz _ hmem, norm_zero]`. Conclude with `mul_nonneg hC0 (hc0 ξ)`.

Conclude with `hon.continuousAt hωn`.
-/
theorem continuous_thV : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ →
      Continuous (thV ψ Φ) := by
  intro F _ _ N _ ψ hF hψ Φ hΦ
  obtain ⟨hc, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨hψc, hψn, -, -⟩ := hψ
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  obtain ⟨k, hk⟩ := GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k))
      (hC 0)
  have hterm : ∀ ξ : Fin N → F, Continuous fun w : VA F N =>
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1) := by
    intro ξ
    refine Continuous.mul (hψc.comp ?_) (hc.comp (continuous_const.add continuous_fst))
    refine Continuous.add ?_ (continuous_const.mul ?_)
    · exact continuous_finset_sum _ fun i _ => continuous_const.mul ((continuous_apply i).comp continuous_snd)
    · exact continuous_finset_sum _ fun i _ =>
        ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)
  have heq : thV ψ Φ = fun w : VA F N => ∑' ξ : Fin N → F,
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1) := by
    funext w
    simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
    rfl
  rw [heq]
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨ω, hωc, hωn⟩ := exists_compact_mem_nhds x
  obtain ⟨c, hcs, hc0, hcb⟩ := hk (Prod.fst '' ω) (hωc.image continuous_fst)
  have hon : ContinuousOn (fun w : VA F N => ∑' ξ : Fin N → F,
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1)) ω := by
    refine continuousOn_tsum (fun ξ => (hterm ξ).continuousOn) (hcs.mul_left C) fun ξ w hw => ?_
    rw [norm_mul, hψn, one_mul]
    by_cases hmem : fin (rat ξ + w.1) ∈ K
    · have h1 := hcb ξ w.1 ⟨w, hw, rfl⟩ hmem
      have h2 := hC (rat ξ + w.1)
      calc ‖Φ (rat ξ + w.1)‖ = ‖Φ (rat ξ + w.1)‖ * 1 := (mul_one _).symm
        _ ≤ ‖Φ (rat ξ + w.1)‖ * (c ξ * (1 + sz (rat ξ + w.1)) ^ k) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = c ξ * (‖Φ (rat ξ + w.1)‖ * (1 + sz (rat ξ + w.1)) ^ k) := by ring
        _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
        _ = C * c ξ := mul_comm _ _
    · rw [hKz _ hmem, norm_zero]
      exact mul_nonneg hC0 (hc0 ξ)
  exact hon.continuousAt hωn

end GlobalTheory.ThetaTransform
