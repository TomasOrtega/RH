import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERD

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D μ hμ`. Take `⟨C1, hC1, hpair⟩` from `Formalism.FourierDecayAlt.P.JCx2.rb_pairAt D μ hμ`. Use `⟨(C1 : ℂ), by exact_mod_cast hC1.ne', fun F H Φ Ψ hF hH hΦ hΨ c => ?_⟩` and prove the remaining obligations. Establish `h` using `Formalism.FourierDecayAlt.P.JCx2.rb_main D μ C1 hpair (n := 0) (fun _ => F) (fun _ => H) (fun _ => Φ) (fun _ => Ψ) (fun _ => hF) (fun _ => hH) (fun _ => hΦ) (fun _ => hΨ)`. Establish `hsum : ∑ _a : Wd.Ix (Fin 0), B.beta D F H = B.beta D F H` using `by simp`.

Rewrite `h` using `[hsum]`. Rewrite using `[← h]`. Unfold `LocFacts₂ P5.form`. Use `integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)` and prove the remaining obligations. Establish `hg : glue (0 : Fin (r + 1)) c c' = glue 0 0 c'`.

Use function extensionality and compare the values at `l`. Simplify using `only [glue]`. Establish `h0 : ((0 : Fin (r + 1)) : ℕ) ≤ (l : ℕ)` using `Nat.zero_le _`. Rewrite using `[dif_pos h0, dif_pos h0]`. Simplify using `only [hg, Finset.univ_unique, Finset.sum_singleton]`.
-/
theorem radial_beta_identity : RDBeta := by
  intro k r Wp Wq _ _ _ _ _ _ D μ hμ
  obtain ⟨C1, hC1, hpair⟩ := Formalism.FourierDecayAlt.P.JCx2.rb_pairAt D μ hμ
  refine ⟨(C1 : ℂ), by exact_mod_cast hC1.ne', fun F H Φ Ψ hF hH hΦ hΨ c => ?_⟩
  have h := Formalism.FourierDecayAlt.P.JCx2.rb_main D μ C1 hpair (n := 0) (fun _ => F) (fun _ => H) (fun _ => Φ) (fun _ => Ψ)
    (fun _ => hF) (fun _ => hH) (fun _ => hΦ) (fun _ => hΨ)
  have hsum : ∑ _a : Wd.Ix (Fin 0), B.beta D F H = B.beta D F H := by simp
  rw [hsum] at h
  rw [← h]
  unfold LocFacts₂ P5.form
  refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
  have hg : glue (0 : Fin (r + 1)) c c' = glue 0 0 c' := by
    funext l
    simp only [glue]
    have h0 : ((0 : Fin (r + 1)) : ℕ) ≤ (l : ℕ) := Nat.zero_le _
    rw [dif_pos h0, dif_pos h0]
  simp only [hg, Finset.univ_unique, Finset.sum_singleton]

end Formalism.FourierDecayAlt.P.CutSE
