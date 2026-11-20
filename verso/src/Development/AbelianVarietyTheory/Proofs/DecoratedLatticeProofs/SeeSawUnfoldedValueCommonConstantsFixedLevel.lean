import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepValueFixedLevelPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsValueFixedLevelPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.GValAll

/- English proof (translation)
Introduce `D c v n G hc hv hG`. Use `⟨fun j => if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose else if h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧ (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.h …` and prove the remaining obligations. Introduce `j dsimp only`. Distinguish the cases in `h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m`. Rewrite using `[dif_pos h1]`.

Conclude with `(GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose_spec.1`. Rewrite using `[dif_neg h1]`. Distinguish the cases in `h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧ (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram`. Rewrite using `[dif_pos h2]`. Conclude with `(GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose_spec.1`.

Rewrite using `[dif_neg h2]`. Conclude with `one_ne_zero`. Introduce `t _ hw`. Use `⟨fun j σ h Ψ₁ Ψ₂ h₁ h₂ => ?_, fun j h Ψ₁ Ψ₂ h₁ h₂ => ?_⟩` and prove the remaining obligations. Establish `h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m` using `⟨σ, h⟩`.

Establish `hσ : h1.choose = σ` using `by have := h1.choose_spec; omega`. Use `show _ = (if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then _ else _) • _`. Rewrite using `[dif_pos h1]`. Establish `key` using `(GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose_spec.2`. Use `revert key`.

Generalize the expression as in `(GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose = C`. Introduce `key`. Substitute `hσ` using the available equality. Conclude with `key _ _ Ψ₁ Ψ₂ h₁ h₂`. Establish `h1 : ¬ ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m` using `by rintro ⟨σ, hσ⟩; omega`.

Take `⟨hr, hτ⟩` from `hw.tau j h`. Establish `h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧ (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram` using `⟨h, hr, hτ⟩`. Use `show _ = (if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then _ else _) • _`. Rewrite using `[dif_neg h1, dif_pos h2]`. Conclude with `(GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose_spec.2 _ Ψ₁ Ψ₂ h₁ h₂`.
-/
theorem gValue_common : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∃ a : ℕ → ℂ, (∀ j, a j ≠ 0) ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → GValue (t := t) (v.withCG a) := by
  intro D c v n G hc hv hG
  classical
  refine ⟨fun j => if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose
    else if h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
      (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram then
      (GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose else 1, ?_, ?_⟩
  · intro j
    dsimp only
    by_cases h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m
    · rw [dif_pos h1]; exact (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose_spec.1
    · rw [dif_neg h1]
      by_cases h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
          (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram
      · rw [dif_pos h2]; exact (GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose_spec.1
      · rw [dif_neg h2]; exact one_ne_zero
  · intro t _ hw
    refine ⟨fun j σ h Ψ₁ Ψ₂ h₁ h₂ => ?_, fun j h Ψ₁ Ψ₂ h₁ h₂ => ?_⟩
    · have h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m := ⟨σ, h⟩
      have hσ : h1.choose = σ := by have := h1.choose_spec; omega
      show _ = (if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then _ else _) • _
      rw [dif_pos h1]
      have key := (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose_spec.2
      revert key
      generalize (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose = C
      intro key
      subst hσ
      exact key _ _ Ψ₁ Ψ₂ h₁ h₂
    · have h1 : ¬ ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m := by rintro ⟨σ, hσ⟩; omega
      obtain ⟨hr, hτ⟩ := hw.tau j h
      have h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
          (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram := ⟨h, hr, hτ⟩
      show _ = (if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then _ else _) • _
      rw [dif_neg h1, dif_pos h2]
      exact (GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose_spec.2 _ Ψ₁ Ψ₂ h₁ h₂

end GlobalTheory.SeeSaw.GValAll
