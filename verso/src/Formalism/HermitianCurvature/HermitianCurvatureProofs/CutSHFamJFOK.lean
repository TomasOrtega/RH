import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm

open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P T j G hG t ht`. Take `⟨hsm, hcpt⟩` from `hG`. Take `⟨C, hC, ε, hε, hCε⟩` from `hcpt {t} isCompact_singleton (by`. Introduce `s hs`. Rewrite `hs` using `[Set.mem_singleton_iff]`.

Rewrite using `[hs]`. Conclude with `ht)`. Establish `hzero : ∀ γ, γ ∉ C → G t γ = 0`. Introduce `γ hγ`. Assume the negation of the conclusion as `h`.

Conclude with `hγ (hCε t rfl γ h).1`. Establish `hCk : B.CkOn ⊤ (B.GV P.k (P.r - (j + 1))) (G t)`. Introduce `γ₀ hγ₀`. Take `⟨U, f, hU, hmem, hf, hfe⟩` from `hsm t ht γ₀ hγ₀`. Use `⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), ?_, hmem, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `hU.preimage (continuous_const.prodMk continuous_id)`. Establish `hd : ContDiff ℝ ∞ (fun γ : B.Mat P.k (P.r - (j + 1)) => (t, γ))` using `contDiff_const.prodMk contDiff_id`. Conclude with `hf.comp hd.contDiffOn (fun γ hγ => hγ)`. Introduce `γ hγ hγV`. Conclude with `hfe (t, γ) hγ hγV`.

Use `⟨⟨?_, ε, hε, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `JFxG.cptInCC_G hCk hC (fun g _ hg => hzero g hg)`. Introduce `g hg hne`. Conclude with `(hCε t rfl g hne).2 hg`. Use `HasCompactSupport.intro hC ?_` and prove the remaining obligations.

Conclude with `hzero`.
-/
theorem family_orbital_valid : FamJFOK := by
  intro Wp Wq _ _ _ _ _ _ P T j G hG t ht
  obtain ⟨hsm, hcpt⟩ := hG
  obtain ⟨C, hC, ε, hε, hCε⟩ := hcpt {t} isCompact_singleton (by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact ht)
  have hzero : ∀ γ, γ ∉ C → G t γ = 0 := by
    intro γ hγ
    by_contra h
    exact hγ (hCε t rfl γ h).1
  have hCk : B.CkOn ⊤ (B.GV P.k (P.r - (j + 1))) (G t) := by
    intro γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hsm t ht γ₀ hγ₀
    refine ⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), ?_, hmem, ?_, ?_⟩
    · exact hU.preimage (continuous_const.prodMk continuous_id)
    · have hd : ContDiff ℝ ∞ (fun γ : B.Mat P.k (P.r - (j + 1)) => (t, γ)) :=
        contDiff_const.prodMk contDiff_id
      exact hf.comp hd.contDiffOn (fun γ hγ => hγ)
    · intro γ hγ hγV
      exact hfe (t, γ) hγ hγV
  refine ⟨⟨?_, ε, hε, ?_⟩, ?_⟩
  · exact JFxG.cptInCC_G hCk hC (fun g _ hg => hzero g hg)
  · intro g hg hne
    exact (hCε t rfl g hne).2 hg
  · refine HasCompactSupport.intro hC ?_
    exact hzero

end Formalism.FourierDecayAlt.P.CutSH
