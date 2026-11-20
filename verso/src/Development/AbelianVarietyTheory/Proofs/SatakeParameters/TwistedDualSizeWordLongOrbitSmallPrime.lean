import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersLeastPowerDepthSpecStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordClusterDepthLongOrbitStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersClusterDepthAtPrimeEqLeastPowerDepthStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWordStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSmallBoundsLeParametersRoundedSizeBoundStatement

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

/- English proof (translation)
Introduce `D L hP C C₂ j ε n g ψ l hR hO hC hl hlA hord`. Take `⟨hn, hg⟩` from `hO`. Substitute `hn` using the available equality. Establish `hgl : g = letter (g 0) ψ`. Use function extensionality and compare the values at `a`.

Rewrite using `[hg a]`. Both sides reduce to the same expression. Generalize the expression as in `g 0 = τ at hgl`. Substitute `hgl` using the available equality. Establish `hjA : jA L l = depth L l` using `GlobalTheory.T.clusterDepthAtPrime_eq_leastPowerDepth L l hl hlA`.

Establish `hA` using `GlobalTheory.T.twistedDualPageWord_clusterDepth_long_orbit L hP C j ε τ ψ l hR hl hlA hord`. Take `⟨_, _, hjn, _, hcl⟩` from `hA`. Establish `hD` using `GlobalTheory.T.leastPowerDepth_spec L hP l hl`. Establish `hth : ThickN (recWord L j ε (letter τ ψ)).b (recWord L j ε (letter τ ψ)).η (recWord L j ε (letter τ ψ)).sz = (pageWord L j ε τ ψ).thick`. Use function extensionality and compare the values at `a`.

Conclude with `propext (GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε τ ψ hR a).2.2.2`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hjA]`. Conclude with `hjn`. Break down `le_or_gt 0 C₂ with h0 | h0` into its components or cases.

Rewrite using `[hjA]`. Conclude with `GlobalTheory.T.mul_smallBounds_le_roundedSizeBound L C₂ C (depth L l) hR h0 hC hD.2.1`. Establish `h1 : (0 : ℝ) ≤ ((jA L l : ℝ) + 1) * ((((recWord L j ε (letter τ ψ)).w + (recWord L j ε (letter τ ψ)).S + (recWord L j ε (letter τ ψ)).η : ℕ) : ℝ) + 1)`. Check the signs of the components of the expression. Establish `h2 : C₂ * ((jA L l : ℝ) + 1) * ((((recWord L j ε (letter τ ψ)).w + (recWord L j ε (letter τ ψ)).S + (recWord L j ε (letter τ ψ)).η : ℕ) : ℝ) + 1) ≤ 0`.

Rewrite using `[mul_assoc]`. Conclude with `mul_nonpos_of_nonpos_of_nonneg h0.le h1`. Conclude with `h2.trans (Nat.cast_nonneg _)`. Rewrite using `[hth, hjA]`. Conclude with `hcl`.
-/
theorem wordsB_recWord_of_long_orbit : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (C C₂ : ℝ) (j : Fin D.R.m)
    (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 2 * C₂ ≤ C →
    11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → 4 * D.host.Lw < orderOf ψ.2 → WordsB L l C₂ (recWord L j ε g) := by
  intro D L hP C C₂ j ε n g ψ l hR hO hC hl hlA hord
  obtain ⟨hn, hg⟩ := hO
  subst hn
  have hgl : g = letter (g 0) ψ := by
    funext a
    rw [hg a]
    rfl
  generalize g 0 = τ at hgl
  subst hgl
  have hjA : jA L l = depth L l := GlobalTheory.T.clusterDepthAtPrime_eq_leastPowerDepth L l hl hlA
  have hA := GlobalTheory.T.twistedDualPageWord_clusterDepth_long_orbit L hP C j ε τ ψ l hR hl hlA hord
  obtain ⟨_, _, hjn, _, hcl⟩ := hA
  have hD := GlobalTheory.T.leastPowerDepth_spec L hP l hl
  have hth : ThickN (recWord L j ε (letter τ ψ)).b
      (recWord L j ε (letter τ ψ)).η (recWord L j ε (letter τ ψ)).sz =
      (pageWord L j ε τ ψ).thick := by
    funext a
    exact propext (GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε τ ψ hR a).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hjA]; exact hjn
  · rcases le_or_gt 0 C₂ with h0 | h0
    · rw [hjA]
      exact GlobalTheory.T.mul_smallBounds_le_roundedSizeBound L C₂ C (depth L l) hR h0 hC hD.2.1
    · have h1 : (0 : ℝ) ≤ ((jA L l : ℝ) + 1) * ((((recWord L j ε (letter τ ψ)).w +
          (recWord L j ε (letter τ ψ)).S + (recWord L j ε (letter τ ψ)).η : ℕ) : ℝ) + 1) := by
        positivity
      have h2 : C₂ * ((jA L l : ℝ) + 1) * ((((recWord L j ε (letter τ ψ)).w +
          (recWord L j ε (letter τ ψ)).S + (recWord L j ε (letter τ ψ)).η : ℕ) : ℝ) + 1) ≤ 0 := by
        rw [mul_assoc]; exact mul_nonpos_of_nonpos_of_nonneg h0.le h1
      exact h2.trans (Nat.cast_nonneg _)
  · rw [hth, hjA]; exact hcl

end GlobalTheory.HTW.Rec
