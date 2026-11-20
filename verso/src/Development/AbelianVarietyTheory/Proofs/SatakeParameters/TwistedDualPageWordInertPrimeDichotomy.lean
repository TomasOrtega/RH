import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBoxStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNonthickLetterNoThreeThickStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingSignAlternateOfSignNegStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickIffThickEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordConjHypATAllThickStatement

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Prove the second alternative.

Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem pageWord_inert_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ)
    (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → φ.1.2 = -1 →
    (pageWord L j ε τ φ).Box ∧ ((pageWord L j ε τ φ).HypNT ∨
      (φ = D.R.cc ∧ (pageWord L j ε τ φ).HypAT l ∧ ∀ i, (pageWord L j ε τ φ).thick i)) := by
  intro D L C j ε τ φ l hR hl hφ
  refine ⟨GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR, ?_⟩
  by_cases h : φ = D.R.cc ∧ Thick D.host τ
  · obtain ⟨rfl, hτ⟩ := h
    exact Or.inr ⟨rfl, GlobalTheory.T.twistedDualOrbitPageWord_conj_hypAT_allThick L C j ε τ l hR hl hτ⟩
  · left
    have hLw : 3 ≤ D.host.Lw := by
      have := L.weightLength_ge_depth
      omega
    obtain ⟨h3, i, hi⟩ := GlobalTheory.T.inertPrime_nonthick_letter_no_three_thick D.host τ φ hLw hφ h
    have hth := GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ φ hR
    refine ⟨(GlobalTheory.T.embeddingSign_alternate_of_sign_neg ε τ φ hφ).2, ⟨i, fun h' => hi ((hth i).1 h')⟩, ?_⟩
    intro k hk
    exact h3 k ⟨(hth _).1 hk.1, (hth _).1 hk.2.1, (hth _).1 hk.2.2⟩

end GlobalTheory.HTW
