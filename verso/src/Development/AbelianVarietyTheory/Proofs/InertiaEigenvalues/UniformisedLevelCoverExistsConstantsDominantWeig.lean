import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitConstantCoverPullbackReadingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverComponentOverBaseComponentRationalIsometryStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverRead.Cover

/- English proof (translation)
Introduce `D T hT j hj σ hσ C hC n`. Take `⟨u, hu1, hu⟩` from `GlobalTheory.T.exists_unitConstant_coverPullbackReading D T hT j hj σ hσ C hC n`. Apply the tactic sequence `choose k γ hk using fun k₂ => GlobalTheory.T.coverComponent_over_baseComponent_rationalIsometry D T hT j hj σ hσ C hC k₂`. Establish `hu0 : ∀ k₂, u k₂ ≠ 0` using `fun k₂ h => by simpa [h] using hu1 k₂`. Use `⟨fun k₂ => T.cE j σ (k k₂) / u k₂, fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Introduce `k₂ show ‖T.cE j σ (k k₂) / u k₂‖ = 1`. Rewrite using `[norm_div, hu1, hT.cUnit j hj σ hσ, div_one]`. Introduce `f hf f₂ hf₂ hp`. Use function extensionality and compare the values at `g`. Establish `hp' : C.IsPull f f₂` using `hp`.

Establish `h3 : (T.dict j σ g).1 = k (C.dict₂ g).1` using `(hk (C.dict₂ g).1).2.2.1 g rfl`. Use `show (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * (T.cE j σ (k (C.dict₂ g).1) / u (C.dict₂ g).1 * T.mu j σ g * rdU C.U₂ f₂ (C.dict₂ g).1 (C.dict₂ g).2) = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * (T.cE j σ (T.dict j σ g).1 * T.mu j σ g * rdU (T.U j σ) f (T.dict j σ g).1 (T.dict j σ g).2)`. Rewrite using `[hu a ha f hf f₂ hf₂ hp' g, ← h3]`. Clear denominators, using `[hu0 (C.dict₂ g).1]` for the nonvanishing conditions.
-/
theorem exists_pinned_dom : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ,
    GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∃ cc₂ : C.U₂.Comp → ℂ,
      ∀ a : (D.host.E →+* ℂ) × ℕ → ℕ, Dom a n → ({ C with cc₂ := cc₂ } : Cover T j σ).IsPinned a n := by
  intro D T hT j hj σ hσ C hC n
  obtain ⟨u, hu1, hu⟩ := GlobalTheory.T.exists_unitConstant_coverPullbackReading D T hT j hj σ hσ C hC n
  choose k γ hk using fun k₂ => GlobalTheory.T.coverComponent_over_baseComponent_rationalIsometry D T hT j hj σ hσ C hC k₂
  have hu0 : ∀ k₂, u k₂ ≠ 0 := fun k₂ h => by simpa [h] using hu1 k₂
  refine ⟨fun k₂ => T.cE j σ (k k₂) / u k₂, fun a ha => ⟨?_, ?_⟩⟩
  · intro k₂
    show ‖T.cE j σ (k k₂) / u k₂‖ = 1
    rw [norm_div, hu1, hT.cUnit j hj σ hσ, div_one]
  · intro f hf f₂ hf₂ hp
    funext g
    have hp' : C.IsPull f f₂ := hp
    have h3 : (T.dict j σ g).1 = k (C.dict₂ g).1 := (hk (C.dict₂ g).1).2.2.1 g rfl
    show (lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
        (T.cE j σ (k (C.dict₂ g).1) / u (C.dict₂ g).1 * T.mu j σ g * rdU C.U₂ f₂ (C.dict₂ g).1 (C.dict₂ g).2) =
      (lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
        (T.cE j σ (T.dict j σ g).1 * T.mu j σ g * rdU (T.U j σ) f (T.dict j σ g).1 (T.dict j σ g).2)
    rw [hu a ha f hf f₂ hf₂ hp' g, ← h3]
    field_simp [hu0 (C.dict₂ g).1]

end GlobalTheory.CoverRead.Cover
