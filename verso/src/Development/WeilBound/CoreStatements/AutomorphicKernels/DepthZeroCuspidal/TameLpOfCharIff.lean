import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DZC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, a, ha, H⟩ σ hσ`. Unfold `WD.lpOfChar at ha`. Take `⟨e, he, -⟩` from `WD.mk_eq_mk.mp ha`. Establish `h1 : ∀ u : Fin 1 → ℂ, (WDRep.ofChars h (ι` using `Fin 1) (fun _ => ξ) fun _ => hξ).ρ σ u = u := by`.

Introduce `u`. Take `⟨v, rfl⟩` from `e.surjective u`. Rewrite using `[← he, H σ hσ]`. Both sides reduce to the same expression. Establish `h2` using `congrFun (h1 fun _ => 1) 0`.

Rewrite `h2` using `[WDRep.ofChars_ρ, diagEnd_apply, mul_one]`. Conclude with `Units.ext h2`. Introduce `H`. Use `⟨1, WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) (fun _ => hξ), rfl, fun σ hσ => ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun v => funext fun i => ?_` and prove the remaining obligations.

Rewrite using `[WDRep.ofChars_ρ, diagEnd_apply, H σ hσ]`. Simplify using the standard rewrite rules.
-/
theorem tame_lpOfChar_iff (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) :
    IsTameWD (WD.lpOfChar h ξ hξ) ↔ ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → ξ σ = 1 := by
  constructor
  · rintro ⟨n, a, ha, H⟩ σ hσ
    unfold WD.lpOfChar at ha
    obtain ⟨e, he, -⟩ := WD.mk_eq_mk.mp ha
    have h1 : ∀ u : Fin 1 → ℂ,
        (WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) fun _ => hξ).ρ σ u = u := by
      intro u
      obtain ⟨v, rfl⟩ := e.surjective u
      rw [← he, H σ hσ]
      rfl
    have h2 := congrFun (h1 fun _ => 1) 0
    rw [WDRep.ofChars_ρ, diagEnd_apply, mul_one] at h2
    exact Units.ext h2
  · intro H
    refine ⟨1, WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) (fun _ => hξ), rfl, fun σ hσ => ?_⟩
    refine LinearMap.ext fun v => funext fun i => ?_
    rw [WDRep.ofChars_ρ, diagEnd_apply, H σ hσ]
    simp

end PositivityTheory.LocalParametersCuspidal.DZC

end
