import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointsBaseLatticeStabilizerFixedFrameUnipote
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeAsm.RatIsomReal

/- English proof (translation)
Introduce `D X C Γ hΓ`. Use extensionality with `m`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn, hm⟩`. Take `⟨x, hx⟩` from `Formalism.L2.SG.Pf.ratPt_holds D X n (hΓ n hn)`.

Conclude with `⟨x.1, ⟨x, n, hx, rfl, hn⟩, GLinkPf.eq_of_act C (GLinkPf.trI_act C hx) (fun τ y => hm τ y)⟩`. Introduce and unpack `⟨_, ⟨x, n, hx, rfl, hn⟩, rfl⟩`. Conclude with `⟨n, hn, fun τ y => GLinkPf.trI_act C hx τ y⟩`.
-/
theorem realPts_eq_image : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (Γ : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)),
    (∀ n ∈ Γ, n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) →
      GlobalTheory.DegVol.realPts (phiV C) Γ = trI C '' {y | ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
        RatLink X x n ∧ y = x.1 ∧ n ∈ Γ} := by
  intro D X C Γ hΓ
  ext m
  constructor
  · rintro ⟨n, hn, hm⟩
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n (hΓ n hn)
    exact ⟨x.1, ⟨x, n, hx, rfl, hn⟩, GLinkPf.eq_of_act C (GLinkPf.trI_act C hx) (fun τ y => hm τ y)⟩
  · rintro ⟨_, ⟨x, n, hx, rfl, hn⟩, rfl⟩
    exact ⟨n, hn, fun τ y => GLinkPf.trI_act C hx τ y⟩

end GlobalTheory.TypeAsm.RatIsomReal
