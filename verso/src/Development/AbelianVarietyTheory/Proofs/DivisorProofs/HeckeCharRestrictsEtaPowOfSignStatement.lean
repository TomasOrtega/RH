import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharRestrictsEtaPowOfSign
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPhaseAt

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeckeCharRestrictsEtaPowOfSign.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.heckeChar_restricts_eta_pow_of_sign : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (N : ℕ), IsHeckeChar D χ →
    (∀ x y : (AE D)ˣ, (y : AE D) = x * cA D x → χ y = 1) →
    ∀ θ : InfFam D, IsInfFam θ →
    (∀ (τ : D.what₂.Tau) (x : (AE D)ˣ), finPart D (x : AE D) = 1 → θ τ (infPart D (x : AE D)) = -1 →
      (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) → ((χ x : Circle) : ℂ) = (-1) ^ N) →
    ResEta D χ N := by
  first | exact @GlobalTheory.HeckeSignEta.resEta_of_sign | exact GlobalTheory.HeckeSignEta.resEta_of_sign | (intros; apply GlobalTheory.HeckeSignEta.resEta_of_sign <;> assumption)
