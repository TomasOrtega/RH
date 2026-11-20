import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSchwartzFiniteValues
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeisenbergSchwartzFiniteValues.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.heisenberg_schwartz_finite_values : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ g ∈ SB (κ → Af F), ∀ Ω : Set ((κ → Af F) × (κ → Af F) × Af F), IsCompact Ω →
      ((fun w : (κ → Af F) × (κ → Af F) × Af F => GlobalTheory.HeisSchA.finS ψ g w.1 w.2.1 w.2.2) '' Ω).Finite := by
  first | exact @GlobalTheory.HeisFinFin.finS_image_finite | exact GlobalTheory.HeisFinFin.finS_image_finite | (intros; apply GlobalTheory.HeisFinFin.finS_image_finite <;> assumption)
