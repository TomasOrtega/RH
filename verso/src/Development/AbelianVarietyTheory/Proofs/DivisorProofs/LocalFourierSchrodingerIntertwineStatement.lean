import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchrodingerIntertwine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WeylFour.schr_fourV_loc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalFourierSchrodingerIntertwine.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.local_fourier_schrodinger_intertwine : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl F) (κ : Type) [Fintype κ]
    (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    fourV ψ v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (w.2, -w.1) (fourV ψ v φ) := by
  first | exact @GlobalTheory.WeylFour.schr_fourV_loc | exact GlobalTheory.WeylFour.schr_fourV_loc | (intros; apply GlobalTheory.WeylFour.schr_fourV_loc <;> assumption)
