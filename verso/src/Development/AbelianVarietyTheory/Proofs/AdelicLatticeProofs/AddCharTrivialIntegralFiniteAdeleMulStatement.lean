import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FAddCharTrivialIntegralFiniteAdeleMul.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.addChar_trivial_integralFiniteAdele_mul : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : F, (∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1) → ∀ α ∈ intAf F, ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := by
  first | exact @GlobalTheory.IntDense.addChar_eq_one_of_integral | exact GlobalTheory.IntDense.addChar_eq_one_of_integral | (intros; apply GlobalTheory.IntDense.addChar_eq_one_of_integral <;> assumption)
