import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanSkewHermitianNormalForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCartanSkewHermitianNormalForm.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.cartan_skew_hermitian_normal_form : ∀ (n : ℕ) (M θ : Matrix (Fin n) (Fin n) ℂ) (z : ℂ), star z = -z → z ≠ 0 → (∀ i j, star (M j i) = -M i j) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • M) θ → ∃ (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P ∧ Pᴴ * (z • M.map star) * P = Formalism.REAL.Jm ε ∧ ∃ c : ℂ, c ≠ 0 ∧ P * Formalism.REAL.Jm ε = c • (θ * P) := by
  first | exact @GlobalTheory.CartanFrame.frame | exact GlobalTheory.CartanFrame.frame | (intros; apply GlobalTheory.CartanFrame.frame <;> assumption)
