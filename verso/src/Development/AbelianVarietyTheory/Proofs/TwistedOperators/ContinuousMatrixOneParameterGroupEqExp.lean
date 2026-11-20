import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsUnitIntegral
open scoped Matrix
open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq`. Consider the case `exact _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq`. Consider the case `(apply _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq ..)`.
-/
theorem banach_oneParamGroup_eq_exp {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1)
    (hm : ∀ s t, M (s + t) = M s * M t) :
    ∃ X : 𝔸, ∀ t, NormedSpace.exp (t • X) = M t := by
  first
  | exact @_root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq
  | exact _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq
  | (apply _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq ..)

/- English proof (translation)
Introduce `ι _ _ M hc h0 hm`. Use `letI : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra`. Take `⟨X, hX⟩` from `banach_oneParamGroup_eq_exp M hc h0 hm`. Conclude with `⟨X, fun t => (hX t).symm⟩`.
-/
theorem matrix_oneParamGroup_eq_exp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : ℝ → Matrix ι ι ℝ), Continuous M → M 0 = 1 → (∀ s t, M (s + t) = M s * M t) →
    ∃ X : Matrix ι ι ℝ, ∀ t, M t = NormedSpace.exp (t • X) := by
  intro ι _ _ M hc h0 hm
  letI : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  obtain ⟨X, hX⟩ := banach_oneParamGroup_eq_exp M hc h0 hm
  exact ⟨X, fun t => (hX t).symm⟩

end GlobalTheory
