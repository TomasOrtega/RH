import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LanglandsConstant

section Tate

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

/- English proof (translation)
Apply `localLFactor_ne_zero hμ` to reduce the goal to its premises. Establish `h0 : quasiCharExponent μ = 0` using `by simp [quasiCharExponent, h1]`. Rewrite using `[h0]`. Evaluate the numerical expressions.
-/
theorem localLFactor_half_ne_zero {μ : Kˣ →* ℂˣ} (hμ : Continuous μ)
    (h1 : ‖((μ (unifUnit K) : ℂˣ) : ℂ)‖ = 1) : localLFactor μ (1 / 2) ≠ 0 := by
  apply localLFactor_ne_zero hμ
  have h0 : quasiCharExponent μ = 0 := by simp [quasiCharExponent, h1]
  rw [h0]
  norm_num

/- English proof (translation)
Establish `hu : IsUnramifiedChar (1 : Kˣ →* ℂˣ)` using `isUnramifiedChar_iff.2 fun _ _ => rfl`. Establish `hL : localLFactor (1 : Kˣ →* ℂˣ) (1 / 2) ≠ 0` using `localLFactor_half_ne_zero continuous_const (by simp)`. Establish `hs : (1 : ℂ) - 1 / 2 = 1 / 2` using `by norm_num`. Unfold `Ad3.gam`. Rewrite using `[localEpsilon_of_isUnramified hu, inv_one, hs, mul_div_assoc, div_self hL]`.

Simplify using the standard rewrite rules.
-/
theorem gam_one_half (ψ : AddChar K Circle) : Ad3.gam ψ (1 : Kˣ →* ℂˣ) (1 / 2) = 1 := by
  have hu : IsUnramifiedChar (1 : Kˣ →* ℂˣ) := isUnramifiedChar_iff.2 fun _ _ => rfl
  have hL : localLFactor (1 : Kˣ →* ℂˣ) (1 / 2) ≠ 0 :=
    localLFactor_half_ne_zero continuous_const (by simp)
  have hs : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
  unfold Ad3.gam
  rw [localEpsilon_of_isUnramified hu, inv_one, hs, mul_div_assoc, div_self hL]
  simp

end Tate

end GlobalTheory.CompanionTheory.LanglandsConstant
