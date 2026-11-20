import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneDim
import GroundTheory.LocalFields.LocalZetaEpsilon
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 vecAt awayIntegral awayBox)
open GroundTheory.Automorphic.GJMatrix (cosetInd localTensor localFourierPi localMeasurePi)
open Ad3 Ad3.R
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap nonZeroDivisors Classical

namespace GlobalTheory.CompanionTheory.RSFT

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ hψ N a y`. Take `⟨hc, h1, h0⟩` from `hψ`. Establish `hμ : (GroundTheory.LocalField.selfDualMeasure ψ).real (valBall F N : Set F) = (residueCard F : ℝ) ^ (-N)`. Rewrite using `[measureReal_valBall, selfDualMeasure_real_valBall_zero, h0]`. Simplify using the standard rewrite rules.

Establish `key` using `localFourier_indicator_valBall (GroundTheory.LocalField.selfDualMeasure ψ) hc h1 N y`. Rewrite `key` using `[h0, zero_sub, hμ]`. Establish `e : (fun x => cosetInd (valBall F N) a (a + x) * (ψ ((a + x) * y) : ℂ)) = fun x => (ψ (a * y) : ℂ) * ((valBall F N : Set F).indicator (fun _ => (1 : ℂ)) x * (ψ (x * y) : ℂ))`. Use function extensionality and compare the values at `x`. Rewrite using `[GroundTheory.Automorphic.GJMatrix.cosetInd_apply, add_sub_cancel_left, Set.indicator_apply, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]`.

Simplify using `only [SetLike.mem_coe]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : localFourier (GroundTheory.LocalField.selfDualMeasure ψ) ψ (cosetInd (valBall F N) a) y = (ψ (a * y) : ℂ) * localFourier (GroundTheory.LocalField.selfDualMeasure ψ) ψ ((valBall F N : Set F).indicator fun _ => (1 : ℂ)) y`. Unfold `localFourier`. Rewrite using `[← integral_add_left_eq_self _ a, e, integral_const_mul]`.

Rewrite using `[e2, key, mul_assoc]`.
-/
theorem localFourier_cosetInd_valBall : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (N : ℤ) (a y : F), localFourier (selfDualMeasure ψ) ψ (cosetInd (valBall F N) a) y = (ψ (a * y) : ℂ) * (((residueCard F : ℝ) ^ (-N) : ℝ) : ℂ) * (valBall F (-N) : Set F).indicator (fun _ => (1 : ℂ)) y := by
  intro F _ _ _ _ _ _ ψ hψ N a y
  obtain ⟨hc, h1, h0⟩ := hψ
  have hμ : (GroundTheory.LocalField.selfDualMeasure ψ).real (valBall F N : Set F) =
      (residueCard F : ℝ) ^ (-N) := by
    rw [measureReal_valBall, selfDualMeasure_real_valBall_zero, h0]
    simp
  have key := localFourier_indicator_valBall (GroundTheory.LocalField.selfDualMeasure ψ) hc h1 N y
  rw [h0, zero_sub, hμ] at key
  have e : (fun x => cosetInd (valBall F N) a (a + x) * (ψ ((a + x) * y) : ℂ)) =
      fun x => (ψ (a * y) : ℂ) *
        ((valBall F N : Set F).indicator (fun _ => (1 : ℂ)) x * (ψ (x * y) : ℂ)) := by
    funext x
    rw [GroundTheory.Automorphic.GJMatrix.cosetInd_apply, add_sub_cancel_left, Set.indicator_apply, add_mul,
      AddChar.map_add_eq_mul, Circle.coe_mul]
    simp only [SetLike.mem_coe]
    ring
  have e2 : localFourier (GroundTheory.LocalField.selfDualMeasure ψ) ψ (cosetInd (valBall F N) a) y =
      (ψ (a * y) : ℂ) * localFourier (GroundTheory.LocalField.selfDualMeasure ψ) ψ
        ((valBall F N : Set F).indicator fun _ => (1 : ℂ)) y := by
    unfold localFourier
    rw [← integral_add_left_eq_self _ a, e, integral_const_mul]
  rw [e2, key, mul_assoc]

end GlobalTheory.CompanionTheory.RSFT
