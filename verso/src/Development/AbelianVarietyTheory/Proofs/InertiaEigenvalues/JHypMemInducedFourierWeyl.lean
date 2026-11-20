import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnifConst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierEtaleKProdLocallyConstantCompactSuStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierEtaleKEqIntegralPartialFourierStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TestFunctionLocallyInvariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JHypUnipotentTorusEquivarianceStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.HypJ

/- English proof (translation)
Introduce `F E _ _ _ _ _ A ψ hψ μK hsd φ' hφ`. Establish `hH : μK.IsAddHaarMeasure` using `hsd.1`. Establish `hT` using `GlobalTheory.T.partialFourier_etaleKProd_locallyConstantCompactSupport F E A ψ hψ μK hH φ' hφ`. Use `⟨⟨?_, fun z s g => GlobalTheory.T.jHyp_unipotent_torus_equivariance F E A μK hH ψ φ' z s g⟩, ?_⟩` and prove the remaining obligations. Take `⟨U, hU, hk⟩` from `GlobalTheory.T.test_function_locally_invariant A.K _ hT`.

Use `⟨U, hU, fun g k hkU => ?_⟩` and prove the remaining obligations. Unfold `Et.jHyp`. Use `integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Use `hk k hkU (t * g 1 0) (t * g 1 1)` as an intermediate fact. Simplify using `only at this`.

Establish `e1 : ((g * k : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 0 = g 1 0 * k 0 0 + g 1 1 * k 1 0`. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e2 : ((g * k : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 1 = g 1 0 * k 0 1 + g 1 1 * k 1 1`. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using `only [e1, e2]`.

Apply the tactic sequence `rw [← this]; congr 2 <;> ring`. Introduce `h`. Establish `key : ∀ c u, A.tilde μK ψ (A.fourK μK ψ φ') c u = A.tilde μK ψ φ' (-u) c`. Introduce `c u`. Establish `hG` using `GlobalTheory.TestFn.slice_test _ hT c`.

Use `hsd.2 _ hG u` as an intermediate fact. Rewrite using `[← this]`. Unfold `Et.tilde fourB`. Use `integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[GlobalTheory.T.fourierEtaleK_eq_integral_partialFourier F E A ψ hψ μK hH φ' hφ b c]`. Unfold `fourB Et.tilde Et.kerK`. Rewrite using `[mul_comm u b]`. Unfold `Et.jHyp`. Use `integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[key]`. Use `congr 2`. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using `[wS]`.

Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using `[wS]`.
-/
theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) →
    ∀ φ', IsTest φ' → A.InI (A.jHyp μK ψ φ') ∧
      ∀ h, A.jHyp μK ψ (A.fourK μK ψ φ') h = A.jHyp μK ψ φ' (h * wS A.K) := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd φ' hφ
  have hH : μK.IsAddHaarMeasure := hsd.1
  have hT := GlobalTheory.T.partialFourier_etaleKProd_locallyConstantCompactSupport F E A ψ hψ μK hH φ' hφ
  refine ⟨⟨?_, fun z s g => GlobalTheory.T.jHyp_unipotent_torus_equivariance F E A μK hH ψ φ' z s g⟩, ?_⟩
  · obtain ⟨U, hU, hk⟩ := GlobalTheory.T.test_function_locally_invariant A.K _ hT
    refine ⟨U, hU, fun g k hkU => ?_⟩
    unfold Et.jHyp
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have := hk k hkU (t * g 1 0) (t * g 1 1)
    simp only at this
    have e1 : ((g * k : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 0 =
        g 1 0 * k 0 0 + g 1 1 * k 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have e2 : ((g * k : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 1 =
        g 1 0 * k 0 1 + g 1 1 * k 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [e1, e2]
    rw [← this]; congr 2 <;> ring
  · intro h
    have key : ∀ c u, A.tilde μK ψ (A.fourK μK ψ φ') c u = A.tilde μK ψ φ' (-u) c := by
      intro c u
      have hG := GlobalTheory.TestFn.slice_test _ hT c
      have := hsd.2 _ hG u
      rw [← this]
      unfold Et.tilde fourB
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      rw [GlobalTheory.T.fourierEtaleK_eq_integral_partialFourier F E A ψ hψ μK hH φ' hφ b c]
      unfold fourB Et.tilde Et.kerK
      rw [mul_comm u b]
    unfold Et.jHyp
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [key]
    congr 2
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [wS]
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [wS]

end GlobalTheory.JR.HypJ
