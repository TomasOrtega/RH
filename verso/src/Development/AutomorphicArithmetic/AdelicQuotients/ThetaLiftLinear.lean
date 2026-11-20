import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
import Development.WeilBound.ThetaLifts.LatticeBasics.PolFin
import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsL

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions

open UpperTheory.TP

namespace UpperTheory.TP.LiftLin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

/- English proof (translation)
Establish `hc : Cpt σ X.J` using `T.cpt F E σ B n X n 0 hP.base (Or.inl hP.herm) (by simp)`. Take `⟨h1, h2, -⟩` from `(T.basic F E σ B n d X W M χX χW om n 0 d 0 hP).1 Φ hΦ`. Establish `hcont : Continuous fun g => theta om Φ g h * star (φ g)` using `(h1.comp (continuous_id.prodMk continuous_const)).mul (continuous_star.comp hφ.1)`. Take `⟨C, hC⟩` from `hc.bdd hcont fun γ hγ g => by`. Establish `e` using `h2 γ hγ 1 (one_mem _) g h`.

Rewrite `e` using `[one_mul]`. Simplify using `only [e, hφ.2 γ hγ g]`. Conclude with `Measure.integrableOn_of_bounded (M := C) (hc.fin M.μ M.dom hP.good.haar hP.good.dom).ne hcont.aestronglyMeasurable (Eventually.of_forall hC)`.
-/
private theorem integrand_int (T : Tools) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    (hP : IsPair B M χX χW om n 0 d 0) {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) {φ : UA σ X.J → ℂ} (hφ : IsFn φ)
    (h : UA σ W.J) : IntegrableOn (fun g => theta om Φ g h * star (φ g)) M.dom M.μ := by
  have hc : Cpt σ X.J := T.cpt F E σ B n X n 0 hP.base (Or.inl hP.herm) (by simp)
  obtain ⟨h1, h2, -⟩ := (T.basic F E σ B n d X W M χX χW om n 0 d 0 hP).1 Φ hΦ
  have hcont : Continuous fun g => theta om Φ g h * star (φ g) :=
    (h1.comp (continuous_id.prodMk continuous_const)).mul (continuous_star.comp hφ.1)
  obtain ⟨C, hC⟩ := hc.bdd hcont fun γ hγ g => by
    have e := h2 γ hγ 1 (one_mem _) g h
    rw [one_mul] at e
    simp only [e, hφ.2 γ hγ g]
  exact Measure.integrableOn_of_bounded (M := C) (hc.fin M.μ M.dom hP.good.haar hP.good.dom).ne
    hcont.aestronglyMeasurable (Eventually.of_forall hC)

end UpperTheory.TP.LiftLin

open UpperTheory.TP.LiftLin in

/- English proof (translation)
Introduce `T F E _ _ _ _ _ σ B n d X W M χX χW om hP`. Establish `hpres : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F (Fin n × Fin d)` using `hP.weil.isUSplitting.pres`. Use `⟨fun Φ hΦ Φ' hΦ' φ hφ => ?_, fun c Φ hΦ φ hφ => ?_, fun Φ hΦ φ φ' hφ hφ' => ?_, fun c Φ hΦ φ hφ => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `h`. Establish `e : ∀ g, theta om (Φ + Φ') g h * star (φ g) = theta om Φ g h * star (φ g) + theta om Φ' g h * star (φ g)` using `fun g => by`.

Establish `: theta om (Φ + Φ') g h = theta om Φ g h + theta om Φ' g h`. Simplify using `only [theta, map_add]`. Conclude with `thetaSum_add F (hpres _ _ hΦ) (hpres _ _ hΦ')`. Rewrite using `[this, add_mul]`. Simplify using `only [lift, Pi.add_apply, e]`.

Conclude with `integral_add (integrand_int T hP hΦ hφ h) (integrand_int T hP hΦ' hφ h)`. Use function extensionality and compare the values at `h`. Establish `e : ∀ g, theta om (c • Φ) g h * star (φ g) = c * (theta om Φ g h * star (φ g))` using `fun g => by`. Simplify using `only [theta, map_smul, thetaSum_smul, mul_assoc]`. Simplify using `only [lift, Pi.smul_apply, smul_eq_mul, e, integral_const_mul]`.

Use function extensionality and compare the values at `h`. Establish `e : ∀ g, theta om Φ g h * star ((φ + φ') g) = theta om Φ g h * star (φ g) + theta om Φ g h * star (φ' g)` using `fun g => by`. Simplify using `only [Pi.add_apply, star_add, mul_add]`. Simplify using `only [lift, Pi.add_apply] at e ⊢`. Simplify using `only [e]`.

Conclude with `integral_add (integrand_int T hP hΦ hφ h) (integrand_int T hP hΦ hφ' h)`. Use function extensionality and compare the values at `h`. Establish `e : ∀ g, theta om Φ g h * star ((c • φ) g) = (starRingEnd ℂ) c * (theta om Φ g h * star (φ g))` using `fun g => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [lift, Pi.smul_apply, smul_eq_mul] at e ⊢`. Simplify using `only [e, integral_const_mul]`.
-/
theorem UpperTheory.theta_lift_linear :
    Tools → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), IsPair B M χX χW om n 0 d 0 → (∀ Φ ∈ schA F (Fin n × Fin d), ∀ Φ' ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → lift M om (Φ + Φ') φ = lift M om Φ φ + lift M om Φ' φ) ∧ (∀ (c : ℂ), ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → lift M om (c • Φ) φ = c • lift M om Φ φ) ∧ (∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ φ' : UA σ X.J → ℂ, IsFn φ → IsFn φ' → lift M om Φ (φ + φ') = lift M om Φ φ + lift M om Φ φ') ∧ (∀ (c : ℂ), ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → lift M om Φ (c • φ) = (starRingEnd ℂ) c • lift M om Φ φ) := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hP
  have hpres : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F (Fin n × Fin d) := hP.weil.isUSplitting.pres
  refine ⟨fun Φ hΦ Φ' hΦ' φ hφ => ?_, fun c Φ hΦ φ hφ => ?_, fun Φ hΦ φ φ' hφ hφ' => ?_, fun c Φ hΦ φ hφ => ?_⟩
  · funext h
    have e : ∀ g, theta om (Φ + Φ') g h * star (φ g) = theta om Φ g h * star (φ g) + theta om Φ' g h * star (φ g) := fun g => by
      have : theta om (Φ + Φ') g h = theta om Φ g h + theta om Φ' g h := by
        simp only [theta, map_add]
        exact thetaSum_add F (hpres _ _ hΦ) (hpres _ _ hΦ')
      rw [this, add_mul]
    simp only [lift, Pi.add_apply, e]
    exact integral_add (integrand_int T hP hΦ hφ h) (integrand_int T hP hΦ' hφ h)
  · funext h
    have e : ∀ g, theta om (c • Φ) g h * star (φ g) = c * (theta om Φ g h * star (φ g)) := fun g => by
      simp only [theta, map_smul, thetaSum_smul, mul_assoc]
    simp only [lift, Pi.smul_apply, smul_eq_mul, e, integral_const_mul]
  · funext h
    have e : ∀ g, theta om Φ g h * star ((φ + φ') g) = theta om Φ g h * star (φ g) + theta om Φ g h * star (φ' g) := fun g => by
      simp only [Pi.add_apply, star_add, mul_add]
    simp only [lift, Pi.add_apply] at e ⊢
    simp only [e]
    exact integral_add (integrand_int T hP hΦ hφ h) (integrand_int T hP hΦ hφ' h)
  · funext h
    have e : ∀ g, theta om Φ g h * star ((c • φ) g) = (starRingEnd ℂ) c * (theta om Φ g h * star (φ g)) := fun g => by
      simp only [Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply]
      ring
    simp only [lift, Pi.smul_apply, smul_eq_mul] at e ⊢
    simp only [e, integral_const_mul]
