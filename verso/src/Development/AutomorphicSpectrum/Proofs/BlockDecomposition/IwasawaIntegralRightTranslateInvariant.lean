import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaHaarMeasureDecomposition
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.RInvL

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

open Classical in

def rat (h : GL (Fin 2) F) : F :=
  if h.val 1 1 ≠ 0 then h.val 0 1 / h.val 1 1 else h.val 0 0 / h.val 1 0

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem row_ne (h : GL (Fin 2) F) (e : h.val 1 1 = 0) : h.val 1 0 ≠ 0 := by
  intro e'
  have hd : (h.val).det ≠ 0 := by
    have := h.isUnit.map (Matrix.detMonoidHom (n := Fin 2) (R := F))
    exact this.ne_zero
  apply hd
  rw [Matrix.det_fin_two, e, e']
  ring

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.
-/
theorem ratio_left_unipotent_add (x : F) (h : GL (Fin 2) F) : rat (uni2 x * h) = rat h + x := by
  have e0 : ∀ j, (uni2 x * h).val 0 j = h.val 0 j + x * h.val 1 j := by
    intro j
    simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]
  have e1 : ∀ j, (uni2 x * h).val 1 j = h.val 1 j := by
    intro j
    simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]
  unfold rat
  rw [e0, e0, e1, e1]
  by_cases c : h.val 1 1 = 0
  · have := row_ne h c
    simp only [c, ne_eq, not_true_eq_false, if_false]
    field_simp
  · simp only [ne_eq, c, not_false_eq_true, if_true]
    field_simp

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem measurable_rat : Measurable (rat (F := F)) := by
  have hc : ∀ i j, Measurable fun h : GL (Fin 2) F => h.val i j := fun i j =>
    (Units.continuous_val.matrix_elem i j).measurable
  unfold rat
  refine Measurable.ite ?_ ((hc 0 1).div (hc 1 1)) ((hc 0 0).div (hc 1 0))
  exact ((hc 1 1) (measurableSet_singleton (0 : F))).compl

def th (ψ : AddChar F Circle) (h : GL (Fin 2) F) : ENNReal :=
  (selfDualMeasure ψ (𝒪[F] : Set F))⁻¹ * (𝒪[F] : Set F).indicator 1 (rat h)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem measurableSet_integers : MeasurableSet (𝒪[F] : Set F) := by
  have hKm : MeasurableSet (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) :=
    (GLnLocal.isOpen_integralGL F 2).measurableSet
  have e : (𝒪[F] : Set F) = uni2 ⁻¹' (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
    ext x
    exact (GlobalTheory.CompanionTheory.IwaHaar.unipotent_mem_integral_GL_iff x).symm
  rw [e]
  exact GlobalTheory.CompanionTheory.IwaHaar.continuous_unipotentGL2.measurable hKm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem measurable_th (ψ : AddChar F Circle) : Measurable (th ψ) :=
  ((measurable_one.indicator measurableSet_integers).comp measurable_rat).const_mul _

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lintegral_th (ψ : AddChar F Circle) (h : GL (Fin 2) F) :
    ∫⁻ x, th ψ (uni2 x * h) ∂selfDualMeasure ψ = 1 := by
  have hO : selfDualMeasure ψ (𝒪[F] : Set F) ≠ 0 := by
    rw [selfDualMeasure_integers]
    exact ENNReal.coe_ne_zero.2 (selfDualMeasure_coeff_ne_zero ψ)
  have hT : selfDualMeasure ψ (𝒪[F] : Set F) ≠ ⊤ := by
    rw [selfDualMeasure_integers]
    exact ENNReal.coe_ne_top
  have hm : Measurable ((𝒪[F] : Set F).indicator (1 : F → ENNReal)) :=
    measurable_one.indicator measurableSet_integers
  have e : ∀ x : F, th ψ (uni2 x * h) =
      (selfDualMeasure ψ (𝒪[F] : Set F))⁻¹ * (𝒪[F] : Set F).indicator 1 (rat h + x) := by
    intro x
    rw [th, ratio_left_unipotent_add]
  simp_rw [e]
  have hm' : Measurable fun x : F => (𝒪[F] : Set F).indicator (1 : F → ENNReal) (rat h + x) :=
    hm.comp (measurable_const_add _)
  rw [lintegral_const_mul _ hm',
    lintegral_add_left_eq_self ((𝒪[F] : Set F).indicator (1 : F → ENNReal)) (rat h),
    lintegral_indicator_one measurableSet_integers]
  exact ENNReal.inv_mul_cancel hO hT

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem lintegral_quot (ψ : AddChar F Circle) {c : ENNReal}
    (hc : ∀ f : GL (Fin 2) F → ENNReal, Measurable f →
      ∫⁻ p, ∫⁻ x, ENNReal.ofReal (wR p) * f (uni2 x * hI p) ∂selfDualMeasure ψ ∂mIw ψ =
        c * ∫⁻ g, f g ∂LFS.hG ψ)
    {f φ : GL (Fin 2) F → ENNReal} (hf : Measurable f) (hN : ∀ x h, f (uni2 x * h) = f h)
    (hφ : Measurable φ) (h1 : ∀ h, ∫⁻ x, φ (uni2 x * h) ∂selfDualMeasure ψ = 1) :
    ∫⁻ p, ENNReal.ofReal (wR p) * f (hI p) ∂mIw ψ = c * ∫⁻ g, f g * φ g ∂LFS.hG ψ := by
  rw [← hc (fun g => f g * φ g) (hf.mul hφ)]
  refine lintegral_congr fun p => ?_
  have e : ∀ x, ENNReal.ofReal (wR p) * (f (uni2 x * hI p) * φ (uni2 x * hI p)) =
      (ENNReal.ofReal (wR p) * f (hI p)) * φ (uni2 x * hI p) := by
    intro x
    rw [hN, mul_assoc]
  simp_rw [e]
  have hm : Measurable fun x : F => φ (uni2 x * hI p) :=
    hφ.comp (GlobalTheory.CompanionTheory.IwaHaar.continuous_unipotentGL2.mul continuous_const).measurable
  rw [lintegral_const_mul _ hm, h1, mul_one]

end Loc

end GlobalTheory.CompanionTheory.RInvL

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Reduce the equality to equality of the corresponding arguments. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem GlobalTheory.CompanionTheory.RInvL.main : ForS fun F _ _ _ _ _ _ ψ => ∀ f : GL (Fin 2) F → ENNReal, Measurable f →
    (∀ x h, f (uni2 x * h) = f h) →
    ∀ g : GL (Fin 2) F, ∫⁻ p, ENNReal.ofReal (wR p) * f (hI p * g) ∂mIw ψ =
      ∫⁻ p, ENNReal.ofReal (wR p) * f (hI p) ∂mIw ψ := by
  intro F _ _ _ _ _ _ ψ hψ f hf hN g
  obtain ⟨c, -, -, hc⟩ := GlobalTheory.CompanionTheory.IwaHaar.main F ψ hψ
  haveI := GlobalTheory.CompanionTheory.IwaHaar.right_inst ψ
  have e1 := GlobalTheory.CompanionTheory.RInvL.lintegral_quot ψ hc (f := fun h => f (h * g))
    (hf.comp (measurable_mul_const g)) (fun x h => by simp only [mul_assoc]; exact hN x _)
    (GlobalTheory.CompanionTheory.RInvL.measurable_th ψ) (GlobalTheory.CompanionTheory.RInvL.lintegral_th ψ)
  have e2 := GlobalTheory.CompanionTheory.RInvL.lintegral_quot ψ hc (f := f) (φ := fun h => GlobalTheory.CompanionTheory.RInvL.th ψ (h * g⁻¹))
    hf hN ((GlobalTheory.CompanionTheory.RInvL.measurable_th ψ).comp (measurable_mul_const _))
    (fun h => by simp only [mul_assoc]; exact GlobalTheory.CompanionTheory.RInvL.lintegral_th ψ _)
  refine e1.trans (Eq.trans ?_ e2.symm)
  congr 1
  rw [← lintegral_mul_right_eq_self (fun h => f h * GlobalTheory.CompanionTheory.RInvL.th ψ (h * g⁻¹)) g]
  simp only [mul_inv_cancel_right]
