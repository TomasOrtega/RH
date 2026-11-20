import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreFubini
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMeasureStereographicIntegralStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.XiPotentialHessianDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def genLin : MvPolynomial (Fin 3) (MvPolynomial (Fin 3) ℝ) := ∑ i, X i * C (X i)

def coordHom : MvPolynomial (Fin 3) ℝ →+* (S2 → ℝ) :=
  RingHom.pi fun p : S2 => MvPolynomial.eval fun i => (p : E3) i

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coordHom_apply (g : MvPolynomial (Fin 3) ℝ) (p : S2) :
    coordHom g p = MvPolynomial.eval (fun i => (p : E3) i) g := rfl

/- English proof (translation)
Simplify using `[lin3, genLin, map_sum, MvPolynomial.map_X, MvPolynomial.map_C, MvPolynomial.eval_X]`.
-/
theorem linear_form_eq_map_eval (n : Fin 3 → ℝ) : lin3 n = MvPolynomial.map (MvPolynomial.eval n) genLin := by
  simp [lin3, genLin, map_sum, MvPolynomial.map_X, MvPolynomial.map_C, MvPolynomial.eval_X]

/- English proof (translation)
Simplify using `only [dotPoly, genLin, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 2`. Use function extensionality and compare the values at `p`. Rewrite using `[coordHom_apply, MvPolynomial.eval_X]`.

Both sides reduce to the same expression.
-/
theorem dotPoly_id_eq_map : dotPoly (id : S2 → S2) = MvPolynomial.map coordHom genLin := by
  simp only [dotPoly, genLin, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext p
  rw [coordHom_apply, MvPolynomial.eval_X]
  rfl

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[show monomial m (coeff m Q) = (coeff m Q) • monomial m (1 : ℝ) by`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]`.

Use `_ = _ := Finset.sum_subset hQ fun m _ hm => by rw [notMem_support_iff.1 hm, zero_mul]`.
-/
theorem linear_expand (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (S : Finset (Fin 3 →₀ ℕ))
    (Q : MvPolynomial (Fin 3) ℝ) (hQ : Q.support ⊆ S) :
    ℓ Q = ∑ m ∈ S, coeff m Q * ℓ (monomial m 1) := by
  calc ℓ Q = ℓ (∑ m ∈ Q.support, monomial m (coeff m Q)) := by rw [support_sum_monomial_coeff]
    _ = ∑ m ∈ Q.support, coeff m Q * ℓ (monomial m 1) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [show monomial m (coeff m Q) = (coeff m Q) • monomial m (1 : ℝ) by
        rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
    _ = _ := Finset.sum_subset hQ fun m _ hm => by rw [notMem_support_iff.1 hm, zero_mul]

/- English proof (translation)
Introduce `ℓ N`. Establish `: IsProbabilityMeasure sphereMeasure` using `GroundTheory.Heights₂.Heights.Inter.FibreLocal.isProbabilityMeasure_sphere`. Establish `key : ∀ f : (Fin 3 → ℝ) → ℝ, Measurable f → (Integrable (fun a : ℂ => f (nS a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) ↔ Integrable (fun m : S2 => f fun i => (m : E3) i) sphereMeasure) ∧ ∫ a : ℂ, f (nS a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2) = ∫ m : S2, f (fun i => (m : E3) i) ∂sphereMea …` using `fun f hf => (GlobalTheory.T.sphere_measure_stereographic_integral).1 f hf`. Take `⟨G, hG⟩ : ∃ G, G = genLin ^ N` from `⟨_, rfl⟩`. Establish `hlin : ∀ a, lin3 (nS a) ^ N = MvPolynomial.map (MvPolynomial.eval (nS a)) G` using `fun a => by`.

Rewrite using `[hG, map_pow, linear_form_eq_map_eval]`. Establish `hdot : dotPoly (id : S2 → S2) ^ N = MvPolynomial.map coordHom G`. Rewrite using `[hG, map_pow, dotPoly_id_eq_map]`. Rewrite using `[hdot]`. Establish `hf : ∀ m, Continuous fun x : Fin 3 → ℝ => MvPolynomial.eval x (coeff m G)` using `fun m => MvPolynomial.continuous_eval _`.

Establish `hcoord : Continuous fun p : S2 => fun i => (p : E3) i` using `by fun_prop`. Establish `hsph : ∀ m, Integrable (fun p : S2 => MvPolynomial.eval (fun i => (p : E3) i) (coeff m G)) sphereMeasure` using `fun m => ((hf m).comp hcoord).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Establish `hpl : ∀ m, Integrable (fun a : ℂ => MvPolynomial.eval (nS a) (coeff m G) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2))` using `fun m => (key _ (hf m).measurable).1.2 (hsph m)`. Establish `hsupp : (momentPoly sphereMeasure (fun _ => 1) (MvPolynomial.map coordHom G)).support ⊆ G.support`. Introduce `m hm`.

Assume the negation of the conclusion as `h`. Rewrite `hm` using `[mem_support_iff]`. Apply `hm` to reduce the goal to its premises. Rewrite using `[GroundTheory.Heights₂.Heights.Inter.DiagFibreMoment.coeff_momentPoly, coeff_map, notMem_support_iff.1 h]`. Simplify using the standard rewrite rules.

Rewrite using `[linear_expand ℓ G.support _ hsupp, Finset.mul_sum]`. Establish `hpt : ∀ a : ℂ, wS a * ℓ (lin3 (nS a) ^ N) = ∑ m ∈ G.support, (MvPolynomial.eval (nS a) (coeff m G) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) * (Real.pi * ℓ (monomial m 1))` using `fun a => by`. Rewrite using `[hlin, linear_expand ℓ G.support _ (support_map_subset _ _), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_map, wS]`.

Establish `hpi` using `Real.pi_ne_zero`. Clear the denominators using the available nonvanishing facts. Repeatedly rewrite using `[hpt]`. Rewrite using `[integral_finsetSum _ fun m _ => (hpl m).mul_const _]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[integral_mul_const, (key _ (hf m).measurable).2, GroundTheory.Heights₂.Heights.Inter.DiagFibreMoment.coeff_momentPoly]`. Simplify using `only [coeff_map, one_mul, coordHom_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stereo_one : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (N : ℕ),
    ∫ a : ℂ, wS a * ℓ (lin3 (nS a) ^ N) =
      Real.pi * ℓ (momentPoly sphereMeasure (fun _ => 1) (dotPoly (id : S2 → S2) ^ N)) := by
  intro ℓ N
  have : IsProbabilityMeasure sphereMeasure := GroundTheory.Heights₂.Heights.Inter.FibreLocal.isProbabilityMeasure_sphere
  have key : ∀ f : (Fin 3 → ℝ) → ℝ, Measurable f →
      (Integrable (fun a : ℂ => f (nS a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) ↔
        Integrable (fun m : S2 => f fun i => (m : E3) i) sphereMeasure) ∧
      ∫ a : ℂ, f (nS a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2) =
        ∫ m : S2, f (fun i => (m : E3) i) ∂sphereMeasure :=
    fun f hf => (GlobalTheory.T.sphere_measure_stereographic_integral).1 f hf
  obtain ⟨G, hG⟩ : ∃ G, G = genLin ^ N := ⟨_, rfl⟩
  have hlin : ∀ a, lin3 (nS a) ^ N = MvPolynomial.map (MvPolynomial.eval (nS a)) G := fun a => by
    rw [hG, map_pow, linear_form_eq_map_eval]
  have hdot : dotPoly (id : S2 → S2) ^ N = MvPolynomial.map coordHom G := by
    rw [hG, map_pow, dotPoly_id_eq_map]
  rw [hdot]
  have hf : ∀ m, Continuous fun x : Fin 3 → ℝ => MvPolynomial.eval x (coeff m G) :=
    fun m => MvPolynomial.continuous_eval _
  have hcoord : Continuous fun p : S2 => fun i => (p : E3) i := by
    fun_prop
  have hsph : ∀ m, Integrable (fun p : S2 => MvPolynomial.eval (fun i => (p : E3) i) (coeff m G))
      sphereMeasure := fun m =>
    ((hf m).comp hcoord).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpl : ∀ m, Integrable (fun a : ℂ => MvPolynomial.eval (nS a) (coeff m G) *
      (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) := fun m =>
    (key _ (hf m).measurable).1.2 (hsph m)
  have hsupp : (momentPoly sphereMeasure (fun _ => 1) (MvPolynomial.map coordHom G)).support ⊆ G.support := by
    intro m hm
    by_contra h
    rw [mem_support_iff] at hm
    apply hm
    rw [GroundTheory.Heights₂.Heights.Inter.DiagFibreMoment.coeff_momentPoly, coeff_map, notMem_support_iff.1 h]
    simp
  rw [linear_expand ℓ G.support _ hsupp, Finset.mul_sum]
  have hpt : ∀ a : ℂ, wS a * ℓ (lin3 (nS a) ^ N) = ∑ m ∈ G.support,
      (MvPolynomial.eval (nS a) (coeff m G) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) *
        (Real.pi * ℓ (monomial m 1)) := fun a => by
    rw [hlin, linear_expand ℓ G.support _ (support_map_subset _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_map, wS]
    have hpi := Real.pi_ne_zero
    field_simp
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => (hpl m).mul_const _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_mul_const, (key _ (hf m).measurable).2,
    GroundTheory.Heights₂.Heights.Inter.DiagFibreMoment.coeff_momentPoly]
  simp only [coeff_map, one_mul, coordHom_apply]
  ring

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
