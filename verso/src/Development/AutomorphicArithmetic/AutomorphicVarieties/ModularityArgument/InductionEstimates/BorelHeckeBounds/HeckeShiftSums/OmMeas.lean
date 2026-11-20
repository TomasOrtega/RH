import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LocFin

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

/- English proof (translation)
Introduce `q`. Take `⟨δ, hδ, e⟩` from `(pkLaws (K := K)).2.2.2 (q.out * ⟨γ, hγ⟩)`. Establish `h1` using `h (Quotient.mk _ (q.out * ⟨γ, hγ⟩))`. Unfold `qx at h1 ⊢`. Rewrite `h1` using `[e, mul_assoc, (hpSpec (K := K)).2.2.1 δ hδ, Subgroup.coe_mul, mul_assoc]`.

Conclude with `h1`.
-/
private theorem om_of_mul {K : Type} [Field K] [NumberField K] {T : ℝ} {γ : G1 K (2 + 2)} (hγ : γ ∈ Gam K (2 + 2))
    {x : G1 K (2 + 2)} (h : Om T x) : Om T (γ * x) := by
  intro q
  obtain ⟨δ, hδ, e⟩ := (pkLaws (K := K)).2.2.2 (q.out * ⟨γ, hγ⟩)
  have h1 := h (Quotient.mk _ (q.out * ⟨γ, hγ⟩))
  unfold qx at h1 ⊢
  rw [e, mul_assoc, (hpSpec (K := K)).2.2.1 δ hδ, Subgroup.coe_mul, mul_assoc] at h1
  exact h1

/- English proof (translation)
Introduce `K _ _ T`. Establish `h1 : ∀ γ ∈ Gam K (2 + 2), ∀ x : G1 K (2 + 2), Om T (γ * x) ↔ Om T x` using `fun γ hγ x => ⟨fun h => by`. Use `om_of_mul (inv_mem hγ) h` as an intermediate fact. Rewrite using `[inv_mul_cancel_left] at this, om_of_mul hγ⟩` and apply the resulting hypothesis. Establish `h2 : IsClosed {x : G1 K (2 + 2) | Om T x}`.

Unfold `Om`. Simplify using `only [Set.setOf_forall]`. Conclude with `isClosed_iInter fun q => isClosed_le ((hpSpec (K := K)).2.2.2.1.comp (continuous_const.mul continuous_id)) continuous_const`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations. Rewrite using `[measurableSet_quotient]`.

Establish `h : Quotient.mk'' ⁻¹' {y : RightCosetSpace (Gam K (2 + 2)) | Om T (Quotient.out y : G1 K (2 + 2))} = {x : G1 K (2 + 2) | Om T x}`. Use extensionality with `x`. Take `⟨γ, hγ⟩` from `mk_eq_mk_iff.1 (Quotient.out_eq (RightCosetSpace.mk (Gam K (2 + 2)) x))`. Express the relevant statement in the definitionally equal form `Om T (Quotient.out (RightCosetSpace.mk (Gam K (2 + 2)) x)) ↔ Om T x`. Rewrite using `[← hγ]`.

Conclude with `h1 _ γ.2 x`. Rewrite using `[h]`. Conclude with `h2.measurableSet`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.omMeas :
    ∀ {K : Type} [Field K] [NumberField K] (T : ℝ), (∀ γ ∈ Gam K (2 + 2), ∀ x : G1 K (2 + 2), Om T (γ * x) ↔ Om T x) ∧ IsClosed {x : G1 K (2 + 2) | Om T x} ∧
      MeasurableSet {y : RightCosetSpace (Gam K (2 + 2)) | Om T (Quotient.out y : G1 K (2 + 2))} := by
  intro K _ _ T
  have h1 : ∀ γ ∈ Gam K (2 + 2), ∀ x : G1 K (2 + 2), Om T (γ * x) ↔ Om T x := fun γ hγ x =>
    ⟨fun h => by
      have := om_of_mul (inv_mem hγ) h
      rwa [inv_mul_cancel_left] at this, om_of_mul hγ⟩
  have h2 : IsClosed {x : G1 K (2 + 2) | Om T x} := by
    unfold Om
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun q => isClosed_le
      ((hpSpec (K := K)).2.2.2.1.comp (continuous_const.mul continuous_id)) continuous_const
  refine ⟨h1, h2, ?_⟩
  rw [measurableSet_quotient]
  have h : Quotient.mk'' ⁻¹' {y : RightCosetSpace (Gam K (2 + 2)) | Om T (Quotient.out y : G1 K (2 + 2))} =
      {x : G1 K (2 + 2) | Om T x} := by
    ext x
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (Quotient.out_eq (RightCosetSpace.mk (Gam K (2 + 2)) x))
    change Om T (Quotient.out (RightCosetSpace.mk (Gam K (2 + 2)) x)) ↔ Om T x
    rw [← hγ]
    exact h1 _ γ.2 x
  rw [h]
  exact h2.measurableSet
