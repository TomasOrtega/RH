import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem slice_int {V M : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup M] [NormedSpace ℝ M] (G : 𝓢(V × M, ℂ)) (y : M) :
    Integrable (fun ξ : V => G (ξ, y)) := by
  have h1 : Function.HasTemperateGrowth (fun ξ : V => (ξ, y)) := by
    have := (ContinuousLinearMap.inl ℝ V M).hasTemperateGrowth.add
      (Function.HasTemperateGrowth.const ((0 : V), y))
    convert this using 1
    ext ξ <;> simp
  have h2 : AntilipschitzWith 1 (fun ξ : V => (ξ, y)) := (Isometry.antilipschitz (by
    refine Isometry.of_dist_eq fun a b => ?_
    simp [Prod.dist_eq]))
  exact (SchwartzMap.compCLMOfAntilipschitz ℝ h1 h2 G).integrable

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem shear_int {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    [MeasurableSpace M] [BorelSpace M] (μ : Measure M) [μ.IsAddHaarMeasure] (N : M →L[ℝ] M)
    (hN : ∀ x, N (N x) = 0) (f : M → ℂ) : ∫ x, f (x + N x) ∂μ = ∫ x, f x ∂μ := by
  let L : M →ₗ[ℝ] M := 1 + (N : M →ₗ[ℝ] M)
  have hnil : IsNilpotent (-(N : M →ₗ[ℝ] M) : Module.End ℝ M) := ⟨2, by
    ext x
    simp [pow_two, hN]⟩
  have hdet : LinearMap.det L = 1 := by
    have := LinearMap.eval_charpoly (-(N : M →ₗ[ℝ] M)) 1
    rw [(LinearMap.isNilpotent_iff_charpoly _).1 hnil] at this
    simpa [L] using this.symm
  have hmap : Measure.map L μ = μ := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  let e : M ≃ₜ M :=
    { toFun := fun x => x + N x
      invFun := fun x => x - N x
      left_inv := fun x => by simp [hN]
      right_inv := fun x => by simp [hN]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hp : MeasurePreserving e.toMeasurableEquiv μ μ := ⟨e.toMeasurableEquiv.measurable, hmap⟩
  exact hp.integral_comp' f

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Af.Smo.betaInt :
    UpperTheory.V.Af.Smo.BetaInt := by
  intro V M _ _ _ _ _ _ _ _ _ _ μ _ B hB G K K' hK hK' w η hw ⟨C, hC⟩ hwB
  have hint : ∀ (F : 𝓢(V × M, ℂ)) (a : V × M → ℂ), Measurable a → (∀ z, ‖a z‖ ≤ C) →
      ∫ u, ∫ x, a (u, x) * F (u, x) ∂μ = ∫ x, (∫ u, a (u, x) * F (u, x)) ∂μ := by
    intro F a ha haC
    refine integral_integral_swap (f := fun u x => a (u, x) * F (u, x)) ?_
    have : Integrable F ((volume : Measure V).prod μ) := F.integrable
    exact this.bdd_mul ha.aestronglyMeasurable (Filter.Eventually.of_forall haC)
  have h1 := hint K' (fun z => w z.2) (hw.comp measurable_snd) (fun z => hC _)
  have h2 := hint K (fun z => (𝐞 ⟪η, z.1⟫ : ℂ) * w z.2)
    (Measurable.mul (Continuous.measurable (by fun_prop)) (hw.comp measurable_snd)) (fun z => by rw [norm_mul, Circle.norm_coe, one_mul]; exact hC _)
  simp only [integral_const_mul] at h1
  rw [← h1]
  have h3 : ∀ u, ∫ x, w x * K' (u, x) ∂μ = ∫ x, (𝐞 ⟪η, u⟫ : ℂ) * w x * K (u, x) ∂μ := by
    intro u
    rw [← shear_int μ (B u) (hB u)]
    congr 1
    ext x
    rw [hwB, hK']
    simp [hB]
  simp only [h3]
  rw [h2]
  congr 1
  ext x
  have hF : 𝓕 (fun ξ => G (ξ, x)) = fun u => K (u, x) := by
    ext u
    rw [hK]; rfl
  have h4 := Continuous.fourierInv_fourier_eq (f := fun ξ => G (ξ, x)) (by fun_prop) (slice_int G x)
    (by rw [hF]; exact slice_int K x)
  have h5 := congrFun h4 η
  rw [hF, Real.fourierInv_eq] at h5
  rw [← h5, ← integral_const_mul]
  congr 1
  ext u
  rw [Circle.smul_def, smul_eq_mul, real_inner_comm]
  ring
