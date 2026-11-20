import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private def ctKer {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (r : ℕ) :
    Submodule ℂ (L2 μ) where
  carrier := {w | constantTermL2 μ r w =ᵐ[μ] 0}
  zero_mem' := by
    change constantTermL2 μ r 0 =ᵐ[μ] 0
    filter_upwards [ae_constantTermL2_sub μ r 0 0] with y hy
    rw [sub_self, sub_self] at hy
    exact hy
  add_mem' := fun {φ ψ} hφ hψ => by
    change constantTermL2 μ r (φ + ψ) =ᵐ[μ] 0
    have h1 : constantTermL2 μ r φ =ᵐ[μ] 0 := hφ
    have h2 : constantTermL2 μ r ψ =ᵐ[μ] 0 := hψ
    filter_upwards [ae_constantTermL2_add μ r φ ψ, h1, h2] with y e1 e2 e3
    rw [e1, e2, e3]
    simp
  smul_mem' := fun c φ hφ => by
    change constantTermL2 μ r (c • φ) =ᵐ[μ] 0
    have h1 : constantTermL2 μ r φ =ᵐ[μ] 0 := hφ
    filter_upwards [ae_constantTermL2_smul μ r c φ, h1] with y e1 e2
    rw [e1, e2]
    simp

/- English proof (translation)
Use `isClosed_of_closure_subset fun φ hφ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `constantTermL2 μ r φ =ᵐ[μ] 0`. Use `ae_of_forall_isCompact μ fun S hS => ?_` and prove the remaining obligations. Take `⟨C, hC, hCφ⟩` from `exists_lintegral_constantTermL2_sq_le μ r hS`. Use `set I := ∫⁻ y in S, ‖constantTermL2 μ r φ y‖ₑ ∂μ`.

Establish `hle : ∀ ε : ℝ, 0 < ε → I ^ 2 ≤ C * ENNReal.ofReal ε ^ 2`. Introduce `ε hε`. Take `⟨ψ, hψ, hdist⟩` from `Metric.mem_closure_iff.1 hφ ε hε`. Establish `hψ' : constantTermL2 μ r ψ =ᵐ[μ] 0` using `hψ`. Establish `hI : I = ∫⁻ y in S, ‖constantTermL2 μ r (φ - ψ) y‖ₑ ∂μ`.

Use `lintegral_congr_ae (ae_restrict_of_ae ?_)` and prove the remaining obligations. Use `filter_upwards [ae_constantTermL2_sub μ r φ ψ, hψ'] with y h1 h2`. Rewrite using `[h1, h2, Pi.zero_apply, sub_zero]`. Rewrite using `[hI]`. Use `(hCφ (φ - ψ)).trans ?_` and prove the remaining obligations.

Use `gcongr`. Rewrite using `[← ofReal_norm, ← dist_eq_norm]`. Conclude with `ENNReal.ofReal_le_ofReal hdist.le`. Establish `hI0 : I ^ 2 = 0`. Use `le_antisymm ?_ zero_le` and prove the remaining obligations.

Establish `ht : Tendsto (fun ε : ℝ => C * ENNReal.ofReal ε ^ 2) (𝓝[>] 0) (𝓝 0)`. Establish `h1 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε ^ 2) (𝓝[>] 0) (𝓝 0)`. Use `(((ENNReal.continuous_pow 2).comp ENNReal.continuous_ofReal).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Simplify using `using ENNReal.Tendsto.const_mul h1 (Or.inr hC)`.

Conclude with `ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε)`. Establish `hI' : I = 0` using `pow_eq_zero_iff two_ne_zero |>.1 hI0`. Establish `hm : AEMeasurable (fun y => ‖constantTermL2 μ r φ y‖ₑ) (μ.restrict S)` using `(stronglyMeasurable_ctFun r (Lp.stronglyMeasurable φ)).measurable.enorm.aemeasurable`. Use `filter_upwards [(lintegral_eq_zero_iff' hm).1 hI'] with y hy`. Simplify using `using hy`.
-/
private theorem ctKer_closed {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (r : ℕ) : IsClosed (ctKer μ r : Set (L2 μ)) := by
  refine isClosed_of_closure_subset fun φ hφ => ?_
  change constantTermL2 μ r φ =ᵐ[μ] 0
  refine ae_of_forall_isCompact μ fun S hS => ?_
  obtain ⟨C, hC, hCφ⟩ := exists_lintegral_constantTermL2_sq_le μ r hS
  set I := ∫⁻ y in S, ‖constantTermL2 μ r φ y‖ₑ ∂μ
  have hle : ∀ ε : ℝ, 0 < ε → I ^ 2 ≤ C * ENNReal.ofReal ε ^ 2 := by
    intro ε hε
    obtain ⟨ψ, hψ, hdist⟩ := Metric.mem_closure_iff.1 hφ ε hε
    have hψ' : constantTermL2 μ r ψ =ᵐ[μ] 0 := hψ
    have hI : I = ∫⁻ y in S, ‖constantTermL2 μ r (φ - ψ) y‖ₑ ∂μ := by
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [ae_constantTermL2_sub μ r φ ψ, hψ'] with y h1 h2
      rw [h1, h2, Pi.zero_apply, sub_zero]
    rw [hI]
    refine (hCφ (φ - ψ)).trans ?_
    gcongr
    rw [← ofReal_norm, ← dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal hdist.le
  have hI0 : I ^ 2 = 0 := by
    refine le_antisymm ?_ zero_le
    have ht : Tendsto (fun ε : ℝ => C * ENNReal.ofReal ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have := (((ENNReal.continuous_pow 2).comp ENNReal.continuous_ofReal).tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        simpa [Function.comp_def] using this
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hC)
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε)
  have hI' : I = 0 := pow_eq_zero_iff two_ne_zero |>.1 hI0
  have hm : AEMeasurable (fun y => ‖constantTermL2 μ r φ y‖ₑ) (μ.restrict S) :=
    (stronglyMeasurable_ctFun r (Lp.stronglyMeasurable φ)).measurable.enorm.aemeasurable
  filter_upwards [(lintegral_eq_zero_iff' hm).1 hI'] with y hy
  simpa using hy

/- English proof (translation)
Introduce `K _ _ n μ _ r`. Conclude with `⟨ctKer μ r, ctKer_closed μ r, fun _ => Iff.rfl⟩`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ctClosed :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (r : ℕ), ∃ S : Submodule ℂ (L2 μ), IsClosed (S : Set (L2 μ)) ∧
      ∀ w, w ∈ S ↔ constantTermL2 μ r w =ᵐ[μ] 0 := by
  intro K _ _ n μ _ r
  exact ⟨ctKer μ r, ctKer_closed μ r, fun _ => Iff.rfl⟩
