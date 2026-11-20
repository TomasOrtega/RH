import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.UiwPow

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [prj, ContinuousLinearMap.comp_apply]`. Conclude with `Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)`.
-/
private theorem prj_prj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) : prj V ∘L prj V = prj V := by
  ext v
  simp only [prj, ContinuousLinearMap.comp_apply]
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

/- English proof (translation)
Use `ext1 v`. Establish `hle : (fixL μ w J).topologicalClosure ≤ LinearMap.eqLocus (rhoL μ w k : LL μ →ₗ[ℂ] LL μ) LinearMap.id`. Apply `Submodule.topologicalClosure_minimal` to reduce the goal to its premises. Unfold `fixL fixF rhoL`. Conclude with `iInf₂_le (AdelicGLn.localEmbedding w k) (Subgroup.mem_map_of_mem _ hk)`.

Conclude with `isClosed_eq (rhoL μ w k).continuous continuous_id`. Conclude with `hle (Submodule.starProjection_apply_mem _ v)`.
-/
private theorem rhoL_prj {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) {k : GL (Fin n) (w.adicCompletion K)} (hk : k ∈ J) :
    rhoL μ w k ∘L prj (fixL μ w J) = prj (fixL μ w J) := by
  ext1 v
  have hle : (fixL μ w J).topologicalClosure ≤
      LinearMap.eqLocus (rhoL μ w k : LL μ →ₗ[ℂ] LL μ) LinearMap.id := by
    apply Submodule.topologicalClosure_minimal
    · unfold fixL fixF rhoL
      exact iInf₂_le (AdelicGLn.localEmbedding w k) (Subgroup.mem_map_of_mem _ hk)
    · exact isClosed_eq (rhoL μ w k).continuous continuous_id
  exact hle (Submodule.starProjection_apply_mem _ v)

/- English proof (translation)
Establish `hs : {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * 1)} = {QuotientGroup.mk 1}`. Use extensionality with `c`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff, mul_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`.

Conclude with `QuotientGroup.eq.mpr (by simpa using hk)`. Introduce and unpack `rfl`. Conclude with `⟨1, J.one_mem, rfl⟩`. Unfold `Hop`. Rewrite using `[hs, finsum_mem_singleton]`.

Apply `rhoL_prj` to reduce the goal to its premises. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul J (1 : GL (Fin n) (w.adicCompletion K))`. Rewrite using `[hh, one_mul]`. Conclude with `h.2`.
-/
private theorem hop_one {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) : Hop μ w J 1 = prj (fixL μ w J) := by
  have hs : {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * 1)} =
      {QuotientGroup.mk 1} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, mul_one]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact QuotientGroup.eq.mpr (by simpa using hk)
    · rintro rfl
      exact ⟨1, J.one_mem, rfl⟩
  unfold Hop
  rw [hs, finsum_mem_singleton]
  apply rhoL_prj
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul J (1 : GL (Fin n) (w.adicCompletion K))
  rw [hh, one_mul]
  exact h.2

/- English proof (translation)
Introduce `K _ _ n μ _ w ν hν j`. Break down `Nat.eq_zero_or_pos j with rfl | hj` into its components or cases. Rewrite using `[pow_zero, zero_smul, Uiw, GroundTheory.Automorphic.Parabolic.diagPow_zero, hop_one]`. Both sides reduce to the same expression. Rewrite using `[(UpperTheory.ConvolutionTheory.Tf.uiwPow K n μ w ν ν hν hν).2.1 j hj, Uiw, Hop, ContinuousLinearMap.comp_assoc, prj_prj]`.
-/
theorem UpperTheory.ConvolutionTheory.C.uiwPow :
    UpperTheory.ConvolutionTheory.C.UiwPow := by
  intro K _ _ n μ _ w ν hν j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, zero_smul, Uiw, GroundTheory.Automorphic.Parabolic.diagPow_zero, hop_one]
    rfl
  · rw [(UpperTheory.ConvolutionTheory.Tf.uiwPow K n μ w ν ν hν hν).2.1 j hj, Uiw, Hop, ContinuousLinearMap.comp_assoc, prj_prj]
