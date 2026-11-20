import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.TwistedTraces.ExistsBoundOfIsRootExpMulForall
import Development.AutomorphicArithmetic.TwistedTraces.NormDerivOrbitLeOfPolynomialAnnihilated

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `φ _`. Simplify using the standard rewrite rules. Consider the case `succ m ih`.

Introduce `φ hφ`. Rewrite using `[pow_succ, pow_succ, ContinuousLinearMap.mul_apply, Module.End.mul_apply, ← cuspToL2_sigma μ k hφ, ih _ (σ_mem_centralCuspForms k hφ)]`.
-/
private theorem pow_cuspVecL {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n))
    [μ.IsHaarMeasure] (k : archCompact K n) (m : ℕ) :
    ∀ φ ∈ centralCuspForms K n, (archRepT μ (k : archGroup K n) ^ m) (cuspVecL μ φ) =
      cuspVecL μ (((gkModuleCusp K n).σ k ^ m) φ) := by
  induction m with
  | zero =>
    intro φ _
    simp
  | succ m ih =>
    intro φ hφ
    rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, Module.End.mul_apply, ← cuspToL2_sigma μ k hφ,
      ih _ (σ_mem_centralCuspForms k hφ)]

/- English proof (translation)
Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add a b ha hb`. Simplify using `only [map_add, ContinuousLinearMap.add_apply, LinearMap.add_apply, ha, hb]`. Consider the case `monomial m c`. Rewrite using `[aeval_monomial, aeval_monomial, Module.End.mul_apply, ContinuousLinearMap.mul_apply, pow_cuspVecL μ k m φ hφ]`.

Simplify using `[Algebra.algebraMap_eq_smul_one]`.
-/
private theorem aeval_cuspVecL {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n))
    [μ.IsHaarMeasure] (k : archCompact K n) (q : ℂ[X]) {φ : cuspForms K n}
    (hφ : φ ∈ centralCuspForms K n) :
    aeval (archRepT μ (k : archGroup K n)) q (cuspVecL μ φ) =
      cuspVecL μ (aeval ((gkModuleCusp K n).σ k) q φ) := by
  induction q using Polynomial.induction_on' with
  | add a b ha hb =>
    simp only [map_add, ContinuousLinearMap.add_apply, LinearMap.add_apply, ha, hb]
  | monomial m c =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, ContinuousLinearMap.mul_apply,
      pow_cuspVecL μ k m φ hφ]
    simp [Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Introduce `K _ _ n μ _ d p Y hp hk`. Set `kk : ℝ → archCompact K n` to `fun t => ⟨(isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y), hk t⟩`. Take `⟨M, hM⟩` from `UpperTheory.exists_bound_of_isRoot_exp_mul_forall d (fun t => p (kk t)) (fun t => hp _)`. Use `⟨M, fun φ hφ hkill => ?_⟩` and prove the remaining obligations. Establish `hy` using `(isExpLieAlgebra K n).hasDerivAt_derivOp (archRepT μ) (isSmoothVector_cuspToL2 μ hφ) ((isExpLieAlgebra K n).ofLie Y)`.

Establish `e` using `derivOp_cuspVecL μ hφ ((isExpLieAlgebra K n).ofLie Y)`. Rewrite `e` using `[IsExpLieAlgebra.toLie_ofLie]`. Rewrite `hy` using `[e]`. Establish `hu : ∀ t : ℝ, (archRepT μ ((kk t : archCompact K n) : archGroup K n)) = archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y))` using `fun t => rfl`. Use `UpperTheory.norm_deriv_orbit_le_of_polynomial_annihilated (CuspL2 μ) (fun t => archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y))) (fun t => p (kk t)) M (cuspVecL μ φ) _ ?_ ?_ ?_ ?_ hy ?_ hM` and prove the remaining obligations.

Use `ext1 x`. Simplify using `[(isExpLieAlgebra K n).expG_zero]`. Introduce `s t ext1 x`. Rewrite using `[(isExpLieAlgebra K n).expG_add_smul, BanachRep.map_mul_apply]`. Both sides reduce to the same expression.

Introduce `t x`. Rewrite using `[archRepT_apply]`. Conclude with `UnitaryRep.norm_map _ _ _`. Establish `hfin` using `(gkModuleCusp K n).locallyFinite φ`. Establish `hle : Submodule.span ℂ (Set.range fun t : ℝ => archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)) (cuspVecL μ φ)) ≤ (Submodule.span ℂ (Set.range fun k => (gkModuleCusp K n).σ k φ)).map (cuspVecL μ)`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `⟨_, Submodule.subset_span ⟨kk t, rfl⟩, cuspToL2_sigma μ (kk t) hφ⟩`. Conclude with `Submodule.finiteDimensional_of_le hle`. Introduce `t`.

Use `aeval_cuspVecL μ (kk t) (p (kk t)) hφ` as an intermediate fact. Rewrite `this` using `[hkill, map_zero]`. Conclude with `this`.
-/
theorem UpperTheory.norm_cuspVecL_gk_action_le_of_aeval_eq_zero :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (d : ℕ) (p : archCompact K n → ℂ[X]) (Y : (isExpLieAlgebra K n).lieSubalgebra), (∀ k, p k ≠ 0 ∧ (p k).natDegree ≤ d) → (∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y) ∈ archCompact K n) → ∃ M : ℝ, ∀ φ ∈ centralCuspForms K n, (∀ k, aeval ((gkModuleCusp K n).σ k) (p k) φ = 0) → ‖cuspVecL μ ((gkModuleCusp K n).ρ Y φ)‖ ≤ M * ‖cuspVecL μ φ‖ := by
  intro K _ _ n μ _ d p Y hp hk
  let kk : ℝ → archCompact K n := fun t => ⟨(isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y), hk t⟩
  obtain ⟨M, hM⟩ := UpperTheory.exists_bound_of_isRoot_exp_mul_forall d (fun t => p (kk t)) (fun t => hp _)
  refine ⟨M, fun φ hφ hkill => ?_⟩
  have hy := (isExpLieAlgebra K n).hasDerivAt_derivOp (archRepT μ) (isSmoothVector_cuspToL2 μ hφ)
    ((isExpLieAlgebra K n).ofLie Y)
  have e := derivOp_cuspVecL μ hφ ((isExpLieAlgebra K n).ofLie Y)
  rw [IsExpLieAlgebra.toLie_ofLie] at e
  rw [e] at hy
  have hu : ∀ t : ℝ, (archRepT μ ((kk t : archCompact K n) : archGroup K n)) =
      archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)) := fun t => rfl
  refine UpperTheory.norm_deriv_orbit_le_of_polynomial_annihilated (CuspL2 μ)
    (fun t => archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)))
    (fun t => p (kk t)) M (cuspVecL μ φ) _ ?_ ?_ ?_ ?_ hy ?_ hM
  · ext1 x
    simp [(isExpLieAlgebra K n).expG_zero]
  · intro s t
    ext1 x
    rw [(isExpLieAlgebra K n).expG_add_smul, BanachRep.map_mul_apply]
    rfl
  · intro t x
    rw [archRepT_apply]
    exact UnitaryRep.norm_map _ _ _
  · have hfin := (gkModuleCusp K n).locallyFinite φ
    have hle : Submodule.span ℂ (Set.range fun t : ℝ =>
        archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)) (cuspVecL μ φ)) ≤
        (Submodule.span ℂ (Set.range fun k => (gkModuleCusp K n).σ k φ)).map (cuspVecL μ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨t, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨kk t, rfl⟩, cuspToL2_sigma μ (kk t) hφ⟩
    exact Submodule.finiteDimensional_of_le hle
  · intro t
    have := aeval_cuspVecL μ (kk t) (p (kk t)) hφ
    rw [hkill, map_zero] at this
    exact this
