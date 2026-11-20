import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResBelow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

/- English proof (translation)
Introduce `H _ _ _ V _ _ _ _ W _ _ _ _ M B β β' k1 k2 u1 u2 ha hc`. Take `⟨-, -, l0, sa, ln, -⟩` from `(projLaws M).2.2.2.2.2.2.2 M.T₀ M.T₀ (by linarith)`. Use `set Λ := M.abelian₂ M.T₀ M.T₀ with hΛ`. Use `set R := M.F.av wR with hR`. Establish `hΛΛ : ∀ x, Λ (Λ x) = Λ x` using `fun x => DFunLike.congr_fun l0 x`.

Establish `below : ∀ S : H →L[ℂ] H, (∀ x, (⟪x, S x⟫_ℂ).re = (⟪x, R x⟫_ℂ).re) → ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖x - Λ (S (Λ x))‖`. Introduce `S hS`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `choose x hx using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat`.

Establish `h0 : ∀ n, x n ≠ 0` using `fun n h => by simpa [h] using hx n`. Set `f : ℕ → H` to `fun n => (‖x n‖⁻¹ : ℂ) • x n`. Establish `hf : ∀ n, ‖f n‖ = 1` using `fun n => norm_smul_inv_norm (h0 n)`. Establish `t0 : Tendsto (fun n => f n - Λ (S (Λ (f n)))) atTop (𝓝 0)`. Use `squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat` and prove the remaining obligations.

Establish `e : f n - Λ (S (Λ (f n))) = (‖x n‖⁻¹ : ℂ) • (x n - Λ (S (Λ (x n))))` using `by simp [f, smul_sub]`. Rewrite using `[e, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_le_iff₀ (norm_pos_iff.2 (h0 n)), mul_comm]`. Conclude with `(hx n).le`. Establish `t1 : Tendsto (fun n => Λ (f n) - f n) atTop (𝓝 0)`. Use `((Λ.continuous.tendsto 0).comp t0).sub t0` as an intermediate fact.

Simplify `this` using `[Function.comp_def, hΛΛ]`. Establish `t2 : Tendsto (fun n => f n - Λ (S (f n))) atTop (𝓝 0)`. Use `t0.add (((Λ ∘L S).continuous.tendsto 0).comp t1)` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `t3 : Tendsto (fun n => ⟪f n, f n - Λ (S (f n))⟫_ℂ + ⟪Λ (f n) - f n, S (f n)⟫_ℂ) atTop (𝓝 0)`.

Establish `a : Tendsto (fun n => ⟪f n, f n - Λ (S (f n))⟫_ℂ) atTop (𝓝 0)` using `squeeze_zero_norm (fun n => (norm_inner_le_norm _ _).trans_eq (by rw [hf, one_mul])) (tendsto_zero_iff_norm_tendsto_zero.1 t2)`. Establish `b : Tendsto (fun n => ⟪Λ (f n) - f n, S (f n)⟫_ℂ) atTop (𝓝 0)`. Use `squeeze_zero_norm (a := fun n => ‖Λ (f n) - f n‖ * ‖S‖) (fun n => (norm_inner_le_norm _ _).trans ?_) ?_` and prove the remaining obligations. Use `gcongr`. Simplify `S.le_opNorm (f n)` using `[hf]`.

Simplify using `using (tendsto_zero_iff_norm_tendsto_zero.1 t1).mul_const ‖S‖`. Simplify using `using a.add b`. Use `resBelow M B β β' k1 k2 u1 u2 ha hc f hf t1 ?_` and prove the remaining obligations. Establish `t4` using `(tendsto_const_nhds (x := (1 : ℝ))).sub ((Complex.continuous_re.tendsto 0).comp t3)`. Simplify using `only [Complex.zero_re, sub_zero] at t4`.

Use `t4.congr fun n => ?_` and prove the remaining obligations. Establish `e1 : ⟪f n, f n⟫_ℂ = 1` using `by rw [inner_self_eq_norm_sq_to_K, hf]; simp`. Rewrite using `[← hS, Function.comp_apply, inner_sub_right, inner_sub_left, sa.isSymmetric.apply_clm, e1]`. Simplify using the standard rewrite rules. Take `⟨c, c0, h1⟩` from `below R fun _ => rfl`.

Take `⟨c', c0', h2⟩` from `below (ContinuousLinearMap.adjoint R) fun x => by`. Rewrite using `[ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, Complex.conj_re]`. Use `set A : H →L[ℂ] H := 1 - Λ ∘L R ∘L Λ with hA`. Establish `anti : AntilipschitzWith ⟨c⁻¹, by positivity⟩ A` using `A.antilipschitz_of_bound fun x => by show ‖x‖ ≤ c⁻¹ * ‖x - Λ (R (Λ x))‖`. Rewrite using `[le_inv_mul_iff₀ c0]`.

Conclude with `h1 x`. Establish `cl : IsClosed (LinearMap.range (A : H →ₗ[ℂ] H) : Set H)` using `anti.isClosed_range A.uniformContinuous`. Establish `bot : (LinearMap.range (A : H →ₗ[ℂ] H))ᗮ = ⊥`. Rewrite using `[Submodule.eq_bot_iff]`. Introduce `y hy`.

Establish `h3 : y - Λ (ContinuousLinearMap.adjoint R (Λ y)) = 0` using `ext_inner_left ℂ fun x => by`. Use `hy (A x) ⟨x, rfl⟩` as an intermediate fact. Rewrite using `[inner_sub_right, ← sa.isSymmetric.apply_clm, ContinuousLinearMap.adjoint_inner_right, ← sa.isSymmetric.apply_clm, ← inner_sub_left, inner_zero_right]`. Conclude with `this`. Use `h2 y` as an intermediate fact.

Rewrite `this` using `[h3, norm_zero]`. Conclude with `norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right this c0')`. Use `haveI := cl.completeSpace_coe`. Conclude with `LinearMap.range_eq_top.1 ((Submodule.orthogonal_eq_bot_iff).1 bot)`.
-/
theorem UpperTheory.V.Z.IntegralApplyAeEq.resInv :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → IsUnit (symb β 0) → IsUnit (symb β' 0) → M.Acts B β β' → IsCompactOperator (M.abelian₂ M.T₀ M.T₀ ∘L B ∘L M.abelian₂ M.T₀ M.T₀) →
      Function.Surjective (1 - M.abelian₂ M.T₀ M.T₀ ∘L M.F.av wR ∘L M.abelian₂ M.T₀ M.T₀ : H →L[ℂ] H) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M B β β' k1 k2 u1 u2 ha hc
  obtain ⟨-, -, l0, sa, ln, -⟩ := (projLaws M).2.2.2.2.2.2.2 M.T₀ M.T₀ (by linarith)
  set Λ := M.abelian₂ M.T₀ M.T₀ with hΛ
  set R := M.F.av wR with hR
  have hΛΛ : ∀ x, Λ (Λ x) = Λ x := fun x => DFunLike.congr_fun l0 x
  have below : ∀ S : H →L[ℂ] H, (∀ x, (⟪x, S x⟫_ℂ).re = (⟪x, R x⟫_ℂ).re) →
      ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖x - Λ (S (Λ x))‖ := by
    intro S hS
    by_contra hcon
    push Not at hcon
    choose x hx using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    have h0 : ∀ n, x n ≠ 0 := fun n h => by simpa [h] using hx n
    let f : ℕ → H := fun n => (‖x n‖⁻¹ : ℂ) • x n
    have hf : ∀ n, ‖f n‖ = 1 := fun n => norm_smul_inv_norm (h0 n)
    have t0 : Tendsto (fun n => f n - Λ (S (Λ (f n)))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      have e : f n - Λ (S (Λ (f n))) = (‖x n‖⁻¹ : ℂ) • (x n - Λ (S (Λ (x n)))) := by simp [f, smul_sub]
      rw [e, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_le_iff₀ (norm_pos_iff.2 (h0 n)), mul_comm]
      exact (hx n).le
    have t1 : Tendsto (fun n => Λ (f n) - f n) atTop (𝓝 0) := by
      have := ((Λ.continuous.tendsto 0).comp t0).sub t0
      simpa [Function.comp_def, hΛΛ] using this
    have t2 : Tendsto (fun n => f n - Λ (S (f n))) atTop (𝓝 0) := by
      have := t0.add (((Λ ∘L S).continuous.tendsto 0).comp t1)
      simpa [Function.comp_def] using this
    have t3 : Tendsto (fun n => ⟪f n, f n - Λ (S (f n))⟫_ℂ + ⟪Λ (f n) - f n, S (f n)⟫_ℂ) atTop (𝓝 0) := by
      have a : Tendsto (fun n => ⟪f n, f n - Λ (S (f n))⟫_ℂ) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n => (norm_inner_le_norm _ _).trans_eq (by rw [hf, one_mul])) (tendsto_zero_iff_norm_tendsto_zero.1 t2)
      have b : Tendsto (fun n => ⟪Λ (f n) - f n, S (f n)⟫_ℂ) atTop (𝓝 0) := by
        refine squeeze_zero_norm (a := fun n => ‖Λ (f n) - f n‖ * ‖S‖) (fun n => (norm_inner_le_norm _ _).trans ?_) ?_
        · gcongr; simpa [hf] using S.le_opNorm (f n)
        · simpa using (tendsto_zero_iff_norm_tendsto_zero.1 t1).mul_const ‖S‖
      simpa using a.add b
    refine resBelow M B β β' k1 k2 u1 u2 ha hc f hf t1 ?_
    have t4 := (tendsto_const_nhds (x := (1 : ℝ))).sub ((Complex.continuous_re.tendsto 0).comp t3)
    simp only [Complex.zero_re, sub_zero] at t4
    refine t4.congr fun n => ?_
    have e1 : ⟪f n, f n⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hf]; simp
    rw [← hS, Function.comp_apply, inner_sub_right, inner_sub_left, sa.isSymmetric.apply_clm, e1]
    simp
  obtain ⟨c, c0, h1⟩ := below R fun _ => rfl
  obtain ⟨c', c0', h2⟩ := below (ContinuousLinearMap.adjoint R) fun x => by
    rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, Complex.conj_re]
  set A : H →L[ℂ] H := 1 - Λ ∘L R ∘L Λ with hA
  have anti : AntilipschitzWith ⟨c⁻¹, by positivity⟩ A := A.antilipschitz_of_bound fun x => by
    show ‖x‖ ≤ c⁻¹ * ‖x - Λ (R (Λ x))‖
    rw [le_inv_mul_iff₀ c0]; exact h1 x
  have cl : IsClosed (LinearMap.range (A : H →ₗ[ℂ] H) : Set H) := anti.isClosed_range A.uniformContinuous
  have bot : (LinearMap.range (A : H →ₗ[ℂ] H))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have h3 : y - Λ (ContinuousLinearMap.adjoint R (Λ y)) = 0 := ext_inner_left ℂ fun x => by
      have := hy (A x) ⟨x, rfl⟩
      rw [inner_sub_right, ← sa.isSymmetric.apply_clm, ContinuousLinearMap.adjoint_inner_right, ← sa.isSymmetric.apply_clm,
        ← inner_sub_left, inner_zero_right]
      exact this
    have := h2 y
    rw [h3, norm_zero] at this
    exact norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right this c0')
  haveI := cl.completeSpace_coe
  exact LinearMap.range_eq_top.1 ((Submodule.orthogonal_eq_bot_iff).1 bot)
