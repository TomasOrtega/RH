import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.TwistedTraces.NormExpSmulSubLeNormDerivOp

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

/- English proof (translation)
Introduce `𝔸 _ _ _ _ G 𝔤 h d b C`. Set `T : 𝔤 →ₗ[ℝ] h.lieSubalgebra` to `{ toFun := h.toLie, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Set `S : h.lieSubalgebra →ₗ[ℝ] 𝔤` to `{ toFun := h.ofLie, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `hST : ∀ X : 𝔤, S (T X) = X` using `fun _ => rfl`. Set `f : 𝔤 → ℝ` to `fun X => (∑ i, |b.repr (h.toLie X) i|) * |C|`.

Establish `hf : Continuous f`. Use `Continuous.mul (continuous_finset_sum _ fun i _ => ?_) continuous_const` and prove the remaining obligations. Conclude with `(LinearMap.continuous_of_finiteDimensional ((b.coord i) ∘ₗ T)).abs`. Establish `hf0 : f 0 = 0`. Establish `: h.toLie 0 = 0` using `rfl`.

Simplify using `[f, this]`. Establish `hO : {X : 𝔤 | f X < 1 / 2} ∈ 𝓝 (0 : 𝔤)` using `(isOpen_lt hf continuous_const).mem_nhds (by simp [hf0])`. Establish `h0 : (0 : 𝔤) ∈ (h.chart 1).symm.source` using `h.zero_mem_nhd`. Establish `hexp0 : h.expG 0 = 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `[IsExpLieAlgebra.coe_expG]`. Use `⟨h.expG '' {X : 𝔤 | f X < 1 / 2}, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `(h.chart 1).symm.image_mem_nhds h0 hO`. Establish `e1 : (h.chart 1).symm 0 = 1` using `by show 1 * h.expG 0 = 1`.

Rewrite using `[hexp0, one_mul]`. Rewrite `h1` using `[e1]`. Use `Filter.mem_of_superset h1 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨X, hX, rfl⟩`. Use `⟨X, hX, ?_⟩` and prove the remaining obligations.

Use `show h.expG X = 1 * h.expG X`. Rewrite using `[one_mul]`. Introduce and unpack `E _ _ π v hπ hv hb _ ⟨X, hX, rfl⟩`. Use `(UpperTheory.norm_exp_smul_sub_le_norm_derivOp 𝔸 G 𝔤 h E π v X hπ hv).trans ?_` and prove the remaining obligations. Establish `hsum : X = ∑ i, b.repr (h.toLie X) i • h.ofLie (b i)` using `by conv_lhs => rw [← hST X] show S (h.toLie X) = _ conv_lhs => rw [← b.sum_repr (h.toLie X)]`.

Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => map_smul S _ _`. Establish `hD : h.derivOp π X v = ∑ i, b.repr (h.toLie X) i • h.derivOp π (h.ofLie (b i)) v` using `by show fderiv ℝ (h.expOrbit π v) 0 X = ∑ i, b.repr (h.toLie X) i • fderiv ℝ (h.expOrbit π v) 0 (h.ofLie (b i)) conv_lhs => rw [hsum]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => map_smul _ _ _`.

Establish `hbound : ‖h.derivOp π X v‖ ≤ f X * ‖v‖`. Rewrite using `[hD]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Simplify using `only [f, Finset.sum_mul]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[norm_smul, Real.norm_eq_abs, mul_assoc]`. Use `mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)` and prove the remaining obligations. Conclude with `(hb i).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg v))`. Conclude with `hbound.trans (mul_le_mul_of_nonneg_right (le_of_lt hX) (norm_nonneg v))`.
-/
theorem UpperTheory.exists_nhds_displacement_le_half_of_derivOp_bound :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ h.lieSubalgebra) (C : ℝ), ∃ N ∈ 𝓝 (1 : G), ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (v : E), (∀ g w, ‖π g w‖ = ‖w‖) → h.IsSmoothVector π v → (∀ i, ‖h.derivOp π (h.ofLie (b i)) v‖ ≤ C * ‖v‖) → ∀ a ∈ N, ‖π a v - v‖ ≤ 1 / 2 * ‖v‖ := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b C
  let T : 𝔤 →ₗ[ℝ] h.lieSubalgebra :=
    { toFun := h.toLie, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let S : h.lieSubalgebra →ₗ[ℝ] 𝔤 :=
    { toFun := h.ofLie, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hST : ∀ X : 𝔤, S (T X) = X := fun _ => rfl
  let f : 𝔤 → ℝ := fun X => (∑ i, |b.repr (h.toLie X) i|) * |C|
  have hf : Continuous f := by
    refine Continuous.mul (continuous_finset_sum _ fun i _ => ?_) continuous_const
    exact (LinearMap.continuous_of_finiteDimensional ((b.coord i) ∘ₗ T)).abs
  have hf0 : f 0 = 0 := by
    have : h.toLie 0 = 0 := rfl
    simp [f, this]
  have hO : {X : 𝔤 | f X < 1 / 2} ∈ 𝓝 (0 : 𝔤) :=
    (isOpen_lt hf continuous_const).mem_nhds (by simp [hf0])
  have h0 : (0 : 𝔤) ∈ (h.chart 1).symm.source := h.zero_mem_nhd
  have hexp0 : h.expG 0 = 1 := by
    apply Subtype.ext; apply Units.ext
    simp [IsExpLieAlgebra.coe_expG]
  refine ⟨h.expG '' {X : 𝔤 | f X < 1 / 2}, ?_, ?_⟩
  · have h1 := (h.chart 1).symm.image_mem_nhds h0 hO
    have e1 : (h.chart 1).symm 0 = 1 := by
      show 1 * h.expG 0 = 1
      rw [hexp0, one_mul]
    rw [e1] at h1
    refine Filter.mem_of_superset h1 ?_
    rintro _ ⟨X, hX, rfl⟩
    refine ⟨X, hX, ?_⟩
    show h.expG X = 1 * h.expG X
    rw [one_mul]
  · rintro E _ _ π v hπ hv hb _ ⟨X, hX, rfl⟩
    refine (UpperTheory.norm_exp_smul_sub_le_norm_derivOp 𝔸 G 𝔤 h E π v X hπ hv).trans ?_
    have hsum : X = ∑ i, b.repr (h.toLie X) i • h.ofLie (b i) := by
      conv_lhs => rw [← hST X]
      show S (h.toLie X) = _
      conv_lhs => rw [← b.sum_repr (h.toLie X)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul S _ _
    have hD : h.derivOp π X v =
        ∑ i, b.repr (h.toLie X) i • h.derivOp π (h.ofLie (b i)) v := by
      show fderiv ℝ (h.expOrbit π v) 0 X = ∑ i, b.repr (h.toLie X) i •
        fderiv ℝ (h.expOrbit π v) 0 (h.ofLie (b i))
      conv_lhs => rw [hsum]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    have hbound : ‖h.derivOp π X v‖ ≤ f X * ‖v‖ := by
      rw [hD]
      refine (norm_sum_le _ _).trans ?_
      simp only [f, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact (hb i).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg v))
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_of_lt hX) (norm_nonneg v))
