import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ArbitraryA

noncomputable section

open Finset Matrix MeasureTheory
open scoped ContDiff Convolution

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

local instance : ProperSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.proper ℝ _

section Conv

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def arbMulB (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℝ] _).toLinearMap.comp
      (LinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem arbMulB_apply (a b : Matrix (Fin n) (Fin n) ℂ) : arbMulB n a b = a * b := rfl

def arbSharp (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => Formalism.REAL.Jm ε * pᴴ * Formalism.REAL.Jm ε
      map_add' := fun p q => by simp [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r p => by simp [Matrix.conjTranspose_smul] }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem arbSharp_apply (p : Matrix (Fin n) (Fin n) ℂ) :
    arbSharp ε p = Formalism.REAL.Jm ε * pᴴ * Formalism.REAL.Jm ε := rfl

/- English proof (translation)
Rewrite using `[arbSharp_apply]`. Establish `hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1`. Rewrite using `[Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hγ : (Formalism.MainNotions.S.umat γ)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.umat γ = Formalism.REAL.Jm ε` using `γ.2`. Establish `hinv : Formalism.MainNotions.S.umat γ * Formalism.MainNotions.S.umat γ⁻¹ = 1` using `by show ((γ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * (((γ⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1`. Rewrite using `[Subgroup.coe_inv, Units.mul_inv]`. Use `symm`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hinv, Matrix.mul_one]`. Use `_ = Formalism.REAL.Jm ε * ((Formalism.MainNotions.S.umat γ)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat γ⁻¹ := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.MainNotions.S.umat γ⁻¹ := by`.

Rewrite using `[hγ, hJ, Matrix.one_mul]`.
-/
theorem arb_umat_inv (γ : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.umat γ⁻¹ = arbSharp ε (Formalism.MainNotions.S.umat γ) := by
  rw [arbSharp_apply]
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hγ : (Formalism.MainNotions.S.umat γ)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.umat γ = Formalism.REAL.Jm ε := γ.2
  have hinv : Formalism.MainNotions.S.umat γ * Formalism.MainNotions.S.umat γ⁻¹ = 1 := by
    show ((γ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      (((γ⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  symm
  calc Formalism.REAL.Jm ε * (Formalism.MainNotions.S.umat γ)ᴴ * Formalism.REAL.Jm ε
      = Formalism.REAL.Jm ε * (Formalism.MainNotions.S.umat γ)ᴴ * Formalism.REAL.Jm ε * (Formalism.MainNotions.S.umat γ * Formalism.MainNotions.S.umat γ⁻¹) := by
        rw [hinv, Matrix.mul_one]
    _ = Formalism.REAL.Jm ε * ((Formalism.MainNotions.S.umat γ)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat γ⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.MainNotions.S.umat γ⁻¹ := by
        rw [hγ, hJ, Matrix.one_mul]

@[reducible] def arbMS (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _

attribute [local instance] arbMS

local instance : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩

/- English proof (translation)
Establish `hemb : MeasurableEmbedding (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y)` using `(Formalism.REAL.isClosedEmbeddingMatrix n ε).1.measurableEmbedding`. Introduce `x`. Use `⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩` and prove the remaining obligations. Rewrite using `[hemb.integrableOn_map_iff]`. Conclude with `(arb_orbit_cont hσ w).continuousOn.integrableOn_compact ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isCompact_preimage (isCompact_closedBall x 1))`.
-/
theorem arb_locInt (hσ : IsURepOn (UJset ε) σ) (w : H) :
    LocallyIntegrable (fun m : Matrix (Fin n) (Fin n) ℂ => σ m w)
      ((Formalism.REAL.muG ε).map (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y)) := by
  have hemb : MeasurableEmbedding (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.measurableEmbedding
  intro x
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
  rw [hemb.integrableOn_map_iff]
  exact (arb_orbit_cont hσ w).continuousOn.integrableOn_compact
    ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isCompact_preimage (isCompact_closedBall x 1))

/- English proof (translation)
Establish `key` using `contDiffOn_convolution_right_with_param_comp (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (μ := μ) ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] V →L[ℝ] V).flip) (s := (Set.univ : Set P)) (v := fun _ => (0 : E)) contDiffOn_const (f := f) (g := fun p x => Ψ p (-x)) (k := -k) isOpen_univ hk.neg (fun p x _ …`. Rewrite `key` using `[contDiffOn_univ]`. Use `key using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `[MeasureTheory.convolution]`.
-/
theorem arb_param_integral {E P V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [hB : BorelSpace E] [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] {μ : Measure E} {f : E → V} (hf : LocallyIntegrable f μ)
    {Ψ : P → E → ℂ} {k : Set E} (hk : IsCompact k) (hΨ0 : ∀ p x, x ∉ k → Ψ p x = 0)
    (hΨ : ContDiff ℝ ∞ (Function.uncurry Ψ)) : ContDiff ℝ ∞ (fun p => ∫ y, Ψ p y • f y ∂μ) := by
  have key := contDiffOn_convolution_right_with_param_comp (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (μ := μ)
    ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] V →L[ℝ] V).flip) (s := (Set.univ : Set P))
    (v := fun _ => (0 : E)) contDiffOn_const (f := f) (g := fun p x => Ψ p (-x)) (k := -k) isOpen_univ hk.neg
    (fun p x _ hx => hΨ0 p (-x) (by simpa using hx)) hf
    (hΨ.comp (contDiff_fst.prodMk contDiff_snd.neg)).contDiffOn
  rw [contDiffOn_univ] at key
  convert key using 1
  funext p
  simp [MeasureTheory.convolution]

/- English proof (translation)
Unfold `IsSmoothVecU S7.SmoothOnGV`. Introduce `g₀ _`. Use `set K₀ : Set (Matrix (Fin n) (Fin n) ℂ) := (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2) '' (Metric.closedBall g₀ 1 ×ˢ tsupport α) with hK₀`. Establish `hK₀c : IsCompact K₀` using `((isCompact_closedBall g₀ 1).prod hαc.isCompact).image (continuous_fst.matrix_mul continuous_snd)`. Choose the witnesses or unpack the hypotheses as in `⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ K₀ ⊆ Metric.closedBall 0 R := by`.

Take `⟨R, hR⟩` from `hK₀c.isBounded.subset_closedBall 0`. Conclude with `⟨max R 1, by positivity, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩`. Set `χ : ContDiffBump (0 : Matrix (Fin n) (Fin n) ℂ)` to `⟨R, R + 1, hR0, by linarith⟩`. Set `Ψ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℂ` to `fun p y => (χ y : ℂ) * α (arbSharp ε p * y)`. Establish `hΨ : ContDiff ℝ ∞ (Function.uncurry Ψ)`.

Apply `ContDiff.mul` to reduce the goal to its premises. Conclude with `Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp contDiff_snd)`. Conclude with `hα.comp (((arbMulB n).contDiff.comp ((arbSharp ε).contDiff.comp contDiff_fst)).clm_apply contDiff_snd)`. Establish `key : ContDiff ℝ ∞ (fun p => ∫ y, Ψ p y • σ y w ∂((Formalism.REAL.muG ε).map (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y)))` using `arb_param_integral (hB := ⟨rfl⟩) (arb_locInt hσ w) (k := tsupport χ) χ.hasCompactSupport.isCompact (fun p x hx => by`. Establish `: χ x = 0` using `image_eq_zero_of_notMem_tsupport hx`.

Simplify using `[Ψ, this]) hΨ`. Use `⟨Metric.ball g₀ 1, fun p => ∫ y, Ψ p y • σ y w ∂((Formalism.REAL.muG ε).map (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y)), Metric.isOpen_ball, Metric.mem_ball_self one_pos, key.contDiffOn, ?_⟩` and prove the remaining obligations. Introduce `g hg hgU`. Take `⟨γ, rfl⟩` from `arb_exists_umat (ε := ε) hgU`. Use `beta_reduce`.

Rewrite using `[opConv_translate hσ w hα.continuous hαc γ, (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.integral_map]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Use `show α (Formalism.MainNotions.S.umat (γ⁻¹ * y)) • _ = ((χ (Formalism.MainNotions.S.umat y) : ℂ) * α (arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y)) • _`. Establish `e1 : Formalism.MainNotions.S.umat (γ⁻¹ * y) = arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y` using `by show Formalism.MainNotions.S.umat γ⁻¹ * Formalism.MainNotions.S.umat y = _`.

Rewrite using `[arb_umat_inv]`. Rewrite using `[e1]`. Distinguish the cases in `h0 : α (arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y) = 0`. Rewrite using `[h0]`. Simplify using the standard rewrite rules.

Establish `hy : Formalism.MainNotions.S.umat y ∈ K₀`. Use `⟨(Formalism.MainNotions.S.umat γ, arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y), ⟨Metric.ball_subset_closedBall hg, subset_tsupport _ h0⟩, ?_⟩` and prove the remaining obligations. Use `show Formalism.MainNotions.S.umat γ * (arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y) = Formalism.MainNotions.S.umat y`. Rewrite using `[← Matrix.mul_assoc, ← arb_umat_inv]`. Use `show Formalism.MainNotions.S.umat (γ * γ⁻¹) * Formalism.MainNotions.S.umat y = Formalism.MainNotions.S.umat y`.

Rewrite using `[mul_inv_cancel]`. Conclude with `Matrix.one_mul _`. Establish `: χ (Formalism.MainNotions.S.umat y) = 1` using `χ.one_of_mem_closedBall (hR hy)`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem opConv_smooth (hσ : IsURepOn (UJset ε) σ) (w : H) {α : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α) : IsSmoothVecU ε σ (opConv ε σ α w) := by
  unfold IsSmoothVecU S7.SmoothOnGV
  intro g₀ _
  set K₀ : Set (Matrix (Fin n) (Fin n) ℂ) :=
    (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2) ''
      (Metric.closedBall g₀ 1 ×ˢ tsupport α) with hK₀
  have hK₀c : IsCompact K₀ :=
    ((isCompact_closedBall g₀ 1).prod hαc.isCompact).image (continuous_fst.matrix_mul continuous_snd)
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ K₀ ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := hK₀c.isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  let χ : ContDiffBump (0 : Matrix (Fin n) (Fin n) ℂ) := ⟨R, R + 1, hR0, by linarith⟩
  let Ψ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℂ :=
    fun p y => (χ y : ℂ) * α (arbSharp ε p * y)
  have hΨ : ContDiff ℝ ∞ (Function.uncurry Ψ) := by
    apply ContDiff.mul
    · exact Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp contDiff_snd)
    · exact hα.comp
        (((arbMulB n).contDiff.comp ((arbSharp ε).contDiff.comp contDiff_fst)).clm_apply contDiff_snd)
  have key : ContDiff ℝ ∞ (fun p => ∫ y, Ψ p y • σ y w
      ∂((Formalism.REAL.muG ε).map (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y))) :=
    arb_param_integral (hB := ⟨rfl⟩) (arb_locInt hσ w) (k := tsupport χ) χ.hasCompactSupport.isCompact
      (fun p x hx => by
        have : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [Ψ, this]) hΨ
  refine ⟨Metric.ball g₀ 1, fun p => ∫ y, Ψ p y • σ y w
      ∂((Formalism.REAL.muG ε).map (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y)),
    Metric.isOpen_ball, Metric.mem_ball_self one_pos, key.contDiffOn, ?_⟩
  · intro g hg hgU
    obtain ⟨γ, rfl⟩ := arb_exists_umat (ε := ε) hgU
    beta_reduce
    rw [opConv_translate hσ w hα.continuous hαc γ, (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.integral_map]
    congr 1
    funext y
    show α (Formalism.MainNotions.S.umat (γ⁻¹ * y)) • _ =
      ((χ (Formalism.MainNotions.S.umat y) : ℂ) * α (arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y)) • _
    have e1 : Formalism.MainNotions.S.umat (γ⁻¹ * y) = arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y := by
      show Formalism.MainNotions.S.umat γ⁻¹ * Formalism.MainNotions.S.umat y = _
      rw [arb_umat_inv]
    rw [e1]
    by_cases h0 : α (arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y) = 0
    · rw [h0]
      simp
    · have hy : Formalism.MainNotions.S.umat y ∈ K₀ := by
        refine ⟨(Formalism.MainNotions.S.umat γ, arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y),
          ⟨Metric.ball_subset_closedBall hg, subset_tsupport _ h0⟩, ?_⟩
        show Formalism.MainNotions.S.umat γ * (arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y) = Formalism.MainNotions.S.umat y
        rw [← Matrix.mul_assoc, ← arb_umat_inv]
        show Formalism.MainNotions.S.umat (γ * γ⁻¹) * Formalism.MainNotions.S.umat y = Formalism.MainNotions.S.umat y
        rw [mul_inv_cancel]
        exact Matrix.one_mul _
      have : χ (Formalism.MainNotions.S.umat y) = 1 := χ.one_of_mem_closedBall (hR hy)
      rw [this]
      simp

/- English proof (translation)
Set `f : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] H)` to `fun g => (σ g).comp S.subtypeL - S.subtypeL`. Establish `hf : ContinuousOn f (UJset ε)`. Rewrite using `[continuousOn_clm_apply]`. Introduce `y`. Use `ContinuousOn.congr (f := fun x => σ x (y : H) - (y : H)) ((hσ.2.2 (y : H)).sub (continuousOn_const (c := (y : H)))) fun x _ => ?_` and prove the remaining obligations.

Simplify using `[f]`. Establish `h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε` using `arb_umat_mem (1 : Formalism.REAL.UJ ε)`. Establish `hf1 : f 1 = 0`. Use extensionality with `y`. Simplify using `[f, hσ.1.1]`.

Take `⟨δ, hδ, hδf⟩` from `Metric.continuousOn_iff.1 hf 1 h1 (1 / 2) (by norm_num)`. Establish `hclose : ∀ g ∈ UJset ε, ‖g - 1‖ < δ → ∀ w ∈ S, ‖σ g w - w‖ ≤ ‖w‖ / 2`. Introduce `g hg hgd w hw`. Establish `h2` using `hδf g hg (by rwa [dist_eq_norm])`. Rewrite `h2` using `[hf1, dist_zero_right]`.

Establish `h3 : σ g w - w = f g ⟨w, hw⟩` using `by simp [f]`. Rewrite using `[h3]`. Combine the equalities or inequalities in the displayed calculation. Establish `hbc : Continuous (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y))` using `(contDiff_arbB δ).continuous.comp arb_umat_cont`. Establish `hbs : HasCompactSupport (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y))` using `(hasCompactSupport_arbB hδ).comp_isClosedEmbedding (Formalism.REAL.isClosedEmbeddingMatrix n ε).1`.

Use `set c : ℝ := ∫ y, arbB δ (Formalism.MainNotions.S.umat y) ∂(Formalism.REAL.muG ε) with hc`. Establish `hcpos : 0 < c` using `hbc.integral_pos_of_hasCompactSupport_nonneg_nonzero hbs (fun y => arbB_nonneg δ _) (x := (1 : Formalism.REAL.UJ ε)) (arbB_one_pos hδ).ne'`. Establish `hφc : Continuous (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y) / c)` using `hbc.div_const c`. Establish `hφs : HasCompactSupport (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y) / c)` using `((hasCompactSupport_arbB hδ).comp_left (g := fun t : ℝ => t / c) (by simp)).comp_isClosedEmbedding (Formalism.REAL.isClosedEmbeddingMatrix n ε).1`. Establish `hbi : Integrable (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y) / c) (Formalism.REAL.muG ε)` using `hφc.integrable_of_hasCompactSupport hφs`.

Establish `hint1 : ∫ y, arbB δ (Formalism.MainNotions.S.umat y) / c ∂(Formalism.REAL.muG ε) = 1`. Rewrite using `[integral_div, ← hc, div_self hcpos.ne']`. Use `⟨fun g => ((arbB δ g / c : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Complex.ofRealCLM.contDiff.comp ((contDiff_arbB δ).div_const c)`. Conclude with `(hasCompactSupport_arbB hδ).comp_left (g := fun t : ℝ => ((t / c : ℝ) : ℂ)) (by simp)`.

Introduce `k hk g`. Simplify using `only [arbB_conj δ hk g]`. Introduce `w hw`. Establish `hsm : ∀ y : Formalism.REAL.UJ ε, ((arbB δ (Formalism.MainNotions.S.umat y) / c : ℝ) : ℂ) • σ (Formalism.MainNotions.S.umat y) w = (arbB δ (Formalism.MainNotions.S.umat y) / c) • σ (Formalism.MainNotions.S.umat y) w` using `fun y => (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm`. Establish `hi2 : Integrable (fun y : Formalism.REAL.UJ ε => (arbB δ (Formalism.MainNotions.S.umat y) / c) • σ (Formalism.MainNotions.S.umat y) w) (Formalism.REAL.muG ε)` using `(hφc.smul (arb_orbit_cont hσ w)).integrable_of_hasCompactSupport hφs.smul_right`.

Establish `hi3 : Integrable (fun y : Formalism.REAL.UJ ε => (arbB δ (Formalism.MainNotions.S.umat y) / c) • w) (Formalism.REAL.muG ε)` using `hbi.smul_const w`. Establish `e : opConv ε σ (fun g => ((arbB δ g / c : ℝ) : ℂ)) w - w = ∫ y, (arbB δ (Formalism.MainNotions.S.umat y) / c) • (σ (Formalism.MainNotions.S.umat y) w - w) ∂(Formalism.REAL.muG ε)`. Unfold `opConv`. Simplify using `only [hsm]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[integral_smul_const, hint1, one_smul]`. Use `_ = _ := by`. Rewrite using `[← integral_sub hi2 hi3]`. Use `congr 1`. Use function extensionality and compare the values at `y`.

Rewrite using `[smul_sub]`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Use `norm_integral_le_of_norm_le (hbi.mul_const _) (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Establish `hnn : 0 ≤ arbB δ (Formalism.MainNotions.S.umat y) / c` using `div_nonneg (arbB_nonneg δ _) hcpos.le`.

Rewrite using `[norm_smul, Real.norm_of_nonneg hnn]`. Distinguish the cases in `h0 : arbB δ (Formalism.MainNotions.S.umat y) = 0`. Simplify using `[h0]`. Conclude with `mul_le_mul_of_nonneg_left (hclose _ (arb_umat_mem y) (norm_lt_of_arbB_ne hδ h0) w hw) hnn`. Use `_ = ‖w‖ / 2 := by rw [integral_mul_const, hint1, one_mul]`.
-/
theorem exists_good_moll (hσ : IsURepOn (UJset ε) σ) (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    ∃ α : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ IsAdKInv ε α ∧
      ∀ w ∈ S, ‖opConv ε σ α w - w‖ ≤ ‖w‖ / 2 := by
  let f : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] H) := fun g => (σ g).comp S.subtypeL - S.subtypeL
  have hf : ContinuousOn f (UJset ε) := by
    rw [continuousOn_clm_apply]
    intro y
    refine ContinuousOn.congr (f := fun x => σ x (y : H) - (y : H))
      ((hσ.2.2 (y : H)).sub (continuousOn_const (c := (y : H)))) fun x _ => ?_
    simp [f]
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := arb_umat_mem (1 : Formalism.REAL.UJ ε)
  have hf1 : f 1 = 0 := by
    ext y
    simp [f, hσ.1.1]
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousOn_iff.1 hf 1 h1 (1 / 2) (by norm_num)
  have hclose : ∀ g ∈ UJset ε, ‖g - 1‖ < δ → ∀ w ∈ S, ‖σ g w - w‖ ≤ ‖w‖ / 2 := by
    intro g hg hgd w hw
    have h2 := hδf g hg (by rwa [dist_eq_norm])
    rw [hf1, dist_zero_right] at h2
    have h3 : σ g w - w = f g ⟨w, hw⟩ := by simp [f]
    rw [h3]
    calc ‖f g ⟨w, hw⟩‖ ≤ ‖f g‖ * ‖(⟨w, hw⟩ : S)‖ := (f g).le_opNorm _
      _ ≤ (1 / 2) * ‖(⟨w, hw⟩ : S)‖ := mul_le_mul_of_nonneg_right h2.le (norm_nonneg _)
      _ = ‖w‖ / 2 := by rw [show ‖(⟨w, hw⟩ : S)‖ = ‖w‖ from rfl]; ring
  have hbc : Continuous (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y)) :=
    (contDiff_arbB δ).continuous.comp arb_umat_cont
  have hbs : HasCompactSupport (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y)) :=
    (hasCompactSupport_arbB hδ).comp_isClosedEmbedding (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  set c : ℝ := ∫ y, arbB δ (Formalism.MainNotions.S.umat y) ∂(Formalism.REAL.muG ε) with hc
  have hcpos : 0 < c :=
    hbc.integral_pos_of_hasCompactSupport_nonneg_nonzero hbs (fun y => arbB_nonneg δ _)
      (x := (1 : Formalism.REAL.UJ ε)) (arbB_one_pos hδ).ne'
  have hφc : Continuous (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y) / c) := hbc.div_const c
  have hφs : HasCompactSupport (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y) / c) :=
    ((hasCompactSupport_arbB hδ).comp_left (g := fun t : ℝ => t / c) (by simp)).comp_isClosedEmbedding
      (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  have hbi : Integrable (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y) / c) (Formalism.REAL.muG ε) :=
    hφc.integrable_of_hasCompactSupport hφs
  have hint1 : ∫ y, arbB δ (Formalism.MainNotions.S.umat y) / c ∂(Formalism.REAL.muG ε) = 1 := by
    rw [integral_div, ← hc, div_self hcpos.ne']
  refine ⟨fun g => ((arbB δ g / c : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((contDiff_arbB δ).div_const c)
  · exact (hasCompactSupport_arbB hδ).comp_left (g := fun t : ℝ => ((t / c : ℝ) : ℂ)) (by simp)
  · intro k hk g
    simp only [arbB_conj δ hk g]
  · intro w hw
    have hsm : ∀ y : Formalism.REAL.UJ ε, ((arbB δ (Formalism.MainNotions.S.umat y) / c : ℝ) : ℂ) • σ (Formalism.MainNotions.S.umat y) w =
        (arbB δ (Formalism.MainNotions.S.umat y) / c) • σ (Formalism.MainNotions.S.umat y) w := fun y =>
      (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
    have hi2 : Integrable (fun y : Formalism.REAL.UJ ε => (arbB δ (Formalism.MainNotions.S.umat y) / c) • σ (Formalism.MainNotions.S.umat y) w)
        (Formalism.REAL.muG ε) :=
      (hφc.smul (arb_orbit_cont hσ w)).integrable_of_hasCompactSupport hφs.smul_right
    have hi3 : Integrable (fun y : Formalism.REAL.UJ ε => (arbB δ (Formalism.MainNotions.S.umat y) / c) • w) (Formalism.REAL.muG ε) :=
      hbi.smul_const w
    have e : opConv ε σ (fun g => ((arbB δ g / c : ℝ) : ℂ)) w - w =
        ∫ y, (arbB δ (Formalism.MainNotions.S.umat y) / c) • (σ (Formalism.MainNotions.S.umat y) w - w) ∂(Formalism.REAL.muG ε) := by
      unfold opConv
      simp only [hsm]
      calc (∫ y, (arbB δ (Formalism.MainNotions.S.umat y) / c) • σ (Formalism.MainNotions.S.umat y) w ∂(Formalism.REAL.muG ε)) - w
          = (∫ y, (arbB δ (Formalism.MainNotions.S.umat y) / c) • σ (Formalism.MainNotions.S.umat y) w ∂(Formalism.REAL.muG ε)) -
              ∫ y, (arbB δ (Formalism.MainNotions.S.umat y) / c) • w ∂(Formalism.REAL.muG ε) := by
            rw [integral_smul_const, hint1, one_smul]
        _ = _ := by
            rw [← integral_sub hi2 hi3]
            congr 1
            funext y
            rw [smul_sub]
    rw [e]
    calc ‖∫ y, (arbB δ (Formalism.MainNotions.S.umat y) / c) • (σ (Formalism.MainNotions.S.umat y) w - w) ∂(Formalism.REAL.muG ε)‖
        ≤ ∫ y, (arbB δ (Formalism.MainNotions.S.umat y) / c) * (‖w‖ / 2) ∂(Formalism.REAL.muG ε) := by
          refine norm_integral_le_of_norm_le (hbi.mul_const _) (Filter.Eventually.of_forall fun y => ?_)
          have hnn : 0 ≤ arbB δ (Formalism.MainNotions.S.umat y) / c := div_nonneg (arbB_nonneg δ _) hcpos.le
          rw [norm_smul, Real.norm_of_nonneg hnn]
          by_cases h0 : arbB δ (Formalism.MainNotions.S.umat y) = 0
          · simp [h0]
          · exact mul_le_mul_of_nonneg_left
              (hclose _ (arb_umat_mem y) (norm_lt_of_arbB_ne hδ h0) w hw) hnn
      _ = ‖w‖ / 2 := by rw [integral_mul_const, hint1, one_mul]

/- English proof (translation)
Take `⟨α, hαs, hαc, hαK, hS⟩` from `exists_good_moll hσ S`. Conclude with `⟨α, fun v w => opConv_add hσ hαs.continuous hαc v w, fun c v => opConv_smul c v, fun k hk v => opConv_comm_K hσ hαs.continuous hαc hαK hk v, fun v => opConv_smooth hσ v hαs hαc, hS⟩`.
-/
theorem exists_moll_data (hσ : IsURepOn (UJset ε) σ) (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    ∃ α : Matrix (Fin n) (Fin n) ℂ → ℂ,
      (∀ v w : H, opConv ε σ α (v + w) = opConv ε σ α v + opConv ε σ α w) ∧
      (∀ (c : ℂ) (v : H), opConv ε σ α (c • v) = c • opConv ε σ α v) ∧
      (∀ k ∈ Kset ε, ∀ v : H, σ k (opConv ε σ α v) = opConv ε σ α (σ k v)) ∧
      (∀ v : H, IsSmoothVecU ε σ (opConv ε σ α v)) ∧
      ∀ w ∈ S, ‖opConv ε σ α w - w‖ ≤ ‖w‖ / 2 := by
  obtain ⟨α, hαs, hαc, hαK, hS⟩ := exists_good_moll hσ S
  exact ⟨α, fun v w => opConv_add hσ hαs.continuous hαc v w, fun c v => opConv_smul c v,
    fun k hk v => opConv_comm_K hσ hαs.continuous hαc hαK hk v,
    fun v => opConv_smooth hσ v hαs hαc, hS⟩

end Conv

end ReciprocityTheory.ChartRestriction.DS
