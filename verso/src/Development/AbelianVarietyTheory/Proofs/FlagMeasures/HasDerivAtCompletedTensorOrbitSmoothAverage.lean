import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
import Formalism.RealPlaceAnalysis.FinalF

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.AverageDeriv

/- English proof (translation)
Take `⟨-, hmul, hnorm, hcont⟩` from `hσ`. Establish `hcw : Continuous fun g => σ g w` using `hcont w`. Establish `key : ∀ t, σ (a t) (∫ g, f g • σ g w ∂μ) = ∫ g, f ((a t)⁻¹ * g) • σ g w ∂μ`. Introduce `t`. Establish `hint : Integrable (fun g => f g • σ g w) μ` using `(hf.smul hcw).integrable_of_hasCompactSupport (hfc.smul_right)`.

Rewrite using `[← (σ (a t)).integral_comp_comm hint]`. Rewrite using `[← integral_mul_left_eq_self (fun g => f ((a t)⁻¹ * g) • σ g w) (a t)]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[map_smul, inv_mul_cancel_left, hmul]`.

Both sides reduce to the same expression. Take `⟨C, hC⟩` from `hf'.bounded_above_of_compact_support hfc'`. Use `set K : Set G := (fun p : ℝ × G => a p.1 * p.2) '' (Set.Icc (-1 : ℝ) 1 ×ˢ tsupport f') with hK`. Establish `hKc : IsCompact K` using `(isCompact_Icc.prod hfc').image ((ha.comp continuous_fst).mul continuous_snd)`. Establish `hsupp : ∀ s ∈ Metric.ball (0 : ℝ) 1, ∀ g, g ∉ K → f' ((a s)⁻¹ * g) = 0`.

Introduce `s hs g hg`. Assume the negation of the conclusion as `h`. Apply `hg` to reduce the goal to its premises. Use `⟨(s, (a s)⁻¹ * g), ⟨?_, subset_tsupport _ h⟩, by simp⟩` and prove the remaining obligations. Rewrite `hs` using `[Real.ball_eq_Ioo, zero_sub, zero_add]`.

Conclude with `Set.Ioo_subset_Icc_self hs`. Establish `hbound_int : Integrable (K.indicator fun _ => C * ‖w‖) μ` using `(continuousOn_const.integrableOn_compact hKc).integrable_indicator hKc.isClosed.measurableSet`. Establish `hcont_tr : ∀ (k : G → ℂ), Continuous k → ∀ s : ℝ, Continuous fun g => k ((a s)⁻¹ * g) • σ g w` using `fun k hk s => (hk.comp (continuous_const.mul continuous_id)).smul hcw`. Establish `hder` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ)) (F := fun s g => f ((a s)⁻¹ * g) • σ g w) (F' := fun s g => f' ((a s)⁻¹ * g) • σ g w) (bound := K.indicator fun _ => C * ‖w‖) (Metric.ball_mem_nhds 0 one_pos) (Filter.Eventually.of_forall fun s => (hcont_tr …`. Simplify using `only [ha0, inv_one, one_mul]`.

Conclude with `(hf.smul hcw).integrable_of_hasCompactSupport (hfc.smul_right))`. Use the proof step `(hcont_tr f' hf' 0).aestronglyMeasurable`. Use the proof step `(Filter.Eventually.of_forall fun g s hs => by`. Distinguish the cases in `hg : g ∈ K`. Rewrite using `[Set.indicator_of_mem hg, norm_smul, hnorm]`.

Conclude with `mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)`. Rewrite using `[Set.indicator_of_notMem hg, hsupp s hs g hg, zero_smul, norm_zero])`. Use `hbound_int`. Use the proof step `(Filter.Eventually.of_forall fun g s _ => (hd g s).smul_const (σ g w))`. Establish `hfun : (fun t => σ (a t) (∫ g, f g • σ g w ∂μ)) = fun t => ∫ g, f ((a t)⁻¹ * g) • σ g w ∂μ`.

Use function extensionality and compare the values at `key`. Rewrite using `[hfun]`. Simplify `hder.2` using `only [ha0, inv_one, one_mul]`.
-/
theorem hasDerivAt_average {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : G → (H →L[ℂ] H)} (hσ : IsURep σ) (w : H) {a : ℝ → G} (ha : Continuous a) (ha0 : a 0 = 1)
    {f f' : G → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (hf' : Continuous f')
    (hfc' : HasCompactSupport f')
    (hd : ∀ g t, HasDerivAt (fun s => f ((a s)⁻¹ * g)) (f' ((a t)⁻¹ * g)) t) :
    HasDerivAt (fun t => σ (a t) (∫ g, f g • σ g w ∂μ)) (∫ g, f' g • σ g w ∂μ) 0 := by
  obtain ⟨-, hmul, hnorm, hcont⟩ := hσ
  have hcw : Continuous fun g => σ g w := hcont w

  have key : ∀ t, σ (a t) (∫ g, f g • σ g w ∂μ) = ∫ g, f ((a t)⁻¹ * g) • σ g w ∂μ := by
    intro t
    have hint : Integrable (fun g => f g • σ g w) μ :=
      (hf.smul hcw).integrable_of_hasCompactSupport (hfc.smul_right)
    rw [← (σ (a t)).integral_comp_comm hint]
    rw [← integral_mul_left_eq_self (fun g => f ((a t)⁻¹ * g) • σ g w) (a t)]
    congr 1
    funext g
    rw [map_smul, inv_mul_cancel_left, hmul]
    rfl

  obtain ⟨C, hC⟩ := hf'.bounded_above_of_compact_support hfc'
  set K : Set G := (fun p : ℝ × G => a p.1 * p.2) '' (Set.Icc (-1 : ℝ) 1 ×ˢ tsupport f') with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod hfc').image ((ha.comp continuous_fst).mul continuous_snd)
  have hsupp : ∀ s ∈ Metric.ball (0 : ℝ) 1, ∀ g, g ∉ K → f' ((a s)⁻¹ * g) = 0 := by
    intro s hs g hg
    by_contra h
    apply hg
    refine ⟨(s, (a s)⁻¹ * g), ⟨?_, subset_tsupport _ h⟩, by simp⟩
    rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hs
    exact Set.Ioo_subset_Icc_self hs
  have hbound_int : Integrable (K.indicator fun _ => C * ‖w‖) μ :=
    (continuousOn_const.integrableOn_compact hKc).integrable_indicator hKc.isClosed.measurableSet
  have hcont_tr : ∀ (k : G → ℂ), Continuous k → ∀ s : ℝ, Continuous fun g => k ((a s)⁻¹ * g) • σ g w :=
    fun k hk s => (hk.comp (continuous_const.mul continuous_id)).smul hcw
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun s g => f ((a s)⁻¹ * g) • σ g w) (F' := fun s g => f' ((a s)⁻¹ * g) • σ g w)
    (bound := K.indicator fun _ => C * ‖w‖) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun s => (hcont_tr f hf s).aestronglyMeasurable)
    (by
      simp only [ha0, inv_one, one_mul]
      exact (hf.smul hcw).integrable_of_hasCompactSupport (hfc.smul_right))
    (hcont_tr f' hf' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g s hs => by
      by_cases hg : g ∈ K
      · rw [Set.indicator_of_mem hg, norm_smul, hnorm]
        exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
      · rw [Set.indicator_of_notMem hg, hsupp s hs g hg, zero_smul, norm_zero])
    hbound_int
    (Filter.Eventually.of_forall fun g s _ => (hd g s).smul_const (σ g w))
  have hfun : (fun t => σ (a t) (∫ g, f g • σ g w ∂μ)) = fun t => ∫ g, f ((a t)⁻¹ * g) • σ g w ∂μ :=
    funext key
  rw [hfun]
  simpa only [ha0, inv_one, one_mul] using hder.2

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `(uMat_expU _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem expU_zero {n : ℕ} {ε : Fin n → Bool} : expU (0 : gLie ε) = 1 := by
  apply Subtype.ext
  apply Units.ext
  refine (uMat_expU _).trans ?_
  simp

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `(uMat_expU _).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg₂ (· * ·) (uMat_expU (a • X)).symm (uMat_expU (b • X)).symm)` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, add_smul]`.

Conclude with `Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left a).smul_right b)`.
-/
theorem expU_add {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (a b : ℝ) :
    expU ((a + b) • X) = expU (a • X) * expU (b • X) := by
  apply Subtype.ext
  apply Units.ext
  refine (uMat_expU _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (uMat_expU (a • X)).symm (uMat_expU (b • X)).symm)
  rw [Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left a).smul_right b)

/- English proof (translation)
Use `inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[← expU_add, add_neg_cancel, zero_smul, expU_zero]`.
-/
theorem expU_inv {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (t : ℝ) : (expU (t • X))⁻¹ = expU ((-t) • X) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← expU_add, add_neg_cancel, zero_smul, expU_zero]

/- English proof (translation)
Establish `hcexp : ∀ A : Matrix (Fin n) (Fin n) ℂ, Continuous fun t : ℝ => NormedSpace.exp (t • A)`. Introduce `A`. Use `letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra`. Conclude with `(differentiable_exp_smul_const ℝ A).continuous`.

Apply `Continuous.subtype_mk` to reduce the goal to its premises. Rewrite using `[Units.continuous_iff]`. Prove the components needed by the constructor for the conclusion. Establish `e : (fun t : ℝ => (((expU (t • X) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) = fun t : ℝ => NormedSpace.exp (t • X.1)`. Use function extensionality and compare the values at `t`.

Rewrite using `[← Submodule.coe_smul]`. Conclude with `uMat_expU (t • X)`. Establish `h` using `hcexp X.1`. Rewrite `h` using `[← e]`. Conclude with `h`.

Establish `e : (fun t : ℝ => ((((expU (t • X) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) = fun t : ℝ => NormedSpace.exp (t • (-X.1))`. Use function extensionality and compare the values at `t`. Establish `h1` using `congrArg (fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) (expU_inv X t)`. Use `h1.trans ((uMat_expU _).trans ?_)` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, neg_smul, smul_neg]`.

Establish `h` using `hcexp (-X.1)`. Rewrite `h` using `[← e]`. Conclude with `h`.
-/
theorem continuous_expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : Continuous fun t : ℝ => expU (t • X) := by
  have hcexp : ∀ A : Matrix (Fin n) (Fin n) ℂ, Continuous fun t : ℝ => NormedSpace.exp (t • A) := by
    intro A
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    exact (differentiable_exp_smul_const ℝ A).continuous
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · have e : (fun t : ℝ => (((expU (t • X) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = fun t : ℝ => NormedSpace.exp (t • X.1) := by
      funext t
      rw [← Submodule.coe_smul]
      exact uMat_expU (t • X)
    have h := hcexp X.1
    rw [← e] at h
    exact h
  · have e : (fun t : ℝ => ((((expU (t • X) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ :
        (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
        fun t : ℝ => NormedSpace.exp (t • (-X.1)) := by
      funext t
      have h1 := congrArg (fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) (expU_inv X t)
      refine h1.trans ((uMat_expU _).trans ?_)
      rw [Submodule.coe_smul, neg_smul, smul_neg]
    have h := hcexp (-X.1)
    rw [← e] at h
    exact h

/- English proof (translation)
Use `letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra`. Establish `h` using `(hasDerivAt_exp_smul_const' (𝕂 := ℝ) X t).mul_const Y`. Set `l : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ` to `{ toFun := fun M => M i j map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `h2` using `(LinearMap.toContinuousLinearMap l).hasFDerivAt.comp_hasDerivAt t h`.

Establish `h3 : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) * Y) i j) ((X * NormedSpace.exp (t • X) * Y) i j) t` using `h2`. Rewrite using `[← mul_assoc]`. Conclude with `h3`.
-/
theorem hasDerivAt_exp_mul_entry {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) * Y) i j) ((X * (NormedSpace.exp (t • X) * Y)) i j) t := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X t).mul_const Y
  let l : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h2 := (LinearMap.toContinuousLinearMap l).hasFDerivAt.comp_hasDerivAt t h
  have h3 : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) * Y) i j)
      ((X * NormedSpace.exp (t • X) * Y) i j) t := h2
  rw [← mul_assoc]
  exact h3

/- English proof (translation)
Rewrite using `[expU_inv]`. Use `show uMat (expU ((-t) • X)) * uMat g = _`. Rewrite using `[uMat_expU, Submodule.coe_smul, neg_smul, smul_neg]`.
-/
theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (t : ℝ) (g : UJ ε) :
    uMat ((expU (t • X))⁻¹ * g) = NormedSpace.exp (t • (-X.1)) * uMat g := by
  rw [expU_inv]
  show uMat (expU ((-t) • X)) * uMat g = _
  rw [uMat_expU, Submodule.coe_smul, neg_smul, smul_neg]

/- English proof (translation)
Introduce `B F E w hσ hF hFc`. Establish `hμ : muInf B.I = Measure.pi (fun v => Formalism.REAL.muG (B.I.ε v))` using `rfl`. Use `haveI : (muInf B.I).IsMulLeftInvariant := by rw [hμ]; infer_instance`. Use `haveI : IsFiniteMeasureOnCompacts (muInf B.I) := by rw [hμ]; infer_instance`. Set `c : B.I.Ginf → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ)` to `fun g v i j => uMat (g v) i j`.

Establish `hc : Topology.IsClosedEmbedding c` using `Topology.IsClosedEmbedding.piMap fun v => (Formalism.REAL.isClosedEmbeddingMatrix B.I.n (B.I.ε v)).1`. Set `Lm : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) →ₗ[ℝ] (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ)` to `{ toFun := fun M v i j => ∑ k, (-(E v).1) i k * M v k j map_add' := by`. Introduce `M N`. Use function extensionality and compare the values at `v i j`. Simplify using `[mul_add, Finset.sum_add_distrib]`.

Use the proof step `map_smul' := by`. Introduce `r M`. Use function extensionality and compare the values at `v i j`. Simplify using `only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _ }`.

Set `L` to `LinearMap.toContinuousLinearMap Lm`. Set `F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ` to `fun M => fderiv ℝ F M (L M)`. Establish `hF's : ContDiff ℝ ∞ F'` using `(contDiff_infty_iff_fderiv.1 hF).2.clm_apply L.contDiff`. Establish `hF'c : HasCompactSupport F'`. Use `(hFc.fderiv (𝕜 := ℝ)).mono' fun M hM => subset_tsupport _ ?_` and prove the remaining obligations.

Introduce `h0`. Apply `hM` to reduce the goal to its premises. Use `show fderiv ℝ F M (L M) = 0`. Rewrite using `[h0]`. Both sides reduce to the same expression.

Use `⟨F', hF's, hF'c, ?_⟩` and prove the remaining obligations. Set `a : ℝ → B.I.Ginf` to `fun t v => expU (t • E v)`. Establish `ha : Continuous a` using `continuous_pi fun v => continuous_expU (E v)`. Establish `ha0 : a 0 = 1`. Use function extensionality and compare the values at `v`.

Use `show expU ((0 : ℝ) • E v) = 1`. Rewrite using `[zero_smul, expU_zero]`. Establish `hcc : Continuous c` using `hc.continuous`. Establish `hd : ∀ g t, HasDerivAt (fun s => F (c ((a s)⁻¹ * g))) (F' (c ((a t)⁻¹ * g))) t`. Introduce `g t`.

Set `p : ℝ → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ)` to `fun s v i j => (NormedSpace.exp (s • (-(E v).1)) * uMat (g v)) i j`. Establish `hp : ∀ s, c ((a s)⁻¹ * g) = p s`. Introduce `s`. Use function extensionality and compare the values at `v i j`. Use `show uMat ((expU (s • E v))⁻¹ * g v) i j = _`.

Rewrite using `[uMat_inv_mul]`. Establish `hp' : HasDerivAt p (L (p t)) t`. Use `hasDerivAt_pi.2 fun v => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_` and prove the remaining obligations. Apply the tactic sequence `exact hasDerivAt_exp_mul_entry _ _ t i j`. Establish `hFd : HasFDerivAt F (fderiv ℝ F (p t)) (p t)` using `(hF.differentiable (by simp)).differentiableAt.hasFDerivAt`.

Establish `h` using `hFd.comp_hasDerivAt t hp'`. Simplify using `only [hp]`. Conclude with `h`. Establish `main` using `hasDerivAt_average (muInf B.I) hσ w (a := a) ha ha0 (f := fun g => F (c g)) (f' := fun g => F' (c g)) (hF.continuous.comp hcc) (hFc.comp_isClosedEmbedding hc) (hF's.continuous.comp hcc) (hF'c.comp_isClosedEmbedding hc) hd`. Conclude with `main`.
-/
theorem hasDerivAt_orbit_average : ∀ (B : RowsAut) (F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (E : gInf B) (w : B.Hs), IsURep B.σs → ContDiff ℝ ∞ F → HasCompactSupport F → ∃ F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F' ∧ HasCompactSupport F' ∧ HasDerivAt (orbit B E (∫ g, F (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I))) (∫ g, F' (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I)) 0 := by
  intro B F E w hσ hF hFc

  have hμ : muInf B.I = Measure.pi (fun v => Formalism.REAL.muG (B.I.ε v)) := rfl
  haveI : (muInf B.I).IsMulLeftInvariant := by rw [hμ]; infer_instance
  haveI : IsFiniteMeasureOnCompacts (muInf B.I) := by rw [hμ]; infer_instance
  let c : B.I.Ginf → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
    fun g v i j => uMat (g v) i j
  have hc : Topology.IsClosedEmbedding c :=
    Topology.IsClosedEmbedding.piMap fun v => (Formalism.REAL.isClosedEmbeddingMatrix B.I.n (B.I.ε v)).1

  let Lm : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) →ₗ[ℝ]
      (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
    { toFun := fun M v i j => ∑ k, (-(E v).1) i k * M v k j
      map_add' := by
        intro M N
        funext v i j
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r M
        funext v i j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _ }
  let L := LinearMap.toContinuousLinearMap Lm
  let F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ := fun M => fderiv ℝ F M (L M)
  have hF's : ContDiff ℝ ∞ F' := (contDiff_infty_iff_fderiv.1 hF).2.clm_apply L.contDiff
  have hF'c : HasCompactSupport F' := by
    refine (hFc.fderiv (𝕜 := ℝ)).mono' fun M hM => subset_tsupport _ ?_
    intro h0
    apply hM
    show fderiv ℝ F M (L M) = 0
    rw [h0]
    rfl
  refine ⟨F', hF's, hF'c, ?_⟩
  let a : ℝ → B.I.Ginf := fun t v => expU (t • E v)
  have ha : Continuous a := continuous_pi fun v => continuous_expU (E v)
  have ha0 : a 0 = 1 := by
    funext v
    show expU ((0 : ℝ) • E v) = 1
    rw [zero_smul, expU_zero]
  have hcc : Continuous c := hc.continuous
  have hd : ∀ g t, HasDerivAt (fun s => F (c ((a s)⁻¹ * g))) (F' (c ((a t)⁻¹ * g))) t := by
    intro g t
    let p : ℝ → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
      fun s v i j => (NormedSpace.exp (s • (-(E v).1)) * uMat (g v)) i j
    have hp : ∀ s, c ((a s)⁻¹ * g) = p s := by
      intro s
      funext v i j
      show uMat ((expU (s • E v))⁻¹ * g v) i j = _
      rw [uMat_inv_mul]
    have hp' : HasDerivAt p (L (p t)) t := by
      refine hasDerivAt_pi.2 fun v => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
      exact hasDerivAt_exp_mul_entry _ _ t i j
    have hFd : HasFDerivAt F (fderiv ℝ F (p t)) (p t) :=
      (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
    have h := hFd.comp_hasDerivAt t hp'
    simp only [hp]
    exact h
  have main := hasDerivAt_average (muInf B.I) hσ w (a := a) ha ha0 (f := fun g => F (c g))
    (f' := fun g => F' (c g)) (hF.continuous.comp hcc) (hFc.comp_isClosedEmbedding hc)
    (hF's.continuous.comp hcc) (hF'c.comp_isClosedEmbedding hc) hd
  exact main

end GlobalTheory.AverageDeriv
