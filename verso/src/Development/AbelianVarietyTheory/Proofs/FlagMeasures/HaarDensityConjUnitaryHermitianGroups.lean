import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheoremStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DensityInChartStatement

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AdDens

/- English proof (translation)
Set `b` to `stdOrthonormalBasis ℝ V`. Rewrite using `[← LinearMap.det_toMatrix b.toBasis A, ← LinearMap.det_toMatrix b.toBasis (LinearMap.adjoint A), LinearMap.toMatrix_adjoint b b A, Matrix.det_conjTranspose, star_trivial]`.
-/
theorem det_adjoint' {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (A : V →ₗ[ℝ] V) : LinearMap.det (LinearMap.adjoint A) = LinearMap.det A := by
  classical
  let b := stdOrthonormalBasis ℝ V
  rw [← LinearMap.det_toMatrix b.toBasis A, ← LinearMap.det_toMatrix b.toBasis (LinearMap.adjoint A),
    LinearMap.toMatrix_adjoint b b A, Matrix.det_conjTranspose, star_trivial]

/- English proof (translation)
Establish `hfin : Module.finrank ℝ V = Module.finrank ℝ W` using `L.finrank_eq`. Set `e : V ≃ₗᵢ[ℝ] W` to `(stdOrthonormalBasis ℝ V).equiv (stdOrthonormalBasis ℝ W) (finCongr hfin)`. Set `M : V →ₗ[ℝ] V` to `e.symm.toLinearEquiv.toLinearMap ∘ₗ L.toLinearMap`. Set `T : V →ₗ[ℝ] V` to `e.symm.toLinearEquiv.toLinearMap ∘ₗ τ ∘ₗ e.toLinearEquiv.toLinearMap`. Establish `hM : ∀ x, e (M x) = L x` using `fun x => by simp [M]`.

Establish `hT : ∀ x, e (T x) = τ (e x)` using `fun x => by simp [T]`. Establish `key : LinearMap.adjoint M ∘ₗ T ∘ₗ M = σ`. Use `LinearMap.ext fun x => ext_inner_right ℝ fun y => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.comp_apply, ← LinearIsometryEquiv.inner_map_map e, hT, hM, hM, h]`. Establish `hsq : ∀ f : V →ₗ[ℝ] V, (∀ x, f (f x) = x) → LinearMap.det f ^ 2 = 1`.

Introduce `f hf`. Establish `: f ∘ₗ f = LinearMap.id` using `LinearMap.ext hf`. Rewrite using `[sq, ← LinearMap.det_comp, this, LinearMap.det_id]`. Establish `hT2 : ∀ x, T (T x) = x` using `fun x => e.injective (by rw [hT, hT, hτ])`. Establish `hdet : |LinearMap.det M| = 1`.

Establish `h1` using `congrArg LinearMap.det key`. Rewrite `h1` using `[LinearMap.det_comp, LinearMap.det_comp, det_adjoint']`. Establish `h4 : |LinearMap.det M| ^ 4 = 1`. Establish `hs` using `hsq σ hσ`. Establish `ht` using `hsq T hT2`.

Rewrite `hs` using `[← h1]`. Rewrite using `[pow_abs, abs_eq_self.mpr (by positivity)]`. Use polynomial arithmetic with `[hs, ht]`. Conclude with `(pow_eq_one_iff_of_nonneg (abs_nonneg _) (by norm_num)).mp h4`. Establish `himg : L '' s = e '' (M '' s)`.

Rewrite using `[Set.image_image]`. Conclude with `Set.image_congr fun x _ => (hM x).symm`. Rewrite using `[himg, LinearIsometryEquiv.image_eq_preimage_symm, e.symm.measurePreserving.measure_preimage_emb e.symm.toHomeomorph.measurableEmbedding, MeasureTheory.Measure.addHaar_image_linearMap, hdet, ENNReal.ofReal_one, one_mul]`.
-/
theorem volume_image_eq {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    (L : V ≃ₗ[ℝ] W) (σ : V →ₗ[ℝ] V) (τ : W →ₗ[ℝ] W) (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x)
    (h : ∀ x y, ⟪τ (L x), L y⟫_ℝ = ⟪σ x, y⟫_ℝ) (s : Set V) : volume (L '' s) = volume s := by
  classical
  have hfin : Module.finrank ℝ V = Module.finrank ℝ W := L.finrank_eq
  let e : V ≃ₗᵢ[ℝ] W := (stdOrthonormalBasis ℝ V).equiv (stdOrthonormalBasis ℝ W) (finCongr hfin)
  let M : V →ₗ[ℝ] V := e.symm.toLinearEquiv.toLinearMap ∘ₗ L.toLinearMap
  let T : V →ₗ[ℝ] V := e.symm.toLinearEquiv.toLinearMap ∘ₗ τ ∘ₗ e.toLinearEquiv.toLinearMap
  have hM : ∀ x, e (M x) = L x := fun x => by simp [M]
  have hT : ∀ x, e (T x) = τ (e x) := fun x => by simp [T]

  have key : LinearMap.adjoint M ∘ₗ T ∘ₗ M = σ := by
    refine LinearMap.ext fun x => ext_inner_right ℝ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.comp_apply,
      ← LinearIsometryEquiv.inner_map_map e, hT, hM, hM, h]
  have hsq : ∀ f : V →ₗ[ℝ] V, (∀ x, f (f x) = x) → LinearMap.det f ^ 2 = 1 := by
    intro f hf
    have : f ∘ₗ f = LinearMap.id := LinearMap.ext hf
    rw [sq, ← LinearMap.det_comp, this, LinearMap.det_id]
  have hT2 : ∀ x, T (T x) = x := fun x => e.injective (by rw [hT, hT, hτ])
  have hdet : |LinearMap.det M| = 1 := by
    have h1 := congrArg LinearMap.det key
    rw [LinearMap.det_comp, LinearMap.det_comp, det_adjoint'] at h1
    have h4 : |LinearMap.det M| ^ 4 = 1 := by
      have hs := hsq σ hσ
      have ht := hsq T hT2
      rw [← h1] at hs
      rw [pow_abs, abs_eq_self.mpr (by positivity)]
      nlinarith [hs, ht]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by norm_num)).mp h4
  have himg : L '' s = e '' (M '' s) := by
    rw [Set.image_image]; exact Set.image_congr fun x _ => (hM x).symm
  rw [himg, LinearIsometryEquiv.image_eq_preimage_symm,
    e.symm.measurePreserving.measure_preimage_emb e.symm.toHomeomorph.measurableEmbedding,
    MeasureTheory.Measure.addHaar_image_linearMap, hdet, ENNReal.ofReal_one, one_mul]

abbrev EE (m : ℕ) := EuclideanSpace ℝ (Fin m × Fin m × Bool)

def rl (m : ℕ) : Matrix (Fin m) (Fin m) ℂ ≃ₗ[ℝ] EE m where
  toFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  invFun := unrealify
  map_add' X Y := by
    ext ⟨i, j, b⟩; cases b <;> simp [realifyFun]
  map_smul' t X := by
    ext ⟨i, j, b⟩; cases b <;> simp [realifyFun]
  left_inv X := by
    ext i j; apply Complex.ext <;> simp [realifyFun, unrealify]
  right_inv x := by
    ext ⟨i, j, b⟩; cases b <;> simp [realifyFun, unrealify]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rl_symm {m : ℕ} (x : EE m) : (rl m).symm x = unrealify x := rfl

/- English proof (translation)
Simplify using `only [rl, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply, Fintype.sum_prod_type, Fintype.sum_bool, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `simp [realifyFun] <;> ring`.
-/
theorem inner_rl {m : ℕ} (X Y : Matrix (Fin m) (Fin m) ℂ) : ⟪rl m X, rl m Y⟫_ℝ = (Matrix.trace (X * Yᴴ)).re := by
  simp only [rl, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply,
    Fintype.sum_prod_type, Fintype.sum_bool, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [realifyFun] <;> ring

def cj {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) : EE m →ₗ[ℝ] EE m where
  toFun x := rl m (A * unrealify x * B)
  map_add' x y := by rw [← rl_symm, ← rl_symm, ← rl_symm, map_add, Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' t x := by
    rw [← rl_symm, ← rl_symm, map_smul, Matrix.mul_smul, Matrix.smul_mul, map_smul]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cj_apply {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) (x : EE m) : cj A B x = rl m (A * unrealify x * B) := rfl

/- English proof (translation)
Rewrite using `[← rl_symm]`. Conclude with `(rl m).symm_apply_apply X`.
-/
theorem unrealify_rl {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : unrealify (rl m X) = X := by rw [← rl_symm]; exact (rl m).symm_apply_apply X

/- English proof (translation)
Rewrite using `[← rl_symm]`. Conclude with `(rl m).apply_symm_apply x`.
-/
theorem rl_unrealify {m : ℕ} (x : EE m) : rl m (unrealify x) = x := by rw [← rl_symm]; exact (rl m).apply_symm_apply x

/- English proof (translation)
Rewrite using `[cj_apply, cj_apply, unrealify_rl, show A * (B * unrealify x * A) * B = (A * B) * unrealify x * (A * B) by simp only [Matrix.mul_assoc], h, Matrix.one_mul, Matrix.mul_one, rl_unrealify]`.
-/
theorem cj_cj {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (h : A * B = 1) (x : EE m) : cj A B (cj B A x) = x := by
  rw [cj_apply, cj_apply, unrealify_rl,
    show A * (B * unrealify x * A) * B = (A * B) * unrealify x * (A * B) by simp only [Matrix.mul_assoc],
    h, Matrix.one_mul, Matrix.mul_one, rl_unrealify]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Bᴴ * H' * B = H at h`. Express the relevant statement in the definitionally equal form `gᴴ * H' * g = H' at hg`. Use `show (A * g * B)ᴴ * H * (A * g * B) = H`. Rewrite using `[← h]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Bᴴ * H' * B := by rw [hAB, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hg]`.
-/
theorem mem_UH_conj {m : ℕ} {H H' A B : Matrix (Fin m) (Fin m) ℂ} (hAB : B * A = 1) (h : Bᴴ * H' * B = H)
    {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UH H') : A * g * B ∈ UH H := by
  change Bᴴ * H' * B = H at h
  change gᴴ * H' * g = H' at hg
  show (A * g * B)ᴴ * H * (A * g * B) = H
  rw [← h]
  calc (A * g * B)ᴴ * (Bᴴ * H' * B) * (A * g * B) = Bᴴ * (gᴴ * ((B * A)ᴴ * H' * (B * A)) * g) * B := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Bᴴ * H' * B := by rw [hAB, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hg]

/- English proof (translation)
Establish `hB : B = A⁻¹` using `(Matrix.inv_eq_right_inv hAB).symm`. Substitute `hB` using the available equality. Conclude with `Matrix.exp_conj A X ((Matrix.isUnit_iff_isUnit_det A).mpr (Matrix.isUnit_det_of_right_inverse hAB))`.
-/
theorem exp_cj {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hAB : A * B = 1) (X : Matrix (Fin m) (Fin m) ℂ) :
    NormedSpace.exp (A * X * B) = A * NormedSpace.exp X * B := by
  have hB : B = A⁻¹ := (Matrix.inv_eq_right_inv hAB).symm
  subst hB
  exact Matrix.exp_conj A X ((Matrix.isUnit_iff_isUnit_det A).mpr (Matrix.isUnit_det_of_right_inverse hAB))

/- English proof (translation)
Establish `hBA : B * A = 1` using `mul_eq_one_comm.1 hAB`. Establish `hsub : (lieE (UH H')).map (cj A B) ≤ lieE (UH H)`. Rewrite using `[lieE, Submodule.map_span]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨X, hX, rfl⟩, rfl⟩`.

Use `⟨A * X * B, fun t => ?_, ?_⟩` and prove the remaining obligations. Use `mem_UH_conj hBA h (hX t)` as an intermediate fact. Rewrite `this` using `[← exp_cj hAB, Matrix.mul_smul, Matrix.smul_mul]`. Then use the resulting hypothesis. Express the relevant statement in the definitionally equal form `rl m (A * X * B) = cj A B (rl m X)`. Rewrite using `[cj_apply, unrealify_rl]`.

Conclude with `hsub (Submodule.mem_map_of_mem hx)`.
-/
theorem cj_mem {m : ℕ} {H H' A B : Matrix (Fin m) (Fin m) ℂ} (hAB : A * B = 1) (h : Bᴴ * H' * B = H)
    {x : EE m} (hx : x ∈ lieE (UH H')) : cj A B x ∈ lieE (UH H) := by
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  have hsub : (lieE (UH H')).map (cj A B) ≤ lieE (UH H) := by
    rw [lieE, Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    refine ⟨A * X * B, fun t => ?_, ?_⟩
    · have := mem_UH_conj hBA h (hX t)
      rwa [← exp_cj hAB, Matrix.mul_smul, Matrix.smul_mul] at this
    · change rl m (A * X * B) = cj A B (rl m X)
      rw [cj_apply, unrealify_rl]
  exact hsub (Submodule.mem_map_of_mem hx)

/- English proof (translation)
Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show IsClosed {g : Matrix (Fin N) (Fin N) ℂ | gᴴ * H * g = H}`. Conclude with `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`. Use `show (1 : Matrix (Fin N) (Fin N) ℂ)ᴴ * H * 1 = H`. Rewrite using `[Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`.

Introduce `a ha b hb`. Express the relevant statement in the definitionally equal form `aᴴ * H * a = H at ha`. Express the relevant statement in the definitionally equal form `bᴴ * H * b = H at hb`. Use `show (a * b)ᴴ * H * (a * b) = H`. Combine the equalities or inequalities in the displayed calculation.

Introduce `a ha`. Express the relevant statement in the definitionally equal form `aᴴ * H * a = H at ha`. Establish `hl : (H * aᴴ * H) * a = 1`. Rewrite using `[show H * aᴴ * H * a = H * (aᴴ * H * a) by simp only [Matrix.mul_assoc], ha, hH]`. Establish `hu : IsUnit a.det` using `Matrix.isUnit_det_of_left_inverse hl`.

Establish `hr : a * a⁻¹ = 1` using `Matrix.mul_nonsing_inv a hu`. Use `⟨?_, hr⟩` and prove the remaining obligations. Use `show (a⁻¹)ᴴ * H * a⁻¹ = H`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isMatGroup_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H * H = 1) : PI.IsMatGroup (UH H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show IsClosed {g : Matrix (Fin N) (Fin N) ℂ | gᴴ * H * g = H}
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · show (1 : Matrix (Fin N) (Fin N) ℂ)ᴴ * H * 1 = H
    rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · intro a ha b hb
    change aᴴ * H * a = H at ha
    change bᴴ * H * b = H at hb
    show (a * b)ᴴ * H * (a * b) = H
    calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [ha, hb]
  · intro a ha
    change aᴴ * H * a = H at ha
    have hl : (H * aᴴ * H) * a = 1 := by
      rw [show H * aᴴ * H * a = H * (aᴴ * H * a) by simp only [Matrix.mul_assoc], ha, hH]
    have hu : IsUnit a.det := Matrix.isUnit_det_of_left_inverse hl
    have hr : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
    refine ⟨?_, hr⟩
    show (a⁻¹)ᴴ * H * a⁻¹ = H
    calc (a⁻¹)ᴴ * H * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * H * a) * a⁻¹ := by rw [ha]
      _ = (a * a⁻¹)ᴴ * H * (a * a⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [hr, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

def cjM {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hAB : A * B = 1) : PI.MtM m ≃ₜ PI.MtM m where
  toFun x := Matrix.of.symm (A * Matrix.of x * B)
  invFun x := Matrix.of.symm (B * Matrix.of x * A)
  left_inv x := by
    show B * (A * Matrix.of x * B) * A = Matrix.of x
    calc _ = (B * A) * Matrix.of x * (B * A) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [mul_eq_one_comm.1 hAB]; simp
  right_inv x := by
    show A * (B * Matrix.of x * A) * B = Matrix.of x
    calc _ = (A * B) * Matrix.of x * (A * B) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hAB]; simp
  continuous_toFun := (continuous_const.matrix_mul (continuous_id (X := Matrix (Fin m) (Fin m) ℂ))).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul (continuous_id (X := Matrix (Fin m) (Fin m) ℂ))).matrix_mul continuous_const

/- English proof (translation)
Establish `hc : Continuous (PI.lmulQ s)`. Unfold `PI.lmulQ`. Conclude with `Continuous.matrix_mul continuous_const continuous_id`. Conclude with `hc.measurable`.
-/
theorem measurable_lmulQ {m : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) : Measurable (PI.lmulQ s) := by
  have hc : Continuous (PI.lmulQ s) := by
    unfold PI.lmulQ
    exact Continuous.matrix_mul continuous_const continuous_id
  exact hc.measurable

/- English proof (translation)
Take `⟨hσ, hne, hnull, hinv⟩` from `hμ`. Use `set e := (cjM hAB).toMeasurableEquiv with he`. Establish `hBA : B * A = 1` using `mul_eq_one_comm.1 hAB`. Use `⟨e.sigmaFinite_map, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Establish `h1` using `congrArg (fun ν => ν.map e.symm) h0`. Simplify `h1` using `[Measure.map_map e.symm.measurable e.measurable]`. Rewrite using `[e.map_apply]`. Use `measure_mono_null ?_ hnull` and prove the remaining obligations.

Introduce `x hx`. Conclude with `fun hxm => hx (mem_UH_conj hBA h hxm)`. Introduce `s hs`. Establish `hcomm : PI.lmulQ s ∘ e = e ∘ PI.lmulQ (B * s * A)`. Use function extensionality and compare the values at `x`.

Use `show s * (A * Matrix.of x * B) = A * (B * s * A * Matrix.of x) * B`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Measure.map_map (measurable_lmulQ s) e.measurable, hcomm, ← Measure.map_map e.measurable (measurable_lmulQ _), hinv _ (mem_UH_conj hAB h' hs)]`.
-/
theorem haar_map {m : ℕ} {H H' A B : Matrix (Fin m) (Fin m) ℂ} (hAB : A * B = 1) (h : Bᴴ * H' * B = H)
    (h' : Aᴴ * H * A = H') {μ : Measure (PI.MtM m)} (hμ : PI.IsHaarOnM (UH H') μ) :
    PI.IsHaarOnM (UH H) (μ.map (cjM hAB).toMeasurableEquiv) := by
  obtain ⟨hσ, hne, hnull, hinv⟩ := hμ
  set e := (cjM hAB).toMeasurableEquiv with he
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  refine ⟨e.sigmaFinite_map, ?_, ?_, ?_⟩
  · intro h0
    apply hne
    have h1 := congrArg (fun ν => ν.map e.symm) h0
    simpa [Measure.map_map e.symm.measurable e.measurable] using h1
  · rw [e.map_apply]
    refine measure_mono_null ?_ hnull
    intro x hx
    exact fun hxm => hx (mem_UH_conj hBA h hxm)
  · intro s hs
    have hcomm : PI.lmulQ s ∘ e = e ∘ PI.lmulQ (B * s * A) := by
      funext x
      show s * (A * Matrix.of x * B) = A * (B * s * A * Matrix.of x) * B
      calc s * (A * Matrix.of x * B) = (A * B) * s * (A * Matrix.of x * B) := by rw [hAB, Matrix.one_mul]
        _ = A * (B * s * A * Matrix.of x) * B := by simp only [Matrix.mul_assoc]
    rw [Measure.map_map (measurable_lmulQ s) e.measurable, hcomm,
      ← Measure.map_map e.measurable (measurable_lmulQ _), hinv _ (mem_UH_conj hAB h' hs)]

def adL {m : ℕ} {H H' A B : Matrix (Fin m) (Fin m) ℂ} (hAB : A * B = 1) (h : Bᴴ * H' * B = H)
    (h' : Aᴴ * H * A = H') : lieE (UH H) ≃ₗ[ℝ] lieE (UH H') :=
  LinearEquiv.ofLinear ((cj B A).restrict fun _ hx => cj_mem (mul_eq_one_comm.1 hAB) h' hx)
    ((cj A B).restrict fun _ hx => cj_mem hAB h hx)
    (by ext1 x; exact Subtype.ext (cj_cj (mul_eq_one_comm.1 hAB) _))
    (by ext1 x; exact Subtype.ext (cj_cj hAB _))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adL_coe {m : ℕ} {H H' A B : Matrix (Fin m) (Fin m) ℂ} (hAB : A * B = 1) (h : Bᴴ * H' * B = H)
    (h' : Aᴴ * H * A = H') (x : lieE (UH H)) : (adL hAB h h' x : EE m) = cj B A x := rfl

/- English proof (translation)
Establish `hHH : Hᴴ * H * H = H` using `by rw [hH, Matrix.mul_assoc, hH2, Matrix.mul_one]`. Establish `hHH' : H'ᴴ * H' * H' = H'` using `by rw [hH', Matrix.mul_assoc, hH2', Matrix.mul_one]`. Set `σ : lieE (UH H) →ₗ[ℝ] lieE (UH H)` to `(cj H H).restrict fun _ hx => cj_mem hH2 hHH hx`. Set `τ : lieE (UH H') →ₗ[ℝ] lieE (UH H')` to `(cj H' H').restrict fun _ hx => cj_mem hH2' hHH' hx`. Establish `hBA : B * A = 1` using `mul_eq_one_comm.1 hAB`.

Establish `k1 : H * (A * H' * Aᴴ) = 1`. Rewrite using `[← h]`. Combine the equalities or inequalities in the displayed calculation. Establish `k2 : A * H' * Aᴴ = H`. Combine the equalities or inequalities in the displayed calculation.

Use `volume_image_eq (adL hAB h h') σ τ (fun x => Subtype.ext (cj_cj hH2 _)) (fun x => Subtype.ext (cj_cj hH2' _)) (fun x y => ?_) s` and prove the remaining obligations. Rewrite using `[Submodule.coe_inner, Submodule.coe_inner]`. Simplify using `only [σ, τ, LinearMap.restrict_coe_apply, LinearEquiv.coe_coe, adL_coe]`. Simplify using `only [cj_apply, unrealify_rl]`. Rewrite using `[← rl_unrealify (y : EE m), inner_rl, inner_rl, unrealify_rl]`.

Use `congr 1`. Use `set X := unrealify (x : EE m)`. Use `set Y := unrealify (y : EE m)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = Matrix.trace (Bᴴ * (H' * B * X * (A * H' * Aᴴ) * Yᴴ)) := Matrix.trace_mul_comm _ _`. Use `_ = Matrix.trace ((Bᴴ * H' * B) * X * (A * H' * Aᴴ) * Yᴴ) := by simp only [Matrix.mul_assoc]`. Use `_ = Matrix.trace (H * X * H * Yᴴ) := by rw [h, k2]`.
-/
theorem volume_adL {m : ℕ} {H H' A B : Matrix (Fin m) (Fin m) ℂ} (hH : Hᴴ = H) (hH2 : H * H = 1)
    (hH' : H'ᴴ = H') (hH2' : H' * H' = 1) (hAB : A * B = 1) (h : Bᴴ * H' * B = H)
    (h' : Aᴴ * H * A = H') (s : Set (lieE (UH H))) : volume (adL hAB h h' '' s) = volume s := by
  have hHH : Hᴴ * H * H = H := by rw [hH, Matrix.mul_assoc, hH2, Matrix.mul_one]
  have hHH' : H'ᴴ * H' * H' = H' := by rw [hH', Matrix.mul_assoc, hH2', Matrix.mul_one]
  let σ : lieE (UH H) →ₗ[ℝ] lieE (UH H) := (cj H H).restrict fun _ hx => cj_mem hH2 hHH hx
  let τ : lieE (UH H') →ₗ[ℝ] lieE (UH H') := (cj H' H').restrict fun _ hx => cj_mem hH2' hHH' hx
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB

  have k1 : H * (A * H' * Aᴴ) = 1 := by
    rw [← h]
    calc Bᴴ * H' * B * (A * H' * Aᴴ) = Bᴴ * (H' * ((B * A) * (H' * Aᴴ))) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBA, Matrix.one_mul, ← Matrix.mul_assoc H', hH2', Matrix.one_mul, ← Matrix.conjTranspose_mul,
          hAB, Matrix.conjTranspose_one]
  have k2 : A * H' * Aᴴ = H := by
    calc A * H' * Aᴴ = (H * H) * (A * H' * Aᴴ) := by rw [hH2, Matrix.one_mul]
      _ = H := by rw [Matrix.mul_assoc, k1, Matrix.mul_one]
  refine volume_image_eq (adL hAB h h') σ τ (fun x => Subtype.ext (cj_cj hH2 _))
    (fun x => Subtype.ext (cj_cj hH2' _)) (fun x y => ?_) s
  rw [Submodule.coe_inner, Submodule.coe_inner]
  simp only [σ, τ, LinearMap.restrict_coe_apply, LinearEquiv.coe_coe, adL_coe]
  simp only [cj_apply, unrealify_rl]
  rw [← rl_unrealify (y : EE m), inner_rl, inner_rl, unrealify_rl]
  congr 1
  set X := unrealify (x : EE m)
  set Y := unrealify (y : EE m)
  calc Matrix.trace (H' * (B * X * A) * H' * (B * Y * A)ᴴ)
      = Matrix.trace ((H' * B * X * (A * H' * Aᴴ) * Yᴴ) * Bᴴ) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Matrix.trace (Bᴴ * (H' * B * X * (A * H' * Aᴴ) * Yᴴ)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((Bᴴ * H' * B) * X * (A * H' * Aᴴ) * Yᴴ) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (H * X * H * Yᴴ) := by rw [h, k2]

/- English proof (translation)
Use `letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra`. Set `U : V →L[ℝ] Matrix (Fin m) (Fin m) ℂ` to `LinearMap.toContinuousLinearMap ((rl m).symm.toLinearMap ∘ₗ V.subtype)`. Establish `hU : ∀ v : V, U v = unrealify (v : EE m)` using `fun v => rl_symm (v : EE m)`. Set `T : Matrix (Fin m) (Fin m) ℂ →L[ℝ] ℂ` to `LinearMap.toContinuousLinearMap { toFun := fun M => (B * M * A) i j map_add' := fun M M' => by simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply] map_smul' := fun t M => by simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, RingHom.id_apply] }`.

Establish `hexp : HasStrictFDerivAt NormedSpace.exp (1 : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ) (U 0)`. Rewrite using `[map_zero]`. Conclude with `hasStrictFDerivAt_exp_zero`. Establish `hall` using `T.hasStrictFDerivAt.comp (0 : V) (hexp.comp (0 : V) U.hasStrictFDerivAt)`. Use `⟨T.comp ((1 : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ).comp U), ?_, fun v => ?_⟩` and prove the remaining obligations.

Establish `hf : (fun x : V => (B * NormedSpace.exp (unrealify (x : EE m)) * A) i j) = T ∘ (NormedSpace.exp ∘ U)`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, hU]`. Both sides reduce to the same expression. Rewrite using `[hf]`.

Conclude with `hall`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, hU]`. Both sides reduce to the same expression.
-/
theorem strict_entry {m : ℕ} (V : Submodule ℝ (EE m)) (A B : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    ∃ D : V →L[ℝ] ℂ, HasStrictFDerivAt (fun x : V => (B * NormedSpace.exp (unrealify (x : EE m)) * A) i j) D 0 ∧
      ∀ v : V, D v = (B * unrealify (v : EE m) * A) i j := by
  letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  let U : V →L[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    LinearMap.toContinuousLinearMap ((rl m).symm.toLinearMap ∘ₗ V.subtype)
  have hU : ∀ v : V, U v = unrealify (v : EE m) := fun v => rl_symm (v : EE m)
  let T : Matrix (Fin m) (Fin m) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun M => (B * M * A) i j
      map_add' := fun M M' => by simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
      map_smul' := fun t M => by simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, RingHom.id_apply] }
  have hexp : HasStrictFDerivAt NormedSpace.exp (1 : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ) (U 0) := by
    rw [map_zero]; exact hasStrictFDerivAt_exp_zero
  have hall := T.hasStrictFDerivAt.comp (0 : V) (hexp.comp (0 : V) U.hasStrictFDerivAt)
  refine ⟨T.comp ((1 : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ).comp U), ?_, fun v => ?_⟩
  · have hf : (fun x : V => (B * NormedSpace.exp (unrealify (x : EE m)) * A) i j) =
        T ∘ (NormedSpace.exp ∘ U) := by
      funext x
      simp only [Function.comp_apply, hU]
      rfl
    rw [hf]
    exact hall
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, hU]
    rfl

/- English proof (translation)
Establish `hBA : B * A = 1` using `mul_eq_one_comm.1 hAB`. Use `set e := (cjM hAB).toMeasurableEquiv with he`. Set `L : lieE (UH H) ≃L[ℝ] lieE (UH H')` to `(adL hAB h h').toContinuousLinearEquiv`. Establish `hLie` using `(GlobalTheory.T.closed_matrix_subgroup_theorem m (UH H) (isMatGroup_UH H hH2)).1`. Establish `hmain` using `GlobalTheory.T.tendsto_measure_image_ball_div_volume m (UH H') μ c (isMatGroup_UH H' hH2') hμ hd (lieE (UH H)) (fun x => B * NormedSpace.exp (unrealify (x : EE m)) * A) L (by simp only [ZeroMemClass.coe_zero]; rw [show unrealify (0 : EE m) = 0 from (rl_symm (0 : EE m)).symm.trans …`.

Establish `hx` using `hLie x 1`. Rewrite `hx` using `[Complex.ofReal_one, one_smul]`. Conclude with `mem_UH_conj hAB h' hx)`. Use the proof step `(fun i j => by`. Apply the tactic sequence `obtain ⟨D, hD, hDv⟩ := strict_entry (lieE (UH H)) A B i j`.

Use `⟨D, hD, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[hDv]`. Use `show (B * unrealify (v : EE m) * A) i j = unrealify ((adL hAB h h' v : lieE (UH H')) : EE m) i j`. Rewrite using `[adL_coe, cj_apply, unrealify_rl])`. Unfold `GlobalTheory.Amp.HasDens`.

Use `hmain.congr fun ρ => ?_` and prove the remaining obligations. Establish `hset : e ⁻¹' GlobalTheory.Amp.expSet (UH H) (Metric.ball 0 ρ) = (fun x : lieE (UH H) => Matrix.of.symm (B * NormedSpace.exp (unrealify (x : EE m)) * A)) '' Metric.ball 0 ρ`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, GlobalTheory.Amp.expSet, Set.mem_image]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨X, hX, hx⟩`. Use `⟨X, hX, ?_⟩` and prove the remaining obligations. Establish `hx' : NormedSpace.exp (unrealify (X : EE m)) = A * Matrix.of x * B` using `hx`. Use `show B * NormedSpace.exp (unrealify (X : EE m)) * A = Matrix.of x`. Rewrite using `[hx']`.

Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨X, hX, rfl⟩`. Use `⟨X, hX, ?_⟩` and prove the remaining obligations. Use `show NormedSpace.exp (unrealify (X : EE m)) = A * (B * NormedSpace.exp (unrealify (X : EE m)) * A) * B`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hAB, Matrix.one_mul, Matrix.mul_one]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`. Establish `hvol : volume (⇑L '' Metric.ball (0 : lieE (UH H)) ρ) = volume (Metric.ball (0 : lieE (UH H)) ρ)` using `volume_adL hH hH2 hH' hH2' hAB h h' _`. Rewrite using `[e.map_apply, hset, hvol]`.
-/
theorem dens_map {m : ℕ} {H H' A B : Matrix (Fin m) (Fin m) ℂ} (hH : Hᴴ = H) (hH2 : H * H = 1)
    (hH' : H'ᴴ = H') (hH2' : H' * H' = 1) (hAB : A * B = 1) (h : Bᴴ * H' * B = H)
    (h' : Aᴴ * H * A = H') {μ : Measure (PI.MtM m)} {c : ℝ≥0∞} (hμ : PI.IsHaarOnM (UH H') μ)
    (hd : HasDens (UH H') μ c) : HasDens (UH H) (μ.map (cjM hAB).toMeasurableEquiv) c := by
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  set e := (cjM hAB).toMeasurableEquiv with he
  let L : lieE (UH H) ≃L[ℝ] lieE (UH H') := (adL hAB h h').toContinuousLinearEquiv
  have hLie := (GlobalTheory.T.closed_matrix_subgroup_theorem m (UH H) (isMatGroup_UH H hH2)).1
  have hmain := GlobalTheory.T.tendsto_measure_image_ball_div_volume m (UH H') μ c (isMatGroup_UH H' hH2') hμ hd (lieE (UH H))
    (fun x => B * NormedSpace.exp (unrealify (x : EE m)) * A) L
    (by simp only [ZeroMemClass.coe_zero]; rw [show unrealify (0 : EE m) = 0 from
      (rl_symm (0 : EE m)).symm.trans (map_zero _), NormedSpace.exp_zero, Matrix.mul_one, hBA])
    (Filter.Eventually.of_forall fun x => by
      have hx := hLie x 1
      rw [Complex.ofReal_one, one_smul] at hx
      exact mem_UH_conj hAB h' hx)
    (fun i j => by
      obtain ⟨D, hD, hDv⟩ := strict_entry (lieE (UH H)) A B i j
      refine ⟨D, hD, fun v => ?_⟩
      rw [hDv]
      show (B * unrealify (v : EE m) * A) i j = unrealify ((adL hAB h h' v : lieE (UH H')) : EE m) i j
      rw [adL_coe, cj_apply, unrealify_rl])
  unfold GlobalTheory.Amp.HasDens
  refine hmain.congr fun ρ => ?_
  have hset : e ⁻¹' GlobalTheory.Amp.expSet (UH H) (Metric.ball 0 ρ) =
      (fun x : lieE (UH H) => Matrix.of.symm (B * NormedSpace.exp (unrealify (x : EE m)) * A)) '' Metric.ball 0 ρ := by
    ext x
    simp only [Set.mem_preimage, GlobalTheory.Amp.expSet, Set.mem_image]
    constructor
    · rintro ⟨X, hX, hx⟩
      refine ⟨X, hX, ?_⟩
      have hx' : NormedSpace.exp (unrealify (X : EE m)) = A * Matrix.of x * B := hx
      show B * NormedSpace.exp (unrealify (X : EE m)) * A = Matrix.of x
      rw [hx']
      calc B * (A * Matrix.of x * B) * A = (B * A) * Matrix.of x * (B * A) := by simp only [Matrix.mul_assoc]
        _ = Matrix.of x := by rw [hBA, Matrix.one_mul, Matrix.mul_one]
    · rintro ⟨X, hX, rfl⟩
      refine ⟨X, hX, ?_⟩
      show NormedSpace.exp (unrealify (X : EE m)) = A * (B * NormedSpace.exp (unrealify (X : EE m)) * A) * B
      calc NormedSpace.exp (unrealify (X : EE m)) = (A * B) * NormedSpace.exp (unrealify (X : EE m)) * (A * B) := by
            rw [hAB, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
  have hvol : volume (⇑L '' Metric.ball (0 : lieE (UH H)) ρ) = volume (Metric.ball (0 : lieE (UH H)) ρ) :=
    volume_adL hH hH2 hH' hH2' hAB h h' _
  rw [e.map_apply, hset, hvol]

/- English proof (translation)
Introduce `m H H' P hH hH2 hH' hH2' hP hPH μ c hμ hd`. Establish `hdet : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).mp hP`. Establish `hAB : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hdet`. Establish `hPP : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hdet`. Establish `h' : (P⁻¹)ᴴ * H * P⁻¹ = H'`.

Rewrite using `[← hPH]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = H' := by rw [hPP, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Establish `hf : (fun x : PI.MtM m => Matrix.of.symm (P⁻¹ * Matrix.of x * P)) = ⇑(cjM hAB).toMeasurableEquiv` using `rfl`.

Rewrite using `[hf]`. Conclude with `⟨haar_map hAB hPH h' hμ, dens_map hH hH2 hH' hH2' hAB hPH h' hμ hd⟩`.
-/
theorem haar_dens_conj : ∀ (m : ℕ) (H H' P : Matrix (Fin m) (Fin m) ℂ), Hᴴ = H → H * H = 1 → H'ᴴ = H' → H' * H' = 1 → IsUnit P → Pᴴ * H' * P = H → ∀ (μ : Measure (PI.MtM m)) (c : ℝ≥0∞), PI.IsHaarOnM (UH H') μ → HasDens (UH H') μ c → PI.IsHaarOnM (UH H) (μ.map fun x : PI.MtM m => Matrix.of.symm (P⁻¹ * Matrix.of x * P)) ∧ HasDens (UH H) (μ.map fun x : PI.MtM m => Matrix.of.symm (P⁻¹ * Matrix.of x * P)) c := by
  intro m H H' P hH hH2 hH' hH2' hP hPH μ c hμ hd
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hAB : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have h' : (P⁻¹)ᴴ * H * P⁻¹ = H' := by
    rw [← hPH]
    calc (P⁻¹)ᴴ * (Pᴴ * H' * P) * P⁻¹ = (P * P⁻¹)ᴴ * H' * (P * P⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H' := by rw [hPP, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hf : (fun x : PI.MtM m => Matrix.of.symm (P⁻¹ * Matrix.of x * P)) = ⇑(cjM hAB).toMeasurableEquiv := rfl
  rw [hf]
  exact ⟨haar_map hAB hPH h' hμ, dens_map hH hH2 hH' hH2' hAB hPH h' hμ hd⟩

end GlobalTheory.AdDens
