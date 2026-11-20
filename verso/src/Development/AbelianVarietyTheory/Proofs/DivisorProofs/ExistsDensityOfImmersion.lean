import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCompactDualHaar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMatExp
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt

noncomputable section

namespace GlobalTheory.SUVol

open MeasureTheory Filter Topology Matrix Metric Set
open scoped ENNReal NNReal

/- English proof (translation)
Take `⟨p₀, hp₀⟩` from `(j : V →ₗ[ℝ] M).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hj)`. Set `p : M →L[ℝ] V` to `LinearMap.toContinuousLinearMap p₀`. Establish `hp : ∀ v, p (j v) = v` using `fun v => LinearMap.congr_fun hp₀ v`. Set `E : M →L[ℝ] V × M` to `p.prod (ContinuousLinearMap.id ℝ M - j.comp p)`. Set `D : V × M →L[ℝ] M` to `j.coprod (ContinuousLinearMap.id ℝ M)`.

Establish `hDE : ∀ x, D (E x) = x` using `fun x => by simp [D, E]`. Set `J : V →ₗᵢ[ℝ] V × M` to `⟨LinearMap.inl ℝ V M, fun v => by simp⟩`. Establish `hJ : E.comp j = J.toContinuousLinearMap`. Apply the tactic sequence `ext v <;> simp [E, J, hp]`. Use `GlobalTheory.CompactDualExists.exists_density_of_chart V (V × M) G lam μ e (fun g => E (m g)) J (fun g => ContinuousLinearMap.id ℝ _ + E.comp ((L g - ContinuousLinearMap.id ℝ M).comp D)) he h0 (hJ ▸ E.hasStrictFDerivAt.comp 0 hd) ?_ (by simp [hL1]) (fun g h => ?_) hn` and prove the remaining obligations.

Conclude with `continuousAt_const.add (continuousAt_const.clm_comp ((hL.sub continuousAt_const).clm_comp continuousAt_const))`. Simplify using `[hm, hDE]`.
-/
theorem exists_density_of_immersion (V M G : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (lam : Measure V) [lam.IsAddHaarMeasure] (μ : Measure G) [μ.IsHaarMeasure]
    (e : V → G) (m : G → M) (j : V →L[ℝ] M) (hj : Function.Injective j) (L : G → M →L[ℝ] M) (he : Continuous e)
    (h0 : e 0 = 1) (hd : HasStrictFDerivAt (fun x => m (e x)) j 0)
    (hL : ContinuousAt L 1) (hL1 : L 1 = ContinuousLinearMap.id ℝ M)
    (hm : ∀ g h, m (g * h) = L g (m h)) (hn : ∀ r : ℝ, 0 < r → e '' ball 0 r ∈ 𝓝 (1 : G)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      Tendsto (fun r : ℝ => μ (e '' ball 0 r) / lam (ball 0 r)) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨p₀, hp₀⟩ := (j : V →ₗ[ℝ] M).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hj)
  let p : M →L[ℝ] V := LinearMap.toContinuousLinearMap p₀
  have hp : ∀ v, p (j v) = v := fun v => LinearMap.congr_fun hp₀ v
  let E : M →L[ℝ] V × M := p.prod (ContinuousLinearMap.id ℝ M - j.comp p)
  let D : V × M →L[ℝ] M := j.coprod (ContinuousLinearMap.id ℝ M)
  have hDE : ∀ x, D (E x) = x := fun x => by simp [D, E]
  let J : V →ₗᵢ[ℝ] V × M := ⟨LinearMap.inl ℝ V M, fun v => by simp⟩
  have hJ : E.comp j = J.toContinuousLinearMap := by
    ext v <;> simp [E, J, hp]
  refine GlobalTheory.CompactDualExists.exists_density_of_chart V (V × M) G lam μ e (fun g => E (m g)) J
    (fun g => ContinuousLinearMap.id ℝ _ + E.comp ((L g - ContinuousLinearMap.id ℝ M).comp D)) he h0
    (hJ ▸ E.hasStrictFDerivAt.comp 0 hd) ?_ (by simp [hL1]) (fun g h => ?_) hn
  · exact continuousAt_const.add (continuousAt_const.clm_comp ((hL.sub continuousAt_const).clm_comp
      continuousAt_const))
  · simp [hm, hDE]

section OneMatrix

variable {r : ℕ}

/- English proof (translation)
Establish `hder : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)).det) X.trace 0`. Establish `h1 : ∀ a b, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) a b) (X a b) 0`. Introduce `a b`. Use `open scoped Matrix.Norms.Operator in`. Establish `h2` using `((Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0 (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)`.

Rewrite `h2` using `[zero_smul, NormedSpace.exp_zero, one_mul]`. Conclude with `h2`. Establish `h3` using `ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t : ℝ => NormedSpace.exp (t • X)) X 0 h1`. Simplify `h3` using `only [zero_smul, NormedSpace.exp_zero, Matrix.adjugate_one, Matrix.one_mul]`. Establish `hadd : ∀ s t : ℝ, NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X)`.

Introduce `s t`. Rewrite using `[add_smul]`. Conclude with `Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)`. Use `set f : ℝ → ℂ := fun t => (NormedSpace.exp (t • X)).det with hf`. Establish `hd : ∀ t, HasDerivAt f (f t * X.trace) t`.

Introduce `t`. Establish `h0 : HasDerivAt f X.trace (t - t)`. Rewrite using `[sub_self]`. Conclude with `hder`. Establish `h1` using `(h0.comp_sub_const t t).const_mul (f t)`.

Use `h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `only [hf]`. Rewrite using `[← Matrix.det_mul, ← hadd, add_sub_cancel]`. Establish `hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f s * Complex.exp (-(s * X.trace))) 0 t`. Introduce `t`.

Establish `h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * X.trace)) (-X.trace) t`. Simplify using `using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const X.trace).fun_neg`. Conclude with `((hd t).fun_mul h1.cexp).congr_deriv (by ring)`. Establish `h2` using `is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0`. Simplify using `only [hf, one_smul, zero_smul, NormedSpace.exp_zero, Matrix.det_one, Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, Complex.exp_neg] at h2`.

Conclude with `(mul_inv_eq_one₀ (Complex.exp_ne_zero _)).1 h2`.
-/
theorem det_exp (X : Matrix (Fin r) (Fin r) ℂ) : (NormedSpace.exp X).det = Complex.exp X.trace := by
  have hder : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)).det) X.trace 0 := by
    have h1 : ∀ a b, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) a b) (X a b) 0 := by
      intro a b
      open scoped Matrix.Norms.Operator in
      have h2 := ((Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
        (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
      rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
      exact h2
    have h3 := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t : ℝ => NormedSpace.exp (t • X)) X 0 h1
    simpa only [zero_smul, NormedSpace.exp_zero, Matrix.adjugate_one, Matrix.one_mul] using h3
  have hadd : ∀ s t : ℝ,
      NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X) := by
    intro s t
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)
  set f : ℝ → ℂ := fun t => (NormedSpace.exp (t • X)).det with hf
  have hd : ∀ t, HasDerivAt f (f t * X.trace) t := by
    intro t
    have h0 : HasDerivAt f X.trace (t - t) := by
      rw [sub_self]; exact hder
    have h1 := (h0.comp_sub_const t t).const_mul (f t)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hf]
    rw [← Matrix.det_mul, ← hadd, add_sub_cancel]
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f s * Complex.exp (-(s * X.trace))) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * X.trace)) (-X.trace) t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const X.trace).fun_neg
    exact ((hd t).fun_mul h1.cexp).congr_deriv (by ring)
  have h2 := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, NormedSpace.exp_zero, Matrix.det_one, Complex.ofReal_one, one_mul,
    Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, Complex.exp_neg] at h2
  exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).1 h2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem map_conj_eq (A : Matrix (Fin r) (Fin r) ℂ) : A.map (starRingEnd ℂ) = Aᴴᵀ := rfl

/- English proof (translation)
Rewrite using `[map_conj_eq, map_conj_eq, Matrix.exp_transpose, Matrix.exp_conjTranspose]`.
-/
theorem exp_map_conj (A : Matrix (Fin r) (Fin r) ℂ) :
    NormedSpace.exp (A.map (starRingEnd ℂ)) = (NormedSpace.exp A).map (starRingEnd ℂ) := by
  rw [map_conj_eq, map_conj_eq, Matrix.exp_transpose, Matrix.exp_conjTranspose]

def twist (H X : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  (H * (-X).map (starRingEnd ℂ) * H⁻¹)ᵀ

/- English proof (translation)
The claim follows from `((continuous_const.matrix_mul (continuous_neg.matrix_map Complex.continuous_conj)).matrix_mul continuous_const).matrix_transpose`.
-/
theorem continuous_twist (H : Matrix (Fin r) (Fin r) ℂ) : Continuous (twist H) :=
  ((continuous_const.matrix_mul (continuous_neg.matrix_map Complex.continuous_conj)).matrix_mul
    continuous_const).matrix_transpose

variable {H : Matrix (Fin r) (Fin r) ℂ}

/- English proof (translation)
Rewrite using `[twist, transpose_transpose, Matrix.nonsing_inv_mul_cancel_right _ _ hH.isUnit, Matrix.map_neg _ (map_neg _), Matrix.mul_neg]`.
-/
theorem twist_transpose_mul (hH : H.det ≠ 0) (X : Matrix (Fin r) (Fin r) ℂ) :
    (twist H X)ᵀ * H = -(H * X.map (starRingEnd ℂ)) := by
  rw [twist, transpose_transpose, Matrix.nonsing_inv_mul_cancel_right _ _ hH.isUnit,
    Matrix.map_neg _ (map_neg _), Matrix.mul_neg]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `twist_transpose_mul hH X` as an intermediate fact. Rewrite `this` using `[h]`. Rewrite using `[this, neg_add_cancel]`.

Introduce `h`. Rewrite using `[twist, Matrix.map_neg _ (map_neg _), Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left h, Matrix.mul_nonsing_inv_cancel_right _ _ hH.isUnit, transpose_transpose]`.
-/
theorem twist_eq_iff (hH : H.det ≠ 0) (X : Matrix (Fin r) (Fin r) ℂ) :
    twist H X = X ↔ Xᵀ * H + H * X.map (starRingEnd ℂ) = 0 := by
  constructor
  · intro h
    have := twist_transpose_mul hH X
    rw [h] at this
    rw [this, neg_add_cancel]
  · intro h
    rw [twist, Matrix.map_neg _ (map_neg _), Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left h,
      Matrix.mul_nonsing_inv_cancel_right _ _ hH.isUnit, transpose_transpose]

/- English proof (translation)
Rewrite using `[twist, Matrix.exp_transpose, transpose_transpose, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det _).2 hH.isUnit), Matrix.nonsing_inv_mul_cancel_right _ _ hH.isUnit, exp_map_conj, Matrix.mul_assoc, ← Matrix.map_mul, GlobalTheory.UpqExpChart.exp_neg_mul_exp]`. Simplify using the standard rewrite rules.
-/
theorem exp_twist (hH : H.det ≠ 0) (X : Matrix (Fin r) (Fin r) ℂ) :
    (NormedSpace.exp (twist H X))ᵀ * H * (NormedSpace.exp X).map (starRingEnd ℂ) = H := by
  rw [twist, Matrix.exp_transpose, transpose_transpose,
    Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det _).2 hH.isUnit),
    Matrix.nonsing_inv_mul_cancel_right _ _ hH.isUnit, exp_map_conj, Matrix.mul_assoc, ← Matrix.map_mul,
    GlobalTheory.UpqExpChart.exp_neg_mul_exp]
  simp

/- English proof (translation)
Establish `h1` using `(exp_twist hH X).trans h.symm`. Establish `h2` using `congrArg (fun A => A * (NormedSpace.exp (-X)).map (starRingEnd ℂ) * H⁻¹) h1`. Simplify using `only [Matrix.mul_assoc _ ((NormedSpace.exp X).map (starRingEnd ℂ)), ← Matrix.map_mul, GlobalTheory.UpqExpChart.exp_mul_exp_neg, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_right _ _ hH.isUnit] at h2`. Conclude with `transpose_injective h2`.
-/
theorem exp_twist_eq (hH : H.det ≠ 0) {X : Matrix (Fin r) (Fin r) ℂ}
    (h : (NormedSpace.exp X)ᵀ * H * (NormedSpace.exp X).map (starRingEnd ℂ) = H) :
    NormedSpace.exp (twist H X) = NormedSpace.exp X := by
  have h1 := (exp_twist hH X).trans h.symm
  have h2 := congrArg (fun A => A * (NormedSpace.exp (-X)).map (starRingEnd ℂ) * H⁻¹) h1
  simp only [Matrix.mul_assoc _ ((NormedSpace.exp X).map (starRingEnd ℂ)), ← Matrix.map_mul,
    GlobalTheory.UpqExpChart.exp_mul_exp_neg, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_right _ _ hH.isUnit] at h2
  exact transpose_injective h2

/- English proof (translation)
Simplify using `[Matrix.trace]`.
-/
theorem trace_map_conj (A : Matrix (Fin r) (Fin r) ℂ) :
    (A.map (starRingEnd ℂ)).trace = starRingEnd ℂ A.trace := by
  simp [Matrix.trace]

/- English proof (translation)
Rewrite using `[twist, trace_transpose, Matrix.trace_mul_comm, Matrix.nonsing_inv_mul_cancel_left _ _ hH.isUnit, trace_map_conj, trace_neg, map_neg]`.
-/
theorem trace_twist (hH : H.det ≠ 0) (A : Matrix (Fin r) (Fin r) ℂ) :
    (twist H A).trace = -starRingEnd ℂ A.trace := by
  rw [twist, trace_transpose, Matrix.trace_mul_comm, Matrix.nonsing_inv_mul_cancel_left _ _ hH.isUnit,
    trace_map_conj, trace_neg, map_neg]

/- English proof (translation)
Rewrite using `[twist, twist, ← transpose_mul, trace_transpose, Matrix.mul_assoc, Matrix.mul_assoc H _ H⁻¹, Matrix.nonsing_inv_mul_cancel_left _ _ hH.isUnit, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hH.isUnit, ← Matrix.map_mul, trace_ma …`.
-/
theorem trace_twist_mul (hH : H.det ≠ 0) (A B : Matrix (Fin r) (Fin r) ℂ) :
    (twist H A * twist H B).trace = starRingEnd ℂ (A * B).trace := by
  rw [twist, twist, ← transpose_mul, trace_transpose, Matrix.mul_assoc, Matrix.mul_assoc H _ H⁻¹,
    Matrix.nonsing_inv_mul_cancel_left _ _ hH.isUnit, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hH.isUnit, ← Matrix.map_mul,
    trace_map_conj, neg_mul_neg, Matrix.trace_mul_comm]

/- English proof (translation)
Establish `h1` using `congrArg Matrix.conjTranspose (twist_transpose_mul hH A)`. Rewrite `h1` using `[conjTranspose_mul, conjTranspose_neg, conjTranspose_mul, hh.eq]`. Establish `e1 : (twist H A).map (starRingEnd ℂ) = (twist H A)ᵀᴴ` using `rfl`. Establish `e2 : Aᵀ = (A.map (starRingEnd ℂ))ᴴ` using `by ext a b; simp`. Rewrite using `[e1, e2, h1]`.
-/
theorem mul_twist_map_conj (hh : H.IsHermitian) (hH : H.det ≠ 0) (A : Matrix (Fin r) (Fin r) ℂ) :
    H * (twist H A).map (starRingEnd ℂ) = -(Aᵀ * H) := by
  have h1 := congrArg Matrix.conjTranspose (twist_transpose_mul hH A)
  rw [conjTranspose_mul, conjTranspose_neg, conjTranspose_mul, hh.eq] at h1
  have e1 : (twist H A).map (starRingEnd ℂ) = (twist H A)ᵀᴴ := rfl
  have e2 : Aᵀ = (A.map (starRingEnd ℂ))ᴴ := by ext a b; simp
  rw [e1, e2, h1]

end OneMatrix

variable {ι : Type} {r : ℕ} {H : ι → Matrix (Fin r) (Fin r) ℂ}

def suMat (g : suGrp H) : ι → Matrix (Fin r) (Fin r) ℂ := fun i => (g.1 i : GL (Fin r) ℂ)

/- English proof (translation)
Introduce `_ _ h` and use `Subtype.ext (funext fun i => Units.ext (congrFun h i))`.
-/
theorem suMat_injective : Function.Injective (suMat (H := H)) :=
  fun _ _ h => Subtype.ext (funext fun i => Units.ext (congrFun h i))

/- English proof (translation)
The claim follows from `continuous_pi fun i => Units.continuous_val.comp ((continuous_apply i).comp continuous_subtype_val)`.
-/
theorem continuous_suMat : Continuous (suMat (H := H)) :=
  continuous_pi fun i => Units.continuous_val.comp ((continuous_apply i).comp continuous_subtype_val)

def suExp (hH : ∀ i, (H i).det ≠ 0) (X : suLie H) : suGrp H :=
  ⟨fun i => ⟨NormedSpace.exp (X.1 i), NormedSpace.exp (-X.1 i), GlobalTheory.UpqExpChart.exp_mul_exp_neg _,
      GlobalTheory.UpqExpChart.exp_neg_mul_exp _⟩, fun i => ⟨by
    have := exp_twist (hH i) (X.1 i)
    rwa [(twist_eq_iff (hH i) _).2 (X.2 i).1] at this, by
    change (NormedSpace.exp (X.1 i)).det = 1
    rw [det_exp, (X.2 i).2, Complex.exp_zero]⟩⟩

/- English proof (translation)
Use `Continuous.subtype_mk (continuous_pi fun i => Units.continuous_iff.2 ⟨?_, ?_⟩) _` and prove the remaining obligations. Conclude with `GlobalTheory.UpqExpChart.continuous_matExp.comp ((continuous_apply i).comp continuous_subtype_val)`. Conclude with `GlobalTheory.UpqExpChart.continuous_matExp.comp ((continuous_apply i).comp continuous_subtype_val).neg`.
-/
theorem continuous_suExp (hH : ∀ i, (H i).det ≠ 0) : Continuous (suExp hH) := by
  refine Continuous.subtype_mk (continuous_pi fun i => Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact GlobalTheory.UpqExpChart.continuous_matExp.comp ((continuous_apply i).comp continuous_subtype_val)
  · exact GlobalTheory.UpqExpChart.continuous_matExp.comp ((continuous_apply i).comp continuous_subtype_val).neg

/- English proof (translation)
Take `⟨e, he, h0⟩` from `GlobalTheory.UpqExpChart.exists_chart (n := Fin r)`. Establish `hinj : Set.InjOn NormedSpace.exp e.source` using `he ▸ e.injOn`. Establish `he0 : e 0 = 1` using `by rw [he]; exact NormedSpace.exp_zero`. Establish `h1 : (1 : Matrix (Fin r) (Fin r) ℂ) ∈ e.target` using `he0 ▸ e.map_source h0`. Establish `hs1 : e.symm 1 = 0` using `he0 ▸ e.left_inv h0`.

Establish `hm : ∀ i, Tendsto (fun g : suGrp H => suMat g i) (𝓝 1) (𝓝 1)` using `fun i => ((continuous_apply i).comp continuous_suMat).tendsto 1`. Establish `hZ : ∀ i, Tendsto (fun g : suGrp H => e.symm (suMat g i)) (𝓝 1) (𝓝 0)` using `fun i => hs1 ▸ (e.continuousAt_symm h1).tendsto.comp (hm i)`. Take `⟨V, hV, hVU⟩` from `(mem_nhds_subtype _ _ _).1 hU`. Establish `a1 : ∀ᶠ g : suGrp H in 𝓝 1, ∀ i, suMat g i ∈ e.target` using `eventually_all.2 fun i => hm i (e.open_target.mem_nhds h1)`. Establish `a2 : ∀ᶠ g : suGrp H in 𝓝 1, ∀ i, twist (H i) (e.symm (suMat g i)) ∈ e.source` using `eventually_all.2 fun i => (((continuous_twist (H i)).tendsto 0).comp (hZ i)) (e.open_source.mem_nhds (by simpa [twist] using h0))`.

Establish `a3 : ∀ᶠ g : suGrp H in 𝓝 1, ∀ i, (e.symm (suMat g i)).trace ∈ ball (0 : ℂ) 1` using `eventually_all.2 fun i => ((continuous_id.matrix_trace.tendsto 0).comp (hZ i)) (isOpen_ball.mem_nhds (by simp))`. Establish `a4 : ∀ᶠ g : suGrp H in 𝓝 1, (fun i => e.symm (suMat g i)) ∈ V` using `(tendsto_pi_nhds.2 hZ) hV`. Use `filter_upwards [a1, a2, a3, a4] with g b1 b2 b3 b4`. Establish `hexp : ∀ i, NormedSpace.exp (e.symm (suMat g i)) = suMat g i` using `fun i => he ▸ e.right_inv (b1 i)`. Establish `hmem : (fun i => e.symm (suMat g i)) ∈ suLie H`.

Introduce `i`. Use `⟨(twist_eq_iff (hH i) _).1 (hinj (b2 i) (e.map_target (b1 i)) (exp_twist_eq (hH i) ?_)), ?_⟩` and prove the remaining obligations. Rewrite using `[hexp]`. Conclude with `(g.2 i).1`. Establish `c1 : Complex.exp (e.symm (suMat g i)).trace = Complex.exp 0`.

Rewrite using `[← det_exp, hexp, Complex.exp_zero]`. Conclude with `(g.2 i).2`. Establish `c2` using `(abs_lt.1 ((Complex.abs_im_le_norm _).trans_lt (mem_ball_zero_iff.1 (b3 i))))`. Use `Real.pi_gt_three` as an intermediate fact. Conclude with `Complex.exp_inj_of_neg_pi_lt_of_le_pi (by linarith [c2.1]) (by linarith [c2.2]) (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]) c1`.

Conclude with `⟨⟨_, hmem⟩, hVU b4, suMat_injective (funext hexp)⟩`.
-/
theorem image_suExp_mem_nhds [Fintype ι] (hH : ∀ i, (H i).det ≠ 0) {U : Set (suLie H)} (hU : U ∈ 𝓝 0) :
    suExp hH '' U ∈ 𝓝 (1 : suGrp H) := by
  obtain ⟨e, he, h0⟩ := GlobalTheory.UpqExpChart.exists_chart (n := Fin r)
  have hinj : Set.InjOn NormedSpace.exp e.source := he ▸ e.injOn
  have he0 : e 0 = 1 := by rw [he]; exact NormedSpace.exp_zero
  have h1 : (1 : Matrix (Fin r) (Fin r) ℂ) ∈ e.target := he0 ▸ e.map_source h0
  have hs1 : e.symm 1 = 0 := he0 ▸ e.left_inv h0
  have hm : ∀ i, Tendsto (fun g : suGrp H => suMat g i) (𝓝 1) (𝓝 1) := fun i =>
    ((continuous_apply i).comp continuous_suMat).tendsto 1
  have hZ : ∀ i, Tendsto (fun g : suGrp H => e.symm (suMat g i)) (𝓝 1) (𝓝 0) := fun i =>
    hs1 ▸ (e.continuousAt_symm h1).tendsto.comp (hm i)
  obtain ⟨V, hV, hVU⟩ := (mem_nhds_subtype _ _ _).1 hU
  have a1 : ∀ᶠ g : suGrp H in 𝓝 1, ∀ i, suMat g i ∈ e.target :=
    eventually_all.2 fun i => hm i (e.open_target.mem_nhds h1)
  have a2 : ∀ᶠ g : suGrp H in 𝓝 1, ∀ i, twist (H i) (e.symm (suMat g i)) ∈ e.source :=
    eventually_all.2 fun i => (((continuous_twist (H i)).tendsto 0).comp (hZ i))
      (e.open_source.mem_nhds (by simpa [twist] using h0))
  have a3 : ∀ᶠ g : suGrp H in 𝓝 1, ∀ i, (e.symm (suMat g i)).trace ∈ ball (0 : ℂ) 1 :=
    eventually_all.2 fun i => ((continuous_id.matrix_trace.tendsto 0).comp (hZ i))
      (isOpen_ball.mem_nhds (by simp))
  have a4 : ∀ᶠ g : suGrp H in 𝓝 1, (fun i => e.symm (suMat g i)) ∈ V :=
    (tendsto_pi_nhds.2 hZ) hV
  filter_upwards [a1, a2, a3, a4] with g b1 b2 b3 b4
  have hexp : ∀ i, NormedSpace.exp (e.symm (suMat g i)) = suMat g i := fun i => he ▸ e.right_inv (b1 i)
  have hmem : (fun i => e.symm (suMat g i)) ∈ suLie H := by
    intro i
    refine ⟨(twist_eq_iff (hH i) _).1 (hinj (b2 i) (e.map_target (b1 i)) (exp_twist_eq (hH i) ?_)), ?_⟩
    · rw [hexp]; exact (g.2 i).1
    · have c1 : Complex.exp (e.symm (suMat g i)).trace = Complex.exp 0 := by
        rw [← det_exp, hexp, Complex.exp_zero]; exact (g.2 i).2
      have c2 := (abs_lt.1 ((Complex.abs_im_le_norm _).trans_lt (mem_ball_zero_iff.1 (b3 i))))
      have := Real.pi_gt_three
      exact Complex.exp_inj_of_neg_pi_lt_of_le_pi (by linarith [c2.1]) (by linarith [c2.2])
        (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]) c1
  exact ⟨⟨_, hmem⟩, hVU b4, suMat_injective (funext hexp)⟩

/- English proof (translation)
Establish `hmem : (fun i => (X.1 i)ᴴ + twist (H i) (X.1 i)ᴴ) ∈ suLie H`. Introduce `i`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[transpose_add, Matrix.map_add _ (map_add _), Matrix.add_mul, Matrix.mul_add, twist_transpose_mul (hH i).2, mul_twist_map_conj (hH i).1 (hH i).2]`. Normalize the expressions using the abelian group laws.

Simplify using `[trace_twist (hH i).2, trace_conjTranspose, (X.2 i).2]`. Establish `h1` using `h ⟨_, hmem⟩`. Establish `h2 : ∀ i, (X.1 i * ((X.1 i)ᴴ + twist (H i) (X.1 i)ᴴ)).trace.re = 2 * (X.1 i * (X.1 i)ᴴ).trace.re`. Introduce `i`. Use `trace_twist_mul (hH i).2 (X.1 i) (X.1 i)ᴴ` as an intermediate fact.

Rewrite `this` using `[(twist_eq_iff (hH i).2 _).2 (X.2 i).1]`. Rewrite using `[Matrix.mul_add, trace_add, this, Complex.add_re, Complex.conj_re, two_mul]`. Establish `h3 : ∀ i, (X.1 i * (X.1 i)ᴴ).trace.re = ∑ a, ∑ b, Complex.normSq (X.1 i a b)`. Introduce `i`. Simplify using `[Matrix.trace, Matrix.mul_apply, Complex.normSq_apply]`.

Simplify using `only [trForm, h2, h3, ← Finset.mul_sum] at h1`. Establish `h4` using `(mul_eq_zero.1 h1).resolve_left two_ne_zero`. Use extensionality with `i a b`. Establish `h5` using `(Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _).1 h4 i (Finset.mem_univ _)`. Establish `h6` using `(Finset.sum_eq_zero_iff_of_nonneg fun a _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _).1 h5 a (Finset.mem_univ _)`.

Conclude with `Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun b _ => Complex.normSq_nonneg _).1 h6 b (Finset.mem_univ _))`.
-/
theorem eq_zero_of_trForm [Fintype ι] (hH : ∀ i, (H i).IsHermitian ∧ (H i).det ≠ 0) (X : suLie H)
    (h : ∀ Y : suLie H, trForm X.1 Y.1 = 0) : X = 0 := by
  have hmem : (fun i => (X.1 i)ᴴ + twist (H i) (X.1 i)ᴴ) ∈ suLie H := by
    intro i
    refine ⟨?_, ?_⟩
    · rw [transpose_add, Matrix.map_add _ (map_add _), Matrix.add_mul, Matrix.mul_add,
        twist_transpose_mul (hH i).2, mul_twist_map_conj (hH i).1 (hH i).2]
      abel
    · simp [trace_twist (hH i).2, trace_conjTranspose, (X.2 i).2]
  have h1 := h ⟨_, hmem⟩
  have h2 : ∀ i, (X.1 i * ((X.1 i)ᴴ + twist (H i) (X.1 i)ᴴ)).trace.re = 2 * (X.1 i * (X.1 i)ᴴ).trace.re := by
    intro i
    have := trace_twist_mul (hH i).2 (X.1 i) (X.1 i)ᴴ
    rw [(twist_eq_iff (hH i).2 _).2 (X.2 i).1] at this
    rw [Matrix.mul_add, trace_add, this, Complex.add_re, Complex.conj_re, two_mul]
  have h3 : ∀ i, (X.1 i * (X.1 i)ᴴ).trace.re = ∑ a, ∑ b, Complex.normSq (X.1 i a b) := by
    intro i
    simp [Matrix.trace, Matrix.mul_apply, Complex.normSq_apply]
  simp only [trForm, h2, h3, ← Finset.mul_sum] at h1
  have h4 := (mul_eq_zero.1 h1).resolve_left two_ne_zero
  ext i a b
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _).1 h4 i (Finset.mem_univ _)
  have h6 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _).1 h5 a (Finset.mem_univ _)
  exact Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun b _ => Complex.normSq_nonneg _).1 h6 b
    (Finset.mem_univ _))

/- English proof (translation)
Introduce `h0`. Take `⟨v, hv, hvG⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 h0`. Set `B : suLie H →ₗ[ℝ] suLie H →ₗ[ℝ] ℝ` to `LinearMap.mk₂ ℝ (fun X Y => trForm X.1 Y.1) (fun X X' Y => by simp [trForm, Matrix.add_mul, Finset.sum_add_distrib]) (fun c X Y => by simp [trForm, Finset.mul_sum]) (fun X Y Y' => by simp [trForm, Matrix.mul_add, Finset.sum_add_distrib]) (fun c X Y => by simp [trForm, Finset.mul_ …`. Establish `h1 : B (b.equivFun.symm v) = 0`. Use `b.ext fun l => ?_` and prove the remaining obligations.

Use `congrFun hvG l` as an intermediate fact. Rewrite using `[Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply]`. Simplify using `only [map_smul, LinearMap.smul_apply, smul_eq_mul]`. Conclude with `this`. Establish `h2` using `eq_zero_of_trForm hH (b.equivFun.symm v) fun Y => LinearMap.congr_fun h1 Y`.

Conclude with `hv (b.equivFun.symm.map_eq_zero_iff.1 h2)`.
-/
theorem det_gram_ne_zero [Fintype ι] (hH : ∀ i, (H i).IsHermitian ∧ (H i).det ≠ 0) {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (suLie H)) : (Matrix.of fun k l => trForm (b k).1 (b l).1).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hvG⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  let B : suLie H →ₗ[ℝ] suLie H →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun X Y => trForm X.1 Y.1)
    (fun X X' Y => by simp [trForm, Matrix.add_mul, Finset.sum_add_distrib])
    (fun c X Y => by simp [trForm, Finset.mul_sum])
    (fun X Y Y' => by simp [trForm, Matrix.mul_add, Finset.sum_add_distrib])
    (fun c X Y => by simp [trForm, Finset.mul_sum])
  have h1 : B (b.equivFun.symm v) = 0 := by
    refine b.ext fun l => ?_
    have := congrFun hvG l
    rw [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact this
  have h2 := eq_zero_of_trForm hH (b.equivFun.symm v) fun Y => LinearMap.congr_fun h1 Y
  exact hv (b.equivFun.symm.map_eq_zero_iff.1 h2)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

/- English proof (translation)
Introduce `ι _ r H hH _ _ m hm`. Establish `hd : ∀ i, (H i).det ≠ 0` using `fun i => (hH i).2`. Set `b` to `Module.finBasis ℝ (suLie H)`. Set `j : (Fin (Module.finrank ℝ (suLie H)) → ℝ) →L[ℝ] (ι → Matrix (Fin r) (Fin r) ℂ)` to `LinearMap.toContinuousLinearMap ((suLie H).subtype ∘ₗ b.equivFun.symm.toLinearMap)`. Establish `hb : Continuous b.equivFun.symm` using `b.equivFun.symm.toLinearMap.continuous_of_finiteDimensional`.

Establish `hb' : Continuous b.equivFun` using `b.equivFun.toLinearMap.continuous_of_finiteDimensional`. Set `L₀ : (ι → Matrix (Fin r) (Fin r) ℂ) →ₗ[ℝ] ((ι → Matrix (Fin r) (Fin r) ℂ) →L[ℝ] (ι → Matrix (Fin r) (Fin r) ℂ))` to `LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℝ _`. Establish `hL₀ : Continuous L₀` using `L₀.continuous_of_finiteDimensional`. Take `⟨c, hc0, hct, hc⟩` from `exists_density_of_immersion _ (ι → Matrix (Fin r) (Fin r) ℂ) (suGrp H) volume m (fun t => suExp hd (b.equivFun.symm t)) suMat j (Subtype.val_injective.comp b.equivFun.symm.injective) (fun g => L₀ (suMat g)) ((continuous_suExp hd).comp hb) (suMat_injective (funext fun i => by`. Rewrite using `[map_zero]`.

Conclude with `NormedSpace.exp_zero (𝔸 := Matrix (Fin r) (Fin r) ℂ)))`. Use the proof step `(by`. Use `hasStrictFDerivAt_pi'' fun i => ?_` and prove the remaining obligations. Establish `h1` using `((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Matrix (Fin r) (Fin r) ℂ) i).comp j).hasStrictFDerivAt (x := 0)`. Establish `h2 : HasStrictFDerivAt (𝕜` using `ℝ) (NormedSpace.exp : Matrix (Fin r) (Fin r) ℂ → _) (ContinuousLinearMap.id ℝ _) (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Matrix (Fin r) (Fin r) ℂ) i).comp j) 0) := by`.

Rewrite using `[map_zero]`. Conclude with `GlobalTheory.CompactDualExists.exp_strict`. Conclude with `h2.comp 0 h1)`. Use the proof step `(hL₀.comp continuous_suMat).continuousAt`. Use the proof step `(by ext1 A; exact one_mul A) (fun g h => rfl)`.

Use the proof step `(fun ε hε => by`. Rewrite using `[← Set.image_image (suExp hd), LinearEquiv.image_symm_eq_preimage]`. Conclude with `image_suExp_mem_nhds hd ((isOpen_ball.preimage hb').mem_nhds (by simpa using hε)))`. Use `set s := ENNReal.ofReal √|(Matrix.of fun k l => trForm (b k).1 (b l).1).det| with hs`. Establish `hs0 : s ≠ 0` using `(ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 (abs_pos.2 (det_gram_ne_zero hH b)))).ne'`.

Establish `hst : s ≠ ⊤` using `ENNReal.ofReal_ne_top`. Use `⟨c / s, ENNReal.div_ne_zero.2 ⟨hc0, hst⟩, ENNReal.div_ne_top hct hs0, _, b, ?_⟩` and prove the remaining obligations. Rewrite using `[← hs, ENNReal.div_mul_cancel hs0 hst]`. Use `hc.congr fun ε => ?_` and prove the remaining obligations. Use `congr 2`.

Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, rfl⟩`. Conclude with `⟨t, ht, fun i => rfl⟩`. Introduce and unpack `⟨t, ht, h⟩`.

Conclude with `⟨t, ht, suMat_injective (funext fun i => (h i).symm)⟩`.
-/
theorem exists_traceDensity : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : ι → Matrix (Fin r) (Fin r) ℂ),
    (∀ i, (H i).IsHermitian ∧ (H i).det ≠ 0) → ∀ [MeasurableSpace (suGrp H)] [BorelSpace (suGrp H)]
    (m : Measure (suGrp H)), m.IsHaarMeasure → ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ TraceDensity H m c := by
  intro ι _ r H hH _ _ m hm
  have hd : ∀ i, (H i).det ≠ 0 := fun i => (hH i).2
  let b := Module.finBasis ℝ (suLie H)
  let j : (Fin (Module.finrank ℝ (suLie H)) → ℝ) →L[ℝ] (ι → Matrix (Fin r) (Fin r) ℂ) :=
    LinearMap.toContinuousLinearMap ((suLie H).subtype ∘ₗ b.equivFun.symm.toLinearMap)
  have hb : Continuous b.equivFun.symm := b.equivFun.symm.toLinearMap.continuous_of_finiteDimensional
  have hb' : Continuous b.equivFun := b.equivFun.toLinearMap.continuous_of_finiteDimensional
  let L₀ : (ι → Matrix (Fin r) (Fin r) ℂ) →ₗ[ℝ]
      ((ι → Matrix (Fin r) (Fin r) ℂ) →L[ℝ] (ι → Matrix (Fin r) (Fin r) ℂ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℝ _
  have hL₀ : Continuous L₀ := L₀.continuous_of_finiteDimensional
  obtain ⟨c, hc0, hct, hc⟩ := exists_density_of_immersion _ (ι → Matrix (Fin r) (Fin r) ℂ) (suGrp H)
    volume m (fun t => suExp hd (b.equivFun.symm t)) suMat j
    (Subtype.val_injective.comp b.equivFun.symm.injective) (fun g => L₀ (suMat g))
    ((continuous_suExp hd).comp hb)
    (suMat_injective (funext fun i => by
      rw [map_zero]; exact NormedSpace.exp_zero (𝔸 := Matrix (Fin r) (Fin r) ℂ)))
    (by
      refine hasStrictFDerivAt_pi''  fun i => ?_
      have h1 := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Matrix (Fin r) (Fin r) ℂ) i).comp
        j).hasStrictFDerivAt (x := 0)
      have h2 : HasStrictFDerivAt (𝕜 := ℝ) (NormedSpace.exp : Matrix (Fin r) (Fin r) ℂ → _)
          (ContinuousLinearMap.id ℝ _) (((ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : ι => Matrix (Fin r) (Fin r) ℂ) i).comp j) 0) := by
        rw [map_zero]; exact GlobalTheory.CompactDualExists.exp_strict
      exact h2.comp 0 h1)
    (hL₀.comp continuous_suMat).continuousAt
    (by ext1 A; exact one_mul A) (fun g h => rfl)
    (fun ε hε => by
      rw [← Set.image_image (suExp hd), LinearEquiv.image_symm_eq_preimage]
      exact image_suExp_mem_nhds hd ((isOpen_ball.preimage hb').mem_nhds (by simpa using hε)))
  set s := ENNReal.ofReal √|(Matrix.of fun k l => trForm (b k).1 (b l).1).det| with hs
  have hs0 : s ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 (abs_pos.2 (det_gram_ne_zero hH b)))).ne'
  have hst : s ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨c / s, ENNReal.div_ne_zero.2 ⟨hc0, hst⟩, ENNReal.div_ne_top hct hs0, _, b, ?_⟩
  rw [← hs, ENNReal.div_mul_cancel hs0 hst]
  refine hc.congr fun ε => ?_
  congr 2
  ext g
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, fun i => rfl⟩
  · rintro ⟨t, ht, h⟩; exact ⟨t, ht, suMat_injective (funext fun i => (h i).symm)⟩

/- English proof (translation)
Take `⟨n, b, h⟩` from `h`. Use `⟨n, b, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Use `(ENNReal.Tendsto.const_mul h (Or.inr ENNReal.coe_ne_top)).congr fun ε => ?_` and prove the remaining obligations. Rewrite using `[Measure.coe_nnreal_smul_apply, mul_div_assoc]`.
-/
theorem TraceDensity.smul [Fintype ι] [MeasurableSpace (suGrp H)] {m : Measure (suGrp H)} {c : ℝ≥0∞}
    (h : TraceDensity H m c) (a : ℝ≥0) : TraceDensity H (a • m) (a * c) := by
  obtain ⟨n, b, h⟩ := h
  refine ⟨n, b, ?_⟩
  rw [mul_assoc]
  refine (ENNReal.Tendsto.const_mul h (Or.inr ENNReal.coe_ne_top)).congr fun ε => ?_
  rw [Measure.coe_nnreal_smul_apply, mul_div_assoc]

end GlobalTheory.SUVol
