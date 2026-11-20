import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange

open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ]

/- English proof (translation)
Simplify using `only [RiemLat.ip, sum_dotProduct, smul_dotProduct, smul_eq_mul]`.
-/
theorem ip_sum_right (R : RiemLat E g Λ) {k : ℕ} (x : Fin g → ℂ) (a : Fin k → ℂ)
    (u : Fin k → Fin g → ℂ) : R.ip x (∑ j, a j • u j) = ∑ j, a j * R.ip x (u j) := by
  simp only [RiemLat.ip, sum_dotProduct, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Simplify using `only [RiemLat.ip, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]`.
-/
theorem ip_sum_left (R : RiemLat E g Λ) {k : ℕ} (a : Fin k → ℂ) (u : Fin k → Fin g → ℂ)
    (y : Fin g → ℂ) : R.ip (∑ i, a i • u i) y = ∑ i, star (a i) * R.ip (u i) y := by
  simp only [RiemLat.ip, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul,
    dotProduct_sum, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Establish `h` using `R.herm`. Simplify using `only [RiemLat.ip]`. Rewrite using `[← star_dotProduct_star, star_mulVec, star_star, h.eq, dotProduct_comm, dotProduct_mulVec]`. Conclude with `dotProduct_comm _ _`.
-/
theorem star_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : star (R.ip x y) = R.ip y x := by
  have h := R.herm
  simp only [RiemLat.ip]
  rw [← star_dotProduct_star, star_mulVec, star_star, h.eq, dotProduct_comm, dotProduct_mulVec]
  exact dotProduct_comm _ _

/- English proof (translation)
Use extensionality with `a a'`. Simplify using `only [RiemLat.gram, Matrix.of_apply, ip_sum_left, ip_sum_right, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_comb (R : RiemLat E g Λ) {k l : ℕ} (T : Matrix (Fin l) (Fin k) ℂ)
    (u : Fin k → Fin g → ℂ) :
    R.gram (fun a => ∑ i, T a i • u i) = T.map star * R.gram u * Tᵀ := by
  ext a a'
  simp only [RiemLat.gram, Matrix.of_apply, ip_sum_left, ip_sum_right, Matrix.mul_apply,
    Matrix.map_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Establish `h1 : (T.map star).det = star T.det`. Establish `: T.map star = Tᴴᵀ` using `by ext; simp`. Rewrite using `[this, det_transpose, det_conjTranspose]`. Rewrite using `[gram_comb, det_mul, det_mul, det_transpose, h1]`. Establish `h2 : star T.det * (R.gram u).det * T.det = (Complex.normSq T.det : ℂ) * (R.gram u).det`.

Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Simplify using `only [Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, Complex.re_ofReal_mul]`.
-/
theorem gram_comb_det (R : RiemLat E g Λ) {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ)
    (u : Fin k → Fin g → ℂ) :
    (R.gram (fun a => ∑ i, T a i • u i)).det.re = Complex.normSq T.det * (R.gram u).det.re := by
  have h1 : (T.map star).det = star T.det := by
    have : T.map star = Tᴴᵀ := by ext; simp
    rw [this, det_transpose, det_conjTranspose]
  rw [gram_comb, det_mul, det_mul, det_transpose, h1]
  have h2 : star T.det * (R.gram u).det * T.det = (Complex.normSq T.det : ℂ) * (R.gram u).det := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [h2, Complex.re_ofReal_mul]

/- English proof (translation)
Simplify using `only [Finset.smul_sum, Matrix.vecMul, dotProduct, Finset.sum_smul, smul_smul]`. Conclude with `Finset.sum_comm`.
-/
theorem sum_comb {V : Type} [AddCommGroup V] [Module ℂ V] {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ)
    (u : Fin k → V) (v : Fin k → ℂ) :
    ∑ i, v i • ∑ j, T i j • u j = ∑ j, (v ᵥ* T) j • u j := by
  simp only [Finset.smul_sum, Matrix.vecMul, dotProduct, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

/- English proof (translation)
Introduce `h`. Take `⟨v, hv, hvT⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 h`. Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `Fintype.linearIndependent_iff.1 hc v ?_ i` and prove the remaining obligations.

Rewrite using `[sum_comb, hvT]`. Simplify using the standard rewrite rules.
-/
theorem det_ne_zero_of_comb {V : Type} [AddCommGroup V] [Module ℂ V] {k : ℕ}
    (T : Matrix (Fin k) (Fin k) ℂ) (u : Fin k → V)
    (hc : LinearIndependent ℂ fun i => ∑ j, T i j • u j) : T.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hvT⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  apply hv
  funext i
  refine Fintype.linearIndependent_iff.1 hc v ?_ i
  rw [sum_comb, hvT]
  simp

/- English proof (translation)
Use `Fintype.linearIndependent_iff.2 fun v hv i => ?_` and prove the remaining obligations. Rewrite `hv` using `[sum_comb]`. Establish `h0 : v ᵥ* T = 0` using `funext fun j => Fintype.linearIndependent_iff.1 hu _ hv j`. Use `Matrix.eq_zero_of_vecMul_eq_zero hT h0` as an intermediate fact. Simplify using `[this]`.
-/
theorem linearIndependent_comb {V : Type} [AddCommGroup V] [Module ℂ V] {k : ℕ}
    (T : Matrix (Fin k) (Fin k) ℂ) (u : Fin k → V) (hu : LinearIndependent ℂ u)
    (hT : T.det ≠ 0) : LinearIndependent ℂ fun i => ∑ j, T i j • u j := by
  refine Fintype.linearIndependent_iff.2 fun v hv i => ?_
  rw [sum_comb] at hv
  have h0 : v ᵥ* T = 0 := funext fun j => Fintype.linearIndependent_iff.1 hu _ hv j
  have := Matrix.eq_zero_of_vecMul_eq_zero hT h0
  simp [this]

/- English proof (translation)
Simplify using `only [Matrix.det_apply]`. Use `DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_smul ?_ _` and prove the remaining obligations. Establish `h1 : ∀ s : Finset (Fin k), DifferentiableOn ℂ (fun t => ∏ i ∈ s, M t (σ i) i) W`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simpa using differentiableOn_const (1 : ℂ)`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.prod_insert ha]`. Conclude with `(h _ _).mul ih`. Conclude with `h1 _`.
-/
theorem differentiableOn_det {n k : ℕ} {W : Set (Fin n → ℂ)}
    {M : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ i j, DifferentiableOn ℂ (fun t => M t i j) W) :
    DifferentiableOn ℂ (fun t => (M t).det) W := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_smul ?_ _
  have h1 : ∀ s : Finset (Fin k), DifferentiableOn ℂ (fun t => ∏ i ∈ s, M t (σ i) i) W := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using differentiableOn_const (1 : ℂ)
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h _ _).mul ih
  exact h1 _

/- English proof (translation)
Establish `hH : (R.gram u).IsHermitian`. Use extensionality with `a b`. Simplify using `only [RiemLat.gram, Matrix.conjTranspose_apply, Matrix.of_apply]`. Conclude with `star_ip R _ _`. Establish `hq : ∀ x : Fin k → ℂ, star x ⬝ᵥ (R.gram u) *ᵥ x = R.ip (∑ i, x i • u i) (∑ i, x i • u i)`.

Introduce `x`. Simplify using `only [ip_sum_left, ip_sum_right, dotProduct, mulVec, RiemLat.gram, Matrix.of_apply, Finset.mul_sum, Pi.star_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hP : (R.gram u).PosDef`. Use `PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_` and prove the remaining obligations. Rewrite using `[hq]`. Use `set w := ∑ i, x i • u i with hw`. Establish `hw0 : w ≠ 0` using `fun h0 => hx (funext (Fintype.linearIndependent_iff.1 hu x h0))`.

Use `Complex.pos_iff.2 ⟨R.pos w hw0, ?_⟩` and prove the remaining obligations. Use `Complex.conj_eq_iff_im.1 (star_ip R w w)` as an intermediate fact. Simplify using `using this.symm`. Conclude with `(Complex.pos_iff.1 hP.det_pos).1`.
-/
theorem gram_det_re_pos (R : RiemLat E g Λ) {k : ℕ} (u : Fin k → Fin g → ℂ)
    (hu : LinearIndependent ℂ u) : 0 < (R.gram u).det.re := by
  have hH : (R.gram u).IsHermitian := by
    ext a b
    simp only [RiemLat.gram, Matrix.conjTranspose_apply, Matrix.of_apply]
    exact star_ip R _ _
  have hq : ∀ x : Fin k → ℂ, star x ⬝ᵥ (R.gram u) *ᵥ x = R.ip (∑ i, x i • u i) (∑ i, x i • u i) := by
    intro x
    simp only [ip_sum_left, ip_sum_right, dotProduct, mulVec, RiemLat.gram, Matrix.of_apply,
      Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hP : (R.gram u).PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    rw [hq]
    set w := ∑ i, x i • u i with hw
    have hw0 : w ≠ 0 := fun h0 =>
      hx (funext (Fintype.linearIndependent_iff.1 hu x h0))
    refine Complex.pos_iff.2 ⟨R.pos w hw0, ?_⟩
    have := Complex.conj_eq_iff_im.1 (star_ip R w w)
    simpa using this.symm
  exact (Complex.pos_iff.1 hP.det_pos).1

/- English proof (translation)
Introduce `E _ _ _ g Λ _ _ n m W R b c t₀ hW ht₀ hb hc hbi hcs hci`. Establish `hinj : LinearMap.ker (Fintype.linearCombination ℂ fun i => b i t₀) = ⊥`. Use `LinearMap.ker_eq_bot'.2 fun v hv => ?_` and prove the remaining obligations. Rewrite `hv` using `[Fintype.linearCombination_apply]`. Conclude with `funext (Fintype.linearIndependent_iff.1 (hbi t₀ ht₀) v hv)`.

Take `⟨φ, hφ⟩` from `LinearMap.exists_leftInverse_of_injective _ hinj`. Establish `hφb : ∀ i, φ (b i t₀) = Pi.single i 1`. Introduce `i`. Establish `h1` using `LinearMap.congr_fun hφ (Pi.single i 1)`. Simplify `h1` using `[Fintype.linearCombination_apply_single]`.

Establish `hφd : ∀ u : (Fin n → ℂ) → Fin g → ℂ, DifferentiableOn ℂ u W → ∀ j, DifferentiableOn ℂ (fun t => φ (u t) j) W`. Introduce `u hu j`. Establish `h1 : DifferentiableOn ℂ (fun t => LinearMap.toContinuousLinearMap φ (u t)) W` using `(LinearMap.toContinuousLinearMap φ).differentiable.comp_differentiableOn hu`. Conclude with `differentiableOn_pi.1 h1 j`. Set `Bm : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ` to `fun t => Matrix.of fun i j => φ (b i t) j`.

Set `Cm : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ` to `fun t => Matrix.of fun i j => φ (c i t) j`. Establish `hdB : DifferentiableOn ℂ (fun t => (Bm t).det) W` using `differentiableOn_det fun i j => hφd _ (hb i) j`. Establish `hdC : DifferentiableOn ℂ (fun t => (Cm t).det) W` using `differentiableOn_det fun i j => hφd _ (hc i) j`. Establish `hT : ∀ t ∈ W, ∃ T : Matrix (Fin m) (Fin m) ℂ, (∀ i, c i t = ∑ j, T i j • b j t) ∧ Cm t = T * Bm t`. Introduce `t ht`.

Establish `h1` using `fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hcs t ht i)`. Use `choose T hT using h1`. Use `⟨Matrix.of T, fun i => (hT i).symm, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [Cm, Bm, Matrix.of_apply, Matrix.mul_apply, ← hT i, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.

Establish `hB0 : Bm t₀ = 1`. Use extensionality with `i j`. Simplify using `only [Bm, Matrix.of_apply, hφb, Matrix.one_apply, Pi.single_apply]`. Distinguish the cases in `h : i = j`. Simplify using `[h]`.

Simplify using `[h, Ne.symm h]`. Take `⟨T₀, hT₀, hCT₀⟩` from `hT t₀ ht₀`. Establish `hf₀ : (Cm t₀).det ≠ 0`. Rewrite using `[hCT₀, hB0, mul_one]`. Establish `h1 : (fun i => c i t₀) = fun i => ∑ j, T₀ i j • b j t₀` using `funext hT₀`.

Conclude with `det_ne_zero_of_comb T₀ _ (h1 ▸ hci)`. Set `f₀ : ℂ` to `(Cm t₀).det`. Set `q : (Fin n → ℂ) → ℂ` to `fun t => (Cm t).det / (Bm t).det / f₀`. Set `V₁ : Set (Fin n → ℂ)` to `W ∩ (fun t => (Bm t).det) ⁻¹' {0}ᶜ`. Establish `hV₁ : IsOpen V₁` using `hdB.continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton`.

Establish `hfd : DifferentiableOn ℂ (fun t => (Cm t).det / (Bm t).det) V₁`. Simplify using `only [div_eq_mul_inv]`. Establish `hinv : DifferentiableOn ℂ (fun t => ((Bm t).det)⁻¹) V₁` using `DifferentiableOn.fun_inv (hdB.mono Set.inter_subset_left) fun t ht => ht.2`. Conclude with `(hdC.mono Set.inter_subset_left).mul hinv`. Establish `hqd : DifferentiableOn ℂ q V₁`.

Establish `h1` using `hfd.mul_const f₀⁻¹`. Simplify `h1` using `only [q, div_eq_mul_inv]`. Set `V : Set (Fin n → ℂ)` to `V₁ ∩ q ⁻¹' Metric.ball 1 1`. Establish `hVo : IsOpen V` using `hqd.continuousOn.isOpen_inter_preimage hV₁ Metric.isOpen_ball`. Establish `hq0 : q t₀ = 1`.

Simplify using `only [q, f₀, hB0, det_one, div_one]`. Conclude with `div_self hf₀`. Establish `hslit : ∀ t ∈ V, q t ∈ Complex.slitPlane`. Introduce `t ht`. Establish `h1 : ‖q t - 1‖ < 1` using `by simpa [dist_eq_norm] using ht.2`.

Establish `h2` using `Complex.mem_slitPlane_of_norm_lt_one h1`. Simplify using `using h2`. Use `⟨V, hVo, ⟨⟨ht₀, by simp [hB0]⟩, by simp [hq0]⟩, fun t ht => ht.1.1, fun t => 2 * Complex.log (q t) + 2 * ((Real.log ‖f₀‖ : ℝ) : ℂ), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(((hqd.mono Set.inter_subset_left).clog hslit).const_mul 2).add_const _`. Introduce `t ht`.

Take `⟨T, hTc, hCT⟩` from `hT t ht.1.1`. Establish `hBne : (Bm t).det ≠ 0` using `ht.1.2`. Establish `hqne : q t ≠ 0` using `Complex.slitPlane_ne_zero (hslit t ht)`. Establish `hdet : T.det = q t * f₀`. Establish `h1 : (Cm t).det = T.det * (Bm t).det` using `by rw [hCT, det_mul]`.

Establish `hf₀' : f₀ ≠ 0` using `hf₀`. Use `show T.det = (Cm t).det / (Bm t).det / f₀ * f₀`. Rewrite using `[div_mul_cancel₀ _ hf₀', h1, mul_div_cancel_right₀ _ hBne]`. Establish `hTne : T.det ≠ 0`. Rewrite using `[hdet]`.

Conclude with `mul_ne_zero hqne hf₀`. Establish `hcf : (fun i => c i t) = fun i => ∑ j, T i j • b j t` using `funext hTc`. Use `⟨hcf ▸ linearIndependent_comb T _ (hbi t ht.1.1) hTne, ?_⟩` and prove the remaining obligations. Establish `hpos` using `gram_det_re_pos (R t) _ (hbi t ht.1.1)`. Rewrite using `[hcf, gram_comb_det, Real.log_mul (by simpa using hTne) hpos.ne', add_comm, hdet]`.

Use `congr 1`. Establish `hf₀n : ‖f₀‖ ≠ 0` using `norm_ne_zero_iff.2 hf₀`. Establish `hqn : ‖q t‖ ≠ 0` using `norm_ne_zero_iff.2 hqne`. Rewrite using `[Complex.normSq_eq_norm_sq, norm_mul, Real.log_pow, Real.log_mul (mul_ne_zero hqn hf₀n |> left_ne_zero_of_mul) hf₀n]`. Simplify using `[Complex.add_re, Complex.mul_re, Complex.log_re]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_gram_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (n m : ℕ) (W : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (b c : Fin m → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ), IsOpen W → t₀ ∈ W → (∀ i, DifferentiableOn ℂ (b i) W) → (∀ i, DifferentiableOn ℂ (c i) W) → (∀ t ∈ W, LinearIndependent ℂ fun i => b i t) → (∀ t ∈ W, ∀ i, c i t ∈ Submodule.span ℂ (Set.range fun j => b j t)) → LinearIndependent ℂ (fun i => c i t₀) → ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ W ∧ ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G V ∧ ∀ t ∈ V, LinearIndependent ℂ (fun i => c i t) ∧ Real.log ((R t).gram fun i => c i t).det.re = Real.log ((R t).gram fun i => b i t).det.re + (G t).re := by
  intro E _ _ _ g Λ _ _ n m W R b c t₀ hW ht₀ hb hc hbi hcs hci
  have hinj : LinearMap.ker (Fintype.linearCombination ℂ fun i => b i t₀) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
    rw [Fintype.linearCombination_apply] at hv
    exact funext (Fintype.linearIndependent_iff.1 (hbi t₀ ht₀) v hv)
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  have hφb : ∀ i, φ (b i t₀) = Pi.single i 1 := by
    intro i
    have h1 := LinearMap.congr_fun hφ (Pi.single i 1)
    simpa [Fintype.linearCombination_apply_single] using h1
  have hφd : ∀ u : (Fin n → ℂ) → Fin g → ℂ, DifferentiableOn ℂ u W →
      ∀ j, DifferentiableOn ℂ (fun t => φ (u t) j) W := by
    intro u hu j
    have h1 : DifferentiableOn ℂ (fun t => LinearMap.toContinuousLinearMap φ (u t)) W :=
      (LinearMap.toContinuousLinearMap φ).differentiable.comp_differentiableOn hu
    exact differentiableOn_pi.1 h1 j
  let Bm : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ := fun t => Matrix.of fun i j => φ (b i t) j
  let Cm : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ := fun t => Matrix.of fun i j => φ (c i t) j
  have hdB : DifferentiableOn ℂ (fun t => (Bm t).det) W :=
    differentiableOn_det fun i j => hφd _ (hb i) j
  have hdC : DifferentiableOn ℂ (fun t => (Cm t).det) W :=
    differentiableOn_det fun i j => hφd _ (hc i) j
  have hT : ∀ t ∈ W, ∃ T : Matrix (Fin m) (Fin m) ℂ,
      (∀ i, c i t = ∑ j, T i j • b j t) ∧ Cm t = T * Bm t := by
    intro t ht
    have h1 := fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hcs t ht i)
    choose T hT using h1
    refine ⟨Matrix.of T, fun i => (hT i).symm, ?_⟩
    ext i j
    simp only [Cm, Bm, Matrix.of_apply, Matrix.mul_apply, ← hT i, map_sum, map_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hB0 : Bm t₀ = 1 := by
    ext i j
    simp only [Bm, Matrix.of_apply, hφb, Matrix.one_apply, Pi.single_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  obtain ⟨T₀, hT₀, hCT₀⟩ := hT t₀ ht₀
  have hf₀ : (Cm t₀).det ≠ 0 := by
    rw [hCT₀, hB0, mul_one]
    have h1 : (fun i => c i t₀) = fun i => ∑ j, T₀ i j • b j t₀ := funext hT₀
    exact det_ne_zero_of_comb T₀ _ (h1 ▸ hci)
  let f₀ : ℂ := (Cm t₀).det
  let q : (Fin n → ℂ) → ℂ := fun t => (Cm t).det / (Bm t).det / f₀
  let V₁ : Set (Fin n → ℂ) := W ∩ (fun t => (Bm t).det) ⁻¹' {0}ᶜ
  have hV₁ : IsOpen V₁ := hdB.continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton
  have hfd : DifferentiableOn ℂ (fun t => (Cm t).det / (Bm t).det) V₁ := by
    simp only [div_eq_mul_inv]
    have hinv : DifferentiableOn ℂ (fun t => ((Bm t).det)⁻¹) V₁ :=
      DifferentiableOn.fun_inv (hdB.mono Set.inter_subset_left) fun t ht => ht.2
    exact (hdC.mono Set.inter_subset_left).mul hinv
  have hqd : DifferentiableOn ℂ q V₁ := by
    have h1 := hfd.mul_const f₀⁻¹
    simpa only [q, div_eq_mul_inv] using h1
  let V : Set (Fin n → ℂ) := V₁ ∩ q ⁻¹' Metric.ball 1 1
  have hVo : IsOpen V := hqd.continuousOn.isOpen_inter_preimage hV₁ Metric.isOpen_ball
  have hq0 : q t₀ = 1 := by
    simp only [q, f₀, hB0, det_one, div_one]
    exact div_self hf₀
  have hslit : ∀ t ∈ V, q t ∈ Complex.slitPlane := by
    intro t ht
    have h1 : ‖q t - 1‖ < 1 := by simpa [dist_eq_norm] using ht.2
    have h2 := Complex.mem_slitPlane_of_norm_lt_one h1
    simpa using h2
  refine ⟨V, hVo, ⟨⟨ht₀, by simp [hB0]⟩, by simp [hq0]⟩, fun t ht => ht.1.1,
    fun t => 2 * Complex.log (q t) + 2 * ((Real.log ‖f₀‖ : ℝ) : ℂ), ?_, ?_⟩
  · exact (((hqd.mono Set.inter_subset_left).clog hslit).const_mul 2).add_const _
  · intro t ht
    obtain ⟨T, hTc, hCT⟩ := hT t ht.1.1
    have hBne : (Bm t).det ≠ 0 := ht.1.2
    have hqne : q t ≠ 0 := Complex.slitPlane_ne_zero (hslit t ht)
    have hdet : T.det = q t * f₀ := by
      have h1 : (Cm t).det = T.det * (Bm t).det := by rw [hCT, det_mul]
      have hf₀' : f₀ ≠ 0 := hf₀
      show T.det = (Cm t).det / (Bm t).det / f₀ * f₀
      rw [div_mul_cancel₀ _ hf₀', h1, mul_div_cancel_right₀ _ hBne]
    have hTne : T.det ≠ 0 := by
      rw [hdet]
      exact mul_ne_zero hqne hf₀
    have hcf : (fun i => c i t) = fun i => ∑ j, T i j • b j t := funext hTc
    refine ⟨hcf ▸ linearIndependent_comb T _ (hbi t ht.1.1) hTne, ?_⟩
    have hpos := gram_det_re_pos (R t) _ (hbi t ht.1.1)
    rw [hcf, gram_comb_det, Real.log_mul (by simpa using hTne) hpos.ne', add_comm, hdet]
    congr 1
    have hf₀n : ‖f₀‖ ≠ 0 := norm_ne_zero_iff.2 hf₀
    have hqn : ‖q t‖ ≠ 0 := norm_ne_zero_iff.2 hqne
    rw [Complex.normSq_eq_norm_sq, norm_mul, Real.log_pow, Real.log_mul (mul_ne_zero hqn hf₀n |> left_ne_zero_of_mul) hf₀n]
    simp [Complex.add_re, Complex.mul_re, Complex.log_re]
    ring

end GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange
