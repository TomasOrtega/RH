import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.SphericalFunctionFixedUnitaryEqOne

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Base0

private def PhiA (k : ℕ) (A : ℝ) (g : Mt k 0) : ℝ≥0∞ := ENNReal.ofReal (gN (Matrix.of g) ^ (-A))

/- English proof (translation)
The claim follows from `ENNReal.ofReal_ne_top`.
-/
private lemma phiA_ne_top (k : ℕ) (A : ℝ) (g : Mt k 0) : PhiA k A g ≠ ∞ := ENNReal.ofReal_ne_top

/- English proof (translation)
Establish `hc : Continuous fun g : Mt k 0 => gN (Matrix.of g)`. Unfold `gN`. Apply `Continuous.sqrt` to reduce the goal to its premises. Use `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))`.

Unfold `PhiA`. Conclude with `ENNReal.measurable_ofReal.comp (hc.measurable.pow_const (-A))`.
-/
private lemma measurable_phiA (k : ℕ) (A : ℝ) : Measurable (PhiA k A) := by
  have hc : Continuous fun g : Mt k 0 => gN (Matrix.of g) := by
    unfold gN
    apply Continuous.sqrt
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))
  unfold PhiA
  exact ENNReal.measurable_ofReal.comp (hc.measurable.pow_const (-A))

private def Gf (k : ℕ) (σ : ℝ) (h g h' : Mt k 0) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt 2)⁻¹ * ‖((Matrix.of h)ᴴ *ᵥ ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0)) (iW k) +
    ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0) (iK k)‖) ^ (-σ)

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `hof : Continuous (fun M : Mt k 0 => (Matrix.of M : Mat k 0))` using `continuous_id`. Establish `h1 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.1` using `hof.comp continuous_fst`. Establish `h21 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.2.1` using `hof.comp (continuous_fst.comp continuous_snd)`. Establish `h22 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.2.2` using `hof.comp (continuous_snd.comp continuous_snd)`. Establish `hw : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => (Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0` using `(h21.matrix_mul h22).matrix_mulVec continuous_const`.

Establish `hv : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => (Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0)` using `h1.matrix_conjTranspose.matrix_mulVec hw`. Establish `hc : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => (Real.sqrt 2)⁻¹ * ‖((Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0)) (iW k) + ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0) (iK k)‖` using `continuous_const.mul ((((continuous_apply (iW k)).comp hv).add ((continuous_apply (iK k)).comp hw)).norm)`. Establish `hm : Measurable (fun p : Mt k 0 × Mt k 0 × Mt k 0 => ENNReal.ofReal ((Real.sqrt 2)⁻¹ * ‖((Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0)) (iW k) + ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0) (iK k)‖) ^ (-σ))` using `(ENNReal.measurable_ofReal.comp hc.measurable).pow_const (-σ)`. Unfold `Gf`. Conclude with `hm`.
-/
private lemma measurable_Gf (k : ℕ) (σ : ℝ) :
    Measurable (fun p : Mt k 0 × Mt k 0 × Mt k 0 => Gf k σ p.1 p.2.1 p.2.2) := by
  have hof : Continuous (fun M : Mt k 0 => (Matrix.of M : Mat k 0)) := continuous_id
  have h1 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.1 := hof.comp continuous_fst
  have h21 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.2.1 :=
    hof.comp (continuous_fst.comp continuous_snd)
  have h22 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.2.2 :=
    hof.comp (continuous_snd.comp continuous_snd)
  have hw : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 =>
      (Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0 :=
    (h21.matrix_mul h22).matrix_mulVec continuous_const
  have hv : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 =>
      (Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0) :=
    h1.matrix_conjTranspose.matrix_mulVec hw
  have hc : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 =>
      (Real.sqrt 2)⁻¹ * ‖((Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0)) (iW k) +
        ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0) (iK k)‖ :=
    continuous_const.mul ((((continuous_apply (iW k)).comp hv).add ((continuous_apply (iK k)).comp hw)).norm)
  have hm : Measurable (fun p : Mt k 0 × Mt k 0 × Mt k 0 => ENNReal.ofReal
      ((Real.sqrt 2)⁻¹ * ‖((Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0)) (iW k) +
        ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0) (iK k)‖) ^ (-σ)) :=
    (ENNReal.measurable_ofReal.comp hc.measurable).pow_const (-σ)
  unfold Gf
  exact hm

/- English proof (translation)
Establish `h` using `hs 0`. Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Simplify using `[s0] at h`. Take `⟨h1, h2⟩` from `h`. Apply the tactic sequence `constructor <;> linarith`.
-/
private lemma s_facts {k : ℕ} (hk : 1 ≤ k) {s : Fin (0 + 1) → ℝ} (hs : SAdm k 0 s) :
    0 ≤ s 0 ∧ s 0 < k := by
  have h := hs 0
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  simp [s0] at h
  obtain ⟨h1, h2⟩ := h
  constructor <;> linarith

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]`. Use `push_cast`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_eq_conj_mul_self]`.

Both sides reduce to the same expression.
-/
private lemma nsq_tr_lemma {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, ∑ j, Complex.normSq (Y i j) : ℝ) : ℂ) = (Yᴴ * Y).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/- English proof (translation)
Unfold `gN`. Use `congr 1`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[nsq_tr_lemma, nsq_tr_lemma, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]`.
-/
private lemma gN_left_lemma_2 {k r : ℕ} {κ : Mat k r} (hκ : κᴴ * κ = 1) (X : Mat k r) : gN (κ * X) = gN X := by
  unfold gN
  congr 1
  apply Complex.ofReal_injective
  rw [nsq_tr_lemma, nsq_tr_lemma, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]

/- English proof (translation)
Establish `hκ' : κ * κᴴ = 1` using `by first`. Consider the case `exact mul_eq_one_comm.mp hκ`. Consider the case `exact (Matrix.mul_eq_one_comm).1 hκ`. Consider the case `exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) hκ`. Unfold `gN`.

Use `congr 1`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[nsq_tr_lemma, nsq_tr_lemma, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hκ', Matrix.mul_one]`.
-/
private lemma gN_right_lemma_3 {k r : ℕ} {κ : Mat k r} (hκ : κᴴ * κ = 1) (X : Mat k r) : gN (X * κ) = gN X := by
  have hκ' : κ * κᴴ = 1 := by
    first
      | exact mul_eq_one_comm.mp hκ
      | exact (Matrix.mul_eq_one_comm).1 hκ
      | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) hκ
  unfold gN
  congr 1
  apply Complex.ofReal_injective
  rw [nsq_tr_lemma, nsq_tr_lemma, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, Matrix.mul_assoc, hκ', Matrix.mul_one]

/- English proof (translation)
Introduce `κ hκ g`. Establish `hu : κᴴ * κ = 1`. Simplify using `only [Kset, Set.mem_setOf_eq] at hκ`. Conclude with `hκ.2`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [PhiA, lmulM]`. Conclude with `congrArg (fun t => ENNReal.ofReal (t ^ (-A))) (gN_left_lemma_2 hu (Matrix.of g))`. Simplify using `only [PhiA, rmulF]`. Conclude with `congrArg (fun t => ENNReal.ofReal (t ^ (-A))) (gN_right_lemma_3 hu (Matrix.of g))`.
-/
private lemma phiA_inv (k : ℕ) (A : ℝ) : ∀ κ ∈ Kset k 0, ∀ g,
    PhiA k A (lmulM κ g) = PhiA k A g ∧ PhiA k A (rmulF κ g) = PhiA k A g := by
  intro κ hκ g
  have hu : κᴴ * κ = 1 := by
    simp only [Kset, Set.mem_setOf_eq] at hκ
    exact hκ.2
  refine ⟨?_, ?_⟩
  · simp only [PhiA, lmulM]
    exact congrArg (fun t => ENNReal.ofReal (t ^ (-A))) (gN_left_lemma_2 hu (Matrix.of g))
  · simp only [PhiA, rmulF]
    exact congrArg (fun t => ENNReal.ofReal (t ^ (-A))) (gN_right_lemma_3 hu (Matrix.of g))

/- English proof (translation)
Rewrite using `[hT k 0 s μG (PhiA k A) hk hμG (measurable_phiA k A) (phiA_inv k A) h hh.1 h' hh'.1, sphericalFunction_fixedUnitary_eq_one hk hh, sphericalFunction_fixedUnitary_eq_one hk hh', mul_one, ENNReal.ofReal_one, one_mul]`. Both sides reduce to the same expression.
-/
private lemma avg_one {k : ℕ} (hk : 1 ≤ k) (hT : TBoth) {s : Fin (0 + 1) → ℝ} {μG : Measure (Mt k 0)}
    (hμG : IsHaarOn (GV k 0) μG) (A : ℝ) {h h' : Mat k 0} (hh : h ∈ U0 k) (hh' : h' ∈ U0 k) :
    ∫⁻ g, PhiA k A g * FsE k 0 s (h⁻¹ * Matrix.of g * h') ∂μG = JInt μG A s := by
  rw [hT k 0 s μG (PhiA k A) hk hμG (measurable_phiA k A) (phiA_inv k A) h hh.1 h' hh'.1, sphericalFunction_fixedUnitary_eq_one hk hh,
    sphericalFunction_fixedUnitary_eq_one hk hh', mul_one, ENNReal.ofReal_one, one_mul]
  rfl

/- English proof (translation)
Establish `hs : Measurable fun q : (Mt k 0 × Mt k 0) × Mt k 0 => q.1.2` using `measurable_snd.comp measurable_fst`. Establish `h1` using `(measurable_phiA k A).comp hs`. Establish `hm : Measurable fun q : (Mt k 0 × Mt k 0) × Mt k 0 => (q.2, q.1.2, q.1.1)` using `by fun_prop`. Establish `h2` using `(measurable_Gf k σ).comp hm`. Simplify using `only [Function.comp_def] at h1 h2`.

Conclude with `h1.mul h2`.
-/
private lemma measurable_haarKernelTriple (k : ℕ) (A σ : ℝ) :
    Measurable (fun q : (Mt k 0 × Mt k 0) × Mt k 0 => PhiA k A q.1.2 * Gf k σ q.2 q.1.2 q.1.1) := by
  have hs : Measurable fun q : (Mt k 0 × Mt k 0) × Mt k 0 => q.1.2 := measurable_snd.comp measurable_fst
  have h1 := (measurable_phiA k A).comp hs
  have hm : Measurable fun q : (Mt k 0 × Mt k 0) × Mt k 0 => (q.2, q.1.2, q.1.1) := by fun_prop
  have h2 := (measurable_Gf k σ).comp hm
  simp only [Function.comp_def] at h1 h2
  exact h1.mul h2

/- English proof (translation)
Establish `step1 : JInt μG A s * (ν Set.univ * ν Set.univ) = ∫⁻ h', ∫⁻ h, JInt μG A s ∂ν ∂ν`. Rewrite using `[lintegral_const, lintegral_const, mul_assoc]`. Establish `step2 : ∫⁻ h', ∫⁻ h, JInt μG A s ∂ν ∂ν = ∫⁻ h', ∫⁻ h, ∫⁻ g, PhiA k A g * Gf k (s 0) h g h' ∂μG ∂ν ∂ν`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_mem_fixedUnitary hν] with h' hh'`.

Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_mem_fixedUnitary hν] with h hh`. Rewrite using `[← avg_one hk hT hμG A hh hh']`. Use `lintegral_congr (fun g => ?_)` and prove the remaining obligations. Rewrite using `[fsE_avg hk hh]`.

Both sides reduce to the same expression. Establish `step3 : ∫⁻ h', ∫⁻ h, ∫⁻ g, PhiA k A g * Gf k (s 0) h g h' ∂μG ∂ν ∂ν = ∫⁻ h', ∫⁻ g, ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂μG ∂ν`. Use `lintegral_congr (fun h' => ?_)` and prove the remaining obligations. Establish `hmap : Measurable (fun p : Mt k 0 × Mt k 0 => ((h', p.2), p.1))` using `(measurable_const.prodMk measurable_snd).prodMk measurable_fst`. Establish `hm : Measurable ((fun q : (Mt k 0 × Mt k 0) × Mt k 0 => PhiA k A q.1.2 * Gf k (s 0) q.2 q.1.2 q.1.1) ∘ (fun p : Mt k 0 × Mt k 0 => ((h', p.2), p.1)))` using `Measurable.comp (measurable_haarKernelTriple k A (s 0)) hmap`.

Conclude with `lintegral_lintegral_swap hm.aemeasurable`. Establish `step4 : ∫⁻ h', ∫⁻ g, ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂μG ∂ν = ∫⁻ g, ∫⁻ h', ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂ν ∂μG` using `lintegral_lintegral_swap (Measurable.lintegral_prod_right' (measurable_haarKernelTriple k A (s 0))).aemeasurable`. Establish `step5 : ∫⁻ g, ∫⁻ h', ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂ν ∂μG = ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG`. Use `lintegral_congr (fun g => ?_)` and prove the remaining obligations. Rewrite using `[← lintegral_const_mul' _ _ (phiA_ne_top k A g)]`.

Use `lintegral_congr (fun h' => ?_)` and prove the remaining obligations. Rewrite using `[lintegral_const_mul' _ _ (phiA_ne_top k A g)]`. Rewrite using `[step1, step2, step3, step4, step5]`.
-/
private lemma avg_key {k : ℕ} (hk : 1 ≤ k) (hT : TBoth) {s : Fin (0 + 1) → ℝ} {μG : Measure (Mt k 0)}
    (hμG : IsHaarOn (GV k 0) μG) (A : ℝ) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν)
    [IsFiniteMeasure ν] [SigmaFinite μG] :
    JInt μG A s * (ν Set.univ * ν Set.univ) =
      ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG := by
  have step1 : JInt μG A s * (ν Set.univ * ν Set.univ) = ∫⁻ h', ∫⁻ h, JInt μG A s ∂ν ∂ν := by
    rw [lintegral_const, lintegral_const, mul_assoc]
  have step2 : ∫⁻ h', ∫⁻ h, JInt μG A s ∂ν ∂ν =
      ∫⁻ h', ∫⁻ h, ∫⁻ g, PhiA k A g * Gf k (s 0) h g h' ∂μG ∂ν ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_fixedUnitary hν] with h' hh'
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_fixedUnitary hν] with h hh
    rw [← avg_one hk hT hμG A hh hh']
    refine lintegral_congr (fun g => ?_)
    rw [fsE_avg hk hh]
    rfl
  have step3 : ∫⁻ h', ∫⁻ h, ∫⁻ g, PhiA k A g * Gf k (s 0) h g h' ∂μG ∂ν ∂ν =
      ∫⁻ h', ∫⁻ g, ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂μG ∂ν := by
    refine lintegral_congr (fun h' => ?_)
    have hmap : Measurable (fun p : Mt k 0 × Mt k 0 => ((h', p.2), p.1)) :=
      (measurable_const.prodMk measurable_snd).prodMk measurable_fst
    have hm : Measurable ((fun q : (Mt k 0 × Mt k 0) × Mt k 0 => PhiA k A q.1.2 * Gf k (s 0) q.2 q.1.2 q.1.1) ∘
        (fun p : Mt k 0 × Mt k 0 => ((h', p.2), p.1))) := Measurable.comp (measurable_haarKernelTriple k A (s 0)) hmap
    exact lintegral_lintegral_swap hm.aemeasurable
  have step4 : ∫⁻ h', ∫⁻ g, ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂μG ∂ν =
      ∫⁻ g, ∫⁻ h', ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂ν ∂μG :=
    lintegral_lintegral_swap (Measurable.lintegral_prod_right' (measurable_haarKernelTriple k A (s 0))).aemeasurable
  have step5 : ∫⁻ g, ∫⁻ h', ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂ν ∂μG =
      ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG := by
    refine lintegral_congr (fun g => ?_)
    rw [← lintegral_const_mul' _ _ (phiA_ne_top k A g)]
    refine lintegral_congr (fun h' => ?_)
    rw [lintegral_const_mul' _ _ (phiA_ne_top k A g)]
  rw [step1, step2, step3, step4, step5]

/- English proof (translation)
Establish `hc2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 : ℝ) / 2`. Rewrite using `[← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num`. Establish `hws` using `outer_ws hg`. Establish `hgkk : 1 ≤ ‖(Matrix.of g : Mat k 0) (iK k) (iK k)‖`. Establish `h1 : 1 ≤ Complex.normSq ((Matrix.of g : Mat k 0) (iK k) (iK k))`.

Use polynomial arithmetic with `[sq_nonneg (tW (iK k) (fun j => star ((Matrix.of g : Mat k 0) (iK k) j)))]`. Rewrite `h1` using `[← Complex.sq_norm]`. Use polynomial arithmetic with `[norm_nonneg ((Matrix.of g : Mat k 0) (iK k) (iK k))]`. Establish `hbn : ‖-star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖ = ‖(Matrix.of g : Mat k 0) (iK k) (iK k)‖`. Rewrite using `[norm_neg, norm_star]`.

Establish `hb0 : -star ((Matrix.of g : Mat k 0) (iK k) (iK k)) ≠ 0`. Introduce `h`. Rewrite `hbn` using `[h, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hvb : tW (iK k) (fun j => star ((Matrix.of g : Mat k 0) (iK k) j)) ^ 2 ≤ Complex.normSq (-star ((Matrix.of g : Mat k 0) (iK k) (iK k)))`.

Establish `: Complex.normSq (star ((Matrix.of g : Mat k 0) (iK k) (iK k))) = Complex.normSq ((Matrix.of g : Mat k 0) (iK k) (iK k))` using `Complex.normSq_conj _`. Rewrite using `[Complex.normSq_neg, this]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono_ae ?_` and prove the remaining obligations.

Use `filter_upwards [ae_mem_fixedUnitary hν] with h' hh'`. Take `⟨e, hne⟩` from `iso_y hk hg hh'.1`. Unfold `Gf`. Conclude with `bnd hk hν hσ (lam := (Real.sqrt 2)⁻¹) (by positivity) ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0) _ hne (le_of_eq e)`. Use `_ = (∫⁻ h', ENNReal.ofReal (1 / 4 * ‖((Matrix.of h')ᴴ *ᵥ (fun j => star ((Matrix.of g : Mat k 0) (iK k) j))) (iW k) + -star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖) ^ (-σ) ∂ν) * (C0 k σ ν + ν Set.univ) := by`.

Rewrite using `[lintegral_mul_const' _ _ hK1f]`. Use `congr 1`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_mem_fixedUnitary hν] with h' hh'`. Rewrite using `[outer_eq hk hh' (Matrix.of g)]`.

Use `congr 2`. Rewrite using `[← mul_assoc, hc2]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (ENNReal.ofReal (1 / 4 * ‖-star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖ / 2) ^ (-σ) * (C0 k σ ν + ν Set.univ)) * (C0 k σ ν + ν Set.univ) := mul_le_mul' (bnd hk hν hσ (by norm_num) _ _ hb0 hvb) le_rfl`. Use `_ ≤ (ENNReal.ofReal (1 / 8) ^ (-σ) * (C0 k σ ν + ν Set.univ)) * (C0 k σ ν + ν Set.univ) := mul_le_mul' (mul_le_mul' (ofReal_rpow_neg_anti hσ (by rw [hbn]; linarith)) le_rfl) le_rfl`.

Use `_ = (C0 k σ ν + ν Set.univ) * (ENNReal.ofReal (1 / 8) ^ (-σ) * (C0 k σ ν + ν Set.univ)) := mul_comm _ _`.
-/
private lemma ptw {k : ℕ} (hk : 1 ≤ k) {σ : ℝ} (hσ : 0 ≤ σ) {ν : Measure (Mt k 0)}
    (hν : IsHaarOn (U0 k) ν) (hK1f : C0 k σ ν + ν Set.univ ≠ ∞) (g : Mt k 0)
    (hg : (Matrix.of g : Mat k 0) ∈ GV k 0) :
    ∫⁻ h', ∫⁻ h, Gf k σ h g h' ∂ν ∂ν ≤
      (C0 k σ ν + ν Set.univ) * (ENNReal.ofReal (1 / 8) ^ (-σ) * (C0 k σ ν + ν Set.univ)) := by
  have hc2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 : ℝ) / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hws := outer_ws hg
  have hgkk : 1 ≤ ‖(Matrix.of g : Mat k 0) (iK k) (iK k)‖ := by
    have h1 : 1 ≤ Complex.normSq ((Matrix.of g : Mat k 0) (iK k) (iK k)) := by
      nlinarith [sq_nonneg (tW (iK k) (fun j => star ((Matrix.of g : Mat k 0) (iK k) j)))]
    rw [← Complex.sq_norm] at h1
    nlinarith [norm_nonneg ((Matrix.of g : Mat k 0) (iK k) (iK k))]
  have hbn : ‖-star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖ = ‖(Matrix.of g : Mat k 0) (iK k) (iK k)‖ := by
    rw [norm_neg, norm_star]
  have hb0 : -star ((Matrix.of g : Mat k 0) (iK k) (iK k)) ≠ 0 := by
    intro h; rw [h, norm_zero] at hbn; linarith
  have hvb : tW (iK k) (fun j => star ((Matrix.of g : Mat k 0) (iK k) j)) ^ 2 ≤
      Complex.normSq (-star ((Matrix.of g : Mat k 0) (iK k) (iK k))) := by
    have : Complex.normSq (star ((Matrix.of g : Mat k 0) (iK k) (iK k))) =
        Complex.normSq ((Matrix.of g : Mat k 0) (iK k) (iK k)) := Complex.normSq_conj _
    rw [Complex.normSq_neg, this]; linarith
  calc ∫⁻ h', ∫⁻ h, Gf k σ h g h' ∂ν ∂ν
      ≤ ∫⁻ h', ENNReal.ofReal ((Real.sqrt 2)⁻¹ *
          ‖((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0) (iK k)‖ / 2) ^ (-σ) *
            (C0 k σ ν + ν Set.univ) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_mem_fixedUnitary hν] with h' hh'
        obtain ⟨e, hne⟩ := iso_y hk hg hh'.1
        unfold Gf
        exact bnd hk hν hσ (lam := (Real.sqrt 2)⁻¹) (by positivity)
          ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0) _ hne (le_of_eq e)
    _ = (∫⁻ h', ENNReal.ofReal (1 / 4 * ‖((Matrix.of h')ᴴ *ᵥ (fun j => star ((Matrix.of g : Mat k 0) (iK k) j)))
          (iW k) + -star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖) ^ (-σ) ∂ν) * (C0 k σ ν + ν Set.univ) := by
        rw [lintegral_mul_const' _ _ hK1f]
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [ae_mem_fixedUnitary hν] with h' hh'
        rw [outer_eq hk hh' (Matrix.of g)]
        congr 2
        rw [← mul_assoc, hc2]; ring
    _ ≤ (ENNReal.ofReal (1 / 4 * ‖-star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖ / 2) ^ (-σ) *
          (C0 k σ ν + ν Set.univ)) * (C0 k σ ν + ν Set.univ) :=
        mul_le_mul' (bnd hk hν hσ (by norm_num) _ _ hb0 hvb) le_rfl
    _ ≤ (ENNReal.ofReal (1 / 8) ^ (-σ) * (C0 k σ ν + ν Set.univ)) * (C0 k σ ν + ν Set.univ) :=
        mul_le_mul' (mul_le_mul' (ofReal_rpow_neg_anti hσ (by rw [hbn]; linarith)) le_rfl) le_rfl
    _ = (C0 k σ ν + ν Set.univ) * (ENNReal.ofReal (1 / 8) ^ (-σ) * (C0 k σ ν + ν Set.univ)) := mul_comm _ _

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCW, hGN, -, -, -, -, -, -, -, -, hHW, -⟩` from `hB2`. Introduce `k hk s hs μG hμG A hA`. Take `⟨hσ0, hσk⟩` from `s_facts hk hs`. Take `⟨ν, hν⟩` from `hHW k 0 (bvec (iK k)) (inWb_iK k) (Tz_iK k)`. Establish `hν' : IsHaarOn (U0 k) ν` using `hν`.

Establish `hνf` using `haar_univ_lt_top hCW hν'`. Establish `hν0 : ν Set.univ ≠ 0` using `fun h => hν.ne_zero (Measure.measure_univ_eq_zero.mp h)`. Establish `: IsFiniteMeasure ν` using `⟨hνf⟩`. Establish `: IsFiniteMeasureOnCompacts μG` using `⟨fun K hK => hμG.finite_compact K hK⟩`. Establish `hC0` using `haarIntegralConstant_lt_top hk hν' hνf hσ0 hσk`.

Establish `hK1f : C0 k (s 0) ν + ν Set.univ ≠ ∞` using `ENNReal.add_ne_top.mpr ⟨hC0.ne, hνf.ne⟩`. Establish `hKc : (C0 k (s 0) ν + ν Set.univ) * (ENNReal.ofReal (1 / 8) ^ (-s 0) * (C0 k (s 0) ν + ν Set.univ)) ≠ ∞`. Use `ENNReal.mul_ne_top hK1f (ENNReal.mul_ne_top ?_ hK1f)` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_rpow_of_pos (by norm_num)]; exact ENNReal.ofReal_ne_top`. Establish `key` using `avg_key hk hT (s := s) hμG A hν'`.

Establish `hfin : ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG < ∞`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono_ae ?_` and prove the remaining obligations. Use `filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμG.conc] with g hg`. Conclude with `mul_le_mul' le_rfl (ptw hk hσ0 hν' hK1f g (not_not.mp hg))`.

Use `_ = (∫⁻ g, PhiA k A g ∂μG) * ((C0 k (s 0) ν + ν Set.univ) * (ENNReal.ofReal (1 / 8) ^ (-s 0) * (C0 k (s 0) ν + ν Set.univ))) := lintegral_mul_const' _ _ hKc`. Use `_ < ∞ := ENNReal.mul_lt_top (hGN k 0 μG A hμG hA) hKc.lt_top`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_lt, top_le_iff]`. Rewrite `key` using `[hc, ENNReal.top_mul (mul_ne_zero hν0 hν0)]`.

Rewrite `hfin` using `[← key]`. Conclude with `lt_irrefl _ hfin`.
-/
theorem aStepBase_of (hB2 : InductiveHeisenbergInputs) (hT : TBoth) : AStepBase := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCW, hGN, -, -, -, -, -, -, -, -, hHW, -⟩ := hB2
  intro k hk s hs μG hμG A hA
  obtain ⟨hσ0, hσk⟩ := s_facts hk hs
  obtain ⟨ν, hν⟩ := hHW k 0 (bvec (iK k)) (inWb_iK k) (Tz_iK k)
  have hν' : IsHaarOn (U0 k) ν := hν
  have hνf := haar_univ_lt_top hCW hν'
  have hν0 : ν Set.univ ≠ 0 := fun h => hν.ne_zero (Measure.measure_univ_eq_zero.mp h)
  have : IsFiniteMeasure ν := ⟨hνf⟩
  have : IsFiniteMeasureOnCompacts μG := ⟨fun K hK => hμG.finite_compact K hK⟩
  have hC0 := haarIntegralConstant_lt_top hk hν' hνf hσ0 hσk
  have hK1f : C0 k (s 0) ν + ν Set.univ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hC0.ne, hνf.ne⟩
  have hKc : (C0 k (s 0) ν + ν Set.univ) *
      (ENNReal.ofReal (1 / 8) ^ (-s 0) * (C0 k (s 0) ν + ν Set.univ)) ≠ ∞ := by
    refine ENNReal.mul_ne_top hK1f (ENNReal.mul_ne_top ?_ hK1f)
    rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]; exact ENNReal.ofReal_ne_top
  have key := avg_key hk hT (s := s) hμG A hν'
  have hfin : ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG < ∞ := by
    calc ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG
        ≤ ∫⁻ g, PhiA k A g * ((C0 k (s 0) ν + ν Set.univ) *
            (ENNReal.ofReal (1 / 8) ^ (-s 0) * (C0 k (s 0) ν + ν Set.univ))) ∂μG := by
          refine lintegral_mono_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμG.conc] with g hg
          exact mul_le_mul' le_rfl (ptw hk hσ0 hν' hK1f g (not_not.mp hg))
      _ = (∫⁻ g, PhiA k A g ∂μG) * ((C0 k (s 0) ν + ν Set.univ) *
            (ENNReal.ofReal (1 / 8) ^ (-s 0) * (C0 k (s 0) ν + ν Set.univ))) :=
          lintegral_mul_const' _ _ hKc
      _ < ∞ := ENNReal.mul_lt_top (hGN k 0 μG A hμG hA) hKc.lt_top
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.top_mul (mul_ne_zero hν0 hν0)] at key
  rw [← key] at hfin
  exact lt_irrefl _ hfin

end ReciprocityTheory.ChartRestriction.DS.Xi
