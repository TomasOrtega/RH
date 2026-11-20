import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfK
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfAs

noncomputable section

open Formalism.IndefR.Datum Matrix MeasureTheory Topology Filter

namespace Formalism.IndefR.Tow.SobPf

variable {n : ℕ}

def qr (k : Fin n → Fin n → ℂ) : ℝ := ∑ a, ∑ j, ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ ^ 2

def qP : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ :=
  ∑ a, ∑ j, (MvPolynomial.X (Sum.inr (a, j)) - MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) ℂ) a j)) *
    (MvPolynomial.X (Sum.inl (a, j)) - MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) ℂ) a j))

/- English proof (translation)
Establish `hδ : ∀ a j : Fin n, starRingEnd ℂ ((1 : Matrix (Fin n) (Fin n) ℂ) a j) = (1 : Matrix (Fin n) (Fin n) ℂ) a j`. Apply the tactic sequence `intro a j; rw [Matrix.one_apply]; split_ifs <;> simp`. Establish `hz : ∀ z : ℂ, starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ)`. Introduce `z`. Rewrite using `[← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]`.

Simplify using `only [evP, qP, qr, map_sum, map_mul, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hz, map_sub, hδ]`.
-/
theorem evP_qP (k : Fin n → Fin n → ℂ) : evP (qP (n := n)) k = (qr k : ℂ) := by

  have hδ : ∀ a j : Fin n, starRingEnd ℂ ((1 : Matrix (Fin n) (Fin n) ℂ) a j) =
      (1 : Matrix (Fin n) (Fin n) ℂ) a j := by
    intro a j; rw [Matrix.one_apply]; split_ifs <;> simp
  have hz : ∀ z : ℂ, starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp only [evP, qP, qr, map_sum, map_mul, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Sum.elim_inl, Sum.elim_inr, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hz, map_sub, hδ]

/- English proof (translation)
Unfold `qr`. Conclude with `continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun j _ => ((continuous_apply_apply a j).sub continuous_const).norm.pow 2`.
-/
theorem continuous_qr : Continuous (qr (n := n)) := by

  unfold qr
  exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun j _ =>
    ((continuous_apply_apply a j).sub continuous_const).norm.pow 2

/- English proof (translation)
Unfold `qr`. Conclude with `Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => sq_nonneg _`.
-/
theorem qr_nonneg (k : Fin n → Fin n → ℂ) : 0 ≤ qr k := by
  unfold qr
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/- English proof (translation)
Simplify using `[qr]`.
-/
theorem qr_one : qr (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) = 0 := by

  simp [qr]

/- English proof (translation)
Unfold `qr at h`. Use function extensionality and compare the values at `a j`. Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg fun j _ => sq_nonneg _)).1 h a (Finset.mem_univ a)`. Establish `h2` using `(Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 h1 j (Finset.mem_univ j)`. Establish `h3 : k a j = (1 : Matrix (Fin n) (Fin n) ℂ) a j`.

Establish `h4 : ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ = 0`. Rewrite `h2` using `[sq_eq_zero_iff]`. Then use the resulting hypothesis. Conclude with `sub_eq_zero.1 (norm_eq_zero.1 h4)`. Conclude with `h3`.
-/
theorem eq_one_of_qr (k : Fin n → Fin n → ℂ) (h : qr k = 0) : k = Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ) := by

  unfold qr at h
  funext a j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ => Finset.sum_nonneg fun j _ => sq_nonneg _)).1 h a (Finset.mem_univ a)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 h1 j (Finset.mem_univ j)
  have h3 : k a j = (1 : Matrix (Fin n) (Fin n) ℂ) a j := by
    have h4 : ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ = 0 := by
      rwa [sq_eq_zero_iff] at h2
    exact sub_eq_zero.1 (norm_eq_zero.1 h4)
  exact h3

/- English proof (translation)
Unfold `qr`. Conclude with `le_trans (Finset.single_le_sum (f := fun j => ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)) (Finset.single_le_sum (f := fun a => ∑ j, ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ ^ 2) (fun a _ => Finset.sum_nonneg fun j _ => sq_no …`.
-/
private theorem norm_sub_one_sq_le_qr (k : Fin n → Fin n → ℂ) (a j : Fin n) :
    ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ ^ 2 ≤ qr k := by
  unfold qr
  exact le_trans (Finset.single_le_sum (f := fun j => ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ j))
    (Finset.single_le_sum (f := fun a => ∑ j, ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ ^ 2)
      (fun a _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ a))

/- English proof (translation)
Rewrite using `[Metric.mem_ball, dist_pi_lt_iff hr]`. Introduce `a`. Rewrite using `[dist_pi_lt_iff hr]`. Introduce `j`. Rewrite using `[dist_eq_norm]`.

Use `show ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ < r`. Establish `h1` using `lt_of_le_of_lt (norm_sub_one_sq_le_qr k a j) h`. Use polynomial arithmetic with `[norm_nonneg (k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j)]`.
-/
private theorem mem_ball_one_of_qr_lt_sq {r : ℝ} (hr : 0 < r) (k : Fin n → Fin n → ℂ) (h : qr k < r ^ 2) :
    k ∈ Metric.ball (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) r := by
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  intro a
  rw [dist_pi_lt_iff hr]
  intro j
  rw [dist_eq_norm]
  show ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ < r
  have h1 := lt_of_le_of_lt (norm_sub_one_sq_le_qr k a j) h
  nlinarith [norm_nonneg (k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j)]

/- English proof (translation)
Use `haveI := hμ.1`. Establish `hae : ∀ᵐ k ∂μ, k ∈ {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s}` using `hμ.2.1`. Establish `hK : IsCompact {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s}` using `isCompact_KAt hs`. Establish `h` using `hf.continuousOn.integrableOn_compact (μ := μ) hK`. Rewrite `h` using `[IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae]`. Then use the resulting hypothesis.
-/
private theorem integrable_of_continuous_of_isHaarK {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s)
    {μ : Measure (Fin n → Fin n → ℂ)} (hμ : IsHaarK G s μ) {f : (Fin n → Fin n → ℂ) → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  haveI := hμ.1
  have hae : ∀ᵐ k ∂μ, k ∈ {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} := hμ.2.1
  have hK : IsCompact {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} := isCompact_KAt hs
  have h := hf.continuousOn.integrableOn_compact (μ := μ) hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h

/- English proof (translation)
Introduce `n G s hs μ hμ U hU η hη`. Use `haveI := hμ.1`. Establish `hKae : ∀ᵐ k ∂μ, Matrix.of k ∈ KAt G s` using `hμ.2.1`. Establish `hK : IsCompact {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s}` using `isCompact_KAt hs`. Take `⟨M, hM⟩` from `hK.bddAbove_image (continuous_qr (n := n)).continuousOn`.

Take `⟨R, hRdef⟩ : ∃ R : ℝ, R = max M 0 + 1` from `⟨_, rfl⟩`. Establish `hMR : M < R` using `by rw [hRdef]; linarith [le_max_left M 0]`. Establish `hRpos : 0 < R` using `by rw [hRdef]; linarith [le_max_right M 0]`. Establish `hRinv : 0 < R⁻¹` using `inv_pos.2 hRpos`. Establish `hbK : ∀ k : Fin n → Fin n → ℂ, Matrix.of k ∈ KAt G s → 0 ≤ 1 - R⁻¹ * qr k ∧ 1 - R⁻¹ * qr k ≤ 1`.

Introduce `k hk`. Establish `h0 : qr k ≤ M` using `hM (Set.mem_image_of_mem qr (show k ∈ {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} from hk))`. Establish `h2 : R⁻¹ * qr k ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : 0 ≤ R⁻¹ * qr k` using `mul_nonneg hRinv.le (qr_nonneg k)`.

Apply the tactic sequence `constructor <;> linarith`. Take `⟨r, hr, hball⟩` from `Metric.mem_nhds_iff.1 hU`. Take `⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (r ^ 2) R` from `⟨_, rfl⟩`. Establish `hε : 0 < ε` using `by rw [hεdef]; exact lt_min (pow_pos hr 2) hRpos`. Establish `hεr : ε ≤ r ^ 2` using `by rw [hεdef]; exact min_le_left _ _`.

Establish `hεR : R⁻¹ * ε ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Take `⟨β, hβdef⟩ : ∃ β : ℝ, β = 1 - R⁻¹ * ε` from `⟨_, rfl⟩`. Take `⟨α, hαdef⟩ : ∃ α : ℝ, α = 1 - R⁻¹ * (ε / 2)` from `⟨_, rfl⟩`. Establish `hβ0 : 0 ≤ β` using `by rw [hβdef]; linarith`.

Establish `hαβ : β < α` using `by rw [hβdef, hαdef]; nlinarith [mul_pos hRinv hε]`. Establish `hα0 : 0 < α` using `by rw [hαdef]; nlinarith [mul_pos hRinv hε]`. Establish `hbW : ∀ k : Fin n → Fin n → ℂ, ε ≤ qr k → 1 - R⁻¹ * qr k ≤ β`. Introduce `k hk`. Use `mul_le_mul_of_nonneg_left hk hRinv.le` as an intermediate fact.

Rewrite using `[hβdef]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbV : ∀ k : Fin n → Fin n → ℂ, qr k < ε / 2 → α ≤ 1 - R⁻¹ * qr k`. Introduce `k hk`. Use `mul_le_mul_of_nonneg_left hk.le hRinv.le` as an intermediate fact.

Rewrite using `[hαdef]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hVmeas : MeasurableSet {k : Fin n → Fin n → ℂ | qr k < ε / 2}` using `measurableSet_lt (continuous_qr (n := n)).measurable measurable_const`. Establish `hμV : 0 < μ {k : Fin n → Fin n → ℂ | qr k < ε / 2}`. Use `hμ.2.2.2 _ (isOpen_lt continuous_qr continuous_const) ⟨Matrix.of.symm 1, ?_, ?_⟩` and prove the remaining obligations.

Use `show qr (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) < ε / 2`. Rewrite using `[qr_one]`. Check the signs of the components of the expression. Conclude with `one_mem_KAt G s`. Take `⟨m, hmdef⟩ : ∃ m : ℝ, m = (μ {k : Fin n → Fin n → ℂ | qr k < ε / 2}).toReal` from `⟨_, rfl⟩`.

Establish `hm : 0 < m` using `by rw [hmdef]; exact ENNReal.toReal_pos hμV.ne' (measure_ne_top μ _)`. Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one (mul_pos hη hm) ((div_lt_one hα0).2 hαβ)`. Take `⟨g, hgdef⟩ : ∃ g : (Fin n → Fin n → ℂ) → ℝ, g = fun k => (1 - R⁻¹ * qr k) ^ N` from `⟨_, rfl⟩`. Establish `hgk : ∀ k, g k = (1 - R⁻¹ * qr k) ^ N` using `fun k => by rw [hgdef]`. Establish `hg_cont : Continuous g`.

Rewrite using `[hgdef]`. Conclude with `(continuous_const.sub (continuous_const.mul continuous_qr)).pow N`. Establish `hg_int : Integrable g μ` using `integrable_of_continuous_of_isHaarK hs hμ hg_cont`. Establish `hg_nn : ∀ᵐ k ∂μ, 0 ≤ g k` using `hKae.mono fun k hk => by rw [hgk]; exact pow_nonneg (hbK k hk).1 N`. Take `⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ k, g k ∂μ` from `⟨_, rfl⟩`.

Establish `hI : α ^ N * m ≤ I`. Establish `h1 : α ^ N * m ≤ ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε / 2}, g k ∂μ`. Rewrite using `[hmdef]`. Establish `h` using `setIntegral_ge_of_const_le hVmeas (measure_ne_top μ _) (fun k (hk : k ∈ {k : Fin n → Fin n → ℂ | qr k < ε / 2}) => (show α ^ N ≤ g k by rw [hgk]; exact pow_le_pow_left₀ hα0.le (hbV k hk) N)) hg_int.integrableOn`. Use `le_trans (le_of_eq ?_) h` and prove the remaining obligations.

Use `first`. Consider the case `rfl`. Consider the case `exact mul_comm _ _`. Consider the case `ring1`. Consider the case `(simp only [Measure.real]; ring1)`.

Consider the case `(simp [Measure.real, mul_comm]; done)`. Establish `h2 : ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε / 2}, g k ∂μ ≤ ∫ k, g k ∂μ` using `setIntegral_le_integral hg_int hg_nn`. Rewrite using `[hIdef]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hIpos : 0 < I` using `lt_of_lt_of_le (mul_pos (pow_pos hα0 N) hm) hI`.

Establish `hcm : ∫ k, I⁻¹ * g k ∂μ = I⁻¹ * ∫ k, g k ∂μ` using `by first`. Consider the case `exact integral_const_mul I⁻¹ _`. Consider the case `exact integral_mul_left I⁻¹ _`. Establish `hnr : ∀ x : ℝ, 0 ≤ x → ‖(x : ℂ)‖ = x` using `fun x hx => by first`. Consider the case `exact Complex.norm_of_nonneg hx`.

Consider the case `(rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx])`. Consider the case `simp [abs_of_nonneg hx]`. Take `⟨q, hqdef⟩ : ∃ q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, q = MvPolynomial.C ((I⁻¹ : ℝ) : ℂ) * (MvPolynomial.C 1 - MvPolynomial.C ((R⁻¹ : ℝ) : ℂ) * qP) ^ N` from `⟨_, rfl⟩`. Establish `hF : ∀ k, evP q k = ((I⁻¹ * g k : ℝ) : ℂ)`. Introduce `k`.

Establish `hq` using `evP_qP k`. Simplify using `only [evP] at hq ⊢`. Rewrite using `[hqdef, hgk]`. Simplify using `only [map_mul, map_pow, map_sub, MvPolynomial.eval_C, hq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hgI : Integrable (fun k => ((I⁻¹ * g k : ℝ) : ℂ)) μ` using `(hg_int.const_mul I⁻¹).ofReal`. Use `⟨q, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show evP q = fun k => ((I⁻¹ * g k : ℝ) : ℂ) from funext hF]`. Conclude with `hgI`.

Simplify using `only [hF]`. Establish `hc : ∫ k, ((I⁻¹ * g k : ℝ) : ℂ) ∂μ = ((∫ k, I⁻¹ * g k ∂μ : ℝ) : ℂ)` using `by first`. Consider the case `exact integral_complex_ofReal`. Consider the case `exact integral_ofReal`. Consider the case `exact (integral_ofReal (𝕜 := ℂ))`.

Rewrite using `[hc, hcm, ← hIdef, inv_mul_cancel₀ hIpos.ne', Complex.ofReal_one]`. Simplify using `only [hF]`. Establish `hae : (fun k => ‖((I⁻¹ * g k : ℝ) : ℂ)‖) =ᵐ[μ] fun k => I⁻¹ * g k` using `by filter_upwards [hg_nn] with k hk`. Conclude with `hnr _ (mul_nonneg (inv_nonneg.2 hIpos.le) hk)`. Rewrite using `[integral_congr_ae hae, hcm, ← hIdef, inv_mul_cancel₀ hIpos.ne']`.

Simplify using `only [hF]`. Establish `hWU : {k : Fin n → Fin n → ℂ | qr k < ε} ⊆ U` using `fun k hk => hball (mem_ball_one_of_qr_lt_sq hr k (lt_of_lt_of_le hk hεr))`. Establish `hWc : MeasurableSet {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ` using `(measurableSet_lt (continuous_qr (n := n)).measurable measurable_const).compl`. Establish `hni : Integrable (fun k => ‖((I⁻¹ * g k : ℝ) : ℂ)‖) μ` using `hgI.norm`. Establish `step1 : ∫ k in Uᶜ, ‖((I⁻¹ * g k : ℝ) : ℂ)‖ ∂μ ≤ ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ, ‖((I⁻¹ * g k : ℝ) : ℂ)‖ ∂μ` using `setIntegral_mono_set hni.integrableOn (ae_of_all _ fun k => norm_nonneg _) (Set.compl_subset_compl.2 hWU).eventuallyLE`.

Establish `step2 : ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ, ‖((I⁻¹ * g k : ℝ) : ℂ)‖ ∂μ ≤ ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ, I⁻¹ * β ^ N ∂μ`. Use `setIntegral_mono_ae_restrict hni.integrableOn (integrable_const _).integrableOn ?_` and prove the remaining obligations. Rewrite using `[Filter.EventuallyLE, ae_restrict_iff' hWc]`. Use `filter_upwards [hKae] with k hkK hkW`. Establish `hkW' : ε ≤ qr k`.

Assume the negation of the conclusion as `hc`. Conclude with `hkW (not_le.1 hc)`. Establish `hb` using `hbK k hkK`. Rewrite using `[hnr _ (mul_nonneg (inv_nonneg.2 hIpos.le) (by rw [hgk]; exact pow_nonneg hb.1 N)), hgk]`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.1 (hbW k hkW') N) (inv_nonneg.2 hIpos.le)`.

Establish `step3 : ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ, I⁻¹ * β ^ N ∂μ ≤ I⁻¹ * β ^ N`. Rewrite using `[setIntegral_const, smul_eq_mul]`. Use `mul_le_of_le_one_left (mul_nonneg (inv_nonneg.2 hIpos.le) (pow_nonneg hβ0 N)) ?_` and prove the remaining obligations. Use `first`. Consider the case `exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)`.

Consider the case `exact measureReal_le_one`. Consider the case `simp`. Establish `hβN : β ^ N = (β / α) ^ N * α ^ N`. Rewrite using `[div_pow, div_mul_cancel₀ _ (pow_pos hα0 N).ne']`. Establish `h4 : β ^ N < η * I`.

Combine the equalities or inequalities in the displayed calculation. Establish `step4 : I⁻¹ * β ^ N < η`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem polyKernel_holds : PolyKernel := by
  intro n G s hs μ hμ U hU η hη
  haveI := hμ.1
  have hKae : ∀ᵐ k ∂μ, Matrix.of k ∈ KAt G s := hμ.2.1
  have hK : IsCompact {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} := isCompact_KAt hs
  obtain ⟨M, hM⟩ := hK.bddAbove_image (continuous_qr (n := n)).continuousOn
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = max M 0 + 1 := ⟨_, rfl⟩
  have hMR : M < R := by rw [hRdef]; linarith [le_max_left M 0]
  have hRpos : 0 < R := by rw [hRdef]; linarith [le_max_right M 0]
  have hRinv : 0 < R⁻¹ := inv_pos.2 hRpos
  have hbK : ∀ k : Fin n → Fin n → ℂ, Matrix.of k ∈ KAt G s →
      0 ≤ 1 - R⁻¹ * qr k ∧ 1 - R⁻¹ * qr k ≤ 1 := by
    intro k hk
    have h0 : qr k ≤ M := hM (Set.mem_image_of_mem qr
      (show k ∈ {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} from hk))
    have h2 : R⁻¹ * qr k ≤ 1 := by
      calc R⁻¹ * qr k ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (by linarith) hRinv.le
        _ = 1 := inv_mul_cancel₀ hRpos.ne'
    have h3 : 0 ≤ R⁻¹ * qr k := mul_nonneg hRinv.le (qr_nonneg k)
    constructor <;> linarith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (r ^ 2) R := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact lt_min (pow_pos hr 2) hRpos
  have hεr : ε ≤ r ^ 2 := by rw [hεdef]; exact min_le_left _ _
  have hεR : R⁻¹ * ε ≤ 1 := by
    calc R⁻¹ * ε ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (by rw [hεdef]; exact min_le_right _ _) hRinv.le
      _ = 1 := inv_mul_cancel₀ hRpos.ne'
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = 1 - R⁻¹ * ε := ⟨_, rfl⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = 1 - R⁻¹ * (ε / 2) := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := by rw [hβdef]; linarith
  have hαβ : β < α := by rw [hβdef, hαdef]; nlinarith [mul_pos hRinv hε]
  have hα0 : 0 < α := by rw [hαdef]; nlinarith [mul_pos hRinv hε]
  have hbW : ∀ k : Fin n → Fin n → ℂ, ε ≤ qr k → 1 - R⁻¹ * qr k ≤ β := by
    intro k hk
    have := mul_le_mul_of_nonneg_left hk hRinv.le
    rw [hβdef]; linarith
  have hbV : ∀ k : Fin n → Fin n → ℂ, qr k < ε / 2 → α ≤ 1 - R⁻¹ * qr k := by
    intro k hk
    have := mul_le_mul_of_nonneg_left hk.le hRinv.le
    rw [hαdef]; linarith
  have hVmeas : MeasurableSet {k : Fin n → Fin n → ℂ | qr k < ε / 2} :=
    measurableSet_lt (continuous_qr (n := n)).measurable measurable_const
  have hμV : 0 < μ {k : Fin n → Fin n → ℂ | qr k < ε / 2} := by
    refine hμ.2.2.2 _ (isOpen_lt continuous_qr continuous_const) ⟨Matrix.of.symm 1, ?_, ?_⟩
    · show qr (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) < ε / 2
      rw [qr_one]; positivity
    · exact one_mem_KAt G s
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = (μ {k : Fin n → Fin n → ℂ | qr k < ε / 2}).toReal := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hmdef]; exact ENNReal.toReal_pos hμV.ne' (measure_ne_top μ _)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (mul_pos hη hm) ((div_lt_one hα0).2 hαβ)
  obtain ⟨g, hgdef⟩ : ∃ g : (Fin n → Fin n → ℂ) → ℝ, g = fun k => (1 - R⁻¹ * qr k) ^ N := ⟨_, rfl⟩
  have hgk : ∀ k, g k = (1 - R⁻¹ * qr k) ^ N := fun k => by rw [hgdef]
  have hg_cont : Continuous g := by
    rw [hgdef]; exact (continuous_const.sub (continuous_const.mul continuous_qr)).pow N
  have hg_int : Integrable g μ := integrable_of_continuous_of_isHaarK hs hμ hg_cont
  have hg_nn : ∀ᵐ k ∂μ, 0 ≤ g k := hKae.mono fun k hk => by rw [hgk]; exact pow_nonneg (hbK k hk).1 N
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ k, g k ∂μ := ⟨_, rfl⟩
  have hI : α ^ N * m ≤ I := by
    have h1 : α ^ N * m ≤ ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε / 2}, g k ∂μ := by
      rw [hmdef]
      have h := setIntegral_ge_of_const_le hVmeas (measure_ne_top μ _)
        (fun k (hk : k ∈ {k : Fin n → Fin n → ℂ | qr k < ε / 2}) =>
          (show α ^ N ≤ g k by rw [hgk]; exact pow_le_pow_left₀ hα0.le (hbV k hk) N))
        hg_int.integrableOn
      refine le_trans (le_of_eq ?_) h
      first
        | rfl
        | exact mul_comm _ _
        | ring1
        | (simp only [Measure.real]; ring1)
        | (simp [Measure.real, mul_comm]; done)
    have h2 : ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε / 2}, g k ∂μ ≤ ∫ k, g k ∂μ :=
      setIntegral_le_integral hg_int hg_nn
    rw [hIdef]; linarith
  have hIpos : 0 < I := lt_of_lt_of_le (mul_pos (pow_pos hα0 N) hm) hI
  have hcm : ∫ k, I⁻¹ * g k ∂μ = I⁻¹ * ∫ k, g k ∂μ := by
    first
      | exact integral_const_mul I⁻¹ _
      | exact integral_mul_left I⁻¹ _
  have hnr : ∀ x : ℝ, 0 ≤ x → ‖(x : ℂ)‖ = x := fun x hx => by
    first
      | exact Complex.norm_of_nonneg hx
      | (rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx])
      | simp [abs_of_nonneg hx]
  obtain ⟨q, hqdef⟩ : ∃ q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ,
      q = MvPolynomial.C ((I⁻¹ : ℝ) : ℂ) *
        (MvPolynomial.C 1 - MvPolynomial.C ((R⁻¹ : ℝ) : ℂ) * qP) ^ N := ⟨_, rfl⟩
  have hF : ∀ k, evP q k = ((I⁻¹ * g k : ℝ) : ℂ) := by
    intro k
    have hq := evP_qP k
    simp only [evP] at hq ⊢
    rw [hqdef, hgk]
    simp only [map_mul, map_pow, map_sub, MvPolynomial.eval_C, hq]
    push_cast
    ring
  have hgI : Integrable (fun k => ((I⁻¹ * g k : ℝ) : ℂ)) μ := (hg_int.const_mul I⁻¹).ofReal
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · rw [show evP q = fun k => ((I⁻¹ * g k : ℝ) : ℂ) from funext hF]
    exact hgI
  · simp only [hF]
    have hc : ∫ k, ((I⁻¹ * g k : ℝ) : ℂ) ∂μ = ((∫ k, I⁻¹ * g k ∂μ : ℝ) : ℂ) := by
      first
        | exact integral_complex_ofReal
        | exact integral_ofReal
        | exact (integral_ofReal (𝕜 := ℂ))
    rw [hc, hcm, ← hIdef, inv_mul_cancel₀ hIpos.ne', Complex.ofReal_one]
  · simp only [hF]
    have hae : (fun k => ‖((I⁻¹ * g k : ℝ) : ℂ)‖) =ᵐ[μ] fun k => I⁻¹ * g k := by
      filter_upwards [hg_nn] with k hk
      exact hnr _ (mul_nonneg (inv_nonneg.2 hIpos.le) hk)
    rw [integral_congr_ae hae, hcm, ← hIdef, inv_mul_cancel₀ hIpos.ne']
  · simp only [hF]
    have hWU : {k : Fin n → Fin n → ℂ | qr k < ε} ⊆ U := fun k hk =>
      hball (mem_ball_one_of_qr_lt_sq hr k (lt_of_lt_of_le hk hεr))
    have hWc : MeasurableSet {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ :=
      (measurableSet_lt (continuous_qr (n := n)).measurable measurable_const).compl
    have hni : Integrable (fun k => ‖((I⁻¹ * g k : ℝ) : ℂ)‖) μ := hgI.norm
    have step1 : ∫ k in Uᶜ, ‖((I⁻¹ * g k : ℝ) : ℂ)‖ ∂μ ≤
        ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ, ‖((I⁻¹ * g k : ℝ) : ℂ)‖ ∂μ :=
      setIntegral_mono_set hni.integrableOn (ae_of_all _ fun k => norm_nonneg _)
        (Set.compl_subset_compl.2 hWU).eventuallyLE
    have step2 : ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ, ‖((I⁻¹ * g k : ℝ) : ℂ)‖ ∂μ ≤
        ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ, I⁻¹ * β ^ N ∂μ := by
      refine setIntegral_mono_ae_restrict hni.integrableOn (integrable_const _).integrableOn ?_
      rw [Filter.EventuallyLE, ae_restrict_iff' hWc]
      filter_upwards [hKae] with k hkK hkW
      have hkW' : ε ≤ qr k := by
        by_contra hc
        exact hkW (not_le.1 hc)
      have hb := hbK k hkK
      rw [hnr _ (mul_nonneg (inv_nonneg.2 hIpos.le) (by rw [hgk]; exact pow_nonneg hb.1 N)), hgk]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.1 (hbW k hkW') N) (inv_nonneg.2 hIpos.le)
    have step3 : ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ, I⁻¹ * β ^ N ∂μ ≤ I⁻¹ * β ^ N := by
      rw [setIntegral_const, smul_eq_mul]
      refine mul_le_of_le_one_left (mul_nonneg (inv_nonneg.2 hIpos.le) (pow_nonneg hβ0 N)) ?_
      first
        | exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
        | exact measureReal_le_one
        | simp
    have hβN : β ^ N = (β / α) ^ N * α ^ N := by
      rw [div_pow, div_mul_cancel₀ _ (pow_pos hα0 N).ne']
    have h4 : β ^ N < η * I := by
      calc β ^ N = (β / α) ^ N * α ^ N := hβN
        _ < (η * m) * α ^ N := mul_lt_mul_of_pos_right hN (pow_pos hα0 N)
        _ = η * (α ^ N * m) := by ring
        _ ≤ η * I := mul_le_mul_of_nonneg_left hI hη.le
    have step4 : I⁻¹ * β ^ N < η := by
      calc I⁻¹ * β ^ N < I⁻¹ * (η * I) := mul_lt_mul_of_pos_left h4 (inv_pos.2 hIpos)
        _ = η := by rw [mul_comm η, ← mul_assoc, inv_mul_cancel₀ hIpos.ne', one_mul]
    linarith

end Formalism.IndefR.Tow.SobPf

end
