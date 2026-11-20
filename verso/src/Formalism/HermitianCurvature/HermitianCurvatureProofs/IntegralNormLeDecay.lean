import Formalism.HermitianCurvature.HermitianCurvatureProofs.XiBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormLeIntegralFsv

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem norm_fsv (a t : ℂ) : ‖fsv a t‖ = 1 := by
  unfold fsv
  rw [Complex.norm_exp]
  have : (a * t - conj a * conj t).re = 0 := by
    simp [Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.conj_im]
  rw [this, Real.exp_zero]

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem continuous_fsv₂ : Continuous (fun q : ℂ × ℂ => fsv q.1 q.2) := by
  unfold fsv
  exact Complex.continuous_exp.comp ((continuous_fst.mul continuous_snd).sub
    ((Complex.continuous_conj.comp continuous_fst).mul (Complex.continuous_conj.comp continuous_snd)))

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem integrable_fsv_mul {φ : ℂ → ℂ} (hφ : Continuous φ) (hi : Integrable φ) (a : ℂ) :
    Integrable (fun t => fsv a t * φ t) := by
  refine hi.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun t => (norm_fsv a t).le)
  exact (continuous_fsv₂.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem continuous_transform {φ : ℂ → ℂ} (hφ : Continuous φ) (hi : Integrable φ) :
    Continuous (fun s : ℂ => ∫ t, fsv s t * φ t) := by
  refine continuous_of_dominated (bound := fun t => ‖φ t‖) (fun s => ?_) (fun s => ?_) hi.norm ?_
  · exact ((continuous_fsv₂.comp (continuous_const.prodMk continuous_id)).mul hφ).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by rw [norm_mul, norm_fsv, one_mul]
  · exact Filter.Eventually.of_forall fun t =>
      (continuous_fsv₂.comp (continuous_id.prodMk continuous_const)).mul continuous_const

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem integrable_decay3' : Integrable (fun s : ℂ => ((1 + ‖s‖) ^ 3)⁻¹) := by
  have hd : Integrable (fun t : ℂ => (1 + ‖t‖) ^ (-(3 : ℝ))) volume := by
    refine integrable_one_add_norm ?_
    rw [Complex.finrank_real_complex]; norm_num
  refine hd.congr (Filter.Eventually.of_forall fun t => ?_)
  have h1 : (0 : ℝ) < 1 + ‖t‖ := by positivity
  simp only []
  rw [Real.rpow_neg h1.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem integral_norm_le_decay {Ξ : ℂ → ℂ} (hΞ : Continuous Ξ) {K : ℝ} (hK : ∀ s, ‖Ξ s‖ ≤ K * ((1 + ‖s‖) ^ 3)⁻¹) :
    Integrable Ξ ∧ ∫ s, ‖Ξ s‖ ≤ K * ∫ s : ℂ, ((1 + ‖s‖) ^ 3)⁻¹ := by
  have hint : Integrable Ξ :=
    Integrable.mono' (integrable_decay3'.const_mul K) hΞ.aestronglyMeasurable (Filter.Eventually.of_forall hK)
  refine ⟨hint, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hint.norm (integrable_decay3'.const_mul K) hK

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem fsv_sigma {c : ℂ} (hc : c ≠ 0) :
    fsv (Complex.I * (Real.pi : ℂ) / (2 * c)) c = -1 ∧
      ‖Complex.I * (Real.pi : ℂ) / (2 * c)‖ = Real.pi / (2 * ‖c‖) := by
  constructor
  · unfold fsv
    have e1 : Complex.I * (Real.pi : ℂ) / (2 * c) * c = Complex.I * (Real.pi / 2 : ℝ) := by
      push_cast; field_simp
    have e2 : conj (Complex.I * (Real.pi : ℂ) / (2 * c)) * conj c = -(Complex.I * (Real.pi / 2 : ℝ)) := by
      rw [← map_mul, e1, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
    rw [e1, e2, sub_neg_eq_add, ← two_mul, show (2 : ℂ) * (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) =
      Real.pi * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]
  · rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_two, one_mul]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem rr_eq_form {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h : C.LPt)
    (hh : D.IsLocPt h j) :
    p.RR F j w h h = p.form j hj w (KB.slv p.T F j hj w h hh.2) (KB.slv p.T F j hj w h hh.2) := by
  unfold KB.Pl.RR D.RRplace
  rw [dif_pos ⟨hh, hh⟩, dif_pos hj]
  rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem bdd_of_tendsto {u : ℕ → ℂ} {x : ℂ} (hu : Tendsto u atTop (𝓝 x)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖u n‖ ≤ B := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto u hu)
  exact ⟨max B 0, le_max_right _ _, fun n => (hB _ ⟨n, rfl⟩).trans (le_max_left _ _)⟩

end Formalism.FourierDecayAlt.P.PBO
