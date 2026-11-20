import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BetaInfA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Use `⟨?_, fun u v hu hv hl g hg => h2 u v hu hv (by omega) g hg⟩` and prove the remaining obligations. Introduce `g₀ hg₀`. Take `⟨U, f', hU, hg, hf, he⟩` from `h1 g₀ hg₀`. Conclude with `⟨U, f', hU, hg, hf.of_le (by exact_mod_cast (by norm_num : (4 : ℕ) ≤ 5)), he⟩`.
-/
theorem ccle_five_four {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {F : Mat k r → E} {c : ℝ}
    (h : CCle A 5 F c) : CCle A 4 F c := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun u v hu hv hl g hg => h2 u v hu hv (by omega) g hg⟩
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hf, he⟩ := h1 g₀ hg₀
  exact ⟨U, f', hU, hg, hf.of_le (by exact_mod_cast (by norm_num : (4 : ℕ) ≤ 5)), he⟩

/- English proof (translation)
Take `⟨c, hc⟩` from `h`. Conclude with `⟨c, ccle_five_four hc⟩`.
-/
theorem inCC_five_four {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {F : Mat k r → E}
    (h : InCC A 5 F) : InCC A 4 F := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, ccle_five_four hc⟩

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.B.lam Formalism.QuantumDeterminants.ell`. Use `Complex.continuous_re.comp (continuous_const.mul (continuous_finset_sum _ fun a _ => ?_))` and prove the remaining obligations. Use `split_ifs`. Conclude with `(continuous_apply _).comp (continuous_apply _)`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply] fun_prop`.
-/
theorem continuous_lam (z : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun n : Mt k r => lam k r z (Matrix.of n) := by
  unfold Formalism.FourierDecayAlt.B.lam Formalism.QuantumDeterminants.ell
  refine Complex.continuous_re.comp (continuous_const.mul (continuous_finset_sum _ fun a _ => ?_))
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop

/- English proof (translation)
Establish `h1` using `continuous_lam (k := k) (r := r) D.z`. Establish `h2` using `continuous_lam (k := k) (r := r) D.z'`. Unfold `Formalism.FourierDecayAlt.B.xiTau`. Use `Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))` and prove the remaining obligations. Conclude with `((continuous_fst.comp continuous_fst).mul (h1.comp (continuous_snd.comp (continuous_fst.comp continuous_snd)))).sub ((continuous_snd.comp continuous_fst).mul (h2.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))))`.
-/
theorem continuous_xiTau_prod (D : RealPlaceData k r Wp Wq) :
    Continuous fun x : (ℝ × ℝ) × SS k r => xiTau D x.1 x.2 := by
  have h1 := continuous_lam (k := k) (r := r) D.z
  have h2 := continuous_lam (k := k) (r := r) D.z'
  unfold Formalism.FourierDecayAlt.B.xiTau
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact ((continuous_fst.comp continuous_fst).mul
      (h1.comp (continuous_snd.comp (continuous_fst.comp continuous_snd)))).sub
    ((continuous_snd.comp continuous_fst).mul
      (h2.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))))

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.B.xiTau`. Rewrite using `[mul_comm]`. Conclude with `Complex.norm_exp_ofReal_mul_I _`.
-/
theorem norm_xiTau (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (p : SS k r) : ‖xiTau D τ p‖ = 1 := by
  unfold Formalism.FourierDecayAlt.B.xiTau
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

/- English proof (translation)
Use `continuous_of_dominated (bound := fun p => ‖P p‖) (fun τ => ?_) (fun τ => ?_) hP.norm ?_` and prove the remaining obligations. Conclude with `((continuous_xiTau_prod D).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul hP.aestronglyMeasurable`. Conclude with `Filter.Eventually.of_forall fun p => by simp only [norm_mul, norm_xiTau, one_mul, le_refl]`. Conclude with `Filter.Eventually.of_forall fun p => ((continuous_xiTau_prod D).comp (continuous_id.prodMk continuous_const)).mul continuous_const`.
-/
theorem continuous_cf (D : RealPlaceData k r Wp Wq) {P : SS k r → ℂ} (hP : Integrable P D.μSS) :
    Continuous fun τ : ℝ × ℝ => ∫ p, xiTau D τ p * P p ∂D.μSS := by
  refine continuous_of_dominated (bound := fun p => ‖P p‖) (fun τ => ?_) (fun τ => ?_) hP.norm ?_
  · exact ((continuous_xiTau_prod D).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
      hP.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by simp only [norm_mul, norm_xiTau, one_mul, le_refl]
  · exact Filter.Eventually.of_forall fun p =>
      ((continuous_xiTau_prod D).comp (continuous_id.prodMk continuous_const)).mul continuous_const

/- English proof (translation)
The claim follows from `(hw.1.continuous.integrable_of_hasCompactSupport hw.2.1).ofReal`.
-/
theorem integrable_test {w : ℝ → ℝ} (hw : IsTest w) : Integrable (fun x => (w x : ℂ)) volume := (hw.1.continuous.integrable_of_hasCompactSupport hw.2.1).ofReal

/- English proof (translation)
Establish `h` using `MeasureTheory.Integrable.mul_prod (integrable_test h₁) (integrable_test h₂)`. Rewrite using `[Measure.volume_eq_prod]`. Use `push_cast`. Conclude with `h`.
-/
theorem integrable_test2 {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Integrable (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ)) volume := by
  have h := MeasureTheory.Integrable.mul_prod (integrable_test h₁) (integrable_test h₂)
  rw [Measure.volume_eq_prod]
  push_cast
  exact h

/- English proof (translation)
Establish `e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((τ.1 * a - τ.2 * b : ℝ) : ℂ)) = ((w₁ τ.1 : ℂ) * Complex.exp (Complex.I * ((τ.1 * a : ℝ) : ℂ))) * ((w₂ τ.2 : ℂ) * Complex.exp (Complex.I * ((τ.2 * -b : ℝ) : ℂ)))`. Introduce `τ`. Use `push_cast`. Rewrite using `[show Complex.I * ((τ.1 : ℂ) * a - τ.2 * b) = Complex.I * (τ.1 * a) + Complex.I * (τ.2 * -b) by ring, Complex.exp_add]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Measure.volume_eq_prod, integral_congr_ae (Filter.Eventually.of_forall e)]`. Conclude with `MeasureTheory.integral_prod_mul (fun x : ℝ => (w₁ x : ℂ) * Complex.exp (Complex.I * ((x * a : ℝ) : ℂ))) (fun y : ℝ => (w₂ y : ℂ) * Complex.exp (Complex.I * ((y * -b : ℝ) : ℂ)))`.
-/
theorem inner_om (w₁ w₂ : ℝ → ℝ) (a b : ℝ) :
    ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((τ.1 * a - τ.2 * b : ℝ) : ℂ)) = om w₁ a * om w₂ (-b) := by
  have e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((τ.1 * a - τ.2 * b : ℝ) : ℂ)) =
      ((w₁ τ.1 : ℂ) * Complex.exp (Complex.I * ((τ.1 * a : ℝ) : ℂ))) *
        ((w₂ τ.2 : ℂ) * Complex.exp (Complex.I * ((τ.2 * -b : ℝ) : ℂ))) := by
    intro τ
    push_cast
    rw [show Complex.I * ((τ.1 : ℂ) * a - τ.2 * b) =
      Complex.I * (τ.1 * a) + Complex.I * (τ.2 * -b) by ring, Complex.exp_add]
    ring
  rw [Measure.volume_eq_prod, integral_congr_ae (Filter.Eventually.of_forall e)]
  exact MeasureTheory.integral_prod_mul
    (fun x : ℝ => (w₁ x : ℂ) * Complex.exp (Complex.I * ((x * a : ℝ) : ℂ)))
    (fun y : ℝ => (w₂ y : ℂ) * Complex.exp (Complex.I * ((y * -b : ℝ) : ℂ)))

/- English proof (translation)
Use `haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩`. Use `infer_instance`.
-/
theorem sigmaFinite_haarOn {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

/- English proof (translation)
Use `haveI := sigmaFinite_haarOn D.haarW`. Use `haveI := sigmaFinite_haarOn D.haarN`. Use `haveI := sigmaFinite_haarOn D.haarW'`. Unfold `RealPlaceData.μSS`. Use `infer_instance`.
-/
theorem sigmaFinite_SS (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μSS := by
  haveI := sigmaFinite_haarOn D.haarW
  haveI := sigmaFinite_haarOn D.haarN
  haveI := sigmaFinite_haarOn D.haarW'
  unfold RealPlaceData.μSS
  infer_instance

/- English proof (translation)
Use `haveI := sigmaFinite_SS D`. Establish `hint : Integrable (fun x : (ℝ × ℝ) × SS k r => ((w₁ x.1.1 * w₂ x.1.2 : ℝ) : ℂ) * (xiTau D x.1 x.2 * P x.2)) (volume.prod D.μSS)`. Use `(MeasureTheory.Integrable.mul_prod (integrable_test2 h₁ h₂) hP).mono ?_ ?_` and prove the remaining obligations. Use `haveI : OpensMeasurableSpace ((ℝ × ℝ) × SS k r) := Prod.opensMeasurableSpace`. Conclude with `(integrable_test2 h₁ h₂).aestronglyMeasurable.comp_fst.mul ((continuous_xiTau_prod D).aestronglyMeasurable.mul hP.aestronglyMeasurable.comp_snd)`.

Conclude with `Filter.Eventually.of_forall fun x => by simp only [norm_mul, norm_xiTau, one_mul, le_refl]`. Repeatedly rewrite using `[← integral_const_mul]`. Rewrite using `[integral_integral_swap (f := fun τ p => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (xiTau D τ p * P p)) hint]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Establish `e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (xiTau D τ p * P p) = (((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((τ.1 * lam k r D.z (Matrix.of p.1.2) - τ.2 * lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ))) * P p` using `fun τ => by unfold Formalism.FourierDecayAlt.B.xiTau; ring`.

Simplify using `only [e]`. Rewrite using `[integral_mul_const, inner_om]`.
-/
theorem fubini_cf (D : RealPlaceData k r Wp Wq) {P : SS k r → ℂ} (hP : Integrable P D.μSS)
    {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * ∫ p, xiTau D τ p * P p ∂D.μSS =
      ∫ p, om w₁ (lam k r D.z (Matrix.of p.1.2)) * om w₂ (-lam k r D.z' (Matrix.of p.2.2)) * P p ∂D.μSS := by
  haveI := sigmaFinite_SS D
  have hint : Integrable (fun x : (ℝ × ℝ) × SS k r =>
      ((w₁ x.1.1 * w₂ x.1.2 : ℝ) : ℂ) * (xiTau D x.1 x.2 * P x.2)) (volume.prod D.μSS) := by
    refine (MeasureTheory.Integrable.mul_prod (integrable_test2 h₁ h₂) hP).mono ?_ ?_
    · haveI : OpensMeasurableSpace ((ℝ × ℝ) × SS k r) := Prod.opensMeasurableSpace
      exact (integrable_test2 h₁ h₂).aestronglyMeasurable.comp_fst.mul
        ((continuous_xiTau_prod D).aestronglyMeasurable.mul hP.aestronglyMeasurable.comp_snd)
    · exact Filter.Eventually.of_forall fun x => by simp only [norm_mul, norm_xiTau, one_mul, le_refl]
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap (f := fun τ p => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (xiTau D τ p * P p)) hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (xiTau D τ p * P p) =
      (((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * Complex.exp (Complex.I *
        ((τ.1 * lam k r D.z (Matrix.of p.1.2) - τ.2 * lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ))) * P p :=
    fun τ => by unfold Formalism.FourierDecayAlt.B.xiTau; ring
  simp only [e]
  rw [integral_mul_const, inner_om]

/- English proof (translation)
The claim follows from `isOpen_Ioi.prod isOpen_Ioi`.
-/
theorem isOpen_Quad : IsOpen Quad := isOpen_Ioi.prod isOpen_Ioi

/- English proof (translation)
Establish `hK : IsCompact (tsupport w₁ ×ˢ tsupport w₂)` using `h₁.2.1.prod h₂.2.1`. Establish `hKQ : tsupport w₁ ×ˢ tsupport w₂ ⊆ Quad` using `Set.prod_mono h₁.2.2 h₂.2.2`. Establish `hc : ContinuousOn (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * f τ) (tsupport w₁ ×ˢ tsupport w₂)`. Use `ContinuousOn.mul ?_ (hf.mono hKQ)` and prove the remaining obligations. Conclude with `(Complex.continuous_ofReal.comp ((h₁.1.continuous.comp continuous_fst).mul (h₂.1.continuous.comp continuous_snd))).continuousOn`.

Use `MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero (hc.integrableOn_compact (μ := volume) hK) ?_` and prove the remaining obligations. Introduce `τ hτ`. Rewrite `hτ` using `[Set.mem_prod, not_and_or]`. Break down `hτ with h | h` into its components or cases. Simplify using `[image_eq_zero_of_notMem_tsupport h]`.

Simplify using `[image_eq_zero_of_notMem_tsupport h]`.
-/
theorem integrable_test_mul {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) {f : ℝ × ℝ → ℂ}
    (hf : ContinuousOn f Quad) : Integrable (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * f τ) volume := by
  have hK : IsCompact (tsupport w₁ ×ˢ tsupport w₂) := h₁.2.1.prod h₂.2.1
  have hKQ : tsupport w₁ ×ˢ tsupport w₂ ⊆ Quad := Set.prod_mono h₁.2.2 h₂.2.2
  have hc : ContinuousOn (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * f τ)
      (tsupport w₁ ×ˢ tsupport w₂) := by
    refine ContinuousOn.mul ?_ (hf.mono hKQ)
    exact (Complex.continuous_ofReal.comp ((h₁.1.continuous.comp continuous_fst).mul
      (h₂.1.continuous.comp continuous_snd))).continuousOn
  refine MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero
    (hc.integrableOn_compact (μ := volume) hK) ?_
  intro τ hτ
  rw [Set.mem_prod, not_and_or] at hτ
  rcases hτ with h | h
  · simp [image_eq_zero_of_notMem_tsupport h]
  · simp [image_eq_zero_of_notMem_tsupport h]

/- English proof (translation)
Take `⟨-, hcont, -⟩` from `hRB`. Establish `hc1 : ContinuousOn (fun τ => betaInfTau D τ F F') Quad` using `hcont F F' hF hF'`. Establish `hc2 : ContinuousOn (fun τ : ℝ × ℝ => ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS) Quad` using `(continuous_cf D hP).continuousOn`. Establish `hae` using `hAe (fun _ => 0) (fun τ => betaInfTau D τ F F' - ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS) aemeasurable_const (hc1.sub hc2) (fun w₁ w₂ h₁ h₂ _ _ => by`. Use `⟨by simp, ?_⟩` and prove the remaining obligations.

Simplify using `only [mul_zero, MeasureTheory.lintegral_zero, ENNReal.toReal_zero, Complex.ofReal_zero]`. Repeatedly rewrite using `[mul_sub]`. Rewrite using `[integral_sub (integrable_test_mul h₁ h₂ hc1) (integrable_test_mul h₁ h₂ hc2), (hRA F F' hF hF' w₁ w₂ h₁ h₂).2, fubini_cf D hP h₁ h₂, sub_self])`. Establish `h0 : (fun τ => betaInfTau D τ F F' - ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS) =ᵐ[volume.restrict Quad] fun _ => 0` using `by filter_upwards [hae] with τ hτ`. Simplify using `using hτ.2.symm`.

Establish `heq` using `Measure.eqOn_open_of_ae_eq h0 isOpen_Quad (hc1.sub hc2) continuousOn_const`. Establish `h11 : ((1 : ℝ), (1 : ℝ)) ∈ Quad`. Unfold `Quad`. Conclude with `⟨by norm_num, by norm_num⟩`. Use `show betaInfTau D (1, 1) F F' = _`.

Conclude with `sub_eq_zero.mp (heq h11)`.
-/
theorem betaInf_eq_of (D : RealPlaceData k r Wp Wq) [FiniteDimensional ℂ Wq] (A : ℝ) (hAe : AeFromTests)
    (hRB : RegBound D A) (hRA : RegAverage D A) {F F' : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : InCC A 4 F) (hF' : InCC A 4 F') (hP : Integrable (Ph D F F') D.μSS) :
    betaInf D F F' = ∫ p, xiTau D (1, 1) p * Ph D F F' p ∂D.μSS := by
  obtain ⟨-, hcont, -⟩ := hRB
  have hc1 : ContinuousOn (fun τ => betaInfTau D τ F F') Quad := hcont F F' hF hF'
  have hc2 : ContinuousOn (fun τ : ℝ × ℝ => ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS) Quad :=
    (continuous_cf D hP).continuousOn
  have hae := hAe (fun _ => 0)
    (fun τ => betaInfTau D τ F F' - ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS)
    aemeasurable_const (hc1.sub hc2) (fun w₁ w₂ h₁ h₂ _ _ => by
      refine ⟨by simp, ?_⟩
      simp only [mul_zero, MeasureTheory.lintegral_zero, ENNReal.toReal_zero, Complex.ofReal_zero]
      simp_rw [mul_sub]
      rw [integral_sub (integrable_test_mul h₁ h₂ hc1) (integrable_test_mul h₁ h₂ hc2),
        (hRA F F' hF hF' w₁ w₂ h₁ h₂).2, fubini_cf D hP h₁ h₂, sub_self])
  have h0 : (fun τ => betaInfTau D τ F F' - ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS)
      =ᵐ[volume.restrict Quad] fun _ => 0 := by
    filter_upwards [hae] with τ hτ
    simpa using hτ.2.symm
  have heq := Measure.eqOn_open_of_ae_eq h0 isOpen_Quad (hc1.sub hc2) continuousOn_const
  have h11 : ((1 : ℝ), (1 : ℝ)) ∈ Quad := by
    unfold Quad
    exact ⟨by norm_num, by norm_num⟩
  show betaInfTau D (1, 1) F F' = _
  exact sub_eq_zero.mp (heq h11)

end ReciprocityTheory.ChartRestriction.DS.Mult1.BetaInfA
