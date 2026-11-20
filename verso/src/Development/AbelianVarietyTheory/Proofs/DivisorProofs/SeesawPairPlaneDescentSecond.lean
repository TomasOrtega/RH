import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCocompactInArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentNinthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentTenthStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measUA
local instance borelUAX {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

noncomputable section

namespace GlobalTheory.ThKTermX

/- English proof (translation)
Establish `hfin : IsFiniteMeasure (μ.restrict s)` using `isFiniteMeasure_restrict.2 hs`. Establish `hlin : ∑' i, ∫⁻ u in s, ‖f i u‖ₑ ∂μ ≠ ⊤`. Rewrite using `[← lintegral_tsum (fun i => (hm i).enorm)]`. Use `ne_top_of_le_ne_top (b := ∫⁻ _ in s, ENNReal.ofReal C ∂μ) ?_ (lintegral_mono fun u => ?_)` and prove the remaining obligations. Rewrite using `[lintegral_const]`.

Conclude with `ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)`. Repeatedly rewrite using `[← ofReal_norm_eq_enorm]`. Rewrite using `[← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hb u).1]`. Conclude with `ENNReal.ofReal_le_ofReal (hb u).2`. Use `⟨?_, integral_tsum hm hlin⟩` and prove the remaining obligations.

Use `Summable.of_norm_bounded (g := fun i => (∫⁻ u in s, ‖f i u‖ₑ ∂μ).toReal) (ENNReal.summable_toReal hlin) fun i => ?_` and prove the remaining obligations. Use `(norm_integral_le_lintegral_norm _).trans_eq ?_` and prove the remaining obligations. Repeatedly rewrite using `[ofReal_norm_eq_enorm]`.
-/
theorem swap_of_bound {ι G : Type*} [Countable ι] [MeasurableSpace G] (μ : Measure G) (s : Set G) (hs : μ s ≠ ⊤)
    (f : ι → G → ℂ) (hm : ∀ i, AEStronglyMeasurable (f i) (μ.restrict s)) (C : ℝ)
    (hb : ∀ u, Summable (fun i => ‖f i u‖) ∧ ∑' i, ‖f i u‖ ≤ C) :
    Summable (fun i => ∫ u in s, f i u ∂μ) ∧ ∫ u in s, (∑' i, f i u) ∂μ = ∑' i, ∫ u in s, f i u ∂μ := by
  have hfin : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  have hlin : ∑' i, ∫⁻ u in s, ‖f i u‖ₑ ∂μ ≠ ⊤ := by
    rw [← lintegral_tsum (fun i => (hm i).enorm)]
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in s, ENNReal.ofReal C ∂μ) ?_ (lintegral_mono fun u => ?_)
    · rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    · simp_rw [← ofReal_norm_eq_enorm]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hb u).1]
      exact ENNReal.ofReal_le_ofReal (hb u).2
  refine ⟨?_, integral_tsum hm hlin⟩
  refine Summable.of_norm_bounded (g := fun i => (∫⁻ u in s, ‖f i u‖ₑ ∂μ).toReal) (ENNReal.summable_toReal hlin) fun i => ?_
  refine (norm_integral_le_lintegral_norm _).trans_eq ?_
  simp_rw [ofReal_norm_eq_enorm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Simplify using `only [form, add_dotProduct]`.
-/
theorem form_add_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a + b) c = form σ J a c + form σ J b c := by
  simp only [form, add_dotProduct]

/- English proof (translation)
Simplify using `only [form, smul_dotProduct, smul_eq_mul]`.
-/
theorem form_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (t : E) (a c : Fin n → E) :
    form σ J (t • a) c = t * form σ J a c := by
  simp only [form, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Simplify using `only [form, zero_dotProduct]`.
-/
theorem form_zero_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : Fin n → E) : form σ J 0 c = 0 := by
  simp only [form, zero_dotProduct]

/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hJ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_herm_swap {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j) (v w : Fin n → E) : form σ J v w = σ (form σ J w v) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

/- English proof (translation)
Set `Φ : E × (Fin d₂ → E) × E →ₗ[E] (Fin n → E)` to `(LinearMap.smulRight LinearMap.id x).comp (LinearMap.fst E E ((Fin d₂ → E) × E)) + (Matrix.mulVecLin ι).comp ((LinearMap.fst E (Fin d₂ → E) E).comp (LinearMap.snd E E ((Fin d₂ → E) × E))) + (LinearMap.smulRight LinearMap.id y).comp ((LinearMap.snd E (Fin d₂ → E) E).comp (LinearMa …`. Establish `hΦ : ∀ s u r, Φ (s, u, r) = s • x + ι *ᵥ u + r • y` using `fun s u r => by simp [Φ]`. Establish `hyx : form σ J y x = 1` using `by rw [form_herm_swap hσ hJ, hxy, map_one]`. Establish `hΦinj : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce and unpack `⟨s, u, r⟩ h`. Rewrite `h` using `[hΦ]`. Establish `h1` using `congrArg (fun v => form σ J v y) h`. Establish `h2` using `congrArg (fun v => form σ J v x) h`. Simplify using `only [form_add_left, form_smul_left, hxy, hyy, hxx, hyx, (horth u).1, (horth u).2, form_zero_left] at h1 h2`.

Establish `hs : s = 0` using `by simpa using h1`. Establish `hr : r = 0` using `by simpa using h2`. Substitute `hs hr` using the available equality. Establish `hu : ι *ᵥ u = 0` using `by simpa using h`. Establish `hu0 : u = 0` using `hinj (by rw [hu, Matrix.mulVec_zero])`.

Simplify using `[hu0]`. Establish `hsurj : Function.Surjective Φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp; omega)).mp hΦinj`. Introduce `v`. Take `⟨⟨s, u, r⟩, h⟩` from `hsurj v`. Conclude with `⟨s, r, u, by rw [← h, hΦ]⟩`.
-/
theorem span_plane {n d₂ : ℕ} (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    (x y : Fin n → E) (ι : Matrix (Fin n) (Fin d₂) E) (hn : d₂ + 2 = n) (hxx : form σ J x x = 0)
    (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (hinj : Function.Injective ι.mulVec) :
    ∀ v : Fin n → E, ∃ (s t : E) (u : Fin d₂ → E), v = s • x + ι *ᵥ u + t • y := by
  let Φ : E × (Fin d₂ → E) × E →ₗ[E] (Fin n → E) :=
    (LinearMap.smulRight LinearMap.id x).comp (LinearMap.fst E E ((Fin d₂ → E) × E)) +
    (Matrix.mulVecLin ι).comp ((LinearMap.fst E (Fin d₂ → E) E).comp (LinearMap.snd E E ((Fin d₂ → E) × E))) +
    (LinearMap.smulRight LinearMap.id y).comp ((LinearMap.snd E (Fin d₂ → E) E).comp (LinearMap.snd E E ((Fin d₂ → E) × E)))
  have hΦ : ∀ s u r, Φ (s, u, r) = s • x + ι *ᵥ u + r • y := fun s u r => by simp [Φ]
  have hyx : form σ J y x = 1 := by rw [form_herm_swap hσ hJ, hxy, map_one]
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, u, r⟩ h
    rw [hΦ] at h
    have h1 := congrArg (fun v => form σ J v y) h
    have h2 := congrArg (fun v => form σ J v x) h
    simp only [form_add_left, form_smul_left, hxy, hyy, hxx, hyx, (horth u).1, (horth u).2, form_zero_left] at h1 h2
    have hs : s = 0 := by simpa using h1
    have hr : r = 0 := by simpa using h2
    subst hs hr
    have hu : ι *ᵥ u = 0 := by simpa using h
    have hu0 : u = 0 := hinj (by rw [hu, Matrix.mulVec_zero])
    simp [hu0]
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp; omega)).mp hΦinj
  intro v
  obtain ⟨⟨s, u, r⟩, h⟩ := hsurj v
  exact ⟨s, r, u, by rw [← h, hΦ]⟩

end GlobalTheory.ThKTermX

namespace GlobalTheory.ThKTermX

/- English proof (translation)
Establish `hM` using `hP.good`. Establish `hψ` using `hP.base.std`. Take `⟨l₀, hl₀, hl₀eq⟩` from `GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin d₂ × Fin d)`. Use `set z := M.co.e (Matrix.vecMulVec (incV F H.y) (incV F w))`. Establish `hl` using `GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ z (GlobalTheory.ConeMeasV.comp_ev_mem_adm hM hM₁ hE hl₀)`.

Establish `hc` using `hP.weil.2.2 _ hl Ψ hΨ`. Establish `hsplit` using `hP.weil.isUSplitting`. Establish `heq : (fun u : unip σ X H => thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ)))) = fun u : unip σ X H => ((l₀ ∘ₗ e) ∘ₗ GlobalTheory.ConeMeasV.schrLin B.ψ z) (om (u.1, 1) Ψ)`. Use function extensionality and compare the values at `u`. Establish `h1 : om (u.1, 1) Ψ ∈ schA F _` using `hsplit.pres (u.1, 1) Ψ hΨ`.

Establish `h2` using `GlobalTheory.ConeMeasV.schr_mem_schA hψ z h1`. Establish `h3` using `hE.maps _ h2`. Conclude with `(hl₀eq _ h3).symm`. Rewrite using `[heq]`. Conclude with `hc.comp (continuous_subtype_val.prodMk continuous_const)`.
-/
theorem continuous_term {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') {d₂ : ℕ} (H : Plane E n d₂) {V₁ : Spc F E d₂}
    {M₁ : Model σ V₁ W} {e : Fn F n d →ₗ[ℂ] Fn F d₂ d} {I : Set (Matrix (Fin n) (Fin d) (AE F E))}
    (hM₁ : M₁.IsGood B.ψ) (hE : IsEv B M M₁ H.ι 1 I e) (Ψ : Fn F n d) (hΨ : Ψ ∈ schA F (Fin n × Fin d))
    (w : Fin d → E) :
    Continuous (fun u : unip σ X H => thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ)))) := by
  have hM := hP.good
  have hψ := hP.base.std
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin d₂ × Fin d)
  set z := M.co.e (Matrix.vecMulVec (incV F H.y) (incV F w))
  have hl := GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ z (GlobalTheory.ConeMeasV.comp_ev_mem_adm hM hM₁ hE hl₀)
  have hc := hP.weil.2.2 _ hl Ψ hΨ
  have hsplit := hP.weil.isUSplitting
  have heq : (fun u : unip σ X H => thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ)))) =
      fun u : unip σ X H => ((l₀ ∘ₗ e) ∘ₗ GlobalTheory.ConeMeasV.schrLin B.ψ z) (om (u.1, 1) Ψ) := by
    funext u
    have h1 : om (u.1, 1) Ψ ∈ schA F _ := hsplit.pres (u.1, 1) Ψ hΨ
    have h2 := GlobalTheory.ConeMeasV.schr_mem_schA hψ z h1
    have h3 := hE.maps _ h2
    exact (hl₀eq _ h3).symm
  rw [heq]
  exact hc.comp (continuous_subtype_val.prodMk continuous_const)

end GlobalTheory.ThKTermX

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ hE μ 𝓕 _ _ h1 Ψ hΨ`. Take `⟨hn, hxx, hyy, hxy, horth, hinj⟩` from `hH`. Establish `hσ` using `GlobalTheory.SiegelSet.sigma_sigma hP.base.cm`. Establish `hspan` using `GlobalTheory.ThKTermX.span_plane X.J hσ hP.herm.herm H.x H.y H.ι hn hxx hyy hxy horth hinj`. Take `⟨K, hKc, hcov⟩` from `GlobalTheory.UnipHermCover.cocompact_herm F E σ hP.base.cm n d₂ X H hP.herm.herm hxx hyy hxy horth hspan`.

Take `⟨C, hC⟩` from `GlobalTheory.T.seesaw_pair_plane_descent_tenth hK F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H ⟨hn, hxx, hyy, hxy, horth, hinj⟩ V₁ M₁ e hV₁ hM₁ hE Ψ hΨ K hKc`. Establish `hb : ∀ u : unip σ X H, Summable (fun w : Fin d → E => ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ)))‖) ∧ ∑' w : Fin d → E, ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ)))‖ ≤ C`. Introduce `u`. Take `⟨γ, hγ⟩` from `hcov u`. Establish `key : ∀ w : Fin d → E, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ))) = thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om ((γ • u).1, 1) Ψ)))` using `fun w => (GlobalTheory.T.seesaw_pair_plane_descent_ninth hK F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H ⟨hn, hxx, hyy, hxy, horth, hinj⟩ V₁ M₁ e hV₁ hM₁ hE Ψ hΨ w (γ : unip σ X H) u (Subgroup.mem_subgroupOf.1 γ.2)).symm`.

Repeatedly rewrite using `[key]`. Conclude with `hC _ hγ`. Use `haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable`. Conclude with `GlobalTheory.ThKTermX.swap_of_bound μ 𝓕 (by simp [h1]) _ (fun w => (GlobalTheory.ThKTermX.continuous_term hP H hM₁ hE Ψ hΨ w).aestronglyMeasurable) C hb`.
-/
theorem GlobalTheory.ThKTermX.termwise : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ (μ : Measure (unip σ X H)) (𝓕 : Set (unip σ X H)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕 μ → μ 𝓕 = 1 →
    ∀ Ψ ∈ schA F (Fin n × Fin d),
      Summable (fun w : Fin d → E => ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ))) ∂μ) ∧
      ∫ u in 𝓕, (∑' w : Fin d → E, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ)))) ∂μ = ∑' w : Fin d → E, ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ))) ∂μ := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ hE μ 𝓕 _ _ h1 Ψ hΨ
  obtain ⟨hn, hxx, hyy, hxy, horth, hinj⟩ := hH
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hP.base.cm
  have hspan := GlobalTheory.ThKTermX.span_plane X.J hσ hP.herm.herm H.x H.y H.ι hn hxx hyy hxy horth hinj
  obtain ⟨K, hKc, hcov⟩ := GlobalTheory.UnipHermCover.cocompact_herm F E σ hP.base.cm n d₂ X H hP.herm.herm hxx hyy hxy horth hspan
  obtain ⟨C, hC⟩ := GlobalTheory.T.seesaw_pair_plane_descent_tenth hK F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H
    ⟨hn, hxx, hyy, hxy, horth, hinj⟩ V₁ M₁ e hV₁ hM₁ hE Ψ hΨ K hKc
  have hb : ∀ u : unip σ X H, Summable (fun w : Fin d → E => ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ)))‖) ∧ ∑' w : Fin d → E, ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ)))‖ ≤ C := by
    intro u
    obtain ⟨γ, hγ⟩ := hcov u
    have key : ∀ w : Fin d → E, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ))) = thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om ((γ • u).1, 1) Ψ))) :=
      fun w => (GlobalTheory.T.seesaw_pair_plane_descent_ninth hK F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H
        ⟨hn, hxx, hyy, hxy, horth, hinj⟩ V₁ M₁ e hV₁ hM₁ hE Ψ hΨ w (γ : unip σ X H) u
        (Subgroup.mem_subgroupOf.1 γ.2)).symm
    simp_rw [key]
    exact hC _ hγ
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  exact GlobalTheory.ThKTermX.swap_of_bound μ 𝓕 (by simp [h1]) _
    (fun w => (GlobalTheory.ThKTermX.continuous_term hP H hM₁ hE Ψ hΨ w).aestronglyMeasurable) C hb
