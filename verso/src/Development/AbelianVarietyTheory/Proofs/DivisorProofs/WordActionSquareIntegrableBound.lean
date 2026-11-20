import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivArchimedeanLiftTraceFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivArchimedeanWeilRepIntertwineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanCoordsMovedStaySupportedAndRecoveredStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepMovedArchimedeanCoordsPolynomialHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordOperatorL2BoundPolynomialStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ μ hμ p`. Establish `S` using `IsUWeilPair.isUSplitting hP.weil`. Take `⟨T, hT⟩` from `GlobalTheory.T.heisenbergDeriv_archimedeanLift_traceFormula F E σ n d X W M B.ψ hP.base.std`. Take `⟨C3, k3, hsz⟩` from `GlobalTheory.T.weilRep_moved_archimedean_coords_polynomial_height F E σ B n d X W M χX χW om r s r' s' hP`. Use `set c : ℂ := -(2 * Real.pi * Complex.I) with hc`.

Establish `hcn : ‖c‖ = 2 * Real.pi`. Rewrite using `[hc, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]`. Evaluate the numerical expressions. Establish `hc0 : c ≠ 0`. Introduce `h0`.

Rewrite `hcn` using `[h0, norm_zero]`. Combine the linear relations using `[Real.pi_pos]`. Take `⟨C4, hwb⟩` from `GlobalTheory.T.word_operator_L2_bound_polynomial F (Fin n × Fin d) (T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) c Φ hΦ μ hμ p`. Establish `hcl : ∀ ζ, ∀ f ∈ schA F (Fin n × Fin d), heisD M B.ψ (liftI M ζ) f ∈ schA F (Fin n × Fin d)`. Introduce `ζ f hf`.

Rewrite using `[hT ζ f hf, dR]`. Conclude with `Submodule.add_mem _ (GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz F _ (Sum.inl ζ.1) f hf) (Submodule.smul_mem _ c (GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz F _ (Sum.inr _) f hf))`. Establish `hHcl : ∀ zs f, f ∈ schA F (Fin n × Fin d) → wordH M B.ψ zs f ∈ schA F (Fin n × Fin d)`. Introduce `zs f hf`. Proceed by induction on `zs with`.

Consider the case `nil => exact hf`. Consider the case `cons ζ zs ih => exact hcl ζ _ ih`. Establish `hHR : ∀ zs f, f ∈ schA F (Fin n × Fin d) → wordH M B.ψ zs f = wordR F (T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) c zs f`. Introduce `zs f hf`. Proceed by induction on `zs with`.

Consider the case `nil => rfl`. Consider the case `cons ζ zs ih => show heisD M B.ψ (liftI M ζ) (wordH M B.ψ zs f) = dR F _ c ζ (wordR F _ c zs f)`. Rewrite using `[hT ζ _ (hHcl zs f hf), ih]`. Set `dirOf : Op F (Fin n × Fin d) → (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)` to `fun o => Sum.elim (fun v => (v, 0)) (fun l => (0, T.symm l)) o`. Set `cOf : Op F (Fin n × Fin d) → ℂ` to `fun o => Sum.elim (fun _ => 1) (fun _ => c⁻¹) o`.

Establish `hlet : ∀ o, ∀ f ∈ schA F (Fin n × Fin d), app F o f = cOf o • heisD M B.ψ (liftI M (dirOf o)) f`. Introduce `o f hf`. Rewrite using `[hT _ f hf]`. Consider the cases of `o with`. Consider the case `inl v => show dD F v f = (1 : ℂ) • (dD F v f + c • mM F ((T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] _) 0) f)`.

Rewrite using `[map_zero, mM_zero, smul_zero, add_zero, one_smul]`. Consider the case `inr l => show mM F l f = c⁻¹ • (dD F 0 f + c • mM F ((T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] _) (T.symm l)) f)`. Rewrite using `[dD_zero, zero_add, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Use `set C0 : ℝ := max 1 ‖(T.symm : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F))‖ with hC0`. Establish `hC01 : 1 ≤ C0` using `le_max_left _ _`.

Establish `hdir : ∀ o, ‖dirOf o‖ ≤ C0 * size F o`. Introduce `o`. Consider the cases of `o with`. Consider the case `inl v => show ‖((v, 0) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))‖ ≤ C0 * ‖v‖`. Rewrite using `[Prod.norm_def, norm_zero, max_eq_left (norm_nonneg v)]`.

Conclude with `le_mul_of_one_le_left (norm_nonneg v) hC01`. Consider the case `inr l => show ‖((0, T.symm l) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))‖ ≤ C0 * ‖l‖`. Rewrite using `[Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]`. Conclude with `(ContinuousLinearMap.le_opNorm (T.symm : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F)) l).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg l))`. Establish `hcOf : ∀ o, ‖cOf o‖ ≤ 1`.

Introduce `o`. Consider the cases of `o with`. Consider the case `inl v => show ‖(1 : ℂ)‖ ≤ 1`. Rewrite using `[norm_one]`. Consider the case `inr l => show ‖c⁻¹‖ ≤ 1`.

Rewrite using `[norm_inv, hcn]`. Conclude with `inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])`. Use `⟨max C4 0 * (max 1 (max C3 0 * C0)) ^ (2 * p), k3 * (2 * p), fun g h w hw hw1 => ?_⟩` and prove the remaining obligations. Use `set H : ℝ := (ht g : ℝ) * ht h with hH`. Establish `hH1 : 1 ≤ H` using `one_le_mul_of_one_le_of_one_le (by exact_mod_cast one_le_heightGL F g.1) (by exact_mod_cast one_le_heightGL F h.1)`.

Establish `hH0 : 0 ≤ H` using `zero_le_one.trans hH1`. Establish `hΨs : om (g, h) Φ ∈ schA F (Fin n × Fin d)` using `S.pres _ _ hΦ`. Establish `c1 : ∀ w : List (Op F (Fin n × Fin d)), ∃ a : ℂ, ‖a‖ ≤ 1 ∧ word F w (om (g, h) Φ) = a • wordH M B.ψ (w.map dirOf) (om (g, h) Φ)`. Introduce `w`. Proceed by induction on `w with`.

Consider the case `nil => exact ⟨1, by rw [norm_one], by rw [one_smul]; rfl⟩`. Consider the case `cons o w ih`. Take `⟨a, ha, e⟩` from `ih`. Use `⟨a * cOf o, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_one₀ ha (norm_nonneg _) (hcOf o)`. Rewrite using `[word_cons, e, app_smul, hlet o _ (hHcl _ _ hΨs), smul_smul]`. Both sides reduce to the same expression. Establish `c2 : ∀ zs, wordH M B.ψ zs (om (g, h) Φ) = om (g, h) (wordH M B.ψ (zs.map (movI M (g, h))) Φ)`. Introduce `zs`.

Proceed by induction on `zs with`. Consider the case `nil => rfl`. Consider the case `cons ζ zs ih`. Take `⟨hA, hL⟩` from `GlobalTheory.T.archimedeanCoords_moved_stay_supported_and_recovered F E σ n d X W M (g, h) ζ`. Use `show heisD M B.ψ (liftI M ζ) (wordH M B.ψ zs (om (g, h) Φ)) = om (g, h) (heisD M B.ψ (liftI M (movI M (g, h) ζ)) (wordH M B.ψ (zs.map (movI M (g, h))) Φ))`.

Rewrite using `[ih, GlobalTheory.T.heisenbergDeriv_archimedean_weilRep_intertwine F E σ B n d X W M χX χW om r s r' s' hP (g, h) _ hA _ (hHcl _ _ hΦ), hL]`. Take `⟨a, ha, e⟩` from `c1 w`. Establish `ha' : ‖a‖ₑ ≤ 1`. Rewrite using `[← ofReal_norm_eq_enorm]`. Conclude with `ENNReal.ofReal_le_one.2 ha`.

Use `set zs := (w.map dirOf).map (movI M (g, h)) with hzs`. Establish `hG : wordH M B.ψ zs Φ ∈ schA F (Fin n × Fin d)` using `hHcl _ _ hΦ`. Use `set ρ : ℝ := max 1 (max C3 0 * C0 * H ^ k3) with hρdef`. Establish `hρ : ∀ ζ ∈ zs, ‖ζ‖ ≤ ρ`. Introduce `ζ hζ`.

Take `⟨ζ', hζ', rfl⟩` from `List.mem_map.1 hζ`. Take `⟨o, ho, rfl⟩` from `List.mem_map.1 hζ'`. Use `le_max_of_le_right ((hsz g h _).trans ?_)` and prove the remaining obligations. Establish `hk : 0 ≤ H ^ k3` using `pow_nonneg hH0 _`. Combine the equalities or inequalities in the displayed calculation.

Establish `hlen : zs.length ≤ p` using `by rw [hzs, List.length_map, List.length_map]; exact hw`. Establish `hb` using `hwb ρ (le_max_left _ _) zs hlen hρ`. Rewrite `hb` using `[← hHR zs Φ hΦ]`. Establish `hk1 : 1 ≤ H ^ k3` using `one_le_pow₀ hH1`. Establish `hρle : ρ ≤ max 1 (max C3 0 * C0) * H ^ k3` using `max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hk1) (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hk1))`.

Establish `hρ0 : 0 ≤ ρ` using `zero_le_one.trans (le_max_left _ _)`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[e, c2, Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]`.

Use `_ ≤ ∫⁻ x, ‖om (g, h) (wordH M B.ψ zs Φ) x‖ₑ ^ 2 ∂μ := lintegral_mono fun x => mul_le_of_le_one_left bot_le (pow_le_one₀ bot_le ha')`. Use `_ = ∫⁻ x, ‖wordH M B.ψ zs Φ x‖ₑ ^ 2 ∂μ := S.unit μ hμ _ _ hG`. Use `_ ≤ ENNReal.ofReal (C4 * ρ ^ (2 * p)) := hb`. Use `_ ≤ ENNReal.ofReal (max C4 0 * max 1 (max C3 0 * C0) ^ (2 * p) * H ^ (k3 * (2 * p))) := by`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.ArchDecay.word_action_square_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ (μ : @Measure (Fin n × Fin d → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ p : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (w : List (Op F (Fin n × Fin d))), w.length ≤ p → (∀ o ∈ w, size F o ≤ 1) → ∫⁻ x, ‖word F w (om (g, h) Φ) x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * ((ht g : ℝ) * ht h) ^ k) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ μ hμ p
  have S := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨T, hT⟩ := GlobalTheory.T.heisenbergDeriv_archimedeanLift_traceFormula F E σ n d X W M B.ψ hP.base.std
  obtain ⟨C3, k3, hsz⟩ := GlobalTheory.T.weilRep_moved_archimedean_coords_polynomial_height F E σ B n d X W M χX χW om r s r' s' hP
  set c : ℂ := -(2 * Real.pi * Complex.I) with hc
  have hcn : ‖c‖ = 2 * Real.pi := by
    rw [hc, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, mul_one]
    norm_num
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hcn
    linarith [Real.pi_pos]
  obtain ⟨C4, hwb⟩ := GlobalTheory.T.word_operator_L2_bound_polynomial F (Fin n × Fin d)
    (T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ))
    c Φ hΦ μ hμ p
  have hcl : ∀ ζ, ∀ f ∈ schA F (Fin n × Fin d), heisD M B.ψ (liftI M ζ) f ∈ schA F (Fin n × Fin d) := by
    intro ζ f hf
    rw [hT ζ f hf, dR]
    exact Submodule.add_mem _ (GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz F _ (Sum.inl ζ.1) f hf)
      (Submodule.smul_mem _ c (GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz F _ (Sum.inr _) f hf))
  have hHcl : ∀ zs f, f ∈ schA F (Fin n × Fin d) → wordH M B.ψ zs f ∈ schA F (Fin n × Fin d) := by
    intro zs f hf
    induction zs with
    | nil => exact hf
    | cons ζ zs ih => exact hcl ζ _ ih
  have hHR : ∀ zs f, f ∈ schA F (Fin n × Fin d) → wordH M B.ψ zs f =
      wordR F (T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ))
        c zs f := by
    intro zs f hf
    induction zs with
    | nil => rfl
    | cons ζ zs ih =>
      show heisD M B.ψ (liftI M ζ) (wordH M B.ψ zs f) = dR F _ c ζ (wordR F _ c zs f)
      rw [hT ζ _ (hHcl zs f hf), ih]
  let dirOf : Op F (Fin n × Fin d) →
      (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
    fun o => Sum.elim (fun v => (v, 0)) (fun l => (0, T.symm l)) o
  let cOf : Op F (Fin n × Fin d) → ℂ := fun o => Sum.elim (fun _ => 1) (fun _ => c⁻¹) o
  have hlet : ∀ o, ∀ f ∈ schA F (Fin n × Fin d), app F o f = cOf o • heisD M B.ψ (liftI M (dirOf o)) f := by
    intro o f hf
    rw [hT _ f hf]
    cases o with
    | inl v =>
      show dD F v f = (1 : ℂ) • (dD F v f + c • mM F ((T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] _) 0) f)
      rw [map_zero, mM_zero, smul_zero, add_zero, one_smul]
    | inr l =>
      show mM F l f = c⁻¹ • (dD F 0 f + c • mM F ((T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] _) (T.symm l)) f)
      rw [dD_zero, zero_add, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
        inv_mul_cancel₀ hc0, one_smul]
  set C0 : ℝ := max 1 ‖(T.symm : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) →L[ℝ]
    (Fin n × Fin d → mixedEmbedding.mixedSpace F))‖ with hC0
  have hC01 : 1 ≤ C0 := le_max_left _ _
  have hdir : ∀ o, ‖dirOf o‖ ≤ C0 * size F o := by
    intro o
    cases o with
    | inl v =>
      show ‖((v, 0) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))‖ ≤
        C0 * ‖v‖
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg v)]
      exact le_mul_of_one_le_left (norm_nonneg v) hC01
    | inr l =>
      show ‖((0, T.symm l) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))‖ ≤
        C0 * ‖l‖
      rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
      exact (ContinuousLinearMap.le_opNorm (T.symm : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) →L[ℝ]
        (Fin n × Fin d → mixedEmbedding.mixedSpace F)) l).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg l))
  have hcOf : ∀ o, ‖cOf o‖ ≤ 1 := by
    intro o
    cases o with
    | inl v => show ‖(1 : ℂ)‖ ≤ 1; rw [norm_one]
    | inr l =>
      show ‖c⁻¹‖ ≤ 1
      rw [norm_inv, hcn]
      exact inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  refine ⟨max C4 0 * (max 1 (max C3 0 * C0)) ^ (2 * p), k3 * (2 * p), fun g h w hw hw1 => ?_⟩
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH1 : 1 ≤ H := one_le_mul_of_one_le_of_one_le (by exact_mod_cast one_le_heightGL F g.1)
    (by exact_mod_cast one_le_heightGL F h.1)
  have hH0 : 0 ≤ H := zero_le_one.trans hH1
  have hΨs : om (g, h) Φ ∈ schA F (Fin n × Fin d) := S.pres _ _ hΦ
  have c1 : ∀ w : List (Op F (Fin n × Fin d)), ∃ a : ℂ, ‖a‖ ≤ 1 ∧
      word F w (om (g, h) Φ) = a • wordH M B.ψ (w.map dirOf) (om (g, h) Φ) := by
    intro w
    induction w with
    | nil => exact ⟨1, by rw [norm_one], by rw [one_smul]; rfl⟩
    | cons o w ih =>
      obtain ⟨a, ha, e⟩ := ih
      refine ⟨a * cOf o, ?_, ?_⟩
      · rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) (hcOf o)
      · rw [word_cons, e, app_smul, hlet o _ (hHcl _ _ hΨs), smul_smul]
        rfl
  have c2 : ∀ zs, wordH M B.ψ zs (om (g, h) Φ) = om (g, h) (wordH M B.ψ (zs.map (movI M (g, h))) Φ) := by
    intro zs
    induction zs with
    | nil => rfl
    | cons ζ zs ih =>
      obtain ⟨hA, hL⟩ := GlobalTheory.T.archimedeanCoords_moved_stay_supported_and_recovered F E σ n d X W M (g, h) ζ
      show heisD M B.ψ (liftI M ζ) (wordH M B.ψ zs (om (g, h) Φ)) =
        om (g, h) (heisD M B.ψ (liftI M (movI M (g, h) ζ)) (wordH M B.ψ (zs.map (movI M (g, h))) Φ))
      rw [ih, GlobalTheory.T.heisenbergDeriv_archimedean_weilRep_intertwine F E σ B n d X W M χX χW om r s r' s' hP (g, h) _ hA _ (hHcl _ _ hΦ), hL]
  obtain ⟨a, ha, e⟩ := c1 w
  have ha' : ‖a‖ₑ ≤ 1 := by
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_one.2 ha
  set zs := (w.map dirOf).map (movI M (g, h)) with hzs
  have hG : wordH M B.ψ zs Φ ∈ schA F (Fin n × Fin d) := hHcl _ _ hΦ
  set ρ : ℝ := max 1 (max C3 0 * C0 * H ^ k3) with hρdef
  have hρ : ∀ ζ ∈ zs, ‖ζ‖ ≤ ρ := by
    intro ζ hζ
    obtain ⟨ζ', hζ', rfl⟩ := List.mem_map.1 hζ
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hζ'
    refine le_max_of_le_right ((hsz g h _).trans ?_)
    have hk : 0 ≤ H ^ k3 := pow_nonneg hH0 _
    calc C3 * H ^ k3 * ‖dirOf o‖ ≤ max C3 0 * H ^ k3 * (C0 * size F o) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hk) (hdir o) (norm_nonneg _)
            (mul_nonneg (le_max_right _ _) hk)
      _ ≤ max C3 0 * H ^ k3 * (C0 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hw1 o ho) (zero_le_one.trans hC01))
            (mul_nonneg (le_max_right _ _) hk)
      _ = max C3 0 * C0 * H ^ k3 := by ring
  have hlen : zs.length ≤ p := by rw [hzs, List.length_map, List.length_map]; exact hw
  have hb := hwb ρ (le_max_left _ _) zs hlen hρ
  rw [← hHR zs Φ hΦ] at hb
  have hk1 : 1 ≤ H ^ k3 := one_le_pow₀ hH1
  have hρle : ρ ≤ max 1 (max C3 0 * C0) * H ^ k3 :=
    max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hk1)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hk1))
  have hρ0 : 0 ≤ ρ := zero_le_one.trans (le_max_left _ _)
  calc ∫⁻ x, ‖word F w (om (g, h) Φ) x‖ₑ ^ 2 ∂μ
      = ∫⁻ x, ‖a‖ₑ ^ 2 * ‖om (g, h) (wordH M B.ψ zs Φ) x‖ₑ ^ 2 ∂μ := by
        congr 1
        funext x
        rw [e, c2, Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
    _ ≤ ∫⁻ x, ‖om (g, h) (wordH M B.ψ zs Φ) x‖ₑ ^ 2 ∂μ :=
        lintegral_mono fun x => mul_le_of_le_one_left bot_le (pow_le_one₀ bot_le ha')
    _ = ∫⁻ x, ‖wordH M B.ψ zs Φ x‖ₑ ^ 2 ∂μ := S.unit μ hμ _ _ hG
    _ ≤ ENNReal.ofReal (C4 * ρ ^ (2 * p)) := hb
    _ ≤ ENNReal.ofReal (max C4 0 * max 1 (max C3 0 * C0) ^ (2 * p) * H ^ (k3 * (2 * p))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc C4 * ρ ^ (2 * p) ≤ max C4 0 * ρ ^ (2 * p) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hρ0 _)
          _ ≤ max C4 0 * (max 1 (max C3 0 * C0) * H ^ k3) ^ (2 * p) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 hρle _) (le_max_right _ _)
          _ = _ := by rw [mul_pow, ← pow_mul]; ring
