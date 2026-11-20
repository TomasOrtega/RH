import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ParityOfCoefficients

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem Φ hΦ`. Take `⟨f, g, hg, rfl⟩` from `hΦ`. Use `Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) f, fun y => g (-y), ⟨hg.1.comp_continuous continuous_neg, hg.2.comp_homeomorph (Homeomorph.neg _)⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Simplify using `only [pureA, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, ContinuousLinearEquiv.neg_apply]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Conclude with `map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1`. Consider the case `zero => exact Submodule.zero_mem _`.

Consider the case `add a b _ _ ha hb => exact Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => exact Submodule.smul_mem _ c ha`.
-/
theorem neg_mem_schA {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) : (fun x => Φ (-x)) ∈ schA F κ := by
  classical
  induction h using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) f,
      fun y => g (-y), ⟨hg.1.comp_continuous continuous_neg, hg.2.comp_homeomorph (Homeomorph.neg _)⟩, ?_⟩
    funext x
    simp only [pureA, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.neg_apply]
    congr 2
    funext i
    exact map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

/- English proof (translation)
Use `haveI : BorelSpace (κ → AF F) := ⟨rfl⟩`. Take `⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (κ → AF F))` from `inferInstance`. Conclude with `⟨Measure.addHaarMeasure K, inferInstance, fun f => integral_neg_eq_self f _⟩`.
-/
theorem exists_haar : ∃ μ : Measure (κ → AF F), μ.IsAddHaarMeasure ∧
    ∀ f : (κ → AF F) → ℂ, ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ := by
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (κ → AF F)) := inferInstance
  exact ⟨Measure.addHaarMeasure K, inferInstance, fun f => integral_neg_eq_self f _⟩

/- English proof (translation)
Unfold `coef`. Rewrite using `[← hμ]`. Use `integral_congr_ae (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only [schr, Prod.fst_neg, Prod.snd_neg, neg_dotProduct_neg, neg_add]`.
-/
theorem coef_neg (ψ : AddChar (AF F) ℂ) (μ : Measure (κ → AF F))
    (hμ : ∀ f : (κ → AF F) → ℂ, ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ) (Φ₁ Φ₂ : (κ → AF F) → ℂ)
    (w : (κ → AF F) × (κ → AF F)) :
    coef F ψ μ Φ₁ Φ₂ (-w) = coef F ψ μ (fun x => Φ₁ (-x)) (fun x => Φ₂ (-x)) w := by
  unfold coef
  rw [← hμ]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [schr, Prod.fst_neg, Prod.snd_neg, neg_dotProduct_neg, neg_add]

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

def negOne (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J :=
  ⟨-1, by
    change ((-1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F J *
      ((-1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F J
    rw [Units.val_neg, Units.val_one, Matrix.map_neg _ (map_neg (cA σ)),
      Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]
    simp⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_negOne_inv (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mat (negOne σ J)⁻¹ = -1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_one_inv (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mat (1 : UA σ J)⁻¹ = 1 := rfl

end ParityOfCoefficients

open ParityOfCoefficients in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp`. Take `⟨μ, hμ, hneg⟩` from `exists_haar (F := F) (κ := Fin n × Fin d)`. Establish `pres : ∀ Φ ∈ schA F (Fin n × Fin d), om (negOne σ X.J, 1) Φ ∈ schA F (Fin n × Fin d)` using `fun Φ hΦ => (IsUWeilPair.isUSplitting hp.weil).pres _ Φ hΦ`. Establish `key : ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ x u, om (negOne σ X.J, 1) Φ₁ x * (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₂ u) = Φ₁ (-x) * (starRingEnd ℂ) (Φ₂ (-u))`. Introduce `Φ₁ h₁ Φ₂ h₂`.

Use `hF F _ B.ψ hp.base.std μ hμ _ (pres _ h₁) _ (pres _ h₂) _ (neg_mem_schA h₁) _ (neg_mem_schA h₂) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Take `⟨z, rfl⟩` from `M.co.e.surjective w`. Rewrite using `[hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ Φ₁ h₁ Φ₂ h₂, ← coef_neg B.ψ μ hneg, mat_negOne_inv, mat_one_inv, Matrix.transpose_one, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul, map_neg]`. Distinguish the cases in `h0 : ∃ Φ₀ ∈ schA F (Fin n × Fin d), ∃ u, Φ₀ (-u) ≠ 0`.

Take `⟨Φ₀, hΦ₀, u, hu⟩` from `h0`. Establish `h1` using `congrArg norm (key Φ₀ hΦ₀ Φ₀ hΦ₀ u u)`. Simplify using `only [norm_mul, Complex.norm_conj] at h1`. Establish `h2 : ‖om (negOne σ X.J, 1) Φ₀ u‖ = ‖Φ₀ (-u)‖` using `(mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp h1`. Establish `h3 : ‖Φ₀ (-u)‖ ≠ 0` using `norm_ne_zero_iff.mpr hu`.

Establish `h4 : (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₀ u) ≠ 0`. Rewrite using `[← norm_ne_zero_iff, Complex.norm_conj, h2]`. Conclude with `h3`. Use `⟨negOne σ X.J, (starRingEnd ℂ) (Φ₀ (-u)) / (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₀ u), rfl, ?_, fun Φ hΦ => funext fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_div, Complex.norm_conj, Complex.norm_conj, h2, div_self h3]`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key Φ hΦ Φ₀ hΦ₀, mul_comm]`. Use `⟨negOne σ X.J, 1, rfl, norm_one, fun Φ hΦ => ?_⟩` and prove the remaining obligations. Establish `z : ∀ Ψ ∈ schA F (Fin n × Fin d), Ψ = 0` using `fun Ψ hΨ => funext fun x => by`. Assume the negation of the conclusion as `hx`. Conclude with `h0 ⟨Ψ, hΨ, -x, by rwa [neg_neg]⟩`.

Rewrite using `[z _ (pres Φ hΦ), one_smul, z _ (neg_mem_schA hΦ)]`.
-/
theorem parity_of (hC : CoefEq) (hF : FourierInj) : Parity := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨μ, hμ, hneg⟩ := exists_haar (F := F) (κ := Fin n × Fin d)
  have pres : ∀ Φ ∈ schA F (Fin n × Fin d), om (negOne σ X.J, 1) Φ ∈ schA F (Fin n × Fin d) :=
    fun Φ hΦ => (IsUWeilPair.isUSplitting hp.weil).pres _ Φ hΦ
  have key : ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ x u,
      om (negOne σ X.J, 1) Φ₁ x * (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₂ u) =
        Φ₁ (-x) * (starRingEnd ℂ) (Φ₂ (-u)) := by
    intro Φ₁ h₁ Φ₂ h₂
    refine hF F _ B.ψ hp.base.std μ hμ _ (pres _ h₁) _ (pres _ h₂) _ (neg_mem_schA h₁) _ (neg_mem_schA h₂) ?_
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ Φ₁ h₁ Φ₂ h₂, ← coef_neg B.ψ μ hneg, mat_negOne_inv,
      mat_one_inv, Matrix.transpose_one, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul, map_neg]
  by_cases h0 : ∃ Φ₀ ∈ schA F (Fin n × Fin d), ∃ u, Φ₀ (-u) ≠ 0
  · obtain ⟨Φ₀, hΦ₀, u, hu⟩ := h0
    have h1 := congrArg norm (key Φ₀ hΦ₀ Φ₀ hΦ₀ u u)
    simp only [norm_mul, Complex.norm_conj] at h1
    have h2 : ‖om (negOne σ X.J, 1) Φ₀ u‖ = ‖Φ₀ (-u)‖ :=
      (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp h1
    have h3 : ‖Φ₀ (-u)‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have h4 : (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₀ u) ≠ 0 := by
      rw [← norm_ne_zero_iff, Complex.norm_conj, h2]; exact h3
    refine ⟨negOne σ X.J, (starRingEnd ℂ) (Φ₀ (-u)) / (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₀ u), rfl, ?_,
      fun Φ hΦ => funext fun x => ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_conj, h2, div_self h3]
    · rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key Φ hΦ Φ₀ hΦ₀, mul_comm]
  · refine ⟨negOne σ X.J, 1, rfl, norm_one, fun Φ hΦ => ?_⟩
    have z : ∀ Ψ ∈ schA F (Fin n × Fin d), Ψ = 0 := fun Ψ hΨ => funext fun x => by
      by_contra hx
      exact h0 ⟨Ψ, hΨ, -x, by rwa [neg_neg]⟩
    rw [z _ (pres Φ hΦ), one_smul, z _ (neg_mem_schA hΦ)]

end PositivityTheory.ThKEst

end
