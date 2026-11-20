import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblESymmToLinearMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationGoodModelsIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameConjMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapPartRightEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationBijectiveSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationPreservesAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorHaarNormProportionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEvaluationBijectiveSchwartzStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

namespace GlobalTheory.DblInt

/- English proof (translation)
Introduce `φ hφ`. Establish `hconj : ∀ g ∈ schA F κ, conjMap T (schr ψ (A₂, -B₂) g) = schr ψ (a₂, -b₂) (conjMap T g)`. Introduce `g hg`. Establish `hs : star g ∈ schA F κ` using `GlobalTheory.SchAConj.star_mem_schA F κ g hg`. Rewrite using `[conjMap_apply, conjMap_apply, GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (A₂, B₂) g, h2 _ hs]`.

Use `GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (a₂, -b₂) (T (star g))` as an intermediate fact. Simplify `this` using `only [neg_neg]`. Use function extensionality and compare the values at `s`. Establish `hΨ` using `h3 φ hφ`. Establish `hslice` using `GlobalTheory.DoublingEvLaw.sliceL hΨ (s ∘ Sum.inr + a₂)`.

Establish `hinner : (fun x₁ => conjMap T (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂)) (s ∘ Sum.inr)) = ψ (-((s ∘ Sum.inr) ⬝ᵥ b₂) - ⅟(2 : AF F) * (a₂ ⬝ᵥ b₂)) • schr ψ (A₁, B₁) (fun x₁ => partR (conjMap T) φ (Sum.elim x₁ (s ∘ Sum.inr + a₂)))`. Use function extensionality and compare the values at `x₁`. Establish `e1 : (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂)) = ψ (x₁ ⬝ᵥ B₁ + ⅟(2 : AF F) * (A₁ ⬝ᵥ B₁)) • schr ψ (A₂, -B₂) (fun x₂ => φ (Sum.elim (x₁ + A₁) x₂))`. Use function extensionality and compare the values at `x₂`. Simplify using `only [schr, Pi.smul_apply, smul_eq_mul, GlobalTheory.DoublingEvLaw.elim_dot, Sum.elim_add_add]`.

Rewrite using `[← mul_assoc, ← AddChar.map_add_eq_mul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, map_smul, hconj _ (GlobalTheory.DoublingEvLaw.sliceR hφ _)]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, schr, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]`.

Rewrite using `[dotProduct_neg, dotProduct_neg]`. Rewrite using `[show ∀ p q r : ℂ, p * (q * r) = q * (p * r) from fun p q r => by ring]`. Use `congr 2`. Put the polynomial expressions in normal form. Rewrite using `[evDbl_apply, hinner, map_smul, h1 _ hslice]`.

Simplify using `only [schr, Pi.smul_apply, smul_eq_mul, evDbl_apply, GlobalTheory.DoublingEvLaw.elim_dot, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_neg]`. Rewrite using `[← mul_assoc, ← AddChar.map_add_eq_mul]`. Use `congr 2`. Establish `hs : s ⬝ᵥ Sum.elim b₁ (-b₂) = (s ∘ Sum.inl) ⬝ᵥ b₁ - (s ∘ Sum.inr) ⬝ᵥ b₂`. Rewrite using `[← Sum.elim_comp_inl_inr s, GlobalTheory.DoublingEvLaw.elim_dot, dotProduct_neg, Sum.elim_comp_inl, Sum.elim_comp_inr, sub_eq_add_neg]`.

Rewrite using `[hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evDbl_schr {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ))
    (A₁ B₁ A₂ B₂ : κ → AF F) (a₁ b₁ a₂ b₂ : κ₁ → AF F)
    (h1 : ∀ Φ ∈ schA F κ, T (schr ψ (A₁, B₁) Φ) = schr ψ (a₁, b₁) (T Φ))
    (h2 : ∀ Φ ∈ schA F κ, T (schr ψ (A₂, B₂) Φ) = schr ψ (a₂, b₂) (T Φ))
    (h3 : ∀ φ ∈ schA F (κ ⊕ κ), partR (conjMap T) φ ∈ schA F (κ ⊕ κ₁)) :
    ∀ φ ∈ schA F (κ ⊕ κ), evDbl T (schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ) =
      schr ψ (Sum.elim a₁ a₂, Sum.elim b₁ (-b₂)) (evDbl T φ) := by
  intro φ hφ
  have hconj : ∀ g ∈ schA F κ, conjMap T (schr ψ (A₂, -B₂) g) = schr ψ (a₂, -b₂) (conjMap T g) := by
    intro g hg
    have hs : star g ∈ schA F κ := GlobalTheory.SchAConj.star_mem_schA F κ g hg
    rw [conjMap_apply, conjMap_apply, GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (A₂, B₂) g, h2 _ hs]
    have := GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (a₂, -b₂) (T (star g))
    simpa only [neg_neg] using this
  funext s
  have hΨ := h3 φ hφ
  have hslice := GlobalTheory.DoublingEvLaw.sliceL hΨ (s ∘ Sum.inr + a₂)
  have hinner : (fun x₁ => conjMap T (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂))
      (s ∘ Sum.inr)) = ψ (-((s ∘ Sum.inr) ⬝ᵥ b₂) - ⅟(2 : AF F) * (a₂ ⬝ᵥ b₂)) •
        schr ψ (A₁, B₁) (fun x₁ => partR (conjMap T) φ (Sum.elim x₁ (s ∘ Sum.inr + a₂))) := by
    funext x₁
    have e1 : (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂)) =
        ψ (x₁ ⬝ᵥ B₁ + ⅟(2 : AF F) * (A₁ ⬝ᵥ B₁)) • schr ψ (A₂, -B₂) (fun x₂ => φ (Sum.elim (x₁ + A₁) x₂)) := by
      funext x₂
      simp only [schr, Pi.smul_apply, smul_eq_mul, GlobalTheory.DoublingEvLaw.elim_dot, Sum.elim_add_add]
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [e1, map_smul, hconj _ (GlobalTheory.DoublingEvLaw.sliceR hφ _)]
    simp only [Pi.smul_apply, smul_eq_mul, schr, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [dotProduct_neg, dotProduct_neg]
    rw [show ∀ p q r : ℂ, p * (q * r) = q * (p * r) from fun p q r => by ring]
    congr 2
    ring_nf
  rw [evDbl_apply, hinner, map_smul, h1 _ hslice]
  simp only [schr, Pi.smul_apply, smul_eq_mul, evDbl_apply, GlobalTheory.DoublingEvLaw.elim_dot, partR_apply, Sum.elim_comp_inl,
    Sum.elim_comp_inr, dotProduct_neg]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hs : s ⬝ᵥ Sum.elim b₁ (-b₂) = (s ∘ Sum.inl) ⬝ᵥ b₁ - (s ∘ Sum.inr) ⬝ᵥ b₂ := by
    rw [← Sum.elim_comp_inl_inr s, GlobalTheory.DoublingEvLaw.elim_dot, dotProduct_neg, Sum.elim_comp_inl, Sum.elim_comp_inr,
      sub_eq_add_neg]
  rw [hs]
  ring

/- English proof (translation)
Establish `key : ∀ {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}, (∀ Φ ∈ schA F κ, l Φ = l' Φ) → l ∈ (adeleClass F).adm κ → l' ∈ (adeleClass F).adm κ`. Introduce `l l' h hl g hg`. Take `⟨T, hT⟩` from `hl g hg`. Conclude with `⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩`. Conclude with `⟨key h, key fun Φ hΦ => (h Φ hΦ).symm⟩`.
-/
theorem adm_congr {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ Φ ∈ schA F κ, l Φ = l' Φ) : l ∈ (adeleClass F).adm κ ↔ l' ∈ (adeleClass F).adm κ := by
  have key : ∀ {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}, (∀ Φ ∈ schA F κ, l Φ = l' Φ) →
      l ∈ (adeleClass F).adm κ → l' ∈ (adeleClass F).adm κ := by
    intro l l' h hl g hg
    obtain ⟨T, hT⟩ := hl g hg
    exact ⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩
  exact ⟨key h, key fun Φ hΦ => (h Φ hΦ).symm⟩

/- English proof (translation)
Introduce `dd hdd`. Take `⟨hsp, hheis, hadm, hunit⟩` from `hT`. Establish `hS : IsTame F (conjMap T.toLinearMap)` using `GlobalTheory.DoublingEv.isTame_conjMap F κ κ _ ht`. Establish `hSi : IsTame F (conjMap T.symm.toLinearMap)` using `GlobalTheory.DoublingEv.isTame_conjMap F κ κ _ hti`. Establish `hR : IsTame F (partR (κ` using `κ) (conjMap T.toLinearMap)) := GlobalTheory.T.tame_part_right F κ κ κ _ hS`.

Establish `hL : IsTame F (partL (κ'` using `κ) T.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ ht`. Establish `hRi : IsTame F (partR (κ` using `κ) (conjMap T.symm.toLinearMap)) := GlobalTheory.T.tame_part_right F κ κ κ _ hSi`. Establish `hLi : IsTame F (partL (κ'` using `κ) T.symm.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ hti`. Establish `hD : IsTame F (dblE T).toLinearMap` using `hR.comp hL`. Establish `hDi : IsTame F (dblE T).symm.toLinearMap` using `hLi.comp hRi`.

Establish `hstar : ∀ φ : (κ → AF F) → ℂ, φ ∈ schA F κ → star φ ∈ schA F κ` using `fun φ hφ => GlobalTheory.SchAConj.star_mem_schA F κ φ hφ`. Establish `hSsp : ∀ φ, φ ∈ schA F κ ↔ conjE T φ ∈ schA F κ` using `fun φ => by`. Rewrite using `[conjE_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `hstar _ ((hsp _).1 (hstar _ h))`. Introduce `h`. Establish `h1 : T (star φ) ∈ schA F κ` using `by simpa using hstar _ h`. Simplify using `using hstar _ ((hsp _).2 h1)`. Establish `hTL : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖T.toLinearMap φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ` using `hunit`.

Establish `hSL : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖conjMap T.toLinearMap φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ`. Introduce `μ hμ`. Take `⟨c₀, hc₀⟩` from `hunit μ hμ`. Use `⟨c₀, fun φ hφ => ?_⟩` and prove the remaining obligations. Establish `h` using `hc₀ (star φ) (hstar φ hφ)`.

Simplify using `only [conjMap_apply, Pi.star_apply, enorm_eq_nnnorm, nnnorm_star, LinearEquiv.coe_coe] at h ⊢`. Conclude with `h`. Use `⟨dblCo c d₁, dblE T, conjE T, dblCo_isDblCoord c d₁, ⟨fun φ => ⟨fun h => hD.mapsTo φ h, fun h => ?_⟩, fun w φ hφ => ?_, fun l => ⟨fun hl => hD.comp_adm hl, fun hl => ?_⟩, fun μ hμ => ?_⟩, hSsp, fun φ₁ _ φ₂ _ => evDbl_boxFun T.toLinearMap φ₁ φ₂⟩` and prove the remaining obligations. Use `hDi.mapsTo _ h` as an intermediate fact. Rewrite `this` using `[show (dblE T).symm.toLinearMap ((dblE T) φ) = φ from (dblE T).symm_apply_apply φ]`.

Conclude with `this`. Take `⟨w₁, w₂, rfl⟩ : ∃ w₁ w₂, w = Matrix.fromCols w₁ w₂` from `⟨w.toCols₁, w.toCols₂, (Matrix.fromCols_toCols w).symm⟩`. Establish `e1 : dd.rho ψ (Matrix.fromCols w₁ w₂) = schr ψ (Sum.elim (d.e w₁).1 (d.e w₂).1, Sum.elim (d.e w₁).2 (-(d.e w₂).2))`. Unfold `Darboux.rho`. Rewrite using `[hdd]`.

Establish `e2 : (dblCo c d₁).rho ψ (Matrix.fromCols w₁ w₂) = schr ψ (Sum.elim (d₁.e w₁).1 (d₁.e w₂).1, Sum.elim (d₁.e w₁).2 (-(d₁.e w₂).2))`. Unfold `Darboux.rho`. Rewrite using `[dblCo_isDblCoord]`. Rewrite using `[e1, e2]`. Conclude with `evDbl_schr ψ hψ T.toLinearMap _ _ _ _ _ _ _ _ (fun Φ hΦ => hheis w₁ Φ hΦ) (fun Φ hΦ => hheis w₂ Φ hΦ) hR.mapsTo φ hφ`.

Use `hDi.comp_adm hl` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `φ`. Simplify using the standard rewrite rules. Take `⟨c₁, hc₁⟩` from `(GlobalTheory.T.weil_operator_haar_norm_proportional F κ κ T.toLinearMap ht hTL).1 μ hμ`.

Take `⟨c₂, hc₂⟩` from `(GlobalTheory.T.weil_operator_haar_norm_proportional F κ κ (conjMap T.toLinearMap) hS hSL).2 μ hμ`. Use `⟨c₁ * c₂, fun Φ hΦ => ?_⟩` and prove the remaining obligations. Use `show ∫⁻ x, ‖partL (κ' := κ) T.toLinearMap (partR (κ := κ) (conjMap T.toLinearMap) Φ) x‖ₑ ^ 2 ∂μ = _`. Rewrite using `[hc₁ _ (hR.mapsTo Φ hΦ), hc₂ Φ hΦ, mul_assoc]`.
-/
theorem hasDbl_of_tame {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra (AF F) E]
    (c : E →ₐ[AF F] E) {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (d d₁ : Darboux (symp c ξ JA JB) κ) (T : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ))
    (hT : IsGoodInt (adeleClass F) ψ d d₁ T) (ht : IsTame F T.toLinearMap) (hti : IsTame F T.symm.toLinearMap) :
    HasDbl c (adeleClass F) ψ ξ JA JB d d₁ T := by
  intro dd hdd
  obtain ⟨hsp, hheis, hadm, hunit⟩ := hT
  have hS : IsTame F (conjMap T.toLinearMap) := GlobalTheory.DoublingEv.isTame_conjMap F κ κ _ ht
  have hSi : IsTame F (conjMap T.symm.toLinearMap) := GlobalTheory.DoublingEv.isTame_conjMap F κ κ _ hti
  have hR : IsTame F (partR (κ := κ) (conjMap T.toLinearMap)) := GlobalTheory.T.tame_part_right F κ κ κ _ hS
  have hL : IsTame F (partL (κ' := κ) T.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ ht
  have hRi : IsTame F (partR (κ := κ) (conjMap T.symm.toLinearMap)) := GlobalTheory.T.tame_part_right F κ κ κ _ hSi
  have hLi : IsTame F (partL (κ' := κ) T.symm.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ hti
  have hD : IsTame F (dblE T).toLinearMap := hR.comp hL
  have hDi : IsTame F (dblE T).symm.toLinearMap := hLi.comp hRi
  have hstar : ∀ φ : (κ → AF F) → ℂ, φ ∈ schA F κ → star φ ∈ schA F κ := fun φ hφ =>
    GlobalTheory.SchAConj.star_mem_schA F κ φ hφ
  have hSsp : ∀ φ, φ ∈ schA F κ ↔ conjE T φ ∈ schA F κ := fun φ => by
    rw [conjE_apply]
    constructor
    · intro h
      exact hstar _ ((hsp _).1 (hstar _ h))
    · intro h
      have h1 : T (star φ) ∈ schA F κ := by simpa using hstar _ h
      simpa using hstar _ ((hsp _).2 h1)
  have hTL : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖T.toLinearMap φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := hunit
  have hSL : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖conjMap T.toLinearMap φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
    intro μ hμ
    obtain ⟨c₀, hc₀⟩ := hunit μ hμ
    refine ⟨c₀, fun φ hφ => ?_⟩
    have h := hc₀ (star φ) (hstar φ hφ)
    simp only [conjMap_apply, Pi.star_apply, enorm_eq_nnnorm, nnnorm_star, LinearEquiv.coe_coe] at h ⊢
    exact h
  refine ⟨dblCo c d₁, dblE T, conjE T, dblCo_isDblCoord c d₁,
    ⟨fun φ => ⟨fun h => hD.mapsTo φ h, fun h => ?_⟩, fun w φ hφ => ?_, fun l => ⟨fun hl => hD.comp_adm hl, fun hl => ?_⟩,
      fun μ hμ => ?_⟩, hSsp, fun φ₁ _ φ₂ _ => evDbl_boxFun T.toLinearMap φ₁ φ₂⟩
  · have := hDi.mapsTo _ h
    rw [show (dblE T).symm.toLinearMap ((dblE T) φ) = φ from (dblE T).symm_apply_apply φ] at this
    exact this
  · obtain ⟨w₁, w₂, rfl⟩ : ∃ w₁ w₂, w = Matrix.fromCols w₁ w₂ := ⟨w.toCols₁, w.toCols₂, (Matrix.fromCols_toCols w).symm⟩
    have e1 : dd.rho ψ (Matrix.fromCols w₁ w₂) =
        schr ψ (Sum.elim (d.e w₁).1 (d.e w₂).1, Sum.elim (d.e w₁).2 (-(d.e w₂).2)) := by
      unfold Darboux.rho; rw [hdd]
    have e2 : (dblCo c d₁).rho ψ (Matrix.fromCols w₁ w₂) =
        schr ψ (Sum.elim (d₁.e w₁).1 (d₁.e w₂).1, Sum.elim (d₁.e w₁).2 (-(d₁.e w₂).2)) := by
      unfold Darboux.rho; rw [dblCo_isDblCoord]
    rw [e1, e2]
    exact evDbl_schr ψ hψ T.toLinearMap _ _ _ _ _ _ _ _ (fun Φ hΦ => hheis w₁ Φ hΦ) (fun Φ hΦ => hheis w₂ Φ hΦ)
      hR.mapsTo φ hφ
  · have := hDi.comp_adm hl
    convert this using 1
    ext φ
    simp
  · obtain ⟨c₁, hc₁⟩ := (GlobalTheory.T.weil_operator_haar_norm_proportional F κ κ T.toLinearMap ht hTL).1 μ hμ
    obtain ⟨c₂, hc₂⟩ := (GlobalTheory.T.weil_operator_haar_norm_proportional F κ κ (conjMap T.toLinearMap) hS hSL).2 μ hμ
    refine ⟨c₁ * c₂, fun Φ hΦ => ?_⟩
    show ∫⁻ x, ‖partL (κ' := κ) T.toLinearMap (partR (κ := κ) (conjMap T.toLinearMap) Φ) x‖ₑ ^ 2 ∂μ = _
    rw [hc₁ _ (hR.mapsTo Φ hΦ), hc₂ Φ hΦ, mul_assoc]

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe`. Establish `h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hTs : ∀ x, x ∈ schA F (Fin n × Fin d) ↔ T x ∈ schA F (Fin n × Fin d)` using `fun x => by`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Rewrite using `[hTe x hx]`. Conclude with `hbij.mapsTo hx`. Introduce `hx`. Take `⟨y, hy, hyx⟩` from `hbij.surjOn hx`.

Establish `: T y = T x` using `by rw [hTe y hy, hyx]`. Rewrite using `[← T.injective this]`. Conclude with `hy`. Establish `hgood : IsGoodInt (adeleClass F) B.ψ M.co M₁.co T`. Use `⟨hTs, fun w Φ hΦ => ?_, fun l => ?_, fun μ hμ => ?_⟩` and prove the remaining obligations.

Establish `hm : M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d)` using `GlobalTheory.T.schroedinger_preserves_adelic_schwartz F B.ψ hpair.base.std _ (M.co.e w) Φ hΦ`. Use `hev.Heisenberg₂ w Φ hΦ` as an intermediate fact. Rewrite `this` using `[h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]`. Rewrite using `[hTe _ hm, hTe _ hΦ, this]`. Use `(GlobalTheory.T.model_evaluation_bijective_schwartz hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij l).trans (adm_congr ?_)` and prove the remaining obligations.

Introduce `Φ hΦ`. Simplify using `[hTe Φ hΦ]`. Take `⟨c, hc⟩` from `GlobalTheory.T.model_evaluation_preserves_admissible hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ`. Conclude with `⟨c, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hc Φ hΦ⟩`. Establish `ht : IsTame F T.toLinearMap`.

Introduce `g hg`. Take `⟨ι, inst, P, g', hg', hPe⟩` from `GlobalTheory.EvTame.isTame_of_isEv F E σ B n d n d X W X W M M₁ 1 1 ∅ e hpair.good hM₁ hev g hg`. Use `⟨ι, inst, P, g', hg', fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[← hPe f]`. Conclude with `hTe _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)`.

Establish `hti : IsTame F T.symm.toLinearMap` using `GlobalTheory.T.good_model_evaluation_bijective_schwartz hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T.symm.toLinearMap (fun Φ hΦ => by rw [← hTe Φ hΦ]; simp)`. Conclude with `hasDbl_of_tame (cA σ) B.ψ (GlobalTheory.StdCharFromIsStd.norm_psi hpair.base.std) (-1) _ _ M.co M₁.co T hgood ht hti`.
-/
theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) →
      HasDbl (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co M₁.co T := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hTs : ∀ x, x ∈ schA F (Fin n × Fin d) ↔ T x ∈ schA F (Fin n × Fin d) := fun x => by
    constructor
    · intro hx
      rw [hTe x hx]
      exact hbij.mapsTo hx
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hbij.surjOn hx
      have : T y = T x := by rw [hTe y hy, hyx]
      rw [← T.injective this]
      exact hy
  have hgood : IsGoodInt (adeleClass F) B.ψ M.co M₁.co T := by
    refine ⟨hTs, fun w Φ hΦ => ?_, fun l => ?_, fun μ hμ => ?_⟩
    · have hm : M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
        GlobalTheory.T.schroedinger_preserves_adelic_schwartz F B.ψ hpair.base.std _ (M.co.e w) Φ hΦ
      have := hev.Heisenberg₂ w Φ hΦ
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
      rw [hTe _ hm, hTe _ hΦ, this]
    · refine (GlobalTheory.T.model_evaluation_bijective_schwartz hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij l).trans
        (adm_congr ?_)
      intro Φ hΦ
      simp [hTe Φ hΦ]
    · obtain ⟨c, hc⟩ := GlobalTheory.T.model_evaluation_preserves_admissible hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ
      exact ⟨c, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hc Φ hΦ⟩
  have ht : IsTame F T.toLinearMap := by
    intro g hg
    obtain ⟨ι, inst, P, g', hg', hPe⟩ := GlobalTheory.EvTame.isTame_of_isEv F E σ B n d n d X W X W M M₁ 1 1 ∅ e hpair.good hM₁ hev g hg
    refine ⟨ι, inst, P, g', hg', fun f => ?_⟩
    rw [← hPe f]
    exact hTe _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)
  have hti : IsTame F T.symm.toLinearMap :=
    GlobalTheory.T.good_model_evaluation_bijective_schwartz hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T.symm.toLinearMap
      (fun Φ hΦ => by rw [← hTe Φ hΦ]; simp)
  exact hasDbl_of_tame (cA σ) B.ψ (GlobalTheory.StdCharFromIsStd.norm_psi hpair.base.std) (-1) _ _ M.co M₁.co T hgood ht hti

end GlobalTheory.DblInt
