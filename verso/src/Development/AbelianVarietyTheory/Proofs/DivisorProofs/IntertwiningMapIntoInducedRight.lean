import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocallyConstantSplitOm

noncomputable section

open MeasureTheory ValuativeRel Matrix Filter Topology
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

namespace GlobalTheory.KSplit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
The claim follows from `Units.continuous_iff.mpr ⟨Units.continuous_val.matrix_det, (Units.continuous_val.comp continuous_inv).matrix_det⟩`.
-/
theorem continuous_gdet {n : Type} [Fintype n] [DecidableEq n] : Continuous (fun g : GL n k => gdet g) :=
  Units.continuous_iff.mpr ⟨Units.continuous_val.matrix_det, (Units.continuous_val.comp continuous_inv).matrix_det⟩

/- English proof (translation)
Simplify using `[omB]`.
-/
theorem omB_one_apply {A' D : Type} [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (ν α : kˣ →* ℂˣ) (x : GL D k) (Ψ : Matrix A' D k → ℂ) (Y : Matrix A' D k) :
    omB ν α 1 x Ψ Y = (α (gdet x) : ℂ) * apow (gdet x) ((Fintype.card A' : ℂ) / 2) * Ψ (Y * x.val) := by
  simp [omB]

/- English proof (translation)
Establish `h1 : ∀ᶠ u in 𝓝 (1 : GL D k), α (gdet u) = 1`. Establish `: (α.ker : Set kˣ) ∈ 𝓝 (gdet (1 : GL D k))`. Rewrite using `[show gdet (1 : GL D k) = 1 from map_one _]`. Conclude with `hα.1.mem_nhds (one_mem _)`. Use `filter_upwards [continuous_gdet.continuousAt this] with u hu using hu`.

Establish `h2 : ∀ᶠ u in 𝓝 (1 : GL D k), u ∈ KO k D` using `isOpen_KO.mem_nhds (one_mem _)`. Establish `hc : ∀ M : GL D k → Matrix D D k, Continuous M → Continuous fun q : GL D k × Matrix A' D k => q.2 * M q.1` using `fun M hM => continuous_snd.matrix_mul (hM.comp continuous_fst)`. Establish `h3` using `GlobalTheory.WeilM.eventually_comp_eq (p₀ := (1 : GL D k)) (fun u Y => Y * u.val) (fun u Y => Y * (u⁻¹).val) (hc _ Units.continuous_val) (hc _ Units.continuous_coe_inv) (by simp) (by simp) (fun p v => by simp [Matrix.mul_assoc]) (φ := Ψ) hΨ`. Use `filter_upwards [h1, h2, h3] with u hu1 hu2 hu3`. Use function extensionality and compare the values at `Y`.

Rewrite using `[omB_one_apply, hu1, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hu2), hu3 Y]`. Simplify using the standard rewrite rules.
-/
theorem eventually_omB_one_eq {A' D : Type} [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    {ν α : kˣ →* ℂˣ} (hα : IsSmU α) {Ψ : Matrix A' D k → ℂ} (hΨ : Ψ ∈ SB (Matrix A' D k)) :
    ∀ᶠ u in 𝓝 (1 : GL D k), omB ν α 1 u Ψ = Ψ := by
  have h1 : ∀ᶠ u in 𝓝 (1 : GL D k), α (gdet u) = 1 := by
    have : (α.ker : Set kˣ) ∈ 𝓝 (gdet (1 : GL D k)) := by
      rw [show gdet (1 : GL D k) = 1 from map_one _]; exact hα.1.mem_nhds (one_mem _)
    filter_upwards [continuous_gdet.continuousAt this] with u hu using hu
  have h2 : ∀ᶠ u in 𝓝 (1 : GL D k), u ∈ KO k D := isOpen_KO.mem_nhds (one_mem _)
  have hc : ∀ M : GL D k → Matrix D D k, Continuous M →
      Continuous fun q : GL D k × Matrix A' D k => q.2 * M q.1 := fun M hM =>
    continuous_snd.matrix_mul (hM.comp continuous_fst)
  have h3 := GlobalTheory.WeilM.eventually_comp_eq (p₀ := (1 : GL D k)) (fun u Y => Y * u.val) (fun u Y => Y * (u⁻¹).val)
    (hc _ Units.continuous_val) (hc _ Units.continuous_coe_inv) (by simp) (by simp)
    (fun p v => by simp [Matrix.mul_assoc]) (φ := Ψ) hΨ
  filter_upwards [h1, h2, h3] with u hu1 hu2 hu3
  funext Y
  rw [omB_one_apply, hu1, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hu2), hu3 Y]
  simp

/- English proof (translation)
Introduce `k _ _ _ _ a a' α β l hα hl Ψ hΨ`. Use `⟨fun b A D N hb h => ?_, ?_⟩` and prove the remaining obligations. Establish `hY : Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * b.val = D.val * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))`. Use extensionality with `i j`. Rewrite using `[frameMatrixSecondColumnBlock_mul_apply]`.

Take `⟨j', rfl⟩` from `(finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')).surjective j`. Use `congrFun (congrFun hb (Sum.inr i)) j'` as an intermediate fact. Simplify using `only [submatrix_apply] at this`. Break down `j' with j' | j'` into its components or cases. Simplify using `only [fromBlocks_apply₂₁, Matrix.zero_apply] at this`.

Rewrite using `[this, Matrix.mul_apply]`. Use `(Finset.sum_eq_zero fun m _ => ?_).symm` and prove the remaining obligations. Use `j'.isLt` as an intermediate fact. Rewrite using `[Y0, of_apply, if_neg (by simp [Fin.ext_iff]; omega), mul_zero]`. Simplify using `only [fromBlocks_apply₂₂] at this`.

Rewrite using `[this]`. Simplify using `[Matrix.mul_apply, Y0]`. Establish `hdet : gdet b = gdet A * gdet D`. Use `ext`. Establish `e` using `congrArg Matrix.det hb`.

Rewrite `e` using `[det_submatrix_equiv_self, det_fromBlocks_zero₂₁]`. Simplify `e` using `[Matrix.GeneralLinearGroup.val_det_apply]`. Establish `hφ : (fun g : Matrix (Fin a') (Fin a') k => omB (α / β) α 1 h Ψ (g * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) ∈ SB _` using `restrict_Y0 (omB_mem_SB _ _ 1 h hΨ)`. Establish `hψ : (fun X : Matrix (Fin a') (Fin a') k => omB (α / β) α 1 h Ψ (X * D.val * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) ∈ SB _`. Simplify using `using comp_mul_mem_SB (1 : GL (Fin a') k) D hφ`.

Establish `heq` using `hl.2.2 1 D _ hφ`. Simplify using `only [Units.val_one, Matrix.one_mul, map_one, one_mul] at heq`. Establish `hfun : (fun g : Matrix (Fin a') (Fin a') k => omB (α / β) α 1 (b * h) Ψ (g * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) = ((α (gdet b) : ℂ) * apow (gdet b) ((a' : ℂ) / 2)) • (fun X : Matrix (Fin a') (Fin a') k => omB (α / β) α 1 h Ψ (X * D.val * Y0 k (finSumFinEquiv …`. Use function extensionality and compare the values at `g`. Rewrite using `[← one_mul (1 : GL (Fin a') k), omB_mul, omB_one_apply, Matrix.mul_assoc g, hY, ← Matrix.mul_assoc]`.

Simplify using the standard rewrite rules. Establish `hz : apow (gdet D) ((a' : ℂ) / 2) = apow (gdet D) (-(a : ℂ) / 2) * apow (gdet D) (((a + a' : ℕ) : ℂ) / 2)`. Rewrite using `[← apow_add]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hβ : (β (gdet D) : ℂ) ≠ 0` using `Units.ne_zero _`. Unfold `mapB`. Rewrite using `[hfun, hl.2.1 _ _ hψ, ← heq, hdet, map_mul, Units.val_mul, apow_mul, hz, MonoidHom.div_apply, Units.val_div_eq_div_val]`. Clear the denominators using the available nonvanishing facts.

Use `filter_upwards [eventually_omB_one_eq (ν := α / β) hα hΨ] with u hu h`. Rewrite using `[← mapB_omB_right l Ψ u h, hu]`.
-/
theorem mapB_mem_indSp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (α β : kˣ →* ℂˣ) (l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ), IsSmU α →
    IsEqv (α / β) (((a + a' : ℕ) : ℂ) / 2) l → ∀ Ψ ∈ SB (Matrix (Fin a') (Fin (a + a')) k),
      mapB a l (α / β) α Ψ ∈ indSp a a' α β := by
  intro k _ _ _ _ a a' α β l hα hl Ψ hΨ
  refine ⟨fun b A D N hb h => ?_, ?_⟩
  · have hY : Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * b.val =
        D.val * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) := by
      ext i j
      rw [frameMatrixSecondColumnBlock_mul_apply]
      obtain ⟨j', rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')).surjective j
      have := congrFun (congrFun hb (Sum.inr i)) j'
      simp only [submatrix_apply] at this
      rcases j' with j' | j'
      · simp only [fromBlocks_apply₂₁, Matrix.zero_apply] at this
        rw [this, Matrix.mul_apply]
        refine (Finset.sum_eq_zero fun m _ => ?_).symm
        have := j'.isLt
        rw [Y0, of_apply, if_neg (by simp [Fin.ext_iff]; omega), mul_zero]
      · simp only [fromBlocks_apply₂₂] at this
        rw [this]
        simp [Matrix.mul_apply, Y0]
    have hdet : gdet b = gdet A * gdet D := by
      ext
      have e := congrArg Matrix.det hb
      rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁] at e
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using e
    have hφ : (fun g : Matrix (Fin a') (Fin a') k =>
        omB (α / β) α 1 h Ψ (g * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) ∈ SB _ :=
      restrict_Y0 (omB_mem_SB _ _ 1 h hΨ)
    have hψ : (fun X : Matrix (Fin a') (Fin a') k =>
        omB (α / β) α 1 h Ψ (X * D.val * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) ∈ SB _ := by
      simpa using comp_mul_mem_SB (1 : GL (Fin a') k) D hφ
    have heq := hl.2.2 1 D _ hφ
    simp only [Units.val_one, Matrix.one_mul, map_one, one_mul] at heq
    have hfun : (fun g : Matrix (Fin a') (Fin a') k =>
        omB (α / β) α 1 (b * h) Ψ (g * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) =
        ((α (gdet b) : ℂ) * apow (gdet b) ((a' : ℂ) / 2)) • (fun X : Matrix (Fin a') (Fin a') k =>
          omB (α / β) α 1 h Ψ (X * D.val * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) := by
      funext g
      rw [← one_mul (1 : GL (Fin a') k), omB_mul, omB_one_apply, Matrix.mul_assoc g, hY, ← Matrix.mul_assoc]
      simp
    have hz : apow (gdet D) ((a' : ℂ) / 2) = apow (gdet D) (-(a : ℂ) / 2) * apow (gdet D) (((a + a' : ℕ) : ℂ) / 2) := by
      rw [← apow_add]; congr 1; push_cast; ring
    have hβ : (β (gdet D) : ℂ) ≠ 0 := Units.ne_zero _
    unfold mapB
    rw [hfun, hl.2.1 _ _ hψ, ← heq, hdet, map_mul, Units.val_mul, apow_mul, hz, MonoidHom.div_apply,
      Units.val_div_eq_div_val]
    field_simp
  · filter_upwards [eventually_omB_one_eq (ν := α / β) hα hΨ] with u hu h
    rw [← mapB_omB_right l Ψ u h, hu]

end GlobalTheory.KSplit
