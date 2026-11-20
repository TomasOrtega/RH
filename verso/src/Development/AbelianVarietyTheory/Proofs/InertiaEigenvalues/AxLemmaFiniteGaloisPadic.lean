import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldIntegerIffAlgebraicClosureNormStatement
import GroundTheory.PAdicHodge.AxLemma

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Establish `h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l])` using `(map_natCast _ _).symm`. Rewrite using `[h, PadicAlgCl.norm_extends, Padic.norm_p]`.
-/
theorem norm_natCast_self_Om (l : ℕ) [Fact l.Prime] : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := (map_natCast _ _).symm
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

/- English proof (translation)
Establish `h2 : (2 : ℝ) ≤ l` using `by exact_mod_cast hl.out.two_le`. Establish `hexp : (l : ℝ) / ((l : ℝ) - 1) ^ 2 ≤ 2`. Rewrite using `[div_le_iff₀ (by nlinarith)]`. Use the polynomial consequences of the given equalities and inequalities. Unfold `GroundTheory.PAdicHodge.axConstant`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem axConstant_le_sq (l : ℕ) [hl : Fact l.Prime] : GroundTheory.PAdicHodge.axConstant l ≤ (l : ℝ) ^ 2 := by
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hexp : (l : ℝ) / ((l : ℝ) - 1) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  unfold GroundTheory.PAdicHodge.axConstant
  calc (l : ℝ) ^ ((l : ℝ) / ((l : ℝ) - 1) ^ 2) ≤ (l : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    _ = (l : ℝ) ^ 2 := by norm_cast

/- English proof (translation)
Introduce `l _ L _ _ _ _ _ _ _ _ _ _`. Introduce `J x hx`. Establish `hO` using `GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L`. Set `φ : L →ₐ[ℚ_[l]] Om l` to `IsScalarTower.toAlgHom ℚ_[l] L (Om l)`. Establish `hφ : ∀ y : L, φ y = algebraMap L (Om l) y` using `fun y => rfl`.

Set `F : IntermediateField ℚ_[l] L` to `IntermediateField.fixedField J`. Set `E : IntermediateField ℚ_[l] (Om l)` to `F.map φ`. Establish `hmove : ∀ g : Gal(Om l/E), ‖g (φ x) - φ x‖ ≤ 1`. Introduce `g`. Set `g' : Om l ≃ₐ[ℚ_[l]] Om l` to `g.restrictScalars ℚ_[l]`.

Set `τ : L ≃ₐ[ℚ_[l]] L` to `AlgEquiv.restrictNormalHom L g'`. Establish `hτ : ∀ y : L, φ (τ y) = g' (φ y)` using `fun y => AlgEquiv.restrictNormal_commutes g' L y`. Establish `hτJ : τ ∈ J`. Rewrite using `[← IntermediateField.fixingSubgroup_fixedField J]`. Introduce and unpack `⟨y, hy⟩`.

Apply `φ.toRingHom.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `φ (τ y) = φ y`. Rewrite using `[hτ]`. Establish `hyE : φ y ∈ E` using `⟨y, hy, rfl⟩`. Conclude with `g.commutes ⟨φ y, hyE⟩`.

Establish `h1` using `(hO (τ x - x)).1.1 (hx τ hτJ)`. Rewrite `h1` using `[map_sub, ← hφ, ← hφ, hτ]`. Conclude with `h1`. Take `⟨Y, hYE, hY⟩` from `GroundTheory.PAdicHodge.ax_lemma (K := E) (φ x) hmove`. Take `⟨y, hyF, rfl⟩` from `hYE`.

Use `⟨y, fun σ hσ => (IntermediateField.mem_fixedField_iff J y).1 hyF σ hσ, ?_⟩` and prove the remaining obligations. Rewrite using `[(hO _).1, map_mul, map_pow, map_natCast, map_sub, norm_mul, norm_pow, norm_natCast_self_Om, ← hφ, ← hφ]`. Establish `hl : (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Establish `hc` using `axConstant_le_sq l`. Rewrite `hY` using `[mul_one]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem axIn_padic : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)], AxIn ℚ_[l] L l := by
  intro l _ L _ _ _ _ _ _ _ _ _ _
  intro J x hx
  have hO := GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L
  let φ : L →ₐ[ℚ_[l]] Om l := IsScalarTower.toAlgHom ℚ_[l] L (Om l)
  have hφ : ∀ y : L, φ y = algebraMap L (Om l) y := fun y => rfl
  let F : IntermediateField ℚ_[l] L := IntermediateField.fixedField J
  let E : IntermediateField ℚ_[l] (Om l) := F.map φ
  have hmove : ∀ g : Gal(Om l/E), ‖g (φ x) - φ x‖ ≤ 1 := by
    intro g
    let g' : Om l ≃ₐ[ℚ_[l]] Om l := g.restrictScalars ℚ_[l]
    let τ : L ≃ₐ[ℚ_[l]] L := AlgEquiv.restrictNormalHom L g'
    have hτ : ∀ y : L, φ (τ y) = g' (φ y) := fun y => AlgEquiv.restrictNormal_commutes g' L y
    have hτJ : τ ∈ J := by
      rw [← IntermediateField.fixingSubgroup_fixedField J]
      rintro ⟨y, hy⟩
      apply φ.toRingHom.injective
      change φ (τ y) = φ y
      rw [hτ]
      have hyE : φ y ∈ E := ⟨y, hy, rfl⟩
      exact g.commutes ⟨φ y, hyE⟩
    have h1 := (hO (τ x - x)).1.1 (hx τ hτJ)
    rw [map_sub, ← hφ, ← hφ, hτ] at h1
    exact h1
  obtain ⟨Y, hYE, hY⟩ := GroundTheory.PAdicHodge.ax_lemma (K := E) (φ x) hmove
  obtain ⟨y, hyF, rfl⟩ := hYE
  refine ⟨y, fun σ hσ => (IntermediateField.mem_fixedField_iff J y).1 hyF σ hσ, ?_⟩
  rw [(hO _).1, map_mul, map_pow, map_natCast, map_sub, norm_mul, norm_pow, norm_natCast_self_Om, ← hφ, ← hφ]
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hc := axConstant_le_sq l
  rw [mul_one] at hY
  calc ((l : ℝ)⁻¹) ^ 2 * ‖φ x - φ y‖ ≤ ((l : ℝ)⁻¹) ^ 2 * (l : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (hY.trans hc) (by positivity)
    _ = 1 := by rw [inv_pow, inv_mul_cancel₀ (by positivity)]

end GlobalTheory.PMon.Ram
