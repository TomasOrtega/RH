import Mathlib
open Matrix

noncomputable section
namespace GlobalTheory.CompactAvg
open MeasureTheory

/- English proof (translation)
Use `haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH`. Use `letI : MeasurableSpace H := borel H`. Use `haveI : BorelSpace H := ⟨rfl⟩`. Set `μ : Measure H` to `Measure.haarMeasure ⊤`. Use `haveI : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _`.

Set `m : H → Matrix (Fin n) (Fin n) ℂ` to `fun g => (((g⁻¹ : H) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)`. Establish `hm : Continuous m` using `Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)`. Set `f : H → (Fin n → Fin n → ℂ)` to `fun g => ((m g)ᴴ * m g : Matrix (Fin n) (Fin n) ℂ)`. Establish `hf : Continuous f` using `hm.matrix_conjTranspose.matrix_mul hm`. Establish `hfi : Integrable f μ` using `hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.

Set `P₀ : Matrix (Fin n) (Fin n) ℂ` to `Matrix.of (∫ g, f g ∂μ)`. Establish `hinv : ∀ h ∈ H, (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * P₀ * h = P₀`. Introduce `h hh`. Set `M : Matrix (Fin n) (Fin n) ℂ` to `h`. Set `Lₗ : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ)` to `{ toFun := fun A => (Mᴴ * Matrix.of A * M : Matrix (Fin n) (Fin n) ℂ) map_add' := fun A B => by show Mᴴ * Matrix.of (A + B) * M = Mᴴ * Matrix.of A * M + Mᴴ * Matrix.of B * M`.

Rewrite using `[show Matrix.of (A + B) = Matrix.of A + Matrix.of B from rfl, Matrix.mul_add, Matrix.add_mul]`. Use the proof step `map_smul' := fun c A => by show Mᴴ * Matrix.of (c • A) * M = c • (Mᴴ * Matrix.of A * M)`. Rewrite using `[show Matrix.of (c • A) = c • Matrix.of A from rfl, Matrix.mul_smul, Matrix.smul_mul] }`. Set `L` to `LinearMap.toContinuousLinearMap Lₗ`. Establish `e1 : L (∫ g, f g ∂μ) = ∫ g, L (f g) ∂μ` using `(ContinuousLinearMap.integral_comp_comm L hfi).symm`.

Establish `e2 : ∀ g : H, L (f g) = f ((⟨h, hh⟩ : H)⁻¹ * g)`. Introduce `g`. Establish `hq : m ((⟨h, hh⟩ : H)⁻¹ * g) = m g * M` using `by show (((((⟨h, hh⟩ : H)⁻¹ * g)⁻¹ : H) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = m g * M`. Rewrite using `[_root_.mul_inv_rev, inv_inv]`. Both sides reduce to the same expression.

Use `show Mᴴ * ((m g)ᴴ * m g) * M = (m _)ᴴ * m _`. Rewrite using `[hq, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Establish `e3 : ∫ g, f ((⟨h, hh⟩ : H)⁻¹ * g) ∂μ = ∫ g, f g ∂μ` using `integral_mul_left_eq_self f _`. Use `show L (∫ g, f g ∂μ) = ∫ g, f g ∂μ`.

Rewrite using `[e1]`. Repeatedly rewrite using `[e2]`. Conclude with `e3`. Establish `hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P₀ *ᵥ x).re`. Introduce `x hx`.

Set `ℓₗ : (Fin n → Fin n → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun A => star x ⬝ᵥ Matrix.of A *ᵥ x map_add' := fun A B => by show star x ⬝ᵥ Matrix.of (A + B) *ᵥ x = star x ⬝ᵥ Matrix.of A *ᵥ x + star x ⬝ᵥ Matrix.of B *ᵥ x`. Rewrite using `[show Matrix.of (A + B) = Matrix.of A + Matrix.of B from rfl, Matrix.add_mulVec, dotProduct_add]`. Use the proof step `map_smul' := fun c A => by show star x ⬝ᵥ Matrix.of (c • A) *ᵥ x = c • (star x ⬝ᵥ Matrix.of A *ᵥ x)`. Rewrite using `[show Matrix.of (c • A) = c • Matrix.of A from rfl, Matrix.smul_mulVec, dotProduct_smul] }`. Set `ℓ` to `LinearMap.toContinuousLinearMap ℓₗ`.

Establish `e1 : ℓ (∫ g, f g ∂μ) = ∫ g, ℓ (f g) ∂μ` using `(ContinuousLinearMap.integral_comp_comm ℓ hfi).symm`. Establish `hℓi : Integrable (fun g => ℓ (f g)) μ` using `ℓ.integrable_comp hfi`. Establish `e2 : (star x ⬝ᵥ P₀ *ᵥ x).re = ∫ g, RCLike.re (ℓ (f g)) ∂μ`. Rewrite using `[integral_re hℓi, ← e1]`. Both sides reduce to the same expression.

Establish `e3 : ∀ g : H, RCLike.re (ℓ (f g)) = ∑ i, ‖(m g *ᵥ x) i‖ ^ 2`. Introduce `g`. Use `show (star x ⬝ᵥ ((m g)ᴴ * m g) *ᵥ x).re = _`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`. Simplify using `only [dotProduct, Pi.star_apply, Complex.re_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using `[Complex.star_def, Complex.mul_re]`. Establish `hnz : ∀ g : H, m g *ᵥ x ≠ 0`. Introduce `g h0`.

Establish `: (((g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * m g) *ᵥ x = x`. Simplify using `[m]`. Rewrite `this` using `[← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]`. Conclude with `hx this.symm`. Establish `e4 : ∀ g : H, 0 < ∑ i, ‖(m g *ᵥ x) i‖ ^ 2`.

Introduce `g`. Take `⟨i, hi⟩` from `Function.ne_iff.1 (hnz g)`. Establish `hi' : 0 < ‖(m g *ᵥ x) i‖ ^ 2`. Establish `: 0 < ‖(m g *ᵥ x) i‖` using `norm_pos_iff.2 hi`. Check the signs of the components of the expression.

Conclude with `lt_of_lt_of_le hi' (Finset.single_le_sum (f := fun i => ‖(m g *ᵥ x) i‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i))`. Rewrite using `[e2]`. Repeatedly rewrite using `[e3]`. Establish `hgi : Integrable (fun g : H => ∑ i, ‖(m g *ᵥ x) i‖ ^ 2) μ` using `(continuous_finset_sum _ fun i _ => ((continuous_apply i).comp (hm.matrix_mulVec continuous_const)).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Rewrite using `[integral_pos_iff_support_of_nonneg (fun g => (e4 g).le) hgi]`.

Establish `hs : Function.support (fun g : H => ∑ i, ‖(m g *ᵥ x) i‖ ^ 2) = Set.univ` using `Set.eq_univ_of_forall fun g => (e4 g).ne'`. Rewrite using `[hs]`. Conclude with `isOpen_univ.measure_pos μ Set.univ_nonempty`. Use `⟨P₀ + P₀ᴴ, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.IsHermitian, add_comm]`.

Introduce `x hx`. Establish `hc : star x ⬝ᵥ P₀ᴴ *ᵥ x = star (star x ⬝ᵥ P₀ *ᵥ x)`. Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, star_dotProduct]`. Rewrite using `[Matrix.add_mulVec, dotProduct_add, Complex.add_re, hc]`. Use `hpos x hx` as an intermediate fact.

Simplify using `only [Complex.star_def, Complex.conj_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `g hg`. Establish `h1` using `hinv g hg`. Establish `h2 : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P₀ᴴ * g = P₀ᴴ` using `by conv_rhs => rw [← h1]`.

Simplify using `[Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_add, Matrix.add_mul, h1, h2]`.
-/
theorem exists_invariant_posDef_hermitian {n : ℕ} (H : Subgroup (GL (Fin n) ℂ))
    (hH : IsCompact (H : Set (GL (Fin n) ℂ))) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ g ∈ H, (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P * g = P := by
  classical
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  let μ : Measure H := Measure.haarMeasure ⊤
  haveI : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  let m : H → Matrix (Fin n) (Fin n) ℂ := fun g => (((g⁻¹ : H) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have hm : Continuous m := Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)

  let f : H → (Fin n → Fin n → ℂ) := fun g => ((m g)ᴴ * m g : Matrix (Fin n) (Fin n) ℂ)
  have hf : Continuous f := hm.matrix_conjTranspose.matrix_mul hm
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P₀ : Matrix (Fin n) (Fin n) ℂ := Matrix.of (∫ g, f g ∂μ)

  have hinv : ∀ h ∈ H, (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * P₀ * h = P₀ := by
    intro h hh
    let M : Matrix (Fin n) (Fin n) ℂ := h
    let Lₗ : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
      { toFun := fun A => (Mᴴ * Matrix.of A * M : Matrix (Fin n) (Fin n) ℂ)
        map_add' := fun A B => by
          show Mᴴ * Matrix.of (A + B) * M = Mᴴ * Matrix.of A * M + Mᴴ * Matrix.of B * M
          rw [show Matrix.of (A + B) = Matrix.of A + Matrix.of B from rfl, Matrix.mul_add, Matrix.add_mul]
        map_smul' := fun c A => by
          show Mᴴ * Matrix.of (c • A) * M = c • (Mᴴ * Matrix.of A * M)
          rw [show Matrix.of (c • A) = c • Matrix.of A from rfl, Matrix.mul_smul, Matrix.smul_mul] }
    let L := LinearMap.toContinuousLinearMap Lₗ
    have e1 : L (∫ g, f g ∂μ) = ∫ g, L (f g) ∂μ := (ContinuousLinearMap.integral_comp_comm L hfi).symm
    have e2 : ∀ g : H, L (f g) = f ((⟨h, hh⟩ : H)⁻¹ * g) := by
      intro g
      have hq : m ((⟨h, hh⟩ : H)⁻¹ * g) = m g * M := by
        show (((((⟨h, hh⟩ : H)⁻¹ * g)⁻¹ : H) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = m g * M
        rw [_root_.mul_inv_rev, inv_inv]
        rfl
      show Mᴴ * ((m g)ᴴ * m g) * M = (m _)ᴴ * m _
      rw [hq, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have e3 : ∫ g, f ((⟨h, hh⟩ : H)⁻¹ * g) ∂μ = ∫ g, f g ∂μ := integral_mul_left_eq_self f _
    show L (∫ g, f g ∂μ) = ∫ g, f g ∂μ
    rw [e1]; simp_rw [e2]; exact e3

  have hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P₀ *ᵥ x).re := by
    intro x hx
    let ℓₗ : (Fin n → Fin n → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun A => star x ⬝ᵥ Matrix.of A *ᵥ x
        map_add' := fun A B => by
          show star x ⬝ᵥ Matrix.of (A + B) *ᵥ x = star x ⬝ᵥ Matrix.of A *ᵥ x + star x ⬝ᵥ Matrix.of B *ᵥ x
          rw [show Matrix.of (A + B) = Matrix.of A + Matrix.of B from rfl, Matrix.add_mulVec, dotProduct_add]
        map_smul' := fun c A => by
          show star x ⬝ᵥ Matrix.of (c • A) *ᵥ x = c • (star x ⬝ᵥ Matrix.of A *ᵥ x)
          rw [show Matrix.of (c • A) = c • Matrix.of A from rfl, Matrix.smul_mulVec, dotProduct_smul] }
    let ℓ := LinearMap.toContinuousLinearMap ℓₗ
    have e1 : ℓ (∫ g, f g ∂μ) = ∫ g, ℓ (f g) ∂μ := (ContinuousLinearMap.integral_comp_comm ℓ hfi).symm
    have hℓi : Integrable (fun g => ℓ (f g)) μ := ℓ.integrable_comp hfi
    have e2 : (star x ⬝ᵥ P₀ *ᵥ x).re = ∫ g, RCLike.re (ℓ (f g)) ∂μ := by
      rw [integral_re hℓi, ← e1]; rfl
    have e3 : ∀ g : H, RCLike.re (ℓ (f g)) = ∑ i, ‖(m g *ᵥ x) i‖ ^ 2 := by
      intro g
      show (star x ⬝ᵥ ((m g)ᴴ * m g) *ᵥ x).re = _
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.star_def, Complex.mul_re]
    have hnz : ∀ g : H, m g *ᵥ x ≠ 0 := by
      intro g h0
      have : (((g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * m g) *ᵥ x = x := by
        simp [m]
      rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero] at this
      exact hx this.symm
    have e4 : ∀ g : H, 0 < ∑ i, ‖(m g *ᵥ x) i‖ ^ 2 := by
      intro g
      obtain ⟨i, hi⟩ := Function.ne_iff.1 (hnz g)
      have hi' : 0 < ‖(m g *ᵥ x) i‖ ^ 2 := by
        have : 0 < ‖(m g *ᵥ x) i‖ := norm_pos_iff.2 hi
        positivity
      exact lt_of_lt_of_le hi' (Finset.single_le_sum (f := fun i => ‖(m g *ᵥ x) i‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i))
    rw [e2]
    simp_rw [e3]
    have hgi : Integrable (fun g : H => ∑ i, ‖(m g *ᵥ x) i‖ ^ 2) μ :=
      (continuous_finset_sum _ fun i _ =>
        ((continuous_apply i).comp (hm.matrix_mulVec continuous_const)).norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_pos_iff_support_of_nonneg (fun g => (e4 g).le) hgi]
    have hs : Function.support (fun g : H => ∑ i, ‖(m g *ᵥ x) i‖ ^ 2) = Set.univ :=
      Set.eq_univ_of_forall fun g => (e4 g).ne'
    rw [hs]
    exact isOpen_univ.measure_pos μ Set.univ_nonempty
  refine ⟨P₀ + P₀ᴴ, ?_, ?_, ?_⟩
  · simp [Matrix.IsHermitian, add_comm]
  · intro x hx
    have hc : star x ⬝ᵥ P₀ᴴ *ᵥ x = star (star x ⬝ᵥ P₀ *ᵥ x) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, star_dotProduct]
    rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re, hc]
    have := hpos x hx
    simp only [Complex.star_def, Complex.conj_re]
    linarith
  · intro g hg
    have h1 := hinv g hg
    have h2 : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P₀ᴴ * g = P₀ᴴ := by
      conv_rhs => rw [← h1]
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.add_mul, h1, h2]

end GlobalTheory.CompactAvg
