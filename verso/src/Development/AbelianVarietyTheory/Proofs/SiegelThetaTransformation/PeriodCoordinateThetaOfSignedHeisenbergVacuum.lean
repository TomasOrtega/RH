import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaCharacteristicsIffTestFunctionThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsWeilOfSymplectic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergOperatorRationalPointLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CanonicalThetaExponentSymplecticInvariant

section Siegel

open Matrix Complex GlobalTheory GlobalTheory.SW
open scoped ComplexConjugate Real Classical

namespace GlobalTheory.Dict.VacForm

variable {n g : ℕ}

noncomputable abbrev imC (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  τ.map fun z => (z.im : ℂ)

noncomputable def can (h τ : Matrix (Fin g) (Fin g) ℂ) (φ : TF n g) (z : Fin n → Fin g → ℂ) : ℂ :=
  h.det ^ (n / 2) * cexp (π / 2 * ∑ k, (h *ᵥ z k) ⬝ᵥ (imC τ)⁻¹ *ᵥ (h *ᵥ z k)) *
    thS φ τ fun k => h *ᵥ z k

noncomputable def hf (h τ : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℂ) : ℂ :=
  (h *ᵥ u) ⬝ᵥ (imC τ)⁻¹ *ᵥ star (h *ᵥ v)

/- English proof (translation)
Establish `hY : imC τ = (τ.map Complex.im).map (algebraMap ℝ ℂ)`. Use extensionality with `i j`. Simplify using `[imC]`. Establish `hf : (fun t : ℝ => (t : ℂ)) = (algebraMap ℝ ℂ : ℝ → ℂ)` using `rfl`. Rewrite using `[hY, hf]`.

Distinguish the cases in `h : IsUnit (τ.map Complex.im).det`. Use `symm`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `h' : ¬ IsUnit ((τ.map Complex.im).map (algebraMap ℝ ℂ)).det`.

Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Introduce `hu`. Apply `h` to reduce the goal to its premises. Rewrite `hu`, the goal using `[isUnit_iff_ne_zero]`. Introduce `h0`.

Apply `hu` to reduce the goal to its premises. Rewrite using `[h0, map_zero]`. Rewrite using `[Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h']`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_im_inv (τ : Matrix (Fin g) (Fin g) ℂ) :
    ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) = (imC τ)⁻¹ := by
  have hY : imC τ = (τ.map Complex.im).map (algebraMap ℝ ℂ) := by
    ext i j; simp [imC]
  have hf : (fun t : ℝ => (t : ℂ)) = (algebraMap ℝ ℂ : ℝ → ℂ) := rfl
  rw [hY, hf]
  by_cases h : IsUnit (τ.map Complex.im).det
  · symm
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ (map_zero _) (map_one _)]
  · have h' : ¬ IsUnit ((τ.map Complex.im).map (algebraMap ℝ ℂ)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      intro hu
      apply h
      rw [isUnit_iff_ne_zero] at hu ⊢
      intro h0; apply hu; rw [h0, map_zero]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h']
    ext i j; simp

/- English proof (translation)
Establish `h1 : τ.IsSymm` using `hτ.1`. Establish `hs : (imC τ).IsSymm` using `Matrix.IsSymm.ext fun i j => by`. Simplify using `only [imC, Matrix.map_apply]`. Rewrite using `[h1.apply i j]`. Unfold `Matrix.IsSymm at hs ⊢`.

Rewrite using `[Matrix.transpose_nonsing_inv, hs]`.
-/
theorem imC_isSymm {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ Siegel (Fin g)) :
    (imC τ)⁻¹.IsSymm := by
  have h1 : τ.IsSymm := hτ.1
  have hs : (imC τ).IsSymm := Matrix.IsSymm.ext fun i j => by
    simp only [imC, Matrix.map_apply]; rw [h1.apply i j]
  unfold Matrix.IsSymm at hs ⊢
  rw [Matrix.transpose_nonsing_inv, hs]

/- English proof (translation)
Apply `Matrix.nonsing_inv_mul` to reduce the goal to its premises. Use `isUnit_det_im_of_mem_siegel hτ` as an intermediate fact. Simplify `this` using `[imC]`.
-/
theorem imC_inv_mul {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ Siegel (Fin g)) :
    (imC τ)⁻¹ * imC τ = 1 := by
  apply Matrix.nonsing_inv_mul
  have := isUnit_det_im_of_mem_siegel hτ
  simpa [imC] using this

/- English proof (translation)
Use function extensionality and compare the values at `z`. Take `⟨hdet, -, -, -, -⟩` from `SiegelAction.symplectic_action (Fin g) σ hσ τ hτ`. Establish `hv : ∀ k, (((spDen σ τ)⁻¹)ᵀ * h) *ᵥ z k = (h *ᵥ z k) ᵥ* (spDen σ τ)⁻¹`. Introduce `k`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]`.

Simplify using `only [can, hv]`. Establish `hT` using `ht τ hτ (fun k => h *ᵥ z k)`. Simplify using `only [Fintype.card_fin] at hT`. Rewrite using `[hT]`. Establish `hE : cexp (π / 2 * ∑ k, ((h *ᵥ z k) ᵥ* (spDen σ τ)⁻¹) ⬝ᵥ (imC (spAct σ τ))⁻¹ *ᵥ ((h *ᵥ z k) ᵥ* (spDen σ τ)⁻¹)) * cexp (π * I * ∑ k, (h *ᵥ z k) ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ (h *ᵥ z k)) = cexp (π / 2 * ∑ k, (h *ᵥ z k) ⬝ᵥ (imC τ)⁻¹ *ᵥ (h *ᵥ z k))`.

Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hc` using `canon_exponent_invariant (Fin g) σ hσ τ hτ (h *ᵥ z k)`.

Take the linear combination `(π / 2 : ℂ) * hc`. Establish `hD : ((spDen σ τ)⁻¹)ᵀ.det ^ (n / 2) * (spDen σ τ).det ^ (n / 2) = 1`. Rewrite using `[Matrix.det_transpose, Matrix.det_nonsing_inv, ← mul_pow, Ring.inverse_mul_cancel _ (isUnit_iff_ne_zero.mpr hdet), one_pow]`. Rewrite using `[Matrix.det_mul, mul_pow]`. Rewrite using `[show ∀ a b c d e f : ℂ, a * b * c * (d * e * f) = (a * d) * b * (c * e) * f from fun _ _ _ _ _ _ => by ring, hD, hE, one_mul]`.
-/
theorem can_trans {σ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup (Fin g) ℚ) {φ ψ : TF n g} (ht : TransS σ φ ψ)
    {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ Siegel (Fin g)) (h : Matrix (Fin g) (Fin g) ℂ) :
    can (((spDen σ τ)⁻¹)ᵀ * h) (spAct σ τ) ψ = can h τ φ := by
  funext z
  obtain ⟨hdet, -, -, -, -⟩ := SiegelAction.symplectic_action (Fin g) σ hσ τ hτ
  have hv : ∀ k, (((spDen σ τ)⁻¹)ᵀ * h) *ᵥ z k = (h *ᵥ z k) ᵥ* (spDen σ τ)⁻¹ := by
    intro k; rw [← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]
  simp only [can, hv]
  have hT := ht τ hτ (fun k => h *ᵥ z k)
  simp only [Fintype.card_fin] at hT
  rw [hT]
  have hE : cexp (π / 2 * ∑ k, ((h *ᵥ z k) ᵥ* (spDen σ τ)⁻¹) ⬝ᵥ (imC (spAct σ τ))⁻¹ *ᵥ
      ((h *ᵥ z k) ᵥ* (spDen σ τ)⁻¹)) *
      cexp (π * I * ∑ k, (h *ᵥ z k) ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ (h *ᵥ z k)) =
      cexp (π / 2 * ∑ k, (h *ᵥ z k) ⬝ᵥ (imC τ)⁻¹ *ᵥ (h *ᵥ z k)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc := canon_exponent_invariant (Fin g) σ hσ τ hτ (h *ᵥ z k)
    linear_combination (π / 2 : ℂ) * hc
  have hD : ((spDen σ τ)⁻¹)ᵀ.det ^ (n / 2) * (spDen σ τ).det ^ (n / 2) = 1 := by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, ← mul_pow,
      Ring.inverse_mul_cancel _ (isUnit_iff_ne_zero.mpr hdet), one_pow]
  rw [Matrix.det_mul, mul_pow]
  rw [show ∀ a b c d e f : ℂ, a * b * c * (d * e * f) = (a * d) * b * (c * e) * f from
    fun _ _ _ _ _ _ => by ring, hD, hE, one_mul]

/- English proof (translation)
Establish `hs : star (M *ᵥ b) = M.map star *ᵥ star b`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, star_sum, star_mul']`. Rewrite using `[hs, Matrix.mulVec_mulVec, show M *ᵥ a = a ᵥ* Mᵀ from (Matrix.vecMul_transpose M a).symm]`. Simplify using `only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]`.
-/
private theorem mulVec_dotProduct_mulVec_star_eq_transpose_mul {ι : Type} [Fintype ι] (M W : Matrix ι ι ℂ) (a b : ι → ℂ) :
    (M *ᵥ a) ⬝ᵥ W *ᵥ star (M *ᵥ b) = a ⬝ᵥ (Mᵀ * W * M.map star) *ᵥ star b := by
  have hs : star (M *ᵥ b) = M.map star *ᵥ star b := by
    ext i; simp [Matrix.mulVec, dotProduct, star_sum, star_mul']
  rw [hs, Matrix.mulVec_mulVec, show M *ᵥ a = a ᵥ* Mᵀ from (Matrix.vecMul_transpose M a).symm]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

/- English proof (translation)
Take `⟨-, hS', -, hY, -⟩` from `SiegelAction.symplectic_action (Fin g) σ hσ τ hτ`. Establish `symC : ∀ t : Matrix (Fin g) (Fin g) ℂ, t ∈ Siegel (Fin g) → (t.map fun z => (z.im : ℂ))ᵀ = t.map fun z => (z.im : ℂ)`. Introduce `t ht`. Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply]`.

Rewrite using `[ht.1.apply i j]`. Establish `hY2 : (spDen σ τ)ᴴ * imC (spAct σ τ) * spDen σ τ = imC τ`. Establish `h2` using `congrArg Matrix.transpose hY`. Rewrite `h2` using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, symC _ hS', symC _ hτ, ← Matrix.mul_assoc]`. Conclude with `h2`.

Use function extensionality and compare the values at `u v`. Simplify using `only [hf]`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_dotProduct_mulVec_star_eq_transpose_mul ((spDen σ τ)⁻¹)ᵀ]`. Use `congr 2`. Rewrite using `[Matrix.transpose_transpose, ← hY2, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_assoc]`.

Apply the tactic sequence `all_goals rfl`.
-/
theorem hf_trans {σ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup (Fin g) ℚ)
    {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ Siegel (Fin g)) (h : Matrix (Fin g) (Fin g) ℂ) :
    hf (((spDen σ τ)⁻¹)ᵀ * h) (spAct σ τ) = hf h τ := by
  obtain ⟨-, hS', -, hY, -⟩ := SiegelAction.symplectic_action (Fin g) σ hσ τ hτ
  have symC : ∀ t : Matrix (Fin g) (Fin g) ℂ, t ∈ Siegel (Fin g) →
      (t.map fun z => (z.im : ℂ))ᵀ = t.map fun z => (z.im : ℂ) := by
    intro t ht; ext i j; simp only [Matrix.transpose_apply, Matrix.map_apply]; rw [ht.1.apply i j]
  have hY2 : (spDen σ τ)ᴴ * imC (spAct σ τ) * spDen σ τ = imC τ := by
    have h2 := congrArg Matrix.transpose hY
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, symC _ hS',
      symC _ hτ, ← Matrix.mul_assoc] at h2
    exact h2
  funext u v
  simp only [hf]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_dotProduct_mulVec_star_eq_transpose_mul ((spDen σ τ)⁻¹)ᵀ]
  congr 2
  rw [Matrix.transpose_transpose, ← hY2, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    ← Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_assoc]
  all_goals rfl

/- English proof (translation)
Take `⟨-, hth, -⟩` from `heisS_laws (Fin n) (Fin g) a b φ hφ`. Establish `e1 : ∀ k, h *ᵥ (z k + p k) = h *ᵥ z k + qv (a k) + τ *ᵥ qv (b k)`. Introduce `k`. Rewrite using `[Matrix.mulVec_add, hp, add_assoc]`. Simplify using `only [can]`.

Rewrite using `[hth τ hτ]`. Simplify using `only [e1]`. Establish `hx : cexp (π / 2 * ∑ k, (h *ᵥ z k) ⬝ᵥ (imC τ)⁻¹ *ᵥ (h *ᵥ z k)) * cexp (π * I * ∑ k, (qv (b k) ⬝ᵥ τ *ᵥ qv (b k) + 2 * (qv (b k) ⬝ᵥ h *ᵥ z k) + qv (a k) ⬝ᵥ qv (b k))) = cexp (-(π * ∑ k, hf h τ (z k + (1 / 2 : ℂ) • p k) (p k))) * cexp (π / 2 * ∑ k, (h *ᵥ z k + qv (a k) + τ *ᵥ qv (b …`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`.

Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[heis_exponent τ (imC τ)⁻¹ hτ.1 (imC_isSymm hτ) (imC_inv_mul hτ) (a k) (b k) (h *ᵥ z k)]`. Simplify using `only [hf, Matrix.mulVec_add, Matrix.mulVec_smul, hp, add_assoc]`. Take the linear combination `(h.det ^ (n / 2) * thS φ τ (fun k => h *ᵥ z k + qv (a k) + τ *ᵥ qv (b k))) * hx`.
-/
theorem can_heis {h τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ Siegel (Fin g)) {φ : TF n g}
    (hφ : IsSB φ) (a b : Matrix (Fin n) (Fin g) ℚ) (p : Fin n → Fin g → ℂ)
    (hp : ∀ k, h *ᵥ p k = qv (a k) + τ *ᵥ qv (b k)) (z : Fin n → Fin g → ℂ) :
    can h τ (heisS a b φ) z = cexp (-(π * ∑ k, hf h τ (z k + (1 / 2 : ℂ) • p k) (p k))) *
      can h τ φ fun k => z k + p k := by
  obtain ⟨-, hth, -⟩ := heisS_laws (Fin n) (Fin g) a b φ hφ
  have e1 : ∀ k, h *ᵥ (z k + p k) = h *ᵥ z k + qv (a k) + τ *ᵥ qv (b k) := by
    intro k; rw [Matrix.mulVec_add, hp, add_assoc]
  simp only [can]
  rw [hth τ hτ]
  simp only [e1]
  have hx : cexp (π / 2 * ∑ k, (h *ᵥ z k) ⬝ᵥ (imC τ)⁻¹ *ᵥ (h *ᵥ z k)) *
      cexp (π * I * ∑ k, (qv (b k) ⬝ᵥ τ *ᵥ qv (b k) + 2 * (qv (b k) ⬝ᵥ h *ᵥ z k) +
        qv (a k) ⬝ᵥ qv (b k))) =
      cexp (-(π * ∑ k, hf h τ (z k + (1 / 2 : ℂ) • p k) (p k))) *
      cexp (π / 2 * ∑ k, (h *ᵥ z k + qv (a k) + τ *ᵥ qv (b k)) ⬝ᵥ (imC τ)⁻¹ *ᵥ
        (h *ᵥ z k + qv (a k) + τ *ᵥ qv (b k))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [heis_exponent τ (imC τ)⁻¹ hτ.1 (imC_isSymm hτ) (imC_inv_mul hτ) (a k) (b k) (h *ᵥ z k)]
    simp only [hf, Matrix.mulVec_add, Matrix.mulVec_smul, hp, add_assoc]
  linear_combination (h.det ^ (n / 2) *
    thS φ τ (fun k => h *ᵥ z k + qv (a k) + τ *ᵥ qv (b k))) * hx

/- English proof (translation)
Apply `GlobalTheory.SW.eq_of_thS_eq (Fin n) (Fin g) φ ψ hφ hψ τ hτ` to reduce the goal to its premises. Introduce `ζ`. Establish `hz : ∀ k, h *ᵥ (h⁻¹ *ᵥ ζ k) = ζ k`. Introduce `k`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hh, Matrix.one_mulVec]`.

Establish `e'` using `congrFun e fun k => h⁻¹ *ᵥ ζ k`. Simplify using `only [can, hz] at e'`. Conclude with `mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ hh.ne_zero) (Complex.exp_ne_zero _)) e'`.
-/
theorem eq_of_can_eq {h τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ Siegel (Fin g)) (hh : IsUnit h.det)
    {φ ψ : TF n g} (hφ : IsSB φ) (hψ : IsSB ψ) (e : can h τ φ = can h τ ψ) : φ = ψ := by
  apply GlobalTheory.SW.eq_of_thS_eq (Fin n) (Fin g) φ ψ hφ hψ τ hτ
  intro ζ
  have hz : ∀ k, h *ᵥ (h⁻¹ *ᵥ ζ k) = ζ k := by
    intro k; rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hh, Matrix.one_mulVec]
  have e' := congrFun e fun k => h⁻¹ *ᵥ ζ k
  simp only [can, hz] at e'
  exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ hh.ne_zero) (Complex.exp_ne_zero _)) e'

/- English proof (translation)
Simplify using `only [can, thS, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem can_smul (h τ : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (φ : TF n g) (z : Fin n → Fin g → ℂ) :
    can h τ (a • φ) z = a * can h τ φ z := by
  simp only [can, thS, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left]
  ring

/- English proof (translation)
Simplify using `[dotProduct, Matrix.single_apply, ite_and, Finset.sum_ite_eq]`.
-/
theorem sum_single_dot (x : Fin n → Fin g → ℚ) (k : Fin n) (i : Fin g) :
    ∑ l, x l ⬝ᵥ (Matrix.single k i (1 : ℚ)) l = x k i := by
  simp [dotProduct, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

/- English proof (translation)
Establish `z0 : ∀ l, (0 : Matrix (Fin n) (Fin g) ℚ) l = 0` using `fun _ => rfl`. Establish `base : ∀ (y : Matrix (Fin n) (Fin g) ℚ) (k : Fin n) (i : Fin g), ψ (y + Matrix.single k i 1) = cexp (2 * π * I * c₂ i) * ψ y`. Introduce `y k i`. Establish `e` using `congrFun (h2 k i) (y + Matrix.single k i 1)`. Simplify using `only [Pi.smul_apply, smul_eq_mul, heisS, add_sub_cancel_right, z0, dotProduct_zero, zero_dotProduct, mul_zero, sub_zero, Finset.sum_const_zero, Rat.cast_zero, Complex.exp_zero, mul_one] at e`.

Conclude with `e.symm`. Establish `intg : ∀ x : Matrix (Fin n) (Fin g) ℚ, ψ x ≠ 0 → ∀ k i, IsIntegral ℤ (x k i - c₁ i)`. Introduce `x hx k i`. Establish `hsum : (∑ l, (2 * (x l ⬝ᵥ (Matrix.single k i (1 : ℚ)) l) - (Matrix.single k i (1 : ℚ)) l ⬝ᵥ (0 : Matrix (Fin n) (Fin g) ℚ) l)) = 2 * x k i`. Establish `h0 : ∀ l, (Matrix.single k i (1 : ℚ)) l ⬝ᵥ (0 : Matrix (Fin n) (Fin g) ℚ) l = 0` using `fun l => dotProduct_zero _`.

Simplify using `only [h0, sub_zero]`. Rewrite using `[← Finset.mul_sum]`. Conclude with `congrArg (fun t => 2 * t) (sum_single_dot x k i)`. Establish `e` using `congrFun (h1 k i) x`. Simplify using `only [Pi.smul_apply, smul_eq_mul, heisS, sub_zero] at e`.

Rewrite `e` using `[hsum]`. Establish `e2 : cexp (2 * π * I * c₁ i) * cexp (π * I * ((2 * x k i : ℚ) : ℂ)) = 1`. Apply `mul_right_cancel₀ hx` to reduce the goal to its premises. Take the linear combination `e`. Rewrite `e2` using `[← Complex.exp_add, Complex.exp_eq_one_iff]`.

Take `⟨m, hm⟩` from `e2`. Establish `hq : (c₁ i + x k i : ℚ) = m`. Establish `h' : ((c₁ i + x k i : ℚ) : ℂ) = (m : ℂ)`. Establish `h2pi : (2 * π * I : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero, Complex.I_ne_zero]`. Apply `mul_left_cancel₀ h2pi` to reduce the goal to its premises.

Move the coercions through the operations in `at hm ⊢`. Take the linear combination `hm`. Conclude with `h'` after adjusting the coercions. Rewrite using `[CharLink.isIntegral_iff_int]`. Break down `hc i with h0 | h0` into its components or cases.

Conclude with `⟨m, by rw [h0] at hq ⊢; linarith⟩`. Conclude with `⟨m - 1, by push_cast; rw [h0] at hq ⊢; linarith⟩`. Take `⟨S, hS⟩ : ∃ S : Matrix (Fin n) (Fin g) ℚ → ℚ, ∀ y, S y = ∑ l, y l ⬝ᵥ c₂` from `⟨_, fun _ => rfl⟩`. Establish `hSadd : ∀ y k i, S (y + Matrix.single k i 1) = S y + c₂ i`. Introduce `y k i`.

Establish `h3 : ∀ l, (y + Matrix.single k i (1 : ℚ)) l ⬝ᵥ c₂ = y l ⬝ᵥ c₂ + Matrix.single k i (1 : ℚ) l ⬝ᵥ c₂` using `fun l => add_dotProduct _ _ _`. Rewrite using `[hS, hS, Finset.sum_congr rfl fun l _ => h3 l, Finset.sum_add_distrib]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Take `⟨f, hf⟩ : ∃ f : Matrix (Fin n) (Fin g) ℚ → ℂ, ∀ y, f y = ψ y * cexp (-(2 * π * I * ((S y : ℚ) : ℂ)))` from `⟨_, fun _ => rfl⟩`.

Establish `finv : ∀ y k i, f (y + Matrix.single k i 1) = f y`. Introduce `y k i`. Rewrite using `[hf, hf, base, hSadd]`. Use `push_cast`. Rewrite using `[show -(2 * (π : ℂ) * I * ((S y : ℂ) + (c₂ i : ℂ))) = -(2 * π * I * (S y : ℂ)) + -(2 * π * I * (c₂ i : ℂ)) by ring, Complex.exp_add, Complex.exp_neg (2 * π * I * (c₂ i : ℂ))]`.

Clear the denominators using the available nonvanishing facts. Establish `fint : ∀ (m : ℤ) (y : Matrix (Fin n) (Fin g) ℚ) (k : Fin n) (i : Fin g), f (y + (m : ℚ) • Matrix.single k i 1) = f y`. Introduce `m`. Use `Int.induction_on m ?_ ?_ ?_` and prove the remaining obligations. Introduce `y k i`.

Simplify using the standard rewrite rules. Introduce `j ih y k i`. Simplify using `only [Int.cast_add, Int.cast_natCast, Int.cast_one] at ih ⊢`. Rewrite using `[add_smul, one_smul, ← add_assoc, finv, ih]`. Introduce `j ih y k i`.

Simplify using `only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one] at ih ⊢`. Rewrite using `[← finv _ k i, add_assoc, sub_smul, one_smul, sub_add_cancel, ih]`. Establish `fall : ∀ (N : Fin n → Fin g → ℤ) (s : Finset (Fin n × Fin g)) (y : Matrix (Fin n) (Fin g) ℚ), f (y + ∑ p ∈ s, ((N p.1 p.2 : ℤ) : ℚ) • Matrix.single p.1 p.2 (1 : ℚ)) = f y`. Introduce `N s`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations.

Introduce `y`. Simplify using the standard rewrite rules. Introduce `a s ha ih y`. Rewrite using `[Finset.sum_insert ha, ← add_assoc, ih, fint]`. Use `⟨f (Matrix.of fun _ i => c₁ i), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Simplify using `only [Pi.smul_apply, smul_eq_mul, CharLink.chi]`. Use `split_ifs with hx`. Use `choose N hN using fun k i => (CharLink.isIntegral_iff_int _).1 (hx k i)`. Establish `hdec : x = Matrix.of (fun _ i => c₁ i) + ∑ p ∈ (Finset.univ : Finset (Fin n × Fin g)), ((N p.1 p.2 : ℤ) : ℚ) • Matrix.single p.1 p.2 (1 : ℚ)`.

Use extensionality with `k i`. Simplify using `[Matrix.sum_apply, Matrix.single_apply, Fintype.sum_prod_type, ite_and, hN]`. Establish `key` using `fall N Finset.univ (Matrix.of fun _ i => c₁ i)`. Rewrite `key` using `[← hdec]`. Rewrite using `[← key, hf, hS, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]`.

Rewrite using `[mul_zero]`. Assume the negation of the conclusion as `hne`. Conclude with `hx (intg x hne)`.
-/
theorem eq_smul_chi (ψ : TF n g) (c₁ c₂ : Fin g → ℚ) (hc : ∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2)
    (h1 : ∀ k i, cexp (2 * π * I * c₁ i) • heisS (Matrix.single k i 1) 0 ψ = ψ)
    (h2 : ∀ k i, cexp (2 * π * I * c₂ i) • heisS 0 (Matrix.single k i 1) ψ = ψ) :
    ∃ C : ℂ, ψ = C • CharLink.chi (fun _ => c₁) (fun _ => c₂) := by
  have z0 : ∀ l, (0 : Matrix (Fin n) (Fin g) ℚ) l = 0 := fun _ => rfl
  have base : ∀ (y : Matrix (Fin n) (Fin g) ℚ) (k : Fin n) (i : Fin g),
      ψ (y + Matrix.single k i 1) = cexp (2 * π * I * c₂ i) * ψ y := by
    intro y k i
    have e := congrFun (h2 k i) (y + Matrix.single k i 1)
    simp only [Pi.smul_apply, smul_eq_mul, heisS, add_sub_cancel_right, z0, dotProduct_zero,
      zero_dotProduct, mul_zero, sub_zero, Finset.sum_const_zero, Rat.cast_zero,
      Complex.exp_zero, mul_one] at e
    exact e.symm
  have intg : ∀ x : Matrix (Fin n) (Fin g) ℚ, ψ x ≠ 0 → ∀ k i, IsIntegral ℤ (x k i - c₁ i) := by
    intro x hx k i
    have hsum : (∑ l, (2 * (x l ⬝ᵥ (Matrix.single k i (1 : ℚ)) l) -
        (Matrix.single k i (1 : ℚ)) l ⬝ᵥ (0 : Matrix (Fin n) (Fin g) ℚ) l)) = 2 * x k i := by
      have h0 : ∀ l, (Matrix.single k i (1 : ℚ)) l ⬝ᵥ (0 : Matrix (Fin n) (Fin g) ℚ) l = 0 :=
        fun l => dotProduct_zero _
      simp only [h0, sub_zero]
      rw [← Finset.mul_sum]
      exact congrArg (fun t => 2 * t) (sum_single_dot x k i)
    have e := congrFun (h1 k i) x
    simp only [Pi.smul_apply, smul_eq_mul, heisS, sub_zero] at e
    rw [hsum] at e
    have e2 : cexp (2 * π * I * c₁ i) * cexp (π * I * ((2 * x k i : ℚ) : ℂ)) = 1 := by
      apply mul_right_cancel₀ hx
      linear_combination e
    rw [← Complex.exp_add, Complex.exp_eq_one_iff] at e2
    obtain ⟨m, hm⟩ := e2
    have hq : (c₁ i + x k i : ℚ) = m := by
      have h' : ((c₁ i + x k i : ℚ) : ℂ) = (m : ℂ) := by
        have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
        apply mul_left_cancel₀ h2pi
        push_cast at hm ⊢
        linear_combination hm
      exact_mod_cast h'
    rw [CharLink.isIntegral_iff_int]
    rcases hc i with h0 | h0
    · exact ⟨m, by rw [h0] at hq ⊢; linarith⟩
    · exact ⟨m - 1, by push_cast; rw [h0] at hq ⊢; linarith⟩
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin n) (Fin g) ℚ → ℚ, ∀ y, S y = ∑ l, y l ⬝ᵥ c₂ :=
    ⟨_, fun _ => rfl⟩
  have hSadd : ∀ y k i, S (y + Matrix.single k i 1) = S y + c₂ i := by
    intro y k i
    have h3 : ∀ l, (y + Matrix.single k i (1 : ℚ)) l ⬝ᵥ c₂ =
        y l ⬝ᵥ c₂ + Matrix.single k i (1 : ℚ) l ⬝ᵥ c₂ := fun l => add_dotProduct _ _ _
    rw [hS, hS, Finset.sum_congr rfl fun l _ => h3 l, Finset.sum_add_distrib]
    congr 1
    calc ∑ l, Matrix.single k i (1 : ℚ) l ⬝ᵥ c₂ = ∑ l, c₂ ⬝ᵥ Matrix.single k i (1 : ℚ) l :=
          Finset.sum_congr rfl fun l _ => dotProduct_comm _ _
      _ = c₂ i := sum_single_dot (fun _ => c₂) k i
  obtain ⟨f, hf⟩ : ∃ f : Matrix (Fin n) (Fin g) ℚ → ℂ,
      ∀ y, f y = ψ y * cexp (-(2 * π * I * ((S y : ℚ) : ℂ))) := ⟨_, fun _ => rfl⟩
  have finv : ∀ y k i, f (y + Matrix.single k i 1) = f y := by
    intro y k i
    rw [hf, hf, base, hSadd]
    push_cast
    rw [show -(2 * (π : ℂ) * I * ((S y : ℂ) + (c₂ i : ℂ))) =
      -(2 * π * I * (S y : ℂ)) + -(2 * π * I * (c₂ i : ℂ)) by ring, Complex.exp_add,
      Complex.exp_neg (2 * π * I * (c₂ i : ℂ))]
    field_simp
  have fint : ∀ (m : ℤ) (y : Matrix (Fin n) (Fin g) ℚ) (k : Fin n) (i : Fin g),
      f (y + (m : ℚ) • Matrix.single k i 1) = f y := by
    intro m
    refine Int.induction_on m ?_ ?_ ?_
    · intro y k i; simp
    · intro j ih y k i
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_one] at ih ⊢
      rw [add_smul, one_smul, ← add_assoc, finv, ih]
    · intro j ih y k i
      simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one] at ih ⊢
      rw [← finv _ k i, add_assoc, sub_smul, one_smul, sub_add_cancel, ih]
  have fall : ∀ (N : Fin n → Fin g → ℤ) (s : Finset (Fin n × Fin g)) (y : Matrix (Fin n) (Fin g) ℚ),
      f (y + ∑ p ∈ s, ((N p.1 p.2 : ℤ) : ℚ) • Matrix.single p.1 p.2 (1 : ℚ)) = f y := by
    intro N s
    refine Finset.induction_on s ?_ ?_
    · intro y; simp
    · intro a s ha ih y
      rw [Finset.sum_insert ha, ← add_assoc, ih, fint]
  refine ⟨f (Matrix.of fun _ i => c₁ i), ?_⟩
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, CharLink.chi]
  split_ifs with hx
  · choose N hN using fun k i => (CharLink.isIntegral_iff_int _).1 (hx k i)
    have hdec : x = Matrix.of (fun _ i => c₁ i) + ∑ p ∈ (Finset.univ : Finset (Fin n × Fin g)),
        ((N p.1 p.2 : ℤ) : ℚ) • Matrix.single p.1 p.2 (1 : ℚ) := by
      ext k i
      simp [Matrix.sum_apply, Matrix.single_apply, Fintype.sum_prod_type, ite_and, hN]
    have key := fall N Finset.univ (Matrix.of fun _ i => c₁ i)
    rw [← hdec] at key
    rw [← key, hf, hS, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  · rw [mul_zero]
    by_contra hne
    exact hx (intg x hne)

end GlobalTheory.Dict.VacForm

end Siegel

section Basis

open Matrix Complex NumberField GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Dict
open scoped ComplexConjugate Real Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (omegaStd)

namespace GlobalTheory.Dict.VacForm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

variable (X bas) in

noncomputable def spB (b : Fin g ⊕ Fin g → Fin r → E) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℚ :=
  Matrix.of fun p q => crd X bas (b p.swap) q.swap

/- English proof (translation)
Rewrite using `[SymplecticGroup.mem_iff]`. Use extensionality with `p q`. Establish `hE` using `hb p.swap q.swap`. Rewrite `hE` using `[EF_crd hs]`. Apply the tactic sequence `rcases p with i | i <;> rcases q with j | j <;> by_cases hij : i = j <;>`.

Apply the tactic sequence `simp [Matrix.mul_apply, Matrix.J, spB, Fintype.sum_sum_type, omegaStd, Pi.single_apply, Matrix.one_apply, Finset.sum_sub_distrib, @eq_comm _ j i, hij] at hE ⊢ <;> linarith`.
-/
theorem spB_mem (hs : IsSympl X bas) {b : Fin g ⊕ Fin g → Fin r → E}
    (hb : ∀ i j, EF X (b i) (b j) = -(omegaStd (Pi.single i 1) (Pi.single j 1) : ℤ)) :
    spB X bas b ∈ Matrix.symplecticGroup (Fin g) ℚ := by
  rw [SymplecticGroup.mem_iff]
  ext p q
  have hE := hb p.swap q.swap
  rw [EF_crd hs] at hE
  rcases p with i | i <;> rcases q with j | j <;> by_cases hij : i = j <;>
    simp [Matrix.mul_apply, Matrix.J, spB, Fintype.sum_sum_type, omegaStd, Pi.single_apply,
      Matrix.one_apply, Finset.sum_sub_distrib, @eq_comm _ j i, hij] at hE ⊢ <;> linarith

/- English proof (translation)
Establish `hτs` using `(UnAct.tauMat_mem (idx := idx) hs hx).1`. Use extensionality with `i k`. Establish `hc` using `congrFun (hMat_mulVec_per_crd idx hs hx (b (s k))) i`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.add_apply, qv, Function.comp_apply] at hc`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.add_apply, qm, Matrix.map_apply, spB, Sum.swap_swap, Sum.swap_inl, Sum.swap_inr, Dict.pv, Function.comp_apply]`.

Rewrite using `[hc, add_comm]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `hτs.apply i j` as an intermediate fact. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hMat_mul_per (hs : IsSympl X bas) (b : Fin g ⊕ Fin g → Fin r → E)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : Fin g → Fin g ⊕ Fin g) :
    hMat X bas idx x * (Matrix.of fun i k => pv X idx x (b (s k)) i) =
      (qm (Matrix.of fun k j => spB X bas b (s k).swap (Sum.inl j)) * tauMat X bas idx x +
        qm (Matrix.of fun k j => spB X bas b (s k).swap (Sum.inr j)))ᵀ := by
  have hτs := (UnAct.tauMat_mem (idx := idx) hs hx).1
  ext i k
  have hc := congrFun (hMat_mulVec_per_crd idx hs hx (b (s k))) i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, qv, Function.comp_apply] at hc
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.add_apply, qm,
    Matrix.map_apply, spB, Sum.swap_swap, Sum.swap_inl, Sum.swap_inr, Dict.pv, Function.comp_apply]
  rw [hc, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have := hτs.apply i j
  rw [this]
  ring

/- English proof (translation)
Establish `hσ : spB X bas b ∈ symplecticGroup (Fin g) ℚ` using `spB_mem hs hb`. Establish `hτ₀ : tauMat X bas idx x ∈ Siegel (Fin g)` using `UnAct.tauMat_mem (idx := idx) hs hx`. Take `⟨hdet, hS', -, -, -⟩` from `SiegelAction.symplectic_action (Fin g) (spB X bas b) hσ (tauMat X bas idx x) hτ₀`. Establish `e1 : hMat X bas idx x * (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i) = (spDen (spB X bas b) (tauMat X bas idx x))ᵀ` using `hMat_mul_per idx hs b hx Sum.inl`. Establish `e2 : hMat X bas idx x * (Matrix.of fun i k => pv X idx x (b (Sum.inr k)) i) = (qm (spB X bas b).toBlocks₁₁ * tauMat X bas idx x + qm (spB X bas b).toBlocks₁₂)ᵀ` using `hMat_mul_per idx hs b hx Sum.inr`.

Establish `hD : IsUnit (spDen (spB X bas b) (tauMat X bas idx x)).det` using `isUnit_iff_ne_zero.mpr hdet`. Establish `hdetP` using `congrArg Matrix.det e1`. Rewrite `hdetP` using `[Matrix.det_mul, Matrix.det_transpose]`. Establish `hP1u : IsUnit (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i).det` using `isUnit_of_mul_isUnit_right (hdetP ▸ hD)`. Establish `hinv : (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i)⁻¹ = ((spDen (spB X bas b) (tauMat X bas idx x))⁻¹)ᵀ * hMat X bas idx x`.

Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.mul_assoc, e1, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hD, Matrix.transpose_one]`. Establish `hh'` using `hh.trans hinv`. Establish `hP1 : h * (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i) = 1`. Rewrite using `[hh]`.

Conclude with `Matrix.nonsing_inv_mul _ hP1u`. Establish `hτ' : τ = spAct (spB X bas b) (tauMat X bas idx x)`. Rewrite using `[hτ, hh', Matrix.mul_assoc, e2, ← Matrix.transpose_mul]`. Conclude with `hS'.1`. Use `⟨Matrix.isUnit_det_of_right_inverse hP1, hτ' ▸ hS', hh', hτ', fun i => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Establish `col : pv X idx x (b (Sum.inl i)) = (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i) *ᵥ Pi.single i 1`. Rewrite using `[Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Rewrite using `[col, Matrix.mulVec_mulVec, hP1, Matrix.one_mulVec]`. Establish `col : pv X idx x (b (Sum.inr i)) = (Matrix.of fun i k => pv X idx x (b (Sum.inr k)) i) *ᵥ Pi.single i 1`.

Rewrite using `[Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Rewrite using `[col, Matrix.mulVec_mulVec, ← hτ]`.
-/
theorem periods_spB (hs : IsSympl X bas) {b : Fin g ⊕ Fin g → Fin r → E}
    (hb : ∀ i j, EF X (b i) (b j) = -(omegaStd (Pi.single i 1) (Pi.single j 1) : ℤ))
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {h τ : Matrix (Fin g) (Fin g) ℂ}
    (hh : h = (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i)⁻¹)
    (hτ : τ = h * (Matrix.of fun i k => pv X idx x (b (Sum.inr k)) i)) :
    IsUnit h.det ∧ τ ∈ Siegel (Fin g) ∧
      h = ((spDen (spB X bas b) (tauMat X bas idx x))⁻¹)ᵀ * hMat X bas idx x ∧
      τ = spAct (spB X bas b) (tauMat X bas idx x) ∧
      ∀ i, h *ᵥ pv X idx x (b (Sum.inl i)) = Pi.single i 1 ∧
        h *ᵥ pv X idx x (b (Sum.inr i)) = τ *ᵥ Pi.single i 1 := by
  have hσ : spB X bas b ∈ symplecticGroup (Fin g) ℚ := spB_mem hs hb
  have hτ₀ : tauMat X bas idx x ∈ Siegel (Fin g) := UnAct.tauMat_mem (idx := idx) hs hx
  obtain ⟨hdet, hS', -, -, -⟩ :=
    SiegelAction.symplectic_action (Fin g) (spB X bas b) hσ (tauMat X bas idx x) hτ₀
  have e1 : hMat X bas idx x * (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i) =
      (spDen (spB X bas b) (tauMat X bas idx x))ᵀ := hMat_mul_per idx hs b hx Sum.inl
  have e2 : hMat X bas idx x * (Matrix.of fun i k => pv X idx x (b (Sum.inr k)) i) =
      (qm (spB X bas b).toBlocks₁₁ * tauMat X bas idx x + qm (spB X bas b).toBlocks₁₂)ᵀ :=
    hMat_mul_per idx hs b hx Sum.inr
  have hD : IsUnit (spDen (spB X bas b) (tauMat X bas idx x)).det := isUnit_iff_ne_zero.mpr hdet
  have hdetP := congrArg Matrix.det e1
  rw [Matrix.det_mul, Matrix.det_transpose] at hdetP
  have hP1u : IsUnit (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i).det :=
    isUnit_of_mul_isUnit_right (hdetP ▸ hD)
  have hinv : (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i)⁻¹ =
      ((spDen (spB X bas b) (tauMat X bas idx x))⁻¹)ᵀ * hMat X bas idx x := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc, e1, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hD,
      Matrix.transpose_one]
  have hh' := hh.trans hinv
  have hP1 : h * (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i) = 1 := by
    rw [hh]; exact Matrix.nonsing_inv_mul _ hP1u
  have hτ' : τ = spAct (spB X bas b) (tauMat X bas idx x) := by
    rw [hτ, hh', Matrix.mul_assoc, e2, ← Matrix.transpose_mul]
    exact hS'.1
  refine ⟨Matrix.isUnit_det_of_right_inverse hP1, hτ' ▸ hS', hh', hτ', fun i => ⟨?_, ?_⟩⟩
  · have col : pv X idx x (b (Sum.inl i)) =
        (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i) *ᵥ Pi.single i 1 := by
      rw [Matrix.mulVec_single_one]; rfl
    rw [col, Matrix.mulVec_mulVec, hP1, Matrix.one_mulVec]
  · have col : pv X idx x (b (Sum.inr i)) =
        (Matrix.of fun i k => pv X idx x (b (Sum.inr k)) i) *ᵥ Pi.single i 1 := by
      rw [Matrix.mulVec_single_one]; rfl
    rw [col, Matrix.mulVec_mulVec, ← hτ]

/- English proof (translation)
Establish `hwu : w • u ∈ L`. Establish `h` using `L.smul_mem (⟨w, hw⟩ : 𝓞 E) hu`. Conclude with `h`. Take `⟨k, hk⟩` from `(hL.2 u).1 hu (w • u) hwu`. Simplify using `only [Dict.eps1, hk]`.

Break down `Int.even_or_odd' k with ⟨m, rfl | rfl⟩` into its components or cases. Use `⟨0, Or.inl rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[Complex.exp_eq_exp_iff_exists_int]`. Conclude with `⟨m, by push_cast; ring⟩`. Use `⟨1 / 2, Or.inr rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[Complex.exp_eq_exp_iff_exists_int]`. Conclude with `⟨m, by push_cast; ring⟩`.
-/
theorem exists_half {w : E} (hw : IsIntegral ℤ w) {L : Lt E r} (hL : SelfD X L) {u : Fin r → E}
    (hu : u ∈ L) : ∃ c : ℚ, (c = 0 ∨ c = 1 / 2) ∧ eps1 X w u = cexp (2 * π * I * c) := by
  have hwu : w • u ∈ L := by
    have h := L.smul_mem (⟨w, hw⟩ : 𝓞 E) hu
    exact h
  obtain ⟨k, hk⟩ := (hL.2 u).1 hu (w • u) hwu
  simp only [Dict.eps1, hk]
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · refine ⟨0, Or.inl rfl, ?_⟩
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨m, by push_cast; ring⟩
  · refine ⟨1 / 2, Or.inr rfl, ?_⟩
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨m, by push_cast; ring⟩

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [thA, can, imInv, map_im_inv]`.
-/
theorem thA_eq_can (φ : TF n g) (x : Frame X.Ψ r) :
    thA X bas idx φ x = can (hMat X bas idx x) (tauMat X bas idx x) φ := by
  funext z
  simp only [thA, can, imInv, map_im_inv]

/- English proof (translation)
Use function extensionality and compare the values at `u v`. Simplify using `only [Dict.hx, hf, imInv, map_im_inv]`.
-/
theorem hx_eq_hf (x : Frame X.Ψ r) :
    hx X bas idx x = hf (hMat X bas idx x) (tauMat X bas idx x) := by
  funext u v
  simp only [Dict.hx, hf, imInv, map_im_inv]

/- English proof (translation)
Take `⟨R, hR, h1, h2⟩` from `h`. Use `⟨R, hR, fun x hx => h1 x fun h0 => hx (by simp [h0]), fun x y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, h2 x y hy]`.
-/
private theorem isSB_smul_rat_matrix {κ ι : Type} [Fintype κ] [Fintype ι] (c : ℂ)
    {φ : Matrix κ ι ℚ → ℂ} (h : IsSB φ) : IsSB (c • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x fun h0 => hx (by simp [h0]), fun x y hy => ?_⟩
  simp only [Pi.smul_apply, h2 x y hy]

/- English proof (translation)
Take `⟨hvSB, -, hvfix⟩` from `hv`. Establish `hmem : (Pi.single k 1 : Fin n → E) ∈ stdL E n`. Simplify using `[stdL]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Establish `hy : vecMulVec (Pi.single k 1) u ∈ tens (stdL E n) L` using `AddSubgroup.subset_closure ⟨Pi.single k 1, hmem, u, hu, rfl⟩`.

Establish `hyk : vecMulVec (Pi.single k (1 : E)) u k = u`. Use function extensionality and compare the values at `j`. Simplify using `[vecMulVec]`. Establish `hyl : ∀ l, l ≠ k → vecMulVec (Pi.single k (1 : E)) u l = 0`. Introduce `l hl`.

Use function extensionality and compare the values at `j`. Simplify using `[vecMulVec, Pi.single_apply, hl]`. Establish `per0 : per X x 0 = 0`. Use function extensionality and compare the values at `p`. Establish `he : Data.emb (p.1 : E →+* ℂ) (0 : Fin r → E) = 0`.

Use function extensionality and compare the values at `fun a => map_zero (p.1 : E →+* ℂ)`. Simplify using `[per, hermC, he]`. Establish `pv0 : pv X idx x 0 = 0`. Simplify using `only [Dict.pv, per0]`. Both sides reduce to the same expression.

Establish `EF00 : EF X 0 (w • 0) = 0`. Rewrite using `[smul_zero, EF_crd hs, crd_zero hs]`. Simplify using the standard rewrite rules. Establish `heps : epsW X w (vecMulVec (Pi.single k 1) u) = eps1 X w u`. Simplify using `only [epsW, Dict.eps1]`.

Rewrite using `[Finset.sum_eq_single k (fun l _ hl => by rw [hyl l hl, EF00]) (fun h' => absurd (Finset.mem_univ k) h'), hyk]`. Establish `qv0 : qv (0 : Fin g → ℚ) = 0` using `by funext i; simp [qv]`. Establish `hq : ∀ l, h *ᵥ pv X idx x (vecMulVec (Pi.single k 1) u l) = qv (a l) + τ *ᵥ qv (b l)`. Introduce `l`. Distinguish the cases in `hl : l = k`.

Substitute `hl` using the available equality. Rewrite using `[hyk]`. Conclude with `h1`. Rewrite using `[hyl l hl, (h0 l hl).1, (h0 l hl).2, pv0, qv0]`. Simplify using the standard rewrite rules.

Establish `hSB : IsSB (eps1 X w u • heisS a b ψ)` using `isSB_smul_rat_matrix _ (heisS_laws (Fin n) (Fin g) a b ψ hψ).1`. Apply `eq_of_can_eq hτ hh hSB hψ` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Take `⟨-, -, -, hG⟩` from `heisG_laws E r X g bas idx n hs hn`. Take `⟨-, -, -, -, hthA⟩` from `hG (vecMulVec (Pi.single k 1) u) v hvSB`.

Rewrite using `[can_smul, can_heis hτ hψ a b _ hq z, e1, e2]`. Use `conv_rhs => rw [← hvfix _ hy]`. Rewrite using `[UnAct.thA_smul, Pi.smul_apply, smul_eq_mul, hthA x hx z, heps]`. Both sides reduce to the same expression.
-/
theorem heis_fix (hs : IsSympl X bas) (hn : Even n) {w : E} {L : Lt E r} {v ψ : TF n g}
    (hv : IsVac X bas w (tens (stdL E n) L) v) (hψ : IsSB ψ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    {h τ : Matrix (Fin g) (Fin g) ℂ} (hh : IsUnit h.det) (hτ : τ ∈ Siegel (Fin g))
    (e1 : can h τ ψ = thA X bas idx v x) (e2 : hf h τ = Dict.hx X bas idx x)
    {u : Fin r → E} (hu : u ∈ L) (k : Fin n) {a b : Matrix (Fin n) (Fin g) ℚ}
    (h0 : ∀ l, l ≠ k → a l = 0 ∧ b l = 0)
    (h1 : h *ᵥ pv X idx x u = qv (a k) + τ *ᵥ qv (b k)) :
    eps1 X w u • heisS a b ψ = ψ := by
  obtain ⟨hvSB, -, hvfix⟩ := hv
  have hmem : (Pi.single k 1 : Fin n → E) ∈ stdL E n := by
    simp [stdL]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hy : vecMulVec (Pi.single k 1) u ∈ tens (stdL E n) L :=
    AddSubgroup.subset_closure ⟨Pi.single k 1, hmem, u, hu, rfl⟩
  have hyk : vecMulVec (Pi.single k (1 : E)) u k = u := by
    funext j; simp [vecMulVec]
  have hyl : ∀ l, l ≠ k → vecMulVec (Pi.single k (1 : E)) u l = 0 := by
    intro l hl; funext j; simp [vecMulVec, Pi.single_apply, hl]
  have per0 : per X x 0 = 0 := by
    funext p
    have he : Data.emb (p.1 : E →+* ℂ) (0 : Fin r → E) = 0 :=
      funext fun a => map_zero (p.1 : E →+* ℂ)
    simp [per, hermC, he]
  have pv0 : pv X idx x 0 = 0 := by
    simp only [Dict.pv, per0]; rfl
  have EF00 : EF X 0 (w • 0) = 0 := by
    rw [smul_zero, EF_crd hs, crd_zero hs]; simp
  have heps : epsW X w (vecMulVec (Pi.single k 1) u) = eps1 X w u := by
    simp only [epsW, Dict.eps1]
    rw [Finset.sum_eq_single k (fun l _ hl => by rw [hyl l hl, EF00])
      (fun h' => absurd (Finset.mem_univ k) h'), hyk]
  have qv0 : qv (0 : Fin g → ℚ) = 0 := by funext i; simp [qv]
  have hq : ∀ l, h *ᵥ pv X idx x (vecMulVec (Pi.single k 1) u l) = qv (a l) + τ *ᵥ qv (b l) := by
    intro l
    by_cases hl : l = k
    · subst hl; rw [hyk]; exact h1
    · rw [hyl l hl, (h0 l hl).1, (h0 l hl).2, pv0, qv0]; simp
  have hSB : IsSB (eps1 X w u • heisS a b ψ) :=
    isSB_smul_rat_matrix _ (heisS_laws (Fin n) (Fin g) a b ψ hψ).1
  apply eq_of_can_eq hτ hh hSB hψ
  funext z
  obtain ⟨-, -, -, hG⟩ := heisG_laws E r X g bas idx n hs hn
  obtain ⟨-, -, -, -, hthA⟩ := hG (vecMulVec (Pi.single k 1) u) v hvSB
  rw [can_smul, can_heis hτ hψ a b _ hq z, e1, e2]
  conv_rhs => rw [← hvfix _ hy]
  rw [UnAct.thA_smul, Pi.smul_apply, smul_eq_mul, hthA x hx z, heps]
  rfl

end GlobalTheory.Dict.VacForm

end Basis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.VacForm

/- English proof (translation)
Introduce `E _ _ _ r X g bas idx n hs hn w hw _ L hL v hv b hbL hb`. Establish `hσ` using `spB_mem hs hb`. Take `⟨ω, hω⟩` from `exists_weil_of_symplectic (Fin n) (Fin g) (spB X bas b) (by simpa using hn) hσ`. Take `⟨hψSB, hT, -⟩` from `hω v hv.1`. Establish `hbmem : ∀ j, b j ∈ L` using `fun j => (hbL (b j)).2 ⟨Pi.single j 1, by simp [Pi.single_apply, ite_smul]⟩`.

Use `choose c₁ hc₁ he₁ using fun i => exists_half hw hL (hbmem (Sum.inl i))`. Use `choose c₂ hc₂ he₂ using fun i => exists_half hw hL (hbmem (Sum.inr i))`. Take `⟨x₀, hx₀⟩` from `UnAct.exists_mem_dom X`. Take `⟨hh₀, hτ₀, hh₀', hτ₀', hcol₀⟩` from `periods_spB idx hs hb hx₀ rfl rfl`. Establish `e1₀` using `(show can (Matrix.of fun i k => pv X idx x₀ (b (Sum.inl k)) i)⁻¹ ((Matrix.of fun i k => pv X idx x₀ (b (Sum.inl k)) i)⁻¹ * Matrix.of fun i k => pv X idx x₀ (b (Sum.inr k)) i) (ω v) = thA X bas idx v x₀ by`.

Rewrite using `[thA_eq_can, hτ₀', hh₀', can_trans hσ hT (UnAct.tauMat_mem (idx := idx) hs hx₀)])`. Establish `e2₀` using `(show hf (Matrix.of fun i k => pv X idx x₀ (b (Sum.inl k)) i)⁻¹ ((Matrix.of fun i k => pv X idx x₀ (b (Sum.inl k)) i)⁻¹ * Matrix.of fun i k => pv X idx x₀ (b (Sum.inr k)) i) = Dict.hx X bas idx x₀ by`. Rewrite using `[hx_eq_hf, hτ₀', hh₀', hf_trans hσ (UnAct.tauMat_mem (idx := idx) hs hx₀)])`. Establish `qs : ∀ (k : Fin n) (i : Fin g), qv ((Matrix.single k i (1 : ℚ)) k) = Pi.single i 1`. Introduce `k i`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality. Simplify using `[qv, Matrix.single_apply]`. Simplify using `[qv, Matrix.single_apply, Pi.single_apply, hij, Ne.symm hij]`.

Establish `qv0 : ∀ k : Fin n, qv ((0 : Matrix (Fin n) (Fin g) ℚ) k) = 0`. Introduce `k`. Use function extensionality and compare the values at `j`. Simplify using `[qv]`. Establish `hs0 : ∀ (k : Fin n) (i : Fin g) (l : Fin n), l ≠ k → (Matrix.single k i (1 : ℚ)) l = 0`.

Introduce `k i l hl`. Use function extensionality and compare the values at `j`. Simplify using `[Matrix.single_apply, hl, Ne.symm hl]`. Establish `fix₁ : ∀ k i, cexp (2 * Real.pi * I * c₁ i) • heisS (Matrix.single k i 1) 0 (ω v) = ω v`. Introduce `k i`.

Use `heis_fix idx hs hn hv hψSB hx₀ hh₀ hτ₀ e1₀ e2₀ (hbmem (Sum.inl i)) k (a := Matrix.single k i 1) (b := 0) (fun l hl => ⟨hs0 k i l hl, rfl⟩) (by rw [(hcol₀ i).1, qs, qv0, Matrix.mulVec_zero, add_zero])` as an intermediate fact. Rewrite `this` using `[he₁ i]`. Then use the resulting hypothesis. Establish `fix₂ : ∀ k i, cexp (2 * Real.pi * I * c₂ i) • heisS 0 (Matrix.single k i 1) (ω v) = ω v`. Introduce `k i`. Use `heis_fix idx hs hn hv hψSB hx₀ hh₀ hτ₀ e1₀ e2₀ (hbmem (Sum.inr i)) k (a := 0) (b := Matrix.single k i 1) (fun l hl => ⟨rfl, hs0 k i l hl⟩) (by rw [(hcol₀ i).2, qs, qv0, zero_add])` as an intermediate fact.

Rewrite `this` using `[he₂ i]`. Then use the resulting hypothesis. Take `⟨C, hC⟩` from `eq_smul_chi (ω v) c₁ c₂ hc₁ fix₁ fix₂`. Establish `hC0 : C ≠ 0`. Introduce and unpack `rfl`. Establish `hψ0 : ω v = 0` using `by rw [hC, zero_smul]`.

Establish `h00 : thA X bas idx v x₀ = thA X bas idx 0 x₀`. Rewrite using `[← e1₀, hψ0]`. Use function extensionality and compare the values at `z`. Simplify using `[thA, can, thS]`. Establish `hv0` using `UnAct.eq_of_thA_eq idx hs hx₀ hv.1 isSB_zero h00`.

Establish `h1` using `hv.2.1`. Rewrite `h1` using `[hv0]`. Simplify using `[ip, haar, haarAt] at h1`. Use `⟨fun i => ((c₁ i : ℝ) : ℂ), fun i => ((c₂ i : ℝ) : ℂ), C, hC0, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `intro i; rcases hc₁ i with h | h <;> simp [h]`.

Apply the tactic sequence `intro i; rcases hc₂ i with h | h <;> simp [h]`. Introduce `x hx h τ hh hτ`. Take `⟨hhu, hτS, hh', hτ', -⟩` from `periods_spB idx hs hb hx hh hτ`. Establish `e1 : can h τ (ω v) = thA X bas idx v x`. Rewrite using `[thA_eq_can, hτ', hh', can_trans hσ hT (UnAct.tauMat_mem (idx := idx) hs hx)]`.

Establish `e2 : hf h τ = Dict.hx X bas idx x`. Rewrite using `[hx_eq_hf, hτ', hh', hf_trans hσ (UnAct.tauMat_mem (idx := idx) hs hx)]`. Use `⟨hhu, hτS, ?_, fun i => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `z w'`. Rewrite using `[← e2, map_im_inv]`.

Both sides reduce to the same expression. Rewrite using `[he₁ i]`. Simplify using `only [Complex.ofReal_ratCast]`. Rewrite using `[he₂ i]`. Simplify using `only [Complex.ofReal_ratCast]`.

Introduce `z`. Rewrite using `[← e1, hC, can_smul]`. Simplify using `only [can, map_im_inv]`. Rewrite using `[CharLink.thS_chi _ _ hτS.2, Finset.mul_sum, Complex.exp_sum, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thA_vacuum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ b : Fin g ⊕ Fin g → (Fin r → E), (∀ u, u ∈ L ↔ ∃ m : Fin g ⊕ Fin g → ℤ, u = ∑ j, m j • b j) → (∀ i j, EF X (b i) (b j) = -(omegaStd (Pi.single i 1) (Pi.single j 1) : ℤ)) → ∃ (c₁ c₂ : Fin g → ℂ) (C : ℂ), C ≠ 0 ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ ∀ x ∈ X.dom, ∀ h τ : Matrix (Fin g) (Fin g) ℂ, h = (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i)⁻¹ → τ = h * (Matrix.of fun i k => pv X idx x (b (Sum.inr k)) i) → IsUnit h.det ∧ τ ∈ SW.Siegel (Fin g) ∧ (∀ z w' : Fin g → ℂ, hx X bas idx x z w' = (h *ᵥ z) ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) *ᵥ star (h *ᵥ w')) ∧ (∀ i, eps1 X w (b (Sum.inl i)) = cexp (2 * Real.pi * I * c₁ i) ∧ eps1 X w (b (Sum.inr i)) = cexp (2 * Real.pi * I * c₂ i)) ∧ ∀ z : Fin n → Fin g → ℂ, thA X bas idx v x z = C * h.det ^ (n / 2) * ∏ k, (cexp (Real.pi / 2 * ((h *ᵥ z k) ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) *ᵥ (h *ᵥ z k))) * thetaChar τ c₁ c₂ (h *ᵥ z k)) := by
  intro E _ _ _ r X g bas idx n hs hn w hw _ L hL v hv b hbL hb
  have hσ := spB_mem hs hb
  obtain ⟨ω, hω⟩ := exists_weil_of_symplectic (Fin n) (Fin g) (spB X bas b) (by simpa using hn) hσ
  obtain ⟨hψSB, hT, -⟩ := hω v hv.1
  have hbmem : ∀ j, b j ∈ L := fun j =>
    (hbL (b j)).2 ⟨Pi.single j 1, by simp [Pi.single_apply, ite_smul]⟩
  choose c₁ hc₁ he₁ using fun i => exists_half hw hL (hbmem (Sum.inl i))
  choose c₂ hc₂ he₂ using fun i => exists_half hw hL (hbmem (Sum.inr i))
  obtain ⟨x₀, hx₀⟩ := UnAct.exists_mem_dom X
  obtain ⟨hh₀, hτ₀, hh₀', hτ₀', hcol₀⟩ := periods_spB idx hs hb hx₀ rfl rfl
  have e1₀ := (show can (Matrix.of fun i k => pv X idx x₀ (b (Sum.inl k)) i)⁻¹
      ((Matrix.of fun i k => pv X idx x₀ (b (Sum.inl k)) i)⁻¹ *
        Matrix.of fun i k => pv X idx x₀ (b (Sum.inr k)) i) (ω v) = thA X bas idx v x₀ by
    rw [thA_eq_can, hτ₀', hh₀', can_trans hσ hT (UnAct.tauMat_mem (idx := idx) hs hx₀)])
  have e2₀ := (show hf (Matrix.of fun i k => pv X idx x₀ (b (Sum.inl k)) i)⁻¹
      ((Matrix.of fun i k => pv X idx x₀ (b (Sum.inl k)) i)⁻¹ *
        Matrix.of fun i k => pv X idx x₀ (b (Sum.inr k)) i) = Dict.hx X bas idx x₀ by
    rw [hx_eq_hf, hτ₀', hh₀', hf_trans hσ (UnAct.tauMat_mem (idx := idx) hs hx₀)])
  have qs : ∀ (k : Fin n) (i : Fin g), qv ((Matrix.single k i (1 : ℚ)) k) = Pi.single i 1 := by
    intro k i; funext j
    by_cases hij : j = i
    · subst hij; simp [qv, Matrix.single_apply]
    · simp [qv, Matrix.single_apply, Pi.single_apply, hij, Ne.symm hij]
  have qv0 : ∀ k : Fin n, qv ((0 : Matrix (Fin n) (Fin g) ℚ) k) = 0 := by
    intro k; funext j; simp [qv]
  have hs0 : ∀ (k : Fin n) (i : Fin g) (l : Fin n), l ≠ k → (Matrix.single k i (1 : ℚ)) l = 0 := by
    intro k i l hl; funext j; simp [Matrix.single_apply, hl, Ne.symm hl]
  have fix₁ : ∀ k i, cexp (2 * Real.pi * I * c₁ i) • heisS (Matrix.single k i 1) 0 (ω v) = ω v := by
    intro k i
    have := heis_fix idx hs hn hv hψSB hx₀ hh₀ hτ₀ e1₀ e2₀ (hbmem (Sum.inl i)) k
      (a := Matrix.single k i 1) (b := 0) (fun l hl => ⟨hs0 k i l hl, rfl⟩)
      (by rw [(hcol₀ i).1, qs, qv0, Matrix.mulVec_zero, add_zero])
    rwa [he₁ i] at this
  have fix₂ : ∀ k i, cexp (2 * Real.pi * I * c₂ i) • heisS 0 (Matrix.single k i 1) (ω v) = ω v := by
    intro k i
    have := heis_fix idx hs hn hv hψSB hx₀ hh₀ hτ₀ e1₀ e2₀ (hbmem (Sum.inr i)) k
      (a := 0) (b := Matrix.single k i 1) (fun l hl => ⟨rfl, hs0 k i l hl⟩)
      (by rw [(hcol₀ i).2, qs, qv0, zero_add])
    rwa [he₂ i] at this
  obtain ⟨C, hC⟩ := eq_smul_chi (ω v) c₁ c₂ hc₁ fix₁ fix₂
  have hC0 : C ≠ 0 := by
    rintro rfl
    have hψ0 : ω v = 0 := by rw [hC, zero_smul]
    have h00 : thA X bas idx v x₀ = thA X bas idx 0 x₀ := by
      rw [← e1₀, hψ0]; funext z; simp [thA, can, thS]
    have hv0 := UnAct.eq_of_thA_eq idx hs hx₀ hv.1 isSB_zero h00
    have h1 := hv.2.1
    rw [hv0] at h1
    simp [ip, haar, haarAt] at h1
  refine ⟨fun i => ((c₁ i : ℝ) : ℂ), fun i => ((c₂ i : ℝ) : ℂ), C, hC0, ?_, ?_, ?_⟩
  · intro i; rcases hc₁ i with h | h <;> simp [h]
  · intro i; rcases hc₂ i with h | h <;> simp [h]
  intro x hx h τ hh hτ
  obtain ⟨hhu, hτS, hh', hτ', -⟩ := periods_spB idx hs hb hx hh hτ
  have e1 : can h τ (ω v) = thA X bas idx v x := by
    rw [thA_eq_can, hτ', hh', can_trans hσ hT (UnAct.tauMat_mem (idx := idx) hs hx)]
  have e2 : hf h τ = Dict.hx X bas idx x := by
    rw [hx_eq_hf, hτ', hh', hf_trans hσ (UnAct.tauMat_mem (idx := idx) hs hx)]
  refine ⟨hhu, hτS, ?_, fun i => ⟨?_, ?_⟩, ?_⟩
  · intro z w'
    rw [← e2, map_im_inv]
    rfl
  · rw [he₁ i]; simp only [Complex.ofReal_ratCast]
  · rw [he₂ i]; simp only [Complex.ofReal_ratCast]
  · intro z
    rw [← e1, hC, can_smul]
    simp only [can, map_im_inv]
    rw [CharLink.thS_chi _ _ hτS.2, Finset.mul_sum, Complex.exp_sum, Finset.prod_mul_distrib]
    ring

end GlobalTheory.Dict.VacForm
