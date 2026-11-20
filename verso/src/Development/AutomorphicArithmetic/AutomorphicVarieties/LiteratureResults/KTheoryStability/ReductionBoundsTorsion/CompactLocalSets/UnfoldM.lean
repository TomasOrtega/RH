import Mathlib

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexOrder

namespace PositivityTheory.KB.LocalOverlapAverage

/- English proof (translation)
Use `set U : Matrix n n ℂ := (hQ.1.eigenvectorUnitary : Matrix n n ℂ)`. Use `set D : Matrix n n ℂ := diagonal (fun i => ((Real.sqrt (hQ.1.eigenvalues i) : ℝ) : ℂ))`. Use `⟨D * star U, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [hQ.1.spectral_theorem, Unitary.conjStarAlgAut_apply]`. Establish `hU : (star U)ᴴ = U` using `by rw [star_eq_conjTranspose, conjTranspose_conjTranspose]`.

Establish `hD : Dᴴ * D = diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues)`. Simplify using `only [D, diagonal_conjTranspose, diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.star_apply, Function.comp, RCLike.star_def, Complex.conj_ofReal]`.

Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (hQ.eigenvalues_pos i).le]`. Both sides reduce to the same expression. Rewrite using `[conjTranspose_mul, hU, Matrix.mul_assoc, ← Matrix.mul_assoc Dᴴ, hD, ← Matrix.mul_assoc]`.
-/
theorem fac_exists {n : Type} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosDef) :
    ∃ B : Matrix n n ℂ, Bᴴ * B = Q := by
  set U : Matrix n n ℂ := (hQ.1.eigenvectorUnitary : Matrix n n ℂ)
  set D : Matrix n n ℂ := diagonal (fun i => ((Real.sqrt (hQ.1.eigenvalues i) : ℝ) : ℂ))
  refine ⟨D * star U, ?_⟩
  conv_rhs => rw [hQ.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  have hU : (star U)ᴴ = U := by rw [star_eq_conjTranspose, conjTranspose_conjTranspose]
  have hD : Dᴴ * D = diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues) := by
    simp only [D, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, Function.comp, RCLike.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hQ.eigenvalues_pos i).le]
    rfl
  rw [conjTranspose_mul, hU, Matrix.mul_assoc, ← Matrix.mul_assoc Dᴴ, hD, ← Matrix.mul_assoc]

/- English proof (translation)
Take `⟨B, hB⟩` from `fac_exists hQ`. Establish `hdet : IsUnit B.det`. Establish `h1 : Q.det ≠ 0` using `(hQ.det_pos).ne'`. Rewrite `h1` using `[← hB, det_mul, det_conjTranspose]`. Conclude with `isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h1)`.

Establish `hBu : IsUnit B` using `(isUnit_iff_isUnit_det B).mpr hdet`. Use `⟨hBu.unit⁻¹, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hB`. Rewrite using `[coe_units_inv, IsUnit.unit_spec, ← hB, Matrix.mul_inv_rev, conjTranspose_nonsing_inv]`.
-/
theorem gl_fac_exists {n : Type} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosDef) :
    ∃ Y : GL n ℂ, ((Y⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ * ((Y⁻¹ : GL n ℂ) : Matrix n n ℂ) = Q ∧
      (Y : Matrix n n ℂ) * (Y : Matrix n n ℂ)ᴴ = Q⁻¹ := by
  obtain ⟨B, hB⟩ := fac_exists hQ
  have hdet : IsUnit B.det := by
    have h1 : Q.det ≠ 0 := (hQ.det_pos).ne'
    rw [← hB, det_mul, det_conjTranspose] at h1
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h1)
  have hBu : IsUnit B := (isUnit_iff_isUnit_det B).mpr hdet
  refine ⟨hBu.unit⁻¹, ?_, ?_⟩
  · simpa using hB
  · rw [coe_units_inv, IsUnit.unit_spec, ← hB, Matrix.mul_inv_rev, conjTranspose_nonsing_inv]

/- English proof (translation)
Establish `h : (Y * Yᴴ) i i = ((∑ k, ‖Y i k‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[mul_apply, Complex.ofReal_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[conjTranspose_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite using `[h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => by positivity)]`.

Conclude with `Finset.single_le_sum (f := fun k => ‖Y i k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)`.
-/
theorem norm_sq_le_diag {n : Type} [Fintype n] (Y : Matrix n n ℂ) (i j : n) :
    ‖Y i j‖ ^ 2 ≤ ‖(Y * Yᴴ) i i‖ := by
  have h : (Y * Yᴴ) i i = ((∑ k, ‖Y i k‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conjTranspose_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => by positivity)]
  exact Finset.single_le_sum (f := fun k => ‖Y i k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)

/- English proof (translation)
Take `⟨c, hc⟩` from `IsAlgClosed.exists_pow_nat_eq (Y : Matrix (Fin N) (Fin N) ℂ).det (by omega : 0 < N)`. Establish `hY : (Y : Matrix (Fin N) (Fin N) ℂ).det ≠ 0` using `(Matrix.isUnits_det_units Y).ne_zero`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hc` using `[zero_pow (by omega)]`.

Conclude with `hY hc.symm`. Establish `hdetT : (c⁻¹ • (Y : Matrix (Fin N) (Fin N) ℂ)).det = 1`. Rewrite using `[det_smul, Fintype.card_fin, inv_pow, hc, inv_mul_cancel₀ hY]`. Set `T : SpecialLinearGroup (Fin N) ℂ` to `⟨c⁻¹ • (Y : Matrix (Fin N) (Fin N) ℂ), hdetT⟩`. Establish `hT : ((SpecialLinearGroup.toGL T : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = c⁻¹ • (Y : Matrix (Fin N) (Fin N) ℂ)` using `rfl`.

Use `⟨Units.mk0 c hc0, T, ?_, by simpa using hc⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [GeneralLinearGroup.scalar, Units.val_mul, hT]`. Simplify using the standard rewrite rules. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hc0, one_mul]`.
-/
theorem sl_dec {N : ℕ} (hN : 1 ≤ N) (Y : GL (Fin N) ℂ) :
    ∃ (c : ℂˣ) (T : SpecialLinearGroup (Fin N) ℂ),
      Y = GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T ∧ (c : ℂ) ^ N = (Y : Matrix (Fin N) (Fin N) ℂ).det := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (Y : Matrix (Fin N) (Fin N) ℂ).det (by omega : 0 < N)
  have hY : (Y : Matrix (Fin N) (Fin N) ℂ).det ≠ 0 := (Matrix.isUnits_det_units Y).ne_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hc
    exact hY hc.symm
  have hdetT : (c⁻¹ • (Y : Matrix (Fin N) (Fin N) ℂ)).det = 1 := by
    rw [det_smul, Fintype.card_fin, inv_pow, hc, inv_mul_cancel₀ hY]
  let T : SpecialLinearGroup (Fin N) ℂ := ⟨c⁻¹ • (Y : Matrix (Fin N) (Fin N) ℂ), hdetT⟩
  have hT : ((SpecialLinearGroup.toGL T : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      c⁻¹ • (Y : Matrix (Fin N) (Fin N) ℂ) := rfl
  refine ⟨Units.mk0 c hc0, T, ?_, by simpa using hc⟩
  ext i j
  simp only [GeneralLinearGroup.scalar, Units.val_mul, hT]
  simp
  rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

/- English proof (translation)
Establish `hE : Topology.IsClosedEmbedding (fun x : ι → SpecialLinearGroup n ℂ => fun w => (x w : Matrix n n ℂ))` using `Topology.IsClosedEmbedding.piMap fun _ => SpecialLinearGroup.isClosedEmbedding_val`. Establish `hC : IsCompact (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n => Metric.closedBall (0 : ℂ) R)` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Use `hE.isCompact_preimage hC using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Conclude with `⟨fun h w _ i _ j _ => by simpa using h w i j, fun h w i j => by simpa using h w trivial i trivial j trivial⟩`.
-/
theorem isCompact_bddSL {ι : Type} [Fintype ι] {n : Type} [Fintype n] [DecidableEq n] (R : ℝ) :
    IsCompact {x : ι → SpecialLinearGroup n ℂ | ∀ w i j, ‖(x w : Matrix n n ℂ) i j‖ ≤ R} := by
  have hE : Topology.IsClosedEmbedding (fun x : ι → SpecialLinearGroup n ℂ => fun w => (x w : Matrix n n ℂ)) :=
    Topology.IsClosedEmbedding.piMap fun _ => SpecialLinearGroup.isClosedEmbedding_val
  have hC : IsCompact (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n =>
      Metric.closedBall (0 : ℂ) R) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  convert hE.isCompact_preimage hC using 1
  ext x
  exact ⟨fun h w _ i _ j _ => by simpa using h w i j, fun h w i j => by simpa using h w trivial i trivial j trivial⟩

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[GeneralLinearGroup.scalar]`.
-/
theorem coe_scal_mul {n : Type} [Fintype n] [DecidableEq n] (c : ℂˣ) (T : SpecialLinearGroup n ℂ) :
    ((GeneralLinearGroup.scalar n c * SpecialLinearGroup.toGL T : GL n ℂ) : Matrix n n ℂ) =
      (c : ℂ) • (T : Matrix n n ℂ) := by
  ext i j
  simp [GeneralLinearGroup.scalar]

/- English proof (translation)
Use `set a : ℝ := max 1 R2`. Use `set R3' : ℝ := max R3 1`. Use `set m : ℝ := min 1 R3'⁻¹`. Establish `hR3' : 0 < R3'` using `lt_of_lt_of_le one_pos (le_max_right _ _)`. Establish `hm : 0 < m` using `lt_min one_pos (inv_pos.mpr hR3')`.

Establish `ha : 0 ≤ a` using `le_trans zero_le_one (le_max_left _ _)`. Use `⟨a / m, div_nonneg ha hm.le, fun Q hQ h2 h3 => ?_⟩` and prove the remaining obligations. Take `⟨Y, hY1, hY2⟩` from `gl_fac_exists hQ`. Take `⟨c, T, hYd, hc⟩` from `sl_dec hN Y`. Substitute `hYd` using the available equality.

Use `⟨c, T, hY1, ?_⟩` and prove the remaining obligations. Establish `hYb : ∀ i j, ‖((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ a`. Introduce `i j`. Establish `h` using `norm_sq_le_diag ((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j`. Rewrite `h` using `[hY2]`.

Establish `h'` using `h.trans (h2 i i)`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `h1 : 1 < ‖((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖` using `lt_of_le_of_lt (le_max_left _ _) hlt`. Use polynomial arithmetic with `[le_max_right 1 R2]`.

Use `set Y : GL (Fin N) ℂ := GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T with hYdef`. Establish `hdQ : ‖Q.det‖ = ‖((Y⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).det‖ ^ 2`. Rewrite using `[← hY1, det_mul, det_conjTranspose, norm_mul, norm_star, sq]`. Establish `hYY : ‖(Y : Matrix (Fin N) (Fin N) ℂ).det‖ * ‖((Y⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).det‖ = 1`. Rewrite using `[← norm_mul, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, norm_one]`.

Establish `hcN : ‖(c : ℂ)‖ ^ N = ‖(Y : Matrix (Fin N) (Fin N) ℂ).det‖` using `by rw [← norm_pow, hc]`. Establish `hQpos : 0 < ‖Q.det‖` using `norm_pos_iff.mpr hQ.det_pos.ne'`. Establish `hc2 : ‖(c : ℂ)‖ ^ (2 * N) * ‖Q.det‖ = 1`. Rewrite using `[pow_mul', hcN, hdQ, ← mul_pow, hYY, one_pow]`. Establish `hcm : m ≤ ‖(c : ℂ)‖`.

Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `hc1 : ‖(c : ℂ)‖ ≤ 1` using `hlt.le.trans (min_le_left _ _)`. Establish `hpow : ‖(c : ℂ)‖ ^ (2 * N) ≤ ‖(c : ℂ)‖` using `pow_le_of_le_one (norm_nonneg _) hc1 (by omega)`. Establish `hle : ‖Q.det‖ ≤ R3'` using `h3.trans (le_max_left _ _)`.

Establish `: ‖(c : ℂ)‖ ^ (2 * N) * ‖Q.det‖ < 1`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨fun i j => (hYb i j).trans (le_div_self ha hm ?_), fun i j => ?_⟩` and prove the remaining obligations. Conclude with `min_le_left _ _`.

Establish `hcT : (Y : Matrix (Fin N) (Fin N) ℂ) i j = (c : ℂ) * (T : Matrix (Fin N) (Fin N) ℂ) i j`. Rewrite using `[hYdef, coe_scal_mul]`. Both sides reduce to the same expression. Establish `hc0 : 0 < ‖(c : ℂ)‖` using `lt_of_lt_of_le hm hcm`. Establish `: ‖(T : Matrix (Fin N) (Fin N) ℂ) i j‖ = ‖(Y : Matrix (Fin N) (Fin N) ℂ) i j‖ / ‖(c : ℂ)‖`.

Rewrite using `[hcT, norm_mul, mul_div_cancel_left₀ _ hc0.ne']`. Rewrite using `[this]`. Conclude with `div_le_div₀ ha (hYb i j) hm hcm`.
-/
theorem dec_bdd {N : ℕ} (hN : 1 ≤ N) (R2 R3 : ℝ) : ∃ R : ℝ, 0 ≤ R ∧
    ∀ Q : Matrix (Fin N) (Fin N) ℂ, Q.PosDef → (∀ i j, ‖Q⁻¹ i j‖ ≤ R2) → ‖Q.det‖ ≤ R3 →
      ∃ (c : ℂˣ) (T : SpecialLinearGroup (Fin N) ℂ),
        ((((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T)⁻¹ : GL (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)ᴴ *
          (((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T)⁻¹ : GL (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ) = Q) ∧
        (∀ i j, ‖((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T : GL (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R) ∧
        ∀ i j, ‖(T : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R := by
  set a : ℝ := max 1 R2
  set R3' : ℝ := max R3 1
  set m : ℝ := min 1 R3'⁻¹
  have hR3' : 0 < R3' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hm : 0 < m := lt_min one_pos (inv_pos.mpr hR3')
  have ha : 0 ≤ a := le_trans zero_le_one (le_max_left _ _)
  refine ⟨a / m, div_nonneg ha hm.le, fun Q hQ h2 h3 => ?_⟩
  obtain ⟨Y, hY1, hY2⟩ := gl_fac_exists hQ
  obtain ⟨c, T, hYd, hc⟩ := sl_dec hN Y
  subst hYd
  refine ⟨c, T, hY1, ?_⟩

  have hYb : ∀ i j, ‖((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T : GL (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ a := by
    intro i j
    have h := norm_sq_le_diag ((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T : GL (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) i j
    rw [hY2] at h
    have h' := h.trans (h2 i i)
    by_contra hlt
    rw [not_le] at hlt
    have h1 : 1 < ‖((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T : GL (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) i j‖ := lt_of_le_of_lt (le_max_left _ _) hlt
    nlinarith [le_max_right 1 R2]

  set Y : GL (Fin N) ℂ := GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T with hYdef
  have hdQ : ‖Q.det‖ = ‖((Y⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).det‖ ^ 2 := by
    rw [← hY1, det_mul, det_conjTranspose, norm_mul, norm_star, sq]
  have hYY : ‖(Y : Matrix (Fin N) (Fin N) ℂ).det‖ * ‖((Y⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).det‖ = 1 := by
    rw [← norm_mul, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, norm_one]
  have hcN : ‖(c : ℂ)‖ ^ N = ‖(Y : Matrix (Fin N) (Fin N) ℂ).det‖ := by rw [← norm_pow, hc]
  have hQpos : 0 < ‖Q.det‖ := norm_pos_iff.mpr hQ.det_pos.ne'
  have hc2 : ‖(c : ℂ)‖ ^ (2 * N) * ‖Q.det‖ = 1 := by
    rw [pow_mul', hcN, hdQ, ← mul_pow, hYY, one_pow]
  have hcm : m ≤ ‖(c : ℂ)‖ := by
    by_contra hlt
    rw [not_le] at hlt
    have hc1 : ‖(c : ℂ)‖ ≤ 1 := hlt.le.trans (min_le_left _ _)
    have hpow : ‖(c : ℂ)‖ ^ (2 * N) ≤ ‖(c : ℂ)‖ := pow_le_of_le_one (norm_nonneg _) hc1 (by omega)
    have hle : ‖Q.det‖ ≤ R3' := h3.trans (le_max_left _ _)
    have : ‖(c : ℂ)‖ ^ (2 * N) * ‖Q.det‖ < 1 := by
      calc ‖(c : ℂ)‖ ^ (2 * N) * ‖Q.det‖ ≤ ‖(c : ℂ)‖ * R3' :=
            mul_le_mul hpow hle hQpos.le (norm_nonneg _)
        _ < m * R3' := mul_lt_mul_of_pos_right hlt hR3'
        _ ≤ R3'⁻¹ * R3' := mul_le_mul_of_nonneg_right (min_le_right _ _) hR3'.le
        _ = 1 := inv_mul_cancel₀ hR3'.ne'
    linarith
  refine ⟨fun i j => (hYb i j).trans (le_div_self ha hm ?_), fun i j => ?_⟩
  · exact min_le_left _ _
  · have hcT : (Y : Matrix (Fin N) (Fin N) ℂ) i j = (c : ℂ) * (T : Matrix (Fin N) (Fin N) ℂ) i j := by
      rw [hYdef, coe_scal_mul]; rfl
    have hc0 : 0 < ‖(c : ℂ)‖ := lt_of_lt_of_le hm hcm
    have : ‖(T : Matrix (Fin N) (Fin N) ℂ) i j‖ = ‖(Y : Matrix (Fin N) (Fin N) ℂ) i j‖ / ‖(c : ℂ)‖ := by
      rw [hcT, norm_mul, mul_div_cancel_left₀ _ hc0.ne']
    rw [this]
    exact div_le_div₀ ha (hYb i j) hm hcm

/- English proof (translation)
Use `set E : V ≃ᵐ V := e.toHomeomorph.toMeasurableEquiv`. Establish `hE : ∀ x, E x = e x` using `fun _ => rfl`. Establish `hdet : LinearMap.det ((e : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0` using `(LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero`. Establish `hmap : Measure.map E μ = ENNReal.ofReal |(LinearMap.det ((e : V →L[ℝ] V) : V →ₗ[ℝ] V))⁻¹| • μ`. Rewrite using `[← Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet]`.

Both sides reduce to the same expression. Establish `h1 : ∫⁻ q in S, G (e q) ∂μ = ∫⁻ p in e '' S, G p ∂(Measure.map E μ)`. Rewrite using `[MeasurableEquiv.restrict_map]`. Establish `hpre : E ⁻¹' (e '' S) = S`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage, hE, Set.mem_image]`. Conclude with `⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩`. Rewrite using `[hpre, lintegral_map_equiv]`. Both sides reduce to the same expression. Rewrite using `[h1, hmap, Measure.restrict_smul, lintegral_smul_measure]`.

Conclude with `mul_le_mul_right (lintegral_mono_set hK) _`.
-/
theorem lintegral_cle_ge {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (e : V ≃L[ℝ] V)
    (S K : Set V) (hK : K ⊆ e '' S) (G : V → ℝ≥0∞) :
    ENNReal.ofReal |(LinearMap.det ((e : V →L[ℝ] V) : V →ₗ[ℝ] V))⁻¹| * ∫⁻ p in K, G p ∂μ ≤
      ∫⁻ q in S, G (e q) ∂μ := by
  set E : V ≃ᵐ V := e.toHomeomorph.toMeasurableEquiv
  have hE : ∀ x, E x = e x := fun _ => rfl
  have hdet : LinearMap.det ((e : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0 :=
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hmap : Measure.map E μ = ENNReal.ofReal |(LinearMap.det ((e : V →L[ℝ] V) : V →ₗ[ℝ] V))⁻¹| • μ := by
    rw [← Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet]
    rfl
  have h1 : ∫⁻ q in S, G (e q) ∂μ = ∫⁻ p in e '' S, G p ∂(Measure.map E μ) := by
    rw [MeasurableEquiv.restrict_map]
    have hpre : E ⁻¹' (e '' S) = S := by
      ext x
      simp only [Set.mem_preimage, hE, Set.mem_image]
      exact ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
    rw [hpre, lintegral_map_equiv]
    rfl
  rw [h1, hmap, Measure.restrict_smul, lintegral_smul_measure]
  exact mul_le_mul_right (lintegral_mono_set hK) _

end PositivityTheory.KB.LocalOverlapAverage

end
