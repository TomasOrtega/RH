import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LintegralProdPartialSums

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal Nat

namespace GlobalTheory.HuaIntegral

open GlobalTheory.FlagVolume

/- English proof (translation)
Use `open scoped MatrixOrder in`. Take `⟨R, hR⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.posSemidef.nonneg`. Use `⟨R, fun h0 => ?_, hR⟩` and prove the remaining obligations. Use `hA.det_pos.ne'` as an intermediate fact. Rewrite `this` using `[hR, det_mul, h0, mul_zero]`.

Conclude with `this rfl`.
-/
theorem exists_factor {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) :
    ∃ R : Matrix (Fin q) (Fin q) ℂ, R.det ≠ 0 ∧ A = Rᴴ * R := by
  open scoped MatrixOrder in
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.posSemidef.nonneg
  refine ⟨R, fun h0 => ?_, hR⟩
  have := hA.det_pos.ne'
  rw [hR, det_mul, h0, mul_zero] at this
  exact this rfl

/- English proof (translation)
Rewrite using `[det_mul, det_conjTranspose, RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]`.
-/
theorem det_conjTranspose_mul_re {q : ℕ} (R : Matrix (Fin q) (Fin q) ℂ) : (Rᴴ * R).det.re = ‖R.det‖ ^ 2 := by
  rw [det_mul, det_conjTranspose, RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/- English proof (translation)
Establish `h : Rᴴ * R + vecMulVec (star (vecMul y R)) (vecMul y R) = Rᴴ * (1 + replicateCol Unit (star y) * replicateRow Unit y) * R`. Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ R, ← replicateCol_mulVec, ← replicateRow_vecMul, ← star_vecMul, vecMulVec_eq Unit]`. Establish `h2 : (1 + y ⬝ᵥ star y : ℂ) = ((1 + ∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ)`. Simplify using `[dotProduct, Complex.mul_conj']`. Rewrite using `[h, det_mul, det_mul, det_one_add_replicateCol_mul_replicateRow, mul_right_comm, ← det_mul, h2, Complex.re_mul_ofReal, det_conjTranspose_mul_re]`.
-/
theorem det_add_row {q : ℕ} (R : Matrix (Fin q) (Fin q) ℂ) (y : Fin q → ℂ) :
    (Rᴴ * R + vecMulVec (star (vecMul y R)) (vecMul y R)).det.re = ‖R.det‖ ^ 2 * (1 + ∑ k, ‖y k‖ ^ 2) := by
  have h : Rᴴ * R + vecMulVec (star (vecMul y R)) (vecMul y R) =
      Rᴴ * (1 + replicateCol Unit (star y) * replicateRow Unit y) * R := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ _ R, ← replicateCol_mulVec, ← replicateRow_vecMul, ← star_vecMul, vecMulVec_eq Unit]
  have h2 : (1 + y ⬝ᵥ star y : ℂ) = ((1 + ∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ) := by
    simp [dotProduct, Complex.mul_conj']
  rw [h, det_mul, det_mul, det_one_add_replicateCol_mul_replicateRow, mul_right_comm, ← det_mul, h2,
    Complex.re_mul_ofReal, det_conjTranspose_mul_re]

/- English proof (translation)
Take `⟨R, hR, rfl⟩` from `exists_factor hA`. Establish `hc : Continuous fun u : Fin q → ℂ => (Rᴴ * R + vecMulVec (star u) u).det.re`. Use `Complex.continuous_re.comp (Continuous.matrix_det (continuous_const.add ?_))` and prove the remaining obligations. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [vecMulVec_apply, Pi.star_apply]`.

Use `fun_prop`. Establish `hp : 0 < ‖R.det‖ ^ 2` using `by positivity`. Rewrite using `[lintegral_comp_vecMul R hR (by exact (hc.measurable.pow_const _).inv.ennreal_ofReal), det_conjTranspose_mul_re]`. Simplify using `only [det_add_row, mul_pow, mul_inv, ENNReal.ofReal_mul (show 0 ≤ ((‖R.det‖ ^ 2) ^ (m + q + 1))⁻¹ by positivity)]`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_pi_inv_pow q m one_pos, ← mul_assoc, ← ENNReal.ofReal_mul hp.le]`.

Use `congr 2`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem lintegral_add_row {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) (m : ℕ) :
    ∫⁻ u : Fin q → ℂ, ENNReal.ofReal (((A + vecMulVec (star u) u).det.re ^ (m + q + 1))⁻¹) =
      ENNReal.ofReal ((A.det.re ^ (m + q))⁻¹) * ENNReal.ofReal (Real.pi ^ q * m ! / (m + q)!) := by
  obtain ⟨R, hR, rfl⟩ := exists_factor hA
  have hc : Continuous fun u : Fin q → ℂ => (Rᴴ * R + vecMulVec (star u) u).det.re := by
    refine Complex.continuous_re.comp (Continuous.matrix_det (continuous_const.add ?_))
    refine continuous_matrix fun i j => ?_
    simp only [vecMulVec_apply, Pi.star_apply]
    fun_prop
  have hp : 0 < ‖R.det‖ ^ 2 := by positivity
  rw [lintegral_comp_vecMul R hR (by exact (hc.measurable.pow_const _).inv.ennreal_ofReal), det_conjTranspose_mul_re]
  simp only [det_add_row, mul_pow, mul_inv,
    ENNReal.ofReal_mul (show 0 ≤ ((‖R.det‖ ^ 2) ^ (m + q + 1))⁻¹ by positivity)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_pi_inv_pow q m one_pos, ← mul_assoc,
    ← ENNReal.ofReal_mul hp.le]
  congr 2
  · field_simp
    ring
  · simp

def rowSucc (p q : ℕ) : (Fin p × Fin q) ⊕ Fin q → Fin (p + 1) × Fin q
  | .inl a => (a.1.castSucc, a.2)
  | .inr j => (Fin.last p, j)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `rintro (⟨a, b⟩ | j) (⟨a', b'⟩ | j') hh <;>`. Simplify using `[rowSucc, (Fin.castSucc_ne_last _).symm]`. Introduce and unpack `⟨a, b⟩`. Proceed by induction on `a using Fin.lastCases with`.

Consider the case `last => exact ⟨.inr b, rfl⟩`. Consider the case `cast a => exact ⟨.inl (a, b), rfl⟩`.
-/
theorem rowSucc_bijective (p q : ℕ) : Function.Bijective (rowSucc p q) := by
  constructor
  · rintro (⟨a, b⟩ | j) (⟨a', b'⟩ | j') hh <;>
      simp_all [rowSucc, (Fin.castSucc_ne_last _).symm]
  · rintro ⟨a, b⟩
    induction a using Fin.lastCases with
    | last => exact ⟨.inr b, rfl⟩
    | cast a => exact ⟨.inl (a, b), rfl⟩

/- English proof (translation)
Set `e` to `Equiv.ofBijective _ (rowSucc_bijective p q)`. Use `⟨_, (volume_measurePreserving_piCongrLeft (fun _ ↦ ℂ) e).comp (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ ↦ ℂ)), fun u b ↦ ⟨fun a c ↦ ?_, fun j ↦ ?_⟩⟩` and prove the remaining obligations. Conclude with `MeasurableEquiv.piCongrLeft_apply_apply e _ (.inl (a, c))`. Conclude with `MeasurableEquiv.piCongrLeft_apply_apply e _ (.inr j)`.
-/
theorem exists_measurePreserving_rowSucc (p q : ℕ) :
    ∃ Φ : (Fin p × Fin q → ℂ) × (Fin q → ℂ) → (Fin (p + 1) × Fin q → ℂ),
      MeasurePreserving Φ ∧ ∀ v u, (∀ a b, Φ (v, u) (a.castSucc, b) = v (a, b)) ∧
        ∀ j, Φ (v, u) (Fin.last p, j) = u j := by
  let e := Equiv.ofBijective _ (rowSucc_bijective p q)
  refine ⟨_, (volume_measurePreserving_piCongrLeft (fun _ ↦ ℂ) e).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ ↦ ℂ)), fun u b ↦
    ⟨fun a c ↦ ?_, fun j ↦ ?_⟩⟩
  · exact MeasurableEquiv.piCongrLeft_apply_apply e _ (.inl (a, c))
  · exact MeasurableEquiv.piCongrLeft_apply_apply e _ (.inr j)

/- English proof (translation)
Establish `hm : ∀ p s : ℕ, Measurable fun v : Fin p × Fin q → ℂ => ENNReal.ofReal (((1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).det.re ^ s)⁻¹)`. Introduce `p s`. Establish `hc : Continuous fun v : Fin p × Fin q → ℂ => (Matrix.of fun a b => v (a, b))` using `continuous_matrix fun i j => by simp only [of_apply]; fun_prop`. Conclude with `((Complex.continuous_re.comp (continuous_const.add (hc.matrix_conjTranspose.matrix_mul hc)).matrix_det).measurable.pow_const s).inv.ennreal_ofReal`. Proceed by induction on `p with`.

Consider the case `zero => simp [volume_pi]`. Consider the case `succ p ih`. Take `⟨Φ, hΦ, hΦ'⟩` from `exists_measurePreserving_rowSucc p q`. Rewrite using `[← hΦ.lintegral_comp (hm _ _), Measure.volume_eq_prod, lintegral_prod _ (by exact ((hm _ _).comp hΦ.measurable).aemeasurable)]`. Establish `h : ∀ (v : Fin p × Fin q → ℂ) (u : Fin q → ℂ), 1 + (Matrix.of fun a b => Φ (v, u) (a, b))ᴴ * (Matrix.of fun a b => Φ (v, u) (a, b)) = (1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))) + vecMulVec (star u) u`.

Introduce `v u`. Rewrite using `[add_assoc]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[mul_apply, Fin.sum_univ_castSucc, (hΦ' v u).1, (hΦ' v u).2, vecMulVec_apply]`.

Establish `hpos : ∀ v : Fin p × Fin q → ℂ, (1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).PosDef` using `fun v => PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self _)`. Simplify using `only [h, show m + (p + 1) + q = (m + p) + q + 1 by ring, lintegral_add_row (hpos _)]`. Rewrite using `[lintegral_mul_const _ (hm _ _), ih, Finset.prod_range_succ, ENNReal.ofReal_mul (by positivity)]`.
-/
theorem lintegral_det_inv_pow (m q p : ℕ) :
    ∫⁻ v : Fin p × Fin q → ℂ, ENNReal.ofReal
        (((1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).det.re ^ (m + p + q))⁻¹) =
      ENNReal.ofReal (∏ i ∈ Finset.range p, (Real.pi ^ q * (m + i)! / (m + i + q)!)) := by
  have hm : ∀ p s : ℕ, Measurable fun v : Fin p × Fin q → ℂ => ENNReal.ofReal
      (((1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).det.re ^ s)⁻¹) := by
    intro p s
    have hc : Continuous fun v : Fin p × Fin q → ℂ => (Matrix.of fun a b => v (a, b)) :=
      continuous_matrix fun i j => by simp only [of_apply]; fun_prop
    exact ((Complex.continuous_re.comp
      (continuous_const.add (hc.matrix_conjTranspose.matrix_mul hc)).matrix_det).measurable.pow_const
        s).inv.ennreal_ofReal
  induction p with
  | zero => simp [volume_pi]
  | succ p ih =>
    obtain ⟨Φ, hΦ, hΦ'⟩ := exists_measurePreserving_rowSucc p q
    rw [← hΦ.lintegral_comp (hm _ _), Measure.volume_eq_prod,
      lintegral_prod _ (by exact ((hm _ _).comp hΦ.measurable).aemeasurable)]
    have h : ∀ (v : Fin p × Fin q → ℂ) (u : Fin q → ℂ),
        1 + (Matrix.of fun a b => Φ (v, u) (a, b))ᴴ * (Matrix.of fun a b => Φ (v, u) (a, b)) =
        (1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))) + vecMulVec (star u) u := by
      intro v u
      rw [add_assoc]
      congr 1
      ext i j
      simp [mul_apply, Fin.sum_univ_castSucc, (hΦ' v u).1, (hΦ' v u).2, vecMulVec_apply]
    have hpos : ∀ v : Fin p × Fin q → ℂ,
        (1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).PosDef := fun v =>
      PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self _)
    simp only [h, show m + (p + 1) + q = (m + p) + q + 1 by ring, lintegral_add_row (hpos _)]
    rw [lintegral_mul_const _ (hm _ _), ih, Finset.prod_range_succ, ENNReal.ofReal_mul (by positivity)]

/- English proof (translation)
Introduce `p q`. Establish `h` using `lintegral_det_inv_pow 0 q p`. Simplify using `only [zero_add] at h`. Simplify using `only [_root_.zpow_neg, _root_.zpow_natCast]`. Rewrite using `[h, grassConst, inv_div, div_eq_mul_inv, ← Finset.prod_inv_distrib, mul_comm p q, pow_mul, ← Finset.card_range p, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[inv_div, add_comm q i, mul_div_assoc]`.
-/
theorem dual_mass : ∀ p q : ℕ, ∫⁻ v : Fin p × Fin q → ℂ, ENNReal.ofReal ((1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).det.re ^ (-((p + q : ℕ) : ℤ))) = ENNReal.ofReal (grassConst p q)⁻¹ := by
  intro p q
  have h := lintegral_det_inv_pow 0 q p
  simp only [zero_add] at h
  simp only [_root_.zpow_neg, _root_.zpow_natCast]
  rw [h, grassConst, inv_div, div_eq_mul_inv, ← Finset.prod_inv_distrib, mul_comm p q, pow_mul,
    ← Finset.card_range p, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [inv_div, add_comm q i, mul_div_assoc]

end GlobalTheory.HuaIntegral
