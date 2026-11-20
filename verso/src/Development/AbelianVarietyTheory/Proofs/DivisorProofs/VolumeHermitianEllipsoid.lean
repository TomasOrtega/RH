import Mathlib
open MeasureTheory
open scoped ComplexOrder

namespace GlobalTheory

open Matrix
open scoped MatrixOrder

/- English proof (translation)
Establish `h0 : 0 ≤ G` using `hG.posSemidef.nonneg`. Use `⟨CFC.sqrt G, ?_⟩` and prove the remaining obligations. Establish `hs : IsSelfAdjoint (CFC.sqrt G)` using `(CFC.sqrt_nonneg G).isSelfAdjoint`. Rewrite using `[show (CFC.sqrt G)ᴴ = CFC.sqrt G from hs.star_eq, CFC.sqrt_mul_sqrt_self G h0]`.
-/
private lemma ellvol_factor {g : ℕ} {G : Matrix (Fin g) (Fin g) ℂ} (hG : G.PosDef) :
    ∃ B : Matrix (Fin g) (Fin g) ℂ, G = Bᴴ * B := by
  have h0 : 0 ≤ G := hG.posSemidef.nonneg
  refine ⟨CFC.sqrt G, ?_⟩
  have hs : IsSelfAdjoint (CFC.sqrt G) := (CFC.sqrt_nonneg G).isSelfAdjoint
  rw [show (CFC.sqrt G)ᴴ = CFC.sqrt G from hs.star_eq, CFC.sqrt_mul_sqrt_self G h0]

/- English proof (translation)
Establish `h1 : w ⬝ᵥ Hm *ᵥ star w = star (B *ᵥ w) ⬝ᵥ (B *ᵥ w)`. Rewrite using `[dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, hB, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]`. Rewrite using `[h1, dotProduct, Complex.re_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.star_apply, Complex.star_def, Complex.conj_mul']`.

Use `norm_cast`.
-/
private lemma ellvol_form {g : ℕ} (Hm B : Matrix (Fin g) (Fin g) ℂ) (hB : Hmᵀ = Bᴴ * B)
    (w : Fin g → ℂ) : (w ⬝ᵥ Hm *ᵥ star w).re = ∑ k, ‖(B *ᵥ w) k‖ ^ 2 := by
  have h1 : w ⬝ᵥ Hm *ᵥ star w = star (B *ᵥ w) ⬝ᵥ (B *ᵥ w) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, hB, ← mulVec_mulVec,
      dotProduct_mulVec, star_mulVec]
  rw [h1, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast

/- English proof (translation)
Use `haveI : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩`. Establish `hset : {v : Fin g → ℂ | ∑ k, ‖v k‖ ^ 2 < r ^ 2} = {x : Fin g → ℂ | (∑ i, ‖x i‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) < r}`. Use extensionality with `v`. Simplify using `only [Set.mem_setOf_eq, Real.rpow_two]`. Establish `h0 : 0 ≤ ∑ i, ‖v i‖ ^ 2` using `by positivity`.

Rewrite using `[← Real.sqrt_eq_rpow, Real.sqrt_lt' hr]`. Rewrite using `[hset, Complex.volume_sum_rpow_lt (Fin g) (by norm_num) r]`. Establish `e1 : (2:ℝ) / 2 + 1 = 2` using `by norm_num`. Establish `e2 : 2 * (Fintype.card (Fin g) : ℝ) / 2 + 1 = (g : ℝ) + 1`. Rewrite using `[Fintype.card_fin]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, Real.Gamma_two, Real.Gamma_nat_eq_factorial, Fintype.card_fin, mul_one, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma ellvol_ball {g : ℕ} (hg : 0 < g) {r : ℝ} (hr : 0 < r) :
    volume {v : Fin g → ℂ | ∑ k, ‖v k‖ ^ 2 < r ^ 2} =
      ENNReal.ofReal (Real.pi ^ g * r ^ (2 * g) / g.factorial) := by
  haveI : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
  have hset : {v : Fin g → ℂ | ∑ k, ‖v k‖ ^ 2 < r ^ 2} =
      {x : Fin g → ℂ | (∑ i, ‖x i‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) < r} := by
    ext v
    simp only [Set.mem_setOf_eq, Real.rpow_two]
    have h0 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := by positivity
    rw [← Real.sqrt_eq_rpow, Real.sqrt_lt' hr]
  rw [hset, Complex.volume_sum_rpow_lt (Fin g) (by norm_num) r]
  have e1 : (2:ℝ) / 2 + 1 = 2 := by norm_num
  have e2 : 2 * (Fintype.card (Fin g) : ℝ) / 2 + 1 = (g : ℝ) + 1 := by
    rw [Fintype.card_fin]; ring
  rw [e1, e2, Real.Gamma_two, Real.Gamma_nat_eq_factorial, Fintype.card_fin, mul_one,
    ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/- English proof (translation)
Introduce `g Hm r hH hr`. Take `⟨B, hB⟩` from `ellvol_factor hH.transpose`. Establish `hdet : Hm.det = (Complex.normSq B.det : ℂ)`. Rewrite using `[← det_transpose, hB, det_mul, det_conjTranspose, Complex.normSq_eq_conj_mul_self]`. Both sides reduce to the same expression.

Establish `hd : 0 < Complex.normSq B.det`. Use `hH.det_pos` as an intermediate fact. Rewrite `this` using `[hdet, Complex.zero_lt_real]`. Then use the resulting hypothesis. Establish `hre : Hm.det.re = Complex.normSq B.det` using `by rw [hdet, Complex.ofReal_re]`. Establish `hset : {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2} = ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' {v : Fin g → ℂ | ∑ k, ‖v k‖ ^ 2 < r ^ 2}`.

Use extensionality with `w`. Simplify using `[ellvol_form Hm B hB w, Matrix.toLin'_apply]`. Establish `hdetL : LinearMap.det ((Matrix.toLin' B).restrictScalars ℝ) = Complex.normSq B.det`. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]`. Rewrite using `[hset, Measure.addHaar_preimage_linearMap _ (by rw [hdetL]; exact hd.ne'), hdetL, hre]`.

Break down `Nat.eq_zero_or_pos g with rfl | hg` into its components or cases. Establish `hu : {v : Fin 0 → ℂ | ∑ k, ‖v k‖ ^ 2 < r ^ 2} = Set.univ`. Use extensionality with `v`. Simplify using `[hr.ne', sq_pos_of_pos hr]`. Establish `h1 : Complex.normSq B.det = 1` using `by simp`.

Rewrite using `[hu, h1, ← Set.pi_univ Set.univ, volume_pi_pi]`. Simplify using the standard rewrite rules. Rewrite using `[ellvol_ball hg hr, ← ENNReal.ofReal_mul (abs_nonneg _)]`. Use `congr 1`. Rewrite using `[abs_of_pos (inv_pos.mpr hd)]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem volume_hermitian_ellipsoid : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (r : ℝ), Hm.PosDef → 0 < r →
    volume {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2} =
      ENNReal.ofReal (Real.pi ^ g * r ^ (2 * g) / (g.factorial * Hm.det.re)) := by
  intro g Hm r hH hr
  obtain ⟨B, hB⟩ := ellvol_factor hH.transpose
  have hdet : Hm.det = (Complex.normSq B.det : ℂ) := by
    rw [← det_transpose, hB, det_mul, det_conjTranspose, Complex.normSq_eq_conj_mul_self]; rfl
  have hd : 0 < Complex.normSq B.det := by
    have := hH.det_pos; rwa [hdet, Complex.zero_lt_real] at this
  have hre : Hm.det.re = Complex.normSq B.det := by rw [hdet, Complex.ofReal_re]
  have hset : {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2} =
      ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' {v : Fin g → ℂ | ∑ k, ‖v k‖ ^ 2 < r ^ 2} := by
    ext w
    simp [ellvol_form Hm B hB w, Matrix.toLin'_apply]
  have hdetL : LinearMap.det ((Matrix.toLin' B).restrictScalars ℝ) = Complex.normSq B.det := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  rw [hset, Measure.addHaar_preimage_linearMap _ (by rw [hdetL]; exact hd.ne'), hdetL, hre]
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · have hu : {v : Fin 0 → ℂ | ∑ k, ‖v k‖ ^ 2 < r ^ 2} = Set.univ := by
      ext v; simp [hr.ne', sq_pos_of_pos hr]
    have h1 : Complex.normSq B.det = 1 := by simp
    rw [hu, h1, ← Set.pi_univ Set.univ, volume_pi_pi]
    simp
  · rw [ellvol_ball hg hr, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [abs_of_pos (inv_pos.mpr hd)]
    field_simp

end GlobalTheory
