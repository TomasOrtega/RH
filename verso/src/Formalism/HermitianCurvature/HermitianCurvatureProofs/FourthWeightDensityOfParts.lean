import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth

open Matrix Formalism.FourierDecayAlt MeasureTheory
open scoped ENNReal

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Introduce `hR hL s M t φ hs hM ht hφ`. Take `⟨p, rfl⟩ : ∃ p, s = p + 1` from `⟨s - 1, by omega⟩`. Take `⟨q, rfl⟩ : ∃ q, M = q + 2` from `⟨M - 2, by omega⟩`. Establish `e1 : p + 1 - 1 = p` using `by omega`. Establish `e2 : q + 2 - 2 = q` using `by omega`.

Establish `e3 : q + 2 + (p + 1) - 2 = q + p + 1` using `by omega`. Establish `e4 : q + 2 + (p + 1) - 3 = q + p` using `by omega`. Simplify using `only [e1, e2, e3, e4]`. Use `set T := ‖t‖ with hT`. Establish `hTpos : 0 < T` using `norm_pos_iff.mpr ht`.

Establish `hsR : (0 : ℝ) < ((p + 1 : ℕ) : ℝ)` using `by positivity`. Use `set f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ (2 * p ^ 2)) * φ z with hf`. Use `set S : ℂ → ℝ≥0∞ := fun D => ((Polynomial.nthRoots (p + 1) D).map f).sum with hS`. Use `set ψ : ℂ → ℝ≥0∞ := fun D => ENNReal.ofReal (T ^ (2 * p) * ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) * (ENNReal.ofReal (‖D‖ ^ (2 * q)) * S D) with hψ`. Establish `hA : ∀ c : ℂ, ENNReal.ofReal (T ^ (2 * p * (q + p + 1)) * ‖c‖ ^ (2 * q) * (T ^ (2 * p ^ 2))⁻¹ * ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) * ((Polynomial.nthRoots (p + 1) (c * t ^ p)).map f).sum = ψ (t ^ p * c)`.

Introduce `c`. Simplify using `only [hψ, hS, mul_comm c (t ^ p)]`. Rewrite using `[← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]`. Use `congr 2`. Rewrite using `[norm_mul, norm_pow, mul_pow, ← pow_mul, ← hT]`.

Establish `: T ^ (2 * p * (q + p + 1)) = T ^ (2 * p) * T ^ (2 * p ^ 2) * T ^ (p * (2 * q))`. Rewrite using `[← pow_add, ← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Establish `hT2 : T ^ (2 * p ^ 2) ≠ 0` using `pow_ne_zero _ hTpos.ne'`. Clear the denominators using the available nonvanishing facts. Simplify using `only [hA]`. Establish `htp : t ^ p ≠ 0` using `pow_ne_zero _ ht`. Rewrite using `[hL (t ^ p) ψ htp]`.

Establish `hC : ∫⁻ D, ψ D = ENNReal.ofReal (T ^ (2 * p) * ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) * ∫⁻ D, ENNReal.ofReal (‖D‖ ^ (2 * q)) * S D`. Simplify using `only [hψ]`. Conclude with `lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`. Rewrite using `[hC, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]`. Establish `hconst : (‖t ^ p‖ ^ 2)⁻¹ * (T ^ (2 * p) * ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) = ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹`.

Rewrite using `[norm_pow, ← hT, ← pow_mul]`. Establish `: T ^ (p * 2) ≠ 0` using `pow_ne_zero _ hTpos.ne'`. Rewrite using `[mul_comm p 2]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hconst]`.

Use `set g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ (2 * (p + 1) * q + 2 * p ^ 2)) * φ z with hg`. Establish `hD : ∀ D : ℂ, ENNReal.ofReal (‖D‖ ^ (2 * q)) * S D = ((Polynomial.nthRoots (p + 1) D).map g).sum`. Introduce `D`. Simplify using `only [hS]`. Rewrite using `[← Multiset.sum_map_mul_left]`.

Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `z hz`. Rewrite `hz` using `[Polynomial.mem_nthRoots (by omega : 0 < p + 1)]`. Simplify using `only [hf, hg]`.

Rewrite using `[← hz, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), norm_pow, ← pow_mul, ← pow_add]`. Use `congr 3`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hD]`. Establish `hgm : Measurable g`.

Simplify using `only [hg]`. Conclude with `(Measurable.ennreal_ofReal ((continuous_norm.pow _).measurable)).mul hφ`. Rewrite using `[hR (p + 1) g (by omega) hgm]`. Simplify using `only [e1]`. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`.

Use `congr 1`. Use function extensionality and compare the values at `z`. Simplify using `only [hg]`. Rewrite using `[← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]`. Use `congr 2`.

Establish `hs2 : ((((p + 1 : ℕ) : ℝ)) ^ 2) ≠ 0` using `by positivity`. Rewrite using `[show (((p + 1 : ℕ) : ℝ) ^ 2)⁻¹ * (((p + 1 : ℕ) : ℝ) ^ 2 * ‖z‖ ^ (2 * p)) = ‖z‖ ^ (2 * p) by field_simp, ← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourth_weight_density_of_parts : C2.SliceDensityOfChangeOfVariables := by
  intro hR hL s M t φ hs hM ht hφ
  obtain ⟨p, rfl⟩ : ∃ p, s = p + 1 := ⟨s - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, M = q + 2 := ⟨M - 2, by omega⟩
  have e1 : p + 1 - 1 = p := by omega
  have e2 : q + 2 - 2 = q := by omega
  have e3 : q + 2 + (p + 1) - 2 = q + p + 1 := by omega
  have e4 : q + 2 + (p + 1) - 3 = q + p := by omega
  simp only [e1, e2, e3, e4]
  set T := ‖t‖ with hT
  have hTpos : 0 < T := norm_pos_iff.mpr ht
  have hsR : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := by positivity
  set f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ (2 * p ^ 2)) * φ z with hf
  set S : ℂ → ℝ≥0∞ := fun D => ((Polynomial.nthRoots (p + 1) D).map f).sum with hS
  set ψ : ℂ → ℝ≥0∞ := fun D =>
    ENNReal.ofReal (T ^ (2 * p) * ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) * (ENNReal.ofReal (‖D‖ ^ (2 * q)) * S D) with hψ

  have hA : ∀ c : ℂ, ENNReal.ofReal (T ^ (2 * p * (q + p + 1)) * ‖c‖ ^ (2 * q) * (T ^ (2 * p ^ 2))⁻¹ *
      ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) * ((Polynomial.nthRoots (p + 1) (c * t ^ p)).map f).sum = ψ (t ^ p * c) := by
    intro c
    simp only [hψ, hS, mul_comm c (t ^ p)]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [norm_mul, norm_pow, mul_pow, ← pow_mul, ← hT]
    have : T ^ (2 * p * (q + p + 1)) = T ^ (2 * p) * T ^ (2 * p ^ 2) * T ^ (p * (2 * q)) := by
      rw [← pow_add, ← pow_add]; congr 1; ring
    rw [this]
    have hT2 : T ^ (2 * p ^ 2) ≠ 0 := pow_ne_zero _ hTpos.ne'
    field_simp
  simp only [hA]

  have htp : t ^ p ≠ 0 := pow_ne_zero _ ht
  rw [hL (t ^ p) ψ htp]

  have hC : ∫⁻ D, ψ D = ENNReal.ofReal (T ^ (2 * p) * ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) *
      ∫⁻ D, ENNReal.ofReal (‖D‖ ^ (2 * q)) * S D := by
    simp only [hψ]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hC, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hconst : (‖t ^ p‖ ^ 2)⁻¹ * (T ^ (2 * p) * ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) = ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹ := by
    rw [norm_pow, ← hT, ← pow_mul]
    have : T ^ (p * 2) ≠ 0 := pow_ne_zero _ hTpos.ne'
    rw [mul_comm p 2]; field_simp
  rw [hconst]

  set g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ (2 * (p + 1) * q + 2 * p ^ 2)) * φ z with hg
  have hD : ∀ D : ℂ, ENNReal.ofReal (‖D‖ ^ (2 * q)) * S D = ((Polynomial.nthRoots (p + 1) D).map g).sum := by
    intro D
    simp only [hS]
    rw [← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro z hz
    rw [Polynomial.mem_nthRoots (by omega : 0 < p + 1)] at hz
    simp only [hf, hg]
    rw [← hz, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), norm_pow, ← pow_mul, ← pow_add]
    congr 3
    ring
  simp only [hD]

  have hgm : Measurable g := by
    simp only [hg]
    exact (Measurable.ennreal_ofReal ((continuous_norm.pow _).measurable)).mul hφ
  rw [hR (p + 1) g (by omega) hgm]
  simp only [e1]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext z
  simp only [hg]
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have hs2 : ((((p + 1 : ℕ) : ℝ)) ^ 2) ≠ 0 := by positivity
  rw [show (((p + 1 : ℕ) : ℝ) ^ 2)⁻¹ * (((p + 1 : ℕ) : ℝ) ^ 2 * ‖z‖ ^ (2 * p)) = ‖z‖ ^ (2 * p) by
      field_simp, ← pow_add]
  congr 1
  ring

end Formalism.FourierDecayAlt.P
