import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Real ComplexConjugate

noncomputable section

namespace KThetaCubeParseval

/- English proof (translation)
Unfold `torusChar`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma torusChar_eq {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar m u = Complex.exp (((2 * π * ∑ i, (m i : ℝ) * u i : ℝ) : ℂ) * Complex.I) := by
  unfold torusChar
  congr 1
  push_cast
  ring

/- English proof (translation)
Rewrite using `[torusChar_eq, Complex.norm_exp_ofReal_mul_I]`.
-/
lemma norm_torusChar {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) : ‖torusChar m u‖ = 1 := by
  rw [torusChar_eq, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Rewrite using `[torusChar_eq, torusChar_eq, torusChar_eq, ← Complex.exp_conj, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma torusChar_mul_conj {g : ℕ} (k l : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar k u * conj (torusChar l u) = torusChar (k - l) u := by
  rw [torusChar_eq, torusChar_eq, torusChar_eq, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  push_cast
  ring

/- English proof (translation)
Unfold `torusChar`. Use `fun_prop`.
-/
lemma continuous_torusChar {g : ℕ} (m : Fin g → ℤ) : Continuous (torusChar m) := by
  unfold torusChar
  fun_prop

/- English proof (translation)
Simplify using `[Measure.real, Real.volume_Icc_pi]`.
-/
lemma measureReal_cube (g : ℕ) :
    (volume.restrict (Set.Icc (0 : Fin g → ℝ) 1)).real Set.univ = 1 := by
  simp [Measure.real, Real.volume_Icc_pi]

end KThetaCubeParseval

open KThetaCubeParseval in

/- English proof (translation)
Introduce `g c hc`. Use `set μ := volume.restrict (Set.Icc (0 : Fin g → ℝ) 1)`. Use `set F : (Fin g → ℤ) × (Fin g → ℤ) → (Fin g → ℝ) → ℂ := fun p u => c p.1 * conj (c p.2) * torusChar (p.1 - p.2) u with hF`. Establish `hnorm1 : ∀ u, Summable fun k => ‖c k * torusChar k u‖` using `fun u => by`. Simplify `hc` using `[norm_torusChar]`.

Establish `hnorm2 : ∀ u, Summable fun l => ‖conj (c l) * conj (torusChar l u)‖` using `fun u => by`. Simplify `hc` using `[norm_torusChar]`. Establish `hpt : ∀ u, ((‖∑' k, c k * torusChar k u‖ ^ 2 : ℝ) : ℂ) = ∑' p, F p u`. Introduce `u`. Rewrite using `[← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, Complex.conj_tsum]`.

Simplify using `only [map_mul]`. Rewrite using `[tsum_mul_tsum_of_summable_norm (hnorm1 u) (hnorm2 u)]`. Use `congr 1`. Use extensionality with `p`. Rewrite using `[hF]`.

Simplify using `only`. Rewrite using `[← torusChar_mul_conj]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnormF : ∀ p u, ‖F p u‖ = ‖c p.1‖ * ‖c p.2‖`. Introduce `p u`.

Simplify using `[hF, norm_torusChar]`. Establish `hint : ∀ p, Integrable (F p) μ` using `fun p => ((continuous_torusChar (p.1 - p.2)).const_smul (c p.1 * conj (c p.2))).integrableOn_Icc`. Establish `hμ : μ.real Set.univ = 1` using `measureReal_cube g`. Establish `hsum : Summable fun p => ∫ u, ‖F p u‖ ∂μ`. Simplify using `only [hnormF, integral_const, hμ, one_smul]`.

Conclude with `Summable.mul_of_nonneg hc hc (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)`. Establish `hterm : ∀ p, ∫ u, F p u ∂μ = if p.1 - p.2 = 0 then c p.1 * conj (c p.2) else 0`. Introduce `p`. Rewrite using `[hF]`. Simplify using `only`.

Rewrite using `[integral_const_mul, h g (p.1 - p.2)]`. Apply the tactic sequence `split_ifs <;> simp`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[← integral_complex_ofReal, Complex.ofReal_tsum]`. Repeatedly rewrite using `[hpt]`.

Rewrite using `[← integral_tsum_of_summable_integral_norm hint hsum]`. Repeatedly rewrite using `[hterm]`. Establish `hinj : Function.Injective fun k : Fin g → ℤ => (k, k)` using `fun a b hab => (Prod.mk.inj hab).1`. Rewrite using `[← hinj.tsum_eq]`. Use `congr 1`.

Use extensionality with `k`. Simplify using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Introduce `p hp`. Establish `: p.1 - p.2 = 0`. Assume the negation of the conclusion as `hne`.

Conclude with `hp (by simp [hne])`. Conclude with `⟨p.1, Prod.ext rfl (sub_eq_zero.mp this)⟩`.
-/
theorem ThetaCubeParseval.proof (h : ThetaCharIntegral.Statement) : ThetaCubeParseval.Statement := by
  intro g c hc
  set μ := volume.restrict (Set.Icc (0 : Fin g → ℝ) 1)

  set F : (Fin g → ℤ) × (Fin g → ℤ) → (Fin g → ℝ) → ℂ :=
    fun p u => c p.1 * conj (c p.2) * torusChar (p.1 - p.2) u with hF
  have hnorm1 : ∀ u, Summable fun k => ‖c k * torusChar k u‖ := fun u => by
    simpa [norm_torusChar] using hc
  have hnorm2 : ∀ u, Summable fun l => ‖conj (c l) * conj (torusChar l u)‖ := fun u => by
    simpa [norm_torusChar] using hc
  have hpt : ∀ u, ((‖∑' k, c k * torusChar k u‖ ^ 2 : ℝ) : ℂ) = ∑' p, F p u := by
    intro u
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, Complex.conj_tsum]
    simp only [map_mul]
    rw [tsum_mul_tsum_of_summable_norm (hnorm1 u) (hnorm2 u)]
    congr 1
    ext p
    rw [hF]
    dsimp only
    rw [← torusChar_mul_conj]
    ring
  have hnormF : ∀ p u, ‖F p u‖ = ‖c p.1‖ * ‖c p.2‖ := by
    intro p u
    simp [hF, norm_torusChar]
  have hint : ∀ p, Integrable (F p) μ := fun p =>
    ((continuous_torusChar (p.1 - p.2)).const_smul (c p.1 * conj (c p.2))).integrableOn_Icc
  have hμ : μ.real Set.univ = 1 := measureReal_cube g
  have hsum : Summable fun p => ∫ u, ‖F p u‖ ∂μ := by
    simp only [hnormF, integral_const, hμ, one_smul]
    exact Summable.mul_of_nonneg hc hc (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hterm : ∀ p, ∫ u, F p u ∂μ = if p.1 - p.2 = 0 then c p.1 * conj (c p.2) else 0 := by
    intro p
    rw [hF]
    dsimp only
    rw [integral_const_mul, h g (p.1 - p.2)]
    split_ifs <;> simp
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, Complex.ofReal_tsum]
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hterm]
  have hinj : Function.Injective fun k : Fin g → ℤ => (k, k) := fun a b hab => (Prod.mk.inj hab).1
  rw [← hinj.tsum_eq]
  · congr 1
    ext k
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · intro p hp
    have : p.1 - p.2 = 0 := by
      by_contra hne
      exact hp (by simp [hne])
    exact ⟨p.1, Prod.ext rfl (sub_eq_zero.mp this)⟩

end

end GroundTheory.Heights₂.Heights
