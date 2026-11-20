import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `n A h g hA W Z lam d hdet hsig hh hZ hlam hg i₀ x hx hxpos`. Establish `key : ∀ (N B : Matrix (Fin n) (Fin n) ℂ) (u u' : Fin n → ℂ), star (N *ᵥ u) ⬝ᵥ B *ᵥ (N *ᵥ u') = star u ⬝ᵥ (Nᴴ * B * N) *ᵥ u'`. Introduce `N B u u'`. Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]`. Use `set M : Matrix (Fin n) (Fin n) ℂ := (W : Matrix (Fin n) (Fin n) ℂ) * (Z : Matrix (Fin n) (Fin n) ℂ) with hM`.

Establish `hMd : Mᴴ * A * M = diagonal (fun i => (d i : ℂ))`. Rewrite using `[← hZ, hh, hM, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Take `⟨y, rfl⟩ : ∃ y, x = (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y` from `⟨(↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ x, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩`. Establish `hy : ∀ i, i ≠ i₀ → y i = 0`.

Establish `h1 : (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ (diagonal lam *ᵥ y) = (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ (lam i₀ • y)`. Rewrite using `[mulVec_mulVec, ← hg, ← mulVec_mulVec, hx, mulVec_smul]`. Establish `h2 : diagonal lam *ᵥ y = lam i₀ • y`. Use `congrArg (fun v => (↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) h1` as an intermediate fact. Simplify `this` using `only [mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, one_mulVec]`.

Introduce `i hi`. Establish `h3` using `congrFun h2 i`. Rewrite `h3` using `[mulVec_diagonal, Pi.smul_apply, smul_eq_mul]`. Establish `h4 : (lam i - lam i₀) * y i = 0` using `by rw [sub_mul, h3, sub_self]`. Break down `mul_eq_zero.mp h4 with h5 | h5` into its components or cases.

Conclude with `absurd (hlam (sub_eq_zero.mp h5)) hi`. Conclude with `h5`. Establish `hform : star ((Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y) ⬝ᵥ h *ᵥ ((Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y) = ((d i₀ * Complex.normSq (y i₀) : ℝ) : ℂ)`. Rewrite using `[key, hZ]`. Simplify using `only [dotProduct, mulVec_diagonal, Pi.star_apply]`.

Rewrite using `[Finset.sum_eq_single i₀ (fun i _ hi => by simp [hy i hi]) (by simp)]`. Rewrite using `[Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]`. Simplify using `only [RCLike.star_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hxpos` using `[hform, Complex.ofReal_re]`.

Establish `hd0 : 0 < d i₀`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use polynomial arithmetic with `[Complex.normSq_nonneg (y i₀)]`. Use `⟨hd0, fun i hi => ?_⟩` and prove the remaining obligations.

Establish `hNM : ((↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ)) * M = 1`. Rewrite using `[hM, Matrix.mul_assoc, ← Matrix.mul_assoc (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ), Units.inv_mul, Matrix.one_mul, Units.inv_mul]`. Establish `hval : ∀ j k : Fin n, star (M *ᵥ Pi.single j 1) ⬝ᵥ A *ᵥ (M *ᵥ Pi.single k 1) = if j = k then (d j : ℂ) else 0`. Introduce `j k`. Rewrite using `[key, hMd]`.

Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality. Simplify using `[dotProduct, mulVec_diagonal, Pi.single_apply]`. Simplify using `[dotProduct, mulVec_diagonal, Pi.single_apply, hjk]`. Introduce `hkj`.

Conclude with `absurd hkj.symm hjk`. Establish `hne : M *ᵥ Pi.single i (1 : ℂ) ≠ 0`. Introduce `h0`. Use `congrArg (fun v => ((↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) h0` as an intermediate fact. Simplify using `only [mulVec_mulVec, hNM, one_mulVec, mulVec_zero] at this`.

Use `congrFun this i` as an intermediate fact. Simplify using `at this`. Establish `hneg` using `re_form_neg_of_orth_of_sigPosH_eq_one A hA hdet hsig (M *ᵥ Pi.single i₀ 1) (M *ᵥ Pi.single i 1) (by rw [hval]; simpa using hd0) (by rw [hval, if_neg (Ne.symm hi)]) hne`. Rewrite `hneg` using `[hval, if_pos rfl, Complex.ofReal_re]`. Conclude with `hneg`.
-/
theorem diag_sign_of_pos_eigenvector : ∀ {n : ℕ} (A h g : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (W Z : GL (Fin n) ℂ) (lam : Fin n → ℂ) (d : Fin n → ℝ), A.det ≠ 0 → sigPosH hA = 1 → h = (W : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (W : Matrix (Fin n) (Fin n) ℂ) → (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) → Function.Injective lam → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∀ (i₀ : Fin n) (x : Fin n → ℂ), g *ᵥ x = lam i₀ • x → 0 < (star x ⬝ᵥ (h *ᵥ x)).re → 0 < d i₀ ∧ ∀ i, i ≠ i₀ → d i < 0 := by
  intro n A h g hA W Z lam d hdet hsig hh hZ hlam hg i₀ x hx hxpos
  have key : ∀ (N B : Matrix (Fin n) (Fin n) ℂ) (u u' : Fin n → ℂ),
      star (N *ᵥ u) ⬝ᵥ B *ᵥ (N *ᵥ u') = star u ⬝ᵥ (Nᴴ * B * N) *ᵥ u' := by
    intro N B u u'
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  set M : Matrix (Fin n) (Fin n) ℂ := (W : Matrix (Fin n) (Fin n) ℂ) * (Z : Matrix (Fin n) (Fin n) ℂ) with hM
  have hMd : Mᴴ * A * M = diagonal (fun i => (d i : ℂ)) := by
    rw [← hZ, hh, hM, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨y, rfl⟩ : ∃ y, x = (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y :=
    ⟨(↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ x, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩
  have hy : ∀ i, i ≠ i₀ → y i = 0 := by
    have h1 : (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ (diagonal lam *ᵥ y)
        = (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ (lam i₀ • y) := by
      rw [mulVec_mulVec, ← hg, ← mulVec_mulVec, hx, mulVec_smul]
    have h2 : diagonal lam *ᵥ y = lam i₀ • y := by
      have := congrArg (fun v => (↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) h1
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, one_mulVec] using this
    intro i hi
    have h3 := congrFun h2 i
    rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h3
    have h4 : (lam i - lam i₀) * y i = 0 := by rw [sub_mul, h3, sub_self]
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd (hlam (sub_eq_zero.mp h5)) hi
    · exact h5
  have hform : star ((Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y) ⬝ᵥ h *ᵥ ((Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y)
      = ((d i₀ * Complex.normSq (y i₀) : ℝ) : ℂ) := by
    rw [key, hZ]
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hy i hi]) (by simp)]
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.star_def]
    ring
  rw [hform, Complex.ofReal_re] at hxpos
  have hd0 : 0 < d i₀ := by
    by_contra hc
    push_neg at hc
    nlinarith [Complex.normSq_nonneg (y i₀)]
  refine ⟨hd0, fun i hi => ?_⟩
  have hNM : ((↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ)) * M = 1 := by
    rw [hM, Matrix.mul_assoc, ← Matrix.mul_assoc (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ), Units.inv_mul,
      Matrix.one_mul, Units.inv_mul]
  have hval : ∀ j k : Fin n, star (M *ᵥ Pi.single j 1) ⬝ᵥ A *ᵥ (M *ᵥ Pi.single k 1)
      = if j = k then (d j : ℂ) else 0 := by
    intro j k
    rw [key, hMd]
    by_cases hjk : j = k
    · subst hjk; simp [dotProduct, mulVec_diagonal, Pi.single_apply]
    · simp [dotProduct, mulVec_diagonal, Pi.single_apply, hjk]
      intro hkj; exact absurd hkj.symm hjk
  have hne : M *ᵥ Pi.single i (1 : ℂ) ≠ 0 := by
    intro h0
    have := congrArg (fun v => ((↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) h0
    simp only [mulVec_mulVec, hNM, one_mulVec, mulVec_zero] at this
    have := congrFun this i
    simp at this
  have hneg := re_form_neg_of_orth_of_sigPosH_eq_one A hA hdet hsig (M *ᵥ Pi.single i₀ 1)
    (M *ᵥ Pi.single i 1) (by rw [hval]; simpa using hd0) (by rw [hval, if_neg (Ne.symm hi)]) hne
  rw [hval, if_pos rfl, Complex.ofReal_re] at hneg
  exact hneg

end GlobalTheory
