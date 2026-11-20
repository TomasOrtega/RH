import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV

noncomputable section

open MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder

namespace GlobalTheory.UnimodVol

def stdRealBasis (g : ℕ) : Module.Basis (Σ _ : Fin g, Fin 2) ℝ (Fin g → ℂ) :=
  Pi.basis fun _ => Complex.basisOneI

/- English proof (translation)
Establish `h : ZSpan.fundamentalDomain (stdRealBasis g) = Set.pi Set.univ fun _ : Fin g => Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1)`. Use extensionality with `z`. Simplify using `[ZSpan.fundamentalDomain, stdRealBasis, Pi.basis_repr, Sigma.forall, Fin.forall_fin_two]`. Rewrite using `[h, volume_pi_pi]`. Use `Finset.prod_eq_one fun _ _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.volume_preserving_equiv_real_prod.measure_preimage (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]`. Simplify using `[Measure.volume_eq_prod]`.
-/
theorem volume_fundamentalDomain_stdRealBasis (g : ℕ) :
    volume (ZSpan.fundamentalDomain (stdRealBasis g)) = 1 := by
  have h : ZSpan.fundamentalDomain (stdRealBasis g) =
      Set.pi Set.univ fun _ : Fin g =>
        Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    simp [ZSpan.fundamentalDomain, stdRealBasis, Pi.basis_repr, Sigma.forall, Fin.forall_fin_two]
  rw [h, volume_pi_pi]
  refine Finset.prod_eq_one fun _ _ => ?_
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]
  simp [Measure.volume_eq_prod]

/- English proof (translation)
Simplify using `[stdRealBasis, Pi.basis_repr, Fintype.sum_sigma, Fin.sum_univ_two, dotProduct]`.
-/
theorem re_dotProduct_star {g : ℕ} (z w : Fin g → ℂ) :
    (z ⬝ᵥ star w).re = ∑ k, (stdRealBasis g).repr z k * (stdRealBasis g).repr w k := by
  simp [stdRealBasis, Pi.basis_repr, Fintype.sum_sigma, Fin.sum_univ_two, dotProduct]

/- English proof (translation)
Establish `: star ((Complex.I • Hm.map star) *ᵥ w) = (-Complex.I) • Hm *ᵥ star w`. Use extensionality with `k`. Simplify using `[mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Rewrite using `[this, dotProduct_smul, hermForm]`. Simplify using the standard rewrite rules.
-/
theorem im_hermForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    (hermForm Hm z w).im = (z ⬝ᵥ star ((Complex.I • Hm.map star) *ᵥ w)).re := by
  have : star ((Complex.I • Hm.map star) *ᵥ w) = (-Complex.I) • Hm *ᵥ star w := by
    ext k
    simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [this, dotProduct_smul, hermForm]
  simp

/- English proof (translation)
Use `set T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := (Matrix.toLin' (Complex.I • Hm.map star)).restrictScalars ℝ with hT`. Establish `h : (Matrix.of fun i j => (hermForm Hm (v i) (v j)).im) = ((stdRealBasis g).toMatrix v)ᵀ * (stdRealBasis g).toMatrix (T ∘ v)`. Use extensionality with `i j`. Rewrite using `[Matrix.of_apply, im_hermForm, re_dotProduct_star, Matrix.mul_apply]`. Both sides reduce to the same expression.

Establish `hd : LinearMap.det T = ‖Hm.det‖ ^ 2`. Establish `: (Hm.map star).det = star Hm.det` using `((starRingEnd ℂ).map_det Hm).symm`. Rewrite using `[hT, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, Matrix.det_smul, this]`. Simplify using the standard rewrite rules. Rewrite using `[h, Matrix.det_mul, Matrix.det_transpose, ← Module.Basis.det_apply, ← Module.Basis.det_apply, Module.Basis.det_comp, hd]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_gram_im {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (v : (Σ _ : Fin g, Fin 2) → Fin g → ℂ) :
    (Matrix.of fun i j => (hermForm Hm (v i) (v j)).im).det =
      ((stdRealBasis g).det v) ^ 2 * ‖Hm.det‖ ^ 2 := by
  set T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    (Matrix.toLin' (Complex.I • Hm.map star)).restrictScalars ℝ with hT
  have h : (Matrix.of fun i j => (hermForm Hm (v i) (v j)).im) =
      ((stdRealBasis g).toMatrix v)ᵀ * (stdRealBasis g).toMatrix (T ∘ v) := by
    ext i j
    rw [Matrix.of_apply, im_hermForm, re_dotProduct_star, Matrix.mul_apply]
    rfl
  have hd : LinearMap.det T = ‖Hm.det‖ ^ 2 := by
    have : (Hm.map star).det = star Hm.det := ((starRingEnd ℂ).map_det Hm).symm
    rw [hT, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, Matrix.det_smul, this]
    simp
  rw [h, Matrix.det_mul, Matrix.det_transpose, ← Module.Basis.det_apply, ← Module.Basis.det_apply,
    Module.Basis.det_comp, hd]
  ring

/- English proof (translation)
Use `Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_` and prove the remaining obligations. Establish `h1` using `hpos (star x) (by simpa using hx)`. Establish `h2` using `hH.im_star_dotProduct_mulVec_self x`. Rewrite `h1` using `[hermForm, star_star]`. Conclude with `Complex.pos_iff.2 ⟨h1, h2.symm⟩`.
-/
theorem posDef_of_hermForm {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) : Hm.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have h1 := hpos (star x) (by simpa using hx)
  have h2 := hH.im_star_dotProduct_mulVec_self x
  rw [hermForm, star_star] at h1
  exact Complex.pos_iff.2 ⟨h1, h2.symm⟩

/- English proof (translation)
Establish `h` using `(posDef_of_hermForm hH hpos).det_pos`. Conclude with `⟨(Complex.pos_iff.1 h).1, (Complex.re_eq_norm.2 h.le).symm⟩`.
-/
theorem det_re_pos {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    0 < Hm.det.re ∧ ‖Hm.det‖ = Hm.det.re := by
  have h := (posDef_of_hermForm hH hpos).det_pos
  exact ⟨(Complex.pos_iff.1 h).1, (Complex.re_eq_norm.2 h.le).symm⟩

end GlobalTheory.UnimodVol

namespace GlobalTheory

open UnimodVol

/- English proof (translation)
Establish `: IsZLattice ℝ Λ` using `⟨hfull⟩`. Set `b₁` to `Module.Free.chooseBasis ℤ Λ`. Set `b` to `b₁.reindex ((b₁.ofZLatticeBasis ℝ Λ).indexEquiv (stdRealBasis g))`. Establish `hvol : (volume Fd).toReal = |(stdRealBasis g).det (Subtype.val ∘ b)|`. Establish `h1` using `ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hFd`.

Rewrite `h1` using `[ZLattice.covolume_eq_det_mul_measureReal Λ volume b (stdRealBasis g), Measure.real, volume_fundamentalDomain_stdRealBasis]`. Simplify `h1.symm` using `[Measure.real]`. Establish `hu` using `LinearEquiv.isUnit_det (LinearEquiv.ofBijective Ef hbij) b b.dualBasis`. Use `set M := LinearMap.toMatrix b b.dualBasis (LinearEquiv.ofBijective Ef hbij : Λ →ₗ[ℤ] Module.Dual ℤ Λ) with hM`. Establish `hG : (Matrix.of fun i j => (hermForm Hm ((Subtype.val ∘ b) i) ((Subtype.val ∘ b) j)).im) = ((Int.castRingHom ℝ).mapMatrix M)ᵀ`.

Use extensionality with `i j`. Simplify using `[hM, LinearMap.toMatrix_apply, hE]`. Establish `hdet` using `det_gram_im Hm (Subtype.val ∘ b)`. Rewrite `hdet` using `[hG, Matrix.det_transpose, ← RingHom.map_det]`. Take `⟨hp, hn⟩` from `det_re_pos hH hpos`.

Establish `habs : |((M.det : ℤ) : ℝ)| = 1`. Apply the tactic sequence `rcases Int.isUnit_iff.1 hu with h | h <;> simp [h]`. Rewrite `hdet` using `[hn, eq_intCast]`. Rewrite `habs` using `[hdet, ← mul_pow, abs_of_nonneg (sq_nonneg _), ← sq_abs, abs_mul, abs_of_pos hp, pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero]`. Rewrite using `[hvol, habs]`.
-/
theorem volume_mul_det_eq_one_of_unimodular (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Fd : Set (Fin g → ℂ))
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hbij : Function.Bijective Ef)
    (hFd : IsAddFundamentalDomain Λ Fd volume) : (volume Fd).toReal * Hm.det.re = 1 := by
  have : IsZLattice ℝ Λ := ⟨hfull⟩
  let b₁ := Module.Free.chooseBasis ℤ Λ
  let b := b₁.reindex ((b₁.ofZLatticeBasis ℝ Λ).indexEquiv (stdRealBasis g))
  have hvol : (volume Fd).toReal = |(stdRealBasis g).det (Subtype.val ∘ b)| := by
    have h1 := ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hFd
    rw [ZLattice.covolume_eq_det_mul_measureReal Λ volume b (stdRealBasis g), Measure.real,
      volume_fundamentalDomain_stdRealBasis] at h1
    simpa [Measure.real] using h1.symm
  have hu := LinearEquiv.isUnit_det (LinearEquiv.ofBijective Ef hbij) b b.dualBasis
  set M := LinearMap.toMatrix b b.dualBasis (LinearEquiv.ofBijective Ef hbij : Λ →ₗ[ℤ] Module.Dual ℤ Λ)
    with hM
  have hG : (Matrix.of fun i j => (hermForm Hm ((Subtype.val ∘ b) i) ((Subtype.val ∘ b) j)).im) =
      ((Int.castRingHom ℝ).mapMatrix M)ᵀ := by
    ext i j
    simp [hM, LinearMap.toMatrix_apply, hE]
  have hdet := det_gram_im Hm (Subtype.val ∘ b)
  rw [hG, Matrix.det_transpose, ← RingHom.map_det] at hdet
  obtain ⟨hp, hn⟩ := det_re_pos hH hpos
  have habs : |((M.det : ℤ) : ℝ)| = 1 := by
    rcases Int.isUnit_iff.1 hu with h | h <;> simp [h]
  rw [hn, eq_intCast] at hdet
  rw [hdet, ← mul_pow, abs_of_nonneg (sq_nonneg _), ← sq_abs, abs_mul, abs_of_pos hp,
    pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero] at habs
  rw [hvol, habs]

/- English proof (translation)
Establish `h : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W i) (W j)) = (Real.pi : ℂ) • (W * (Hm * Wᴴ))`. Use extensionality with `i j`. Simplify using `[hermForm, Matrix.mul_apply, dotProduct, mulVec]`. Rewrite using `[h, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Fintype.card_fin, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]`. Simplify using `only [Complex.star_def]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_gram_pi_hermForm {g : ℕ} (Hm W : Matrix (Fin g) (Fin g) ℂ) :
    (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W i) (W j)).det =
      (Real.pi : ℂ) ^ g * Hm.det * ((‖W.det‖ ^ 2 : ℝ) : ℂ) := by
  have h : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W i) (W j)) =
      (Real.pi : ℂ) • (W * (Hm * Wᴴ)) := by
    ext i j
    simp [hermForm, Matrix.mul_apply, dotProduct, mulVec]
  rw [h, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Fintype.card_fin,
    ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [Complex.star_def]
  ring

/- English proof (translation)
Establish `h` using `volume_mul_det_eq_one_of_unimodular g Λ hfull Hm Ef Fd hH hpos hE hbij hFd`. Establish `hp` using `(det_re_pos hH hpos).1`. Establish `hW' : 0 < ‖W.det‖` using `norm_pos_iff.2 hW`. Establish `hπ` using `Real.pi_pos`. Use `⟨by positivity, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_inv_of_mul_eq_one_left h]`. Clear the denominators using the available nonvanishing facts. Establish `him : Hm.det = (Hm.det.re : ℂ)` using `Complex.ext rfl (by simpa using (Complex.pos_iff.1 (posDef_of_hermForm hH hpos).det_pos).2.symm)`. Rewrite using `[det_gram_pi_hermForm, him]`. Use `push_cast`.

Simplify using the standard rewrite rules.
-/
theorem volume_div_eq_inv_of_unimodular (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Fd : Set (Fin g → ℂ))
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hbij : Function.Bijective Ef)
    (hFd : IsAddFundamentalDomain Λ Fd volume) (W : Matrix (Fin g) (Fin g) ℂ) (hW : W.det ≠ 0) :
    0 < Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2 ∧
    (volume Fd).toReal / (Real.pi ^ g * ‖W.det‖ ^ 2) = (Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2)⁻¹ ∧
    (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W i) (W j)).det =
      ((Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2 : ℝ) : ℂ) := by
  have h := volume_mul_det_eq_one_of_unimodular g Λ hfull Hm Ef Fd hH hpos hE hbij hFd
  have hp := (det_re_pos hH hpos).1
  have hW' : 0 < ‖W.det‖ := norm_pos_iff.2 hW
  have hπ := Real.pi_pos
  refine ⟨by positivity, ?_, ?_⟩
  · rw [eq_inv_of_mul_eq_one_left h]
    field_simp
  · have him : Hm.det = (Hm.det.re : ℂ) :=
      Complex.ext rfl (by simpa using (Complex.pos_iff.1 (posDef_of_hermForm hH hpos).det_pos).2.symm)
    rw [det_gram_pi_hermForm, him]
    push_cast
    simp

end GlobalTheory
