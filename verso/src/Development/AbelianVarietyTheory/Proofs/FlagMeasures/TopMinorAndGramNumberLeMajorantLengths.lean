import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramSchmidtLengths
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YBound

open GlobalTheory.Amp.GramFlag (eucl_eq)

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular]`. Simplify using `[upper]`. Introduce `a b h`. Establish `h' : b < a` using `h`. Simplify using `[upper, not_lt.2 h'.le, h'.ne']`.
-/
theorem det_upper {r : ℕ} (x : UT r → ℂ) : (upper x).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [upper]
  · intro a b h
    have h' : b < a := h
    simp [upper, not_lt.2 h'.le, h'.ne']

/- English proof (translation)
Establish `e : (Matrix.of fun a b => B (∑ c, U c a • y c) (∑ c, U' c b • y' c)) = Uᵀ * (Matrix.of fun a b => B (y a) (y' b)) * (U'ᴴ)ᵀ`. Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, Matrix.mul_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, Matrix.transpose_apply, Matrix.conjTranspose_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]`. Use `first`. Consider the case `(refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_; simp; ring)`.

Consider the case `(rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_; simp; ring)`. Rewrite using `[e]`. Simplify using `[Matrix.det_mul, Matrix.det_conjTranspose, hU, hU']`.
-/
theorem det_change {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) {j : ℕ} (y : Fin j → V₁) (y' : Fin j → V₂) (U U' : Matrix (Fin j) (Fin j) ℂ)
    (hU : U.det = 1) (hU' : U'.det = 1) :
    (Matrix.of fun a b => B (∑ c, U c a • y c) (∑ c, U' c b • y' c)).det =
      (Matrix.of fun a b => B (y a) (y' b)).det := by
  have e : (Matrix.of fun a b => B (∑ c, U c a • y c) (∑ c, U' c b • y' c)) =
      Uᵀ * (Matrix.of fun a b => B (y a) (y' b)) * (U'ᴴ)ᵀ := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, Matrix.transpose_apply, Matrix.conjTranspose_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    first
      | (refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_; simp; ring)
      | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_; simp; ring)
  rw [e]
  simp [Matrix.det_mul, Matrix.det_conjTranspose, hU, hU']

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem prod_le_pow' {n : ℕ} (f : Fin n → ℝ) (R : ℝ) (h0 : ∀ i, 0 ≤ f i) (h : ∀ i, f i ≤ R) :
    ∏ i, f i ≤ R ^ n := by
  calc _ ≤ ∏ _a : Fin n, R := Finset.prod_le_prod (fun i _ => h0 i) fun i _ => h i
    _ = _ := by simp

def formE {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) →ₗ⋆[ℂ] ℂ :=
  (innerₛₗ ℂ).flip ∘ₗ Matrix.toEuclideanLin H

/- English proof (translation)
Use `show ⟪(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n)), WithLp.toLp 2 (H *ᵥ v)⟫_ℂ = _`. Rewrite using `[EuclideanSpace.inner_toLp_toLp, dotProduct_comm, herm]`.
-/
theorem formE_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    formE H (WithLp.toLp 2 v) (WithLp.toLp 2 w) = herm H v w := by
  show ⟪(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n)), WithLp.toLp 2 (H *ᵥ v)⟫_ℂ = _
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, herm]

/- English proof (translation)
Establish `h1 : ‖Matrix.toEuclideanLin H v‖ = ‖v‖`. Establish `: ⟪Matrix.toEuclideanLin H v, Matrix.toEuclideanLin H v⟫_ℂ = ⟪v, v⟫_ℂ`. Rewrite using `[← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]`. Use `congr 1`. Use extensionality with `i`.

Simplify using `[Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, hH]`. Rewrite using `[norm_eq_sqrt_re_inner (𝕜 := ℂ), this, ← norm_eq_sqrt_re_inner]`. Use `show ‖⟪w, Matrix.toEuclideanLin H v⟫_ℂ‖ ≤ _`. Rewrite using `[mul_comm, ← h1]`. Conclude with `norm_inner_le_norm _ _`.
-/
theorem formE_le {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ * H = 1) (v w : EuclideanSpace ℂ (Fin n)) :
    ‖formE H v w‖ ≤ ‖v‖ * ‖w‖ := by
  have h1 : ‖Matrix.toEuclideanLin H v‖ = ‖v‖ := by
    have : ⟪Matrix.toEuclideanLin H v, Matrix.toEuclideanLin H v⟫_ℂ = ⟪v, v⟫_ℂ := by
      rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      congr 1
      ext i
      simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, hH]
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), this, ← norm_eq_sqrt_re_inner]
  show ‖⟪w, Matrix.toEuclideanLin H v⟫_ℂ‖ ≤ _
  rw [mul_comm, ← h1]
  exact norm_inner_le_norm _ _

/- English proof (translation)
Establish `h : gᴴ * H * g = H` using `hg`. Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]`.
-/
theorem herm_mulVec {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  have h : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

/- English proof (translation)
Establish `h` using `(Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.gramHadamard (EuclideanSpace ℂ (Fin n)) r (fun a => ∑ b, U b a • P.starProjection (WithLp.toLp 2 (v b)))).2 R (fun a => by`. Use `le_trans ?_ (hR a)` and prove the remaining obligations. Rewrite using `[eucl_eq, WithLp.toLp_sum]`. Simplify using `only [← map_smul, ← map_sum, WithLp.toLp_smul]`. Conclude with `P.norm_starProjection_apply_le _)`.

Establish `e : ∀ w : Fin r → EuclideanSpace ℂ (Fin n), (Matrix.gram ℂ w).det = (Matrix.of fun a b => (innerₛₗ ℂ).flip (w a) (w b)).det`. Introduce `w`. Rewrite using `[← Matrix.det_transpose]`. Both sides reduce to the same expression. Unfold `gramProj`.

Rewrite `h` using `[e, det_change _ _ _ U U hU hU, ← e]`. Conclude with `h`.
-/
theorem gramProj_le {n r : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v : Fin r → Fin n → ℂ)
    (U : Matrix (Fin r) (Fin r) ℂ) (hU : U.det = 1) (R : ℝ) (hR : ∀ a, eucl (∑ b, U b a • v b) ≤ R) :
    gramProj P v ≤ R ^ r := by
  have h := (Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.gramHadamard (EuclideanSpace ℂ (Fin n)) r
    (fun a => ∑ b, U b a • P.starProjection (WithLp.toLp 2 (v b)))).2 R (fun a => by
      refine le_trans ?_ (hR a)
      rw [eucl_eq, WithLp.toLp_sum]
      simp only [← map_smul, ← map_sum, WithLp.toLp_smul]
      exact P.norm_starProjection_apply_le _)
  have e : ∀ w : Fin r → EuclideanSpace ℂ (Fin n), (Matrix.gram ℂ w).det =
      (Matrix.of fun a b => (innerₛₗ ℂ).flip (w a) (w b)).det := by
    intro w
    rw [← Matrix.det_transpose]
    rfl
  unfold gramProj
  rw [e, det_change _ _ _ U U hU hU, ← e] at h
  exact h

/- English proof (translation)
Introduce `k r z z' γ hT x hx`. Take `⟨hz, hz', -, -, hg, -, -⟩` from `hT`. Establish `hH : IsUnit (Hpk k r).det` using `Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1`. Establish `hG` using `uHGroup _ _ hH`. Establish `hgx : γ * x ∈ GG k r` using `hG.2.1 _ hg _ hx`.

Take `⟨u', hu', -⟩` from `GramFlag.gramSchmidt_lengths k r z' x hx`. Take `⟨u, hu, -⟩` from `GramFlag.gramSchmidt_lengths k r z _ hgx`. Establish `h1 : ∀ a, eucl (∑ b, upper u b a • ((γ * x)⁻¹ *ᵥ bvec (eI k r b))) ≤ Sg k r z (γ * x)` using `fun a => by`. Rewrite using `[(hu a).1]`. Conclude with `(((LInv.lengths_basic k r z hz).2.2 _).2.1 _).2`.

Establish `h2 : ∀ a, eucl (∑ b, upper u' b a • (x⁻¹ *ᵥ bvec (eI k r b))) ≤ Sg k r z' x` using `fun a => by`. Rewrite using `[(hu' a).1]`. Conclude with `(((LInv.lengths_basic k r z' hz').2.2 _).2.1 _).2`. Establish `hD0 : 0 ≤ Dr k r z z' γ` using `norm_nonneg _`. Use `⟨?_, div_nonneg (Real.sqrt_nonneg _) hD0, ?_⟩` and prove the remaining obligations.

Establish `h` using `Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.wedgeHadamard _ _ (formE (Hpk k r)) (formE_le _ (by rw [(hpkFacts k r).1, (hpkFacts k r).2.1])) r (fun a => ∑ b, upper u' b a • WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r b))) (fun a => ∑ b, upper u b a • WithLp.toLp 2 ((γ * x)⁻¹ …`. Rewrite `h` using `[det_change _ _ _ _ _ (det_upper u') (det_upper u)]`. Establish `e : Dmin k r z z' γ ⟨r, by omega⟩ = (Matrix.of fun a b : Fin r => formE (Hpk k r) (WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r a))) (WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r b)))).det`. Unfold `Dmin`. Rewrite using `[← Matrix.det_transpose]`.

Use `congr 1`. Use extensionality with `a b`. Establish `ha` using `a.2`. Establish `hb` using `b.2`. Simplify using `only at ha hb`.

Simplify using `only [Matrix.transpose_apply, Matrix.submatrix_apply, Zhat, fvec, Matrix.of_apply, formE_apply]`. Rewrite using `[dif_pos (by simpa using ha), dif_pos (by simpa using hb), ← herm_mulVec (hG.2.2 _ hgx).2, Matrix.mulVec_mulVec, Matrix.mul_inv_rev, Matrix.nonsing_inv_mul_cancel_right _ _ (hG.2.2 _ hg).1]`. Both sides reduce to the same expression. Unfold `Dr`. Rewrite using `[e]`.

Use `h.trans (mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_)` and prove the remaining obligations. Use `prod_le_pow' _ _ (fun _ => norm_nonneg _) fun a => le_trans (le_of_eq ?_) (h2 a)` and prove the remaining obligations. Rewrite using `[eucl_eq, WithLp.toLp_sum]`. Both sides reduce to the same expression. Use `prod_le_pow' _ _ (fun _ => norm_nonneg _) fun a => le_trans (le_of_eq ?_) (h1 a)` and prove the remaining obligations.

Rewrite using `[eucl_eq, WithLp.toLp_sum]`. Both sides reduce to the same expression. Conclude with `pow_nonneg (zero_le_one.trans ((LInv.lengths_basic k r z' hz').2.2 _).1) _`. Unfold `Yv`. Use `div_le_div_of_nonneg_right ?_ hD0` and prove the remaining obligations.

Use `gramProj_le _ _ (upper u) (det_upper u) _ fun a => ?_` and prove the remaining obligations. Simplify `h1 a` using `only [Matrix.mulVec_mulVec, Matrix.mul_inv_rev]`.
-/
theorem dr_y_le : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), TwoFl k r z z' γ → ∀ x ∈ GG k r, Dr k r z z' γ ≤ Sg k r z' x ^ r * Sg k r z (γ * x) ^ r ∧ 0 ≤ Yv k r z z' γ x ∧ Yv k r z z' γ x ≤ Sg k r z (γ * x) ^ r / Dr k r z z' γ := by
  intro k r z z' γ hT x hx
  obtain ⟨hz, hz', -, -, hg, -, -⟩ := hT
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hG := uHGroup _ _ hH
  have hgx : γ * x ∈ GG k r := hG.2.1 _ hg _ hx
  obtain ⟨u', hu', -⟩ := GramFlag.gramSchmidt_lengths k r z' x hx
  obtain ⟨u, hu, -⟩ := GramFlag.gramSchmidt_lengths k r z _ hgx
  have h1 : ∀ a, eucl (∑ b, upper u b a • ((γ * x)⁻¹ *ᵥ bvec (eI k r b))) ≤ Sg k r z (γ * x) := fun a => by
    rw [(hu a).1]; exact (((LInv.lengths_basic k r z hz).2.2 _).2.1 _).2
  have h2 : ∀ a, eucl (∑ b, upper u' b a • (x⁻¹ *ᵥ bvec (eI k r b))) ≤ Sg k r z' x := fun a => by
    rw [(hu' a).1]; exact (((LInv.lengths_basic k r z' hz').2.2 _).2.1 _).2
  have hD0 : 0 ≤ Dr k r z z' γ := norm_nonneg _
  refine ⟨?_, div_nonneg (Real.sqrt_nonneg _) hD0, ?_⟩
  · have h := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.wedgeHadamard _ _ (formE (Hpk k r))
      (formE_le _ (by rw [(hpkFacts k r).1, (hpkFacts k r).2.1])) r
      (fun a => ∑ b, upper u' b a • WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r b)))
      (fun a => ∑ b, upper u b a • WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r b)))
    rw [det_change _ _ _ _ _ (det_upper u') (det_upper u)] at h
    have e : Dmin k r z z' γ ⟨r, by omega⟩ = (Matrix.of fun a b : Fin r => formE (Hpk k r)
        (WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r a))) (WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r b)))).det := by
      unfold Dmin
      rw [← Matrix.det_transpose]
      congr 1
      ext a b
      have ha := a.2
      have hb := b.2
      simp only at ha hb
      simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Zhat, fvec, Matrix.of_apply, formE_apply]
      rw [dif_pos (by simpa using ha), dif_pos (by simpa using hb),
        ← herm_mulVec (hG.2.2 _ hgx).2, Matrix.mulVec_mulVec, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_mul_cancel_right _ _ (hG.2.2 _ hg).1]
      rfl
    unfold Dr
    rw [e]
    refine h.trans (mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_)
    · refine prod_le_pow' _ _ (fun _ => norm_nonneg _) fun a => le_trans (le_of_eq ?_) (h2 a)
      rw [eucl_eq, WithLp.toLp_sum]; rfl
    · refine prod_le_pow' _ _ (fun _ => norm_nonneg _) fun a => le_trans (le_of_eq ?_) (h1 a)
      rw [eucl_eq, WithLp.toLp_sum]; rfl
    · exact pow_nonneg (zero_le_one.trans ((LInv.lengths_basic k r z' hz').2.2 _).1) _
  · unfold Yv
    refine div_le_div_of_nonneg_right ?_ hD0
    refine gramProj_le _ _ (upper u) (det_upper u) _ fun a => ?_
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_inv_rev] using h1 a

end GlobalTheory.Amp.YBound
