import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot

/- English proof (translation)
Unfold `bigZ`. Rewrite using `[blockDiagonal_conjTranspose, ← blockDiagonal_mul, ← blockDiagonal_one, ← blockDiagonal_sub]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Rewrite using `[Pi.sub_apply, Pi.one_apply, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]`.

Simplify using `[sub_eq_add_neg]`.
-/
theorem one_sub_bigZ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    1 - (bigZ q t)ᴴ * bigZ q t = blockDiagonal fun τ =>
      fromBlocks (1 - (ballMat q t τ)ᴴ * ballMat q t τ) 0 0 (1 - ((ballMat q t τ)ᵀ)ᴴ * (ballMat q t τ)ᵀ) := by
  unfold bigZ
  rw [blockDiagonal_conjTranspose, ← blockDiagonal_mul, ← blockDiagonal_one, ← blockDiagonal_sub]
  congr 1
  funext τ
  rw [Pi.sub_apply, Pi.one_apply, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp [sub_eq_add_neg]

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[← blockDiagonal_mul, ← blockDiagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[fromBlocks_multiply, Pi.one_apply, ← fromBlocks_one]`.

Establish `h1 : (A k)⁻¹ * A k = 1` using `Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hA k))`. Establish `h2 : (D k)⁻¹ * D k = 1` using `Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hD k))`. Simplify using `[h1, h2]`.
-/
theorem inv_blockDiagonal_fromBlocks {o a b : Type} [Fintype o] [DecidableEq o] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (A : o → Matrix a a ℂ) (D : o → Matrix b b ℂ)
    (hA : ∀ k, (A k).det ≠ 0) (hD : ∀ k, (D k).det ≠ 0) :
    (blockDiagonal fun k => fromBlocks (A k) 0 0 (D k))⁻¹ =
      blockDiagonal fun k => fromBlocks (A k)⁻¹ 0 0 (D k)⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [← blockDiagonal_mul, ← blockDiagonal_one]
  congr 1
  funext k
  rw [fromBlocks_multiply, Pi.one_apply, ← fromBlocks_one]
  have h1 : (A k)⁻¹ * A k = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hA k))
  have h2 : (D k)⁻¹ * D k = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hD k))
  simp [h1, h2]

/- English proof (translation)
Rewrite using `[Matrix.det_one_sub_mul_comm, ← Matrix.det_transpose (1 - Zᴴ * Z)]`. Use `congr 1`. Rewrite using `[transpose_sub, transpose_one, transpose_mul]`. Use `congr 1`.
-/
theorem det_conj_block {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (Z : Matrix b a ℂ) :
    (1 - (Zᵀ)ᴴ * Zᵀ).det = (1 - Zᴴ * Z).det := by
  rw [Matrix.det_one_sub_mul_comm, ← Matrix.det_transpose (1 - Zᴴ * Z)]
  congr 1
  rw [transpose_sub, transpose_one, transpose_mul]
  congr 1

/- English proof (translation)
Establish `hA : ∀ k, (1 - (ballMat q t k)ᴴ * ballMat q t k).det ≠ 0` using `fun k => (ht k).det_pos.ne'`. Establish `hD : ∀ k, (1 - ((ballMat q t k)ᵀ)ᴴ * (ballMat q t k)ᵀ).det ≠ 0` using `fun k => by`. Rewrite using `[det_conj_block]`. Conclude with `hA k`. Rewrite using `[one_sub_bigZ, inv_blockDiagonal_fromBlocks _ _ hA hD]`.

Simplify using the standard rewrite rules.
-/
theorem inv_apply_inl {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ)
    (ht : t ∈ ballDom q) (τ : Ψ) (a b : Fin j') :
    (1 - (bigZ q t)ᴴ * bigZ q t)⁻¹ (Sum.inl a, τ) (Sum.inl b, τ) =
      ((1 - (ballMat q t τ)ᴴ * ballMat q t τ)⁻¹ : Matrix (Fin j') (Fin j') ℂ) a b := by
  have hA : ∀ k, (1 - (ballMat q t k)ᴴ * ballMat q t k).det ≠ 0 := fun k => (ht k).det_pos.ne'
  have hD : ∀ k, (1 - ((ballMat q t k)ᵀ)ᴴ * (ballMat q t k)ᵀ).det ≠ 0 := fun k => by
    rw [det_conj_block]; exact hA k
  rw [one_sub_bigZ, inv_blockDiagonal_fromBlocks _ _ hA hD]
  simp

/- English proof (translation)
Establish `h : 1 - (bigZe e q t)ᴴ * bigZe e q t = (1 - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm`. Unfold `bigZe`. Establish `h1 : (1 : Matrix (Fin g) (Fin g) ℂ) = (1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ).submatrix e.symm e.symm` using `(submatrix_one_equiv e.symm).symm`. Rewrite using `[conjTranspose_submatrix, submatrix_mul_equiv, h1]`. Both sides reduce to the same expression.

Rewrite using `[h, inv_submatrix_equiv]`.
-/
theorem one_sub_bigZe {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹ = ((1 - (bigZ q t)ᴴ * bigZ q t)⁻¹).submatrix e.symm e.symm := by
  have h : 1 - (bigZe e q t)ᴴ * bigZe e q t = (1 - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm := by
    unfold bigZe
    have h1 : (1 : Matrix (Fin g) (Fin g) ℂ) = (1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ).submatrix e.symm e.symm :=
      (submatrix_one_equiv e.symm).symm
    rw [conjTranspose_submatrix, submatrix_mul_equiv, h1]
    rfl
  rw [h, inv_submatrix_equiv]

/- English proof (translation)
Establish `hpos : 0 < A.det` using `hA.det_pos`. Take `⟨hre, him⟩` from `Complex.pos_iff.mp hpos`. Establish `hreal : A.det = (A.det.re : ℂ)`. Apply the tactic sequence `apply Complex.ext <;> simp [← him]`. Establish `hinv : (A⁻¹).det = ((A.det.re)⁻¹ : ℝ)`.

Rewrite using `[Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hreal]`. Simplify using the standard rewrite rules. Rewrite using `[hinv, Complex.ofReal_re, Real.log_inv]`.
-/
theorem log_det_inv {a : Type} [Fintype a] [DecidableEq a] (A : Matrix a a ℂ) (hA : A.PosDef) :
    Real.log (A⁻¹).det.re = -Real.log A.det.re := by
  have hpos : 0 < A.det := hA.det_pos
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hpos
  have hreal : A.det = (A.det.re : ℂ) := by
    apply Complex.ext <;> simp [← him]
  have hinv : (A⁻¹).det = ((A.det.re)⁻¹ : ℝ) := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hreal]
    simp
  rw [hinv, Complex.ofReal_re, Real.log_inv]

/- English proof (translation)
Unfold `RiemLat.logDet ballPot`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `hG : R.gram (fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = ((1 - (ballMat q t τ)ᴴ * ballMat q t τ)⁻¹)ᵀ`. Use extensionality with `a b`.

Establish `hs : star (Pi.single (e (Sum.inl a, τ)) 1 : Fin g → ℂ) = Pi.single (e (Sum.inl a, τ)) 1`. Use extensionality with `i`. Distinguish the cases in `h : i = e (Sum.inl a, τ)`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_eq_of_ne h]`. Simplify using `only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, hs, transpose_apply]`. Rewrite using `[Matrix.mulVec_single_one, single_one_dotProduct, hH, one_sub_bigZe]`. Simplify using `[inv_apply_inl q t ht]`. Rewrite using `[hG, det_transpose, log_det_inv _ (ht τ)]`.
-/
theorem logDet_coord {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ]
    {j j' n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (R : RiemLat E g Λ) (ht : t ∈ ballDom q)
    (hH : R.Hm = (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹) :
    R.logDet (fun τ (i : Fin j') => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = ballPot q t := by
  unfold RiemLat.logDet ballPot
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hG : R.gram (fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) =
      ((1 - (ballMat q t τ)ᴴ * ballMat q t τ)⁻¹)ᵀ := by
    ext a b
    have hs : star (Pi.single (e (Sum.inl a, τ)) 1 : Fin g → ℂ) = Pi.single (e (Sum.inl a, τ)) 1 := by
      ext i
      by_cases h : i = e (Sum.inl a, τ)
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, hs, transpose_apply]
    rw [Matrix.mulVec_single_one, single_one_dotProduct, hH, one_sub_bigZe]
    simp [inv_apply_inl q t ht]
  rw [hG, det_transpose, log_det_inv _ (ht τ)]

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot
