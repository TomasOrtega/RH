import Mathlib
import Formalism.QuotientMetricDivisors.ClassSumDualLe
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ProdFormula
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic

namespace Bl.HermitianVanishing

open scoped ComplexOrder in
/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hy' : (fun i => φ (y i)) ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Use `congrFun h0 i` as an intermediate fact. Conclude with `φ.injective (by simpa using this)`. Establish `hpos` using `hH.dotProduct_mulVec_pos hy'`. Establish `h1 : φ (dotProduct (star y) (Matrix.mulVec H y)) = dotProduct (star (fun i => φ (y i))) (Matrix.mulVec (H.map φ) fun i => φ (y i))`. Simplify using `only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, Matrix.map_apply, hφ, starRingEnd_apply]`.

Rewrite `h1` using `[hy, map_zero]`. Rewrite `hpos` using `[← h1]`. Conclude with `lt_irrefl _ hpos`.
-/
private lemma key_zero {K : Type} [Field K] [StarRing K] (φ : K →+* ℂ)
    (hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (hH : (H.map φ).PosDef) (y : Fin n → K)
    (hy : dotProduct (star y) (Matrix.mulVec H y) = 0) : y = 0 := by
  by_contra hne
  have hy' : (fun i => φ (y i)) ≠ 0 := by
    intro h0
    apply hne
    funext i
    have := congrFun h0 i
    exact φ.injective (by simpa using this)
  have hpos := hH.dotProduct_mulVec_pos hy'
  have h1 : φ (dotProduct (star y) (Matrix.mulVec H y)) =
      dotProduct (star (fun i => φ (y i))) (Matrix.mulVec (H.map φ) fun i => φ (y i)) := by
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, Matrix.map_apply,
      hφ, starRingEnd_apply]
  rw [hy, map_zero] at h1
  rw [← h1] at hpos
  exact lt_irrefl _ hpos

open scoped ComplexOrder in
/- English proof (translation)
Use extensionality with `i j`. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[Matrix.conjTranspose_apply, hφ, starRingEnd_apply]`. Simplify using `using hH.isHermitian.apply i j`.
-/
private lemma herm_of {K : Type} [Field K] [StarRing K] (φ : K →+* ℂ)
    (hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (hH : (H.map φ).PosDef) : H.conjTranspose = H := by
  ext i j
  apply φ.injective
  rw [Matrix.conjTranspose_apply, hφ, starRingEnd_apply]
  simpa using hH.isHermitian.apply i j

/- English proof (translation)
Unfold `Formalism.DivisionValues.OrthProjExists`. Introduce `K _ _ _ v0 hconj n d H hH E hE`. Establish `hφ : ∀ a, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a)` using `hconj`. Establish `hHerm : H.conjTranspose = H` using `herm_of v0.embedding hφ H hH`. Establish `hdetH : IsUnit H.det`.

Rewrite using `[← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]`. Introduce `x y hxy`. Establish `h0 : Matrix.mulVec H (x - y) = 0` using `by rw [Matrix.mulVec_sub, hxy, sub_self]`. Use `key_zero v0.embedding hφ H hH (x - y) (by rw [h0, dotProduct_zero])` as an intermediate fact. Conclude with `sub_eq_zero.mp this`.

Establish `hMu : IsUnit (E.conjTranspose * H * E).det`. Rewrite using `[← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]`. Introduce `x y hxy`. Establish `h0 : Matrix.mulVec (E.conjTranspose * H * E) (x - y) = 0`. Rewrite using `[Matrix.mulVec_sub, hxy, sub_self]`.

Establish `h1 : dotProduct (star (x - y)) (Matrix.mulVec (E.conjTranspose * H * E) (x - y)) = 0`. Rewrite using `[h0, dotProduct_zero]`. Rewrite `h1` using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`. Establish `h2` using `key_zero v0.embedding hφ H hH (Matrix.mulVec E (x - y)) h1`. Rewrite `h2` using `[Matrix.mulVec_sub, sub_eq_zero]`.

Conclude with `hE h2`. Use `⟨hHerm, hdetH, hMu, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hMu]`. Establish `h3 : E.conjTranspose * H * (E * ((E.conjTranspose * H * E)⁻¹ * (E.conjTranspose * H))) = E.conjTranspose * H`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mul]`.

Rewrite using `[Matrix.mul_sub, Matrix.mul_one, h3, sub_self]`. Introduce `Pr hPr`. Take `⟨_, h2⟩` from `hPr`. Rewrite `h2` using `[Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, ← Matrix.mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.nonsing_inv_mul _ hMu, Matrix.one_mul]`. Use `_ = (E.conjTranspose * H * E)⁻¹ * (E.conjTranspose * H * E * Pr) := Matrix.mul_assoc _ _ _`. Use `_ = (E.conjTranspose * H * E)⁻¹ * (E.conjTranspose * H) := congrArg _ h2.symm`.
-/
theorem goal1 :
  Formalism.DivisionValues.OrthProjExists := by
  unfold Formalism.DivisionValues.OrthProjExists
  intro K _ _ _ v0 hconj n d H hH E hE
  have hφ : ∀ a, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hconj
  have hHerm : H.conjTranspose = H := herm_of v0.embedding hφ H hH
  have hdetH : IsUnit H.det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have h0 : Matrix.mulVec H (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have := key_zero v0.embedding hφ H hH (x - y) (by rw [h0, dotProduct_zero])
    exact sub_eq_zero.mp this
  have hMu : IsUnit (E.conjTranspose * H * E).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have h0 : Matrix.mulVec (E.conjTranspose * H * E) (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have h1 : dotProduct (star (x - y)) (Matrix.mulVec (E.conjTranspose * H * E) (x - y)) = 0 := by
      rw [h0, dotProduct_zero]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.star_mulVec] at h1
    have h2 := key_zero v0.embedding hφ H hH (Matrix.mulVec E (x - y)) h1
    rw [Matrix.mulVec_sub, sub_eq_zero] at h2
    exact hE h2
  refine ⟨hHerm, hdetH, hMu, ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hMu]
  · have h3 : E.conjTranspose * H * (E * ((E.conjTranspose * H * E)⁻¹ * (E.conjTranspose * H)))
        = E.conjTranspose * H := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mul]
    rw [Matrix.mul_sub, Matrix.mul_one, h3, sub_self]
  · intro Pr hPr
    obtain ⟨_, h2⟩ := hPr
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, ← Matrix.mul_assoc] at h2
    calc Pr = ((E.conjTranspose * H * E)⁻¹ * (E.conjTranspose * H * E)) * Pr := by
          rw [Matrix.nonsing_inv_mul _ hMu, Matrix.one_mul]
      _ = (E.conjTranspose * H * E)⁻¹ * (E.conjTranspose * H * E * Pr) := Matrix.mul_assoc _ _ _
      _ = (E.conjTranspose * H * E)⁻¹ * (E.conjTranspose * H) := congrArg _ h2.symm

end Bl.HermitianVanishing
