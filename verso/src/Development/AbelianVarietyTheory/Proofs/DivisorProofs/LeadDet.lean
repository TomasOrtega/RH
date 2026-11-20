import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColsComplete
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.LeadDet

/- English proof (translation)
Introduce `R C _ _ f ξ ν N F G lam hFG hI`. Use `set a := (G.map f).rank with ha`. Take `⟨haN, k, k', hdet⟩` from `GlobalTheory.ColComplete.cols_complete C N (G.map f)`. Rewrite `hdet` using `[← ha]`. Set `X : Fin N → Fin N → R` to `fun i => if (i : ℕ) < a then G *ᵥ Pi.single (k i) 1 else Pi.single (k' i) 1`.

Set `Y : Fin N → Fin N → R` to `fun i => if (i : ℕ) < a then Pi.single (k i) 1 else F *ᵥ Pi.single (k' i) 1`. Set `c : Fin N → R` to `fun i => if (i : ℕ) < a then ξ * ν else 1`. Establish `hFGv : ∀ v, F *ᵥ (G *ᵥ v) = (ξ * ν) • v`. Introduce `v`. Rewrite using `[mulVec_mulVec, hFG]`.

Use extensionality with `j`. Simplify using `[mulVec, dotProduct, Matrix.one_apply, Finset.mul_sum]`. Establish `hrow : Matrix.of X * Fᵀ = diagonal c * Matrix.of Y`. Use extensionality with `i j`. Rewrite using `[diagonal_mul, mul_apply]`.

Establish `: (∑ l, Matrix.of X i l * Fᵀ l j) = (F *ᵥ X i) j`. Simplify using `[mulVec, dotProduct, mul_comm]`. Rewrite using `[this]`. Distinguish the cases in `hi : (i : ℕ) < a`. Simplify using `only [X, Y, c, hi, if_true, of_apply]`.

Rewrite using `[hFGv]`. Simplify using the standard rewrite rules. Simplify using `[X, Y, c, hi]`. Establish `hdetR : (Matrix.of X).det * F.det = (ξ * ν) ^ a * (Matrix.of Y).det`. Use `congrArg Matrix.det hrow` as an intermediate fact.

Rewrite `this` using `[det_mul, det_mul, det_transpose, det_diagonal]`. Rewrite using `[this]`. Use `congr 1`. Simplify using `only [c]`. Rewrite using `[Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]`.

Use `congr 1`. Rewrite `haN` using `[← ha]`. Establish `hm : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < a)).map Fin.valEmbedding = Finset.range a`. Use extensionality with `m`. Simplify using `only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi, rfl⟩`. Conclude with `hi`. Introduce `h; exact ⟨⟨m, by omega⟩, h, rfl⟩`. Rewrite using `[← Finset.card_map Fin.valEmbedding, hm, Finset.card_range]`.

Establish `hxmap : (Matrix.of X).map f = Matrix.of (fun i : Fin N => if (i : ℕ) < a then G.map f *ᵥ Pi.single (k i) 1 else Pi.single (k' i) 1)`. Use extensionality with `i j`. Distinguish the cases in `hi : (i : ℕ) < a`. Simplify using `[X, hi, RingHom.map_mulVec]`. Simplify using `[X, hi, Pi.single_apply, apply_ite f]`.

Establish `hymap : ∀ i, (Matrix.of Y).map f i = if (i : ℕ) < a then Pi.single (k i) 1 else F.map f *ᵥ Pi.single (k' i) 1`. Introduce `i`. Use extensionality with `j`. Distinguish the cases in `hi : (i : ℕ) < a`. Simplify using `[Y, hi, Pi.single_apply, apply_ite f]`.

Simplify using `[Y, hi, RingHom.map_mulVec]`. Establish `hY` using `hI (fun i => if (i : ℕ) < a then G.map f *ᵥ Pi.single (k i) 1 else Pi.single (k' i) 1) (fun i => (Matrix.of Y).map f i) (by intro i hi; rw [hymap]; simp [hi]) (by intro i hi; rw [hymap]; simp [Nat.not_lt.mpr hi])`. Use `⟨(Matrix.of X).det, ν ^ a * (Matrix.of Y).det, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hxmap]`. Conclude with `hdet`.

Rewrite using `[hdetR, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, map_pow, RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hxmap]`. Establish `: Matrix.of (fun i => (Matrix.of Y).map f i) = (Matrix.of Y).map f` using `rfl`. Rewrite `hY` using `[this]`.

Rewrite using `[hY]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lead_det : ∀ (R C : Type) [CommRing R] [Field C] (f : R →+* C) (ξ ν : R) (N : ℕ) (F G : Matrix (Fin N) (Fin N) R) (lam : C), F * G = (ξ * ν) • (1 : Matrix (Fin N) (Fin N) R) → IotaScalar (F.map f) (G.map f) (G.map f).rank lam → Lead f ξ F.det (G.map f).rank (lam * f ν ^ (G.map f).rank) := by
  intro R C _ _ f ξ ν N F G lam hFG hI
  set a := (G.map f).rank with ha
  obtain ⟨haN, k, k', hdet⟩ := GlobalTheory.ColComplete.cols_complete C N (G.map f)
  rw [← ha] at hdet
  let X : Fin N → Fin N → R := fun i => if (i : ℕ) < a then G *ᵥ Pi.single (k i) 1 else Pi.single (k' i) 1
  let Y : Fin N → Fin N → R := fun i => if (i : ℕ) < a then Pi.single (k i) 1 else F *ᵥ Pi.single (k' i) 1
  let c : Fin N → R := fun i => if (i : ℕ) < a then ξ * ν else 1
  have hFGv : ∀ v, F *ᵥ (G *ᵥ v) = (ξ * ν) • v := by
    intro v; rw [mulVec_mulVec, hFG]; ext j; simp [mulVec, dotProduct, Matrix.one_apply, Finset.mul_sum]
  have hrow : Matrix.of X * Fᵀ = diagonal c * Matrix.of Y := by
    ext i j
    rw [diagonal_mul, mul_apply]
    have : (∑ l, Matrix.of X i l * Fᵀ l j) = (F *ᵥ X i) j := by
      simp [mulVec, dotProduct, mul_comm]
    rw [this]
    by_cases hi : (i : ℕ) < a
    · simp only [X, Y, c, hi, if_true, of_apply]; rw [hFGv]; simp
    · simp [X, Y, c, hi]
  have hdetR : (Matrix.of X).det * F.det = (ξ * ν) ^ a * (Matrix.of Y).det := by
    have := congrArg Matrix.det hrow
    rw [det_mul, det_mul, det_transpose, det_diagonal] at this
    rw [this]; congr 1
    simp only [c]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    congr 1
    rw [← ha] at haN
    have hm : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < a)).map Fin.valEmbedding = Finset.range a := by
      ext m; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro h; exact ⟨⟨m, by omega⟩, h, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, hm, Finset.card_range]
  have hxmap : (Matrix.of X).map f = Matrix.of (fun i : Fin N => if (i : ℕ) < a then G.map f *ᵥ Pi.single (k i) 1 else Pi.single (k' i) 1) := by
    ext i j
    by_cases hi : (i : ℕ) < a
    · simp [X, hi, RingHom.map_mulVec]
    · simp [X, hi, Pi.single_apply, apply_ite f]
  have hymap : ∀ i, (Matrix.of Y).map f i = if (i : ℕ) < a then Pi.single (k i) 1 else F.map f *ᵥ Pi.single (k' i) 1 := by
    intro i; ext j
    by_cases hi : (i : ℕ) < a
    · simp [Y, hi, Pi.single_apply, apply_ite f]
    · simp [Y, hi, RingHom.map_mulVec]
  have hY := hI (fun i => if (i : ℕ) < a then G.map f *ᵥ Pi.single (k i) 1 else Pi.single (k' i) 1) (fun i => (Matrix.of Y).map f i)
    (by intro i hi; rw [hymap]; simp [hi]) (by intro i hi; rw [hymap]; simp [Nat.not_lt.mpr hi])
  refine ⟨(Matrix.of X).det, ν ^ a * (Matrix.of Y).det, ?_, ?_, ?_⟩
  · rw [RingHom.map_det, RingHom.mapMatrix_apply, hxmap]; exact hdet
  · rw [hdetR, mul_pow]; ring
  · rw [map_mul, map_pow, RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hxmap]
    have : Matrix.of (fun i => (Matrix.of Y).map f i) = (Matrix.of Y).map f := rfl
    rw [this] at hY; rw [hY]; ring

end GlobalTheory.LeadDet
