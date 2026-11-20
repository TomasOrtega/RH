import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

/- English proof (translation)
Simplify using `only [herm, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_mulVec_eq_adj {K : Type} [Field K] (σ : K →+* K)
    {n : ℕ} (x : Matrix (Fin n) (Fin n) K) (y m : Fin n → K) :
    herm σ y (x *ᵥ m) = herm σ ((x.map σ)ᵀ *ᵥ y) m := by
  simp only [herm, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Introduce `O K _ _ _ σ _ n x hx M hM hxM`. Establish `key : ∀ y, y ∈ matLat O x M ↔ (x.map σ)ᵀ *ᵥ y ∈ M`. Introduce `y`. Rewrite using `[hxM y, hM ((x.map σ)ᵀ *ᵥ y)]`. Prove the components needed by the constructor for the conclusion.

Introduce `h m hm`. Rewrite using `[← herm_mulVec_eq_adj]`. Conclude with `h _ ((mem_matLat x M _).2 ⟨m, hm, rfl⟩)`. Introduce `h w hw`. Take `⟨m, hm, rfl⟩` from `(mem_matLat x M w).1 hw`.

Rewrite using `[herm_mulVec_eq_adj]`. Conclude with `h m hm`. Establish `hdet : IsUnit ((x.map σ)ᵀ * x).det`. Establish `e : (x.map σ).det = σ x.det` using `(RingHom.map_det σ x).symm`. Rewrite using `[Matrix.det_mul, Matrix.det_transpose, e]`.

Use `IsUnit.mul ?_ ((Matrix.isUnit_iff_isUnit_det x).1 hx)` and prove the remaining obligations. Establish `h0 : x.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det x).1 hx).ne_zero`. Conclude with `isUnit_iff_ne_zero.2 ((map_ne_zero σ).2 h0)`. Use extensionality with `u`. Rewrite using `[mem_matLat]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, rfl⟩`. Rewrite using `[← Matrix.mulVec_mulVec]`. Conclude with `(key _).1 ((mem_matLat x M _).2 ⟨m, hm, rfl⟩)`. Introduce `hu set A := (x.map σ)ᵀ * x with hA`.

Use `⟨A⁻¹ *ᵥ u, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (x.map σ)ᵀ *ᵥ (x *ᵥ (A⁻¹ *ᵥ u)) ∈ M`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hA, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]`. Conclude with `hu`. Take `⟨m', hm', hxm'⟩` from `(mem_matLat x M _).1 ((key _).2 h1)`.

Establish `: m' = A⁻¹ *ᵥ u`. Establish `hx' : IsUnit x.det` using `(Matrix.isUnit_iff_isUnit_det x).1 hx`. Use `congrArg (fun v => x⁻¹ *ᵥ v) hxm'` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul x hx']`. Conclude with `this ▸ hm'`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]`.
-/
theorem matLat_adj_mul_eq_of_selfDual : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (x : Matrix (Fin n) (Fin n) K), IsUnit x →
    ∀ M : Submodule O (Fin n → K), SelfDual O σ M → SelfDual O σ (matLat O x M) →
    matLat O ((x.map σ)ᵀ * x) M = M := by
  intro O K _ _ _ σ _ n x hx M hM hxM

  have key : ∀ y, y ∈ matLat O x M ↔ (x.map σ)ᵀ *ᵥ y ∈ M := by
    intro y
    rw [hxM y, hM ((x.map σ)ᵀ *ᵥ y)]
    constructor
    · intro h m hm
      rw [← herm_mulVec_eq_adj]
      exact h _ ((mem_matLat x M _).2 ⟨m, hm, rfl⟩)
    · intro h w hw
      obtain ⟨m, hm, rfl⟩ := (mem_matLat x M w).1 hw
      rw [herm_mulVec_eq_adj]
      exact h m hm
  have hdet : IsUnit ((x.map σ)ᵀ * x).det := by
    have e : (x.map σ).det = σ x.det := (RingHom.map_det σ x).symm
    rw [Matrix.det_mul, Matrix.det_transpose, e]
    refine IsUnit.mul ?_ ((Matrix.isUnit_iff_isUnit_det x).1 hx)
    have h0 : x.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det x).1 hx).ne_zero
    exact isUnit_iff_ne_zero.2 ((map_ne_zero σ).2 h0)
  ext u
  rw [mem_matLat]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [← Matrix.mulVec_mulVec]
    exact (key _).1 ((mem_matLat x M _).2 ⟨m, hm, rfl⟩)
  · intro hu
    set A := (x.map σ)ᵀ * x with hA
    refine ⟨A⁻¹ *ᵥ u, ?_, ?_⟩
    · have h1 : (x.map σ)ᵀ *ᵥ (x *ᵥ (A⁻¹ *ᵥ u)) ∈ M := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hA,
          Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
        exact hu
      obtain ⟨m', hm', hxm'⟩ := (mem_matLat x M _).1 ((key _).2 h1)
      have : m' = A⁻¹ *ᵥ u := by
        have hx' : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).1 hx
        have := congrArg (fun v => x⁻¹ *ᵥ v) hxm'
        simpa [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul x hx'] using this
      exact this ▸ hm'
    · rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]

end GlobalTheory.LatOrb
