import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
open Polynomial Matrix

namespace GlobalTheory.LocalCommutant

open GlobalTheory.ClassParam

variable {S : Type} [CommRing S] {n : ℕ}

/- English proof (translation)
Use extensionality with `i`. Simplify using `[krylov, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.
-/
theorem krylov_mulVec (Y : Matrix (Fin n) (Fin n) S) (v c : Fin n → S) :
    krylov Y v *ᵥ c = ∑ j, c j • (Y ^ (j : ℕ) *ᵥ v) := by
  ext i
  simp [krylov, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/- English proof (translation)
Simplify using `[map_sum, aeval_monomial, Algebra.smul_def]`.
-/
theorem aeval_sum_monomial (Y : Matrix (Fin n) (Fin n) S) (c : Fin n → S) :
    aeval Y (∑ j : Fin n, monomial (j : ℕ) (c j)) = ∑ j : Fin n, c j • Y ^ (j : ℕ) := by
  simp [map_sum, aeval_monomial, Algebra.smul_def]

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_cyclic_field (Y.map (IsLocalRing.residue R)) (by rw [charpoly_map]; exact hs.map)`. Use `choose e he using fun i => IsLocalRing.residue_surjective (w i)`. Use `⟨e, (Matrix.isUnit_iff_isUnit_det _).2 ?_⟩` and prove the remaining obligations. Establish `h1 : w = (IsLocalRing.residue R) ∘ e` using `funext fun i => (he i).symm`. Rewrite `hw` using `[h1, ← krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`.

Conclude with `(isUnit_map_iff (IsLocalRing.residue R) _).1 (isUnit_iff_ne_zero.2 hw)`.
-/
theorem exists_isUnit_krylov (R : Type) [CommRing R] [IsLocalRing R] (Y : Matrix (Fin n) (Fin n) R)
    (hs : Y.charpoly.Separable) : ∃ v, IsUnit (krylov Y v) := by
  obtain ⟨w, hw⟩ := exists_cyclic_field (Y.map (IsLocalRing.residue R)) (by rw [charpoly_map]; exact hs.map)
  choose e he using fun i => IsLocalRing.residue_surjective (w i)
  refine ⟨e, (Matrix.isUnit_iff_isUnit_det _).2 ?_⟩
  have h1 : w = (IsLocalRing.residue R) ∘ e := funext fun i => (he i).symm
  rw [h1, ← krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hw
  exact (isUnit_map_iff (IsLocalRing.residue R) _).1 (isUnit_iff_ne_zero.2 hw)

/- English proof (translation)
Take `⟨e, hK⟩` from `exists_isUnit_krylov R Y hs`. Establish `hdet` using `(Matrix.isUnit_iff_isUnit_det _).1 hK`. Use `set K := krylov Y e`. Use `set c := K⁻¹ *ᵥ (T *ᵥ e)`. Use `⟨∑ j : Fin n, monomial (j : ℕ) (c j), ?_⟩` and prove the remaining obligations.

Use `set p : R[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)`. Use `set D := T - aeval Y p`. Establish `hKc : K *ᵥ c = T *ᵥ e`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]`. Establish `hDe : D *ᵥ e = 0`.

Establish `h2 : aeval Y p *ᵥ e = K *ᵥ c`. Rewrite using `[aeval_sum_monomial, Matrix.sum_mulVec, krylov_mulVec]`. Simplify using `[Matrix.smul_mulVec]`. Rewrite using `[Matrix.sub_mulVec, h2, hKc, sub_self]`. Establish `hpY : aeval Y p * Y = Y * aeval Y p`.

Combine the equalities or inequalities in the displayed calculation. Establish `hDY : Commute D Y` using `Commute.sub_left hc hpY`. Establish `hDK : D * K = 0`. Use extensionality with `i j`. Establish `h2 : D *ᵥ (Y ^ (j : ℕ) *ᵥ e) = 0`.

Rewrite using `[Matrix.mulVec_mulVec, (hDY.pow_right _).eq, ← Matrix.mulVec_mulVec, hDe, Matrix.mulVec_zero]`. Use `congrFun h2 i` as an intermediate fact. Simplify `this` using `[K, krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Establish `hD : D = 0`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `sub_eq_zero.1 hD`.
-/
theorem exists_aeval_of_comm (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ)
    (Y T : Matrix (Fin n) (Fin n) R) (hs : Y.charpoly.Separable) (hc : T * Y = Y * T) :
    ∃ p : R[X], T = aeval Y p := by
  obtain ⟨e, hK⟩ := exists_isUnit_krylov R Y hs
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hK
  set K := krylov Y e
  set c := K⁻¹ *ᵥ (T *ᵥ e)
  refine ⟨∑ j : Fin n, monomial (j : ℕ) (c j), ?_⟩
  set p : R[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)
  set D := T - aeval Y p
  have hKc : K *ᵥ c = T *ᵥ e := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hDe : D *ᵥ e = 0 := by
    have h2 : aeval Y p *ᵥ e = K *ᵥ c := by
      rw [aeval_sum_monomial, Matrix.sum_mulVec, krylov_mulVec]
      simp [Matrix.smul_mulVec]
    rw [Matrix.sub_mulVec, h2, hKc, sub_self]
  have hpY : aeval Y p * Y = Y * aeval Y p := by
    calc aeval Y p * Y = aeval Y (p * X) := by simp
      _ = aeval Y (X * p) := by rw [mul_comm]
      _ = Y * aeval Y p := by simp
  have hDY : Commute D Y := Commute.sub_left hc hpY
  have hDK : D * K = 0 := by
    ext i j
    have h2 : D *ᵥ (Y ^ (j : ℕ) *ᵥ e) = 0 := by
      rw [Matrix.mulVec_mulVec, (hDY.pow_right _).eq, ← Matrix.mulVec_mulVec, hDe, Matrix.mulVec_zero]
    have := congrFun h2 i
    simpa [K, krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hD : D = 0 := by
    calc D = D * K * K⁻¹ := by rw [mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
      _ = 0 := by rw [hDK, zero_mul]
  exact sub_eq_zero.1 hD

/- English proof (translation)
The claim follows from `exists_aeval_of_comm`.
-/
example : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y T : Matrix (Fin n) (Fin n) R),
    Y.charpoly.Separable → T * Y = Y * T → ∃ p : R[X], T = aeval Y p := exists_aeval_of_comm

end GlobalTheory.LocalCommutant
