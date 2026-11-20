import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearIndependentIterates

open Polynomial Matrix

namespace GlobalTheory.ConjLocal

/- English proof (translation)
Introduce `R _ _ n Y Y' h hs`. Take `⟨v, hv⟩` from `exists_isUnit_det_iterMat Y hs`. Take `⟨v', hv'⟩` from `exists_isUnit_det_iterMat Y' (h ▸ hs)`. Set `u : GL (Fin n) R` to `nonsingInvUnit (iterMat Y v) hv`. Set `u' : GL (Fin n) R` to `nonsingInvUnit (iterMat Y' v') hv'`.

Establish `e1 : Y * u.val = u.val * compMat Y.charpoly` using `mul_iterMat Y v`. Establish `e2 : Y' * u'.val = u'.val * compMat Y.charpoly` using `by rw [h]; exact mul_iterMat Y' v'`. Use `⟨u * u'⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc (u⁻¹ : GL (Fin n) R).val, Units.inv_mul, one_mul]`. Use `_ = u'.val * ((u⁻¹ : GL (Fin n) R).val * (Y * u.val)) * (u'⁻¹ : GL (Fin n) R).val := by rw [e1]`. Use `_ = _ := by simp only [mul_assoc]`.
-/
theorem conj_of_charpoly_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y Y' : Matrix (Fin n) (Fin n) R),
    Y.charpoly = Y'.charpoly → Y.charpoly.Separable →
    ∃ g : GL (Fin n) R, Y' = (g⁻¹ : GL (Fin n) R).val * Y * g.val := by
  intro R _ _ n Y Y' h hs
  obtain ⟨v, hv⟩ := exists_isUnit_det_iterMat Y hs
  obtain ⟨v', hv'⟩ := exists_isUnit_det_iterMat Y' (h ▸ hs)
  let u : GL (Fin n) R := nonsingInvUnit (iterMat Y v) hv
  let u' : GL (Fin n) R := nonsingInvUnit (iterMat Y' v') hv'
  have e1 : Y * u.val = u.val * compMat Y.charpoly := mul_iterMat Y v
  have e2 : Y' * u'.val = u'.val * compMat Y.charpoly := by rw [h]; exact mul_iterMat Y' v'
  refine ⟨u * u'⁻¹, ?_⟩
  rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
  calc Y' = Y' * u'.val * (u'⁻¹ : GL (Fin n) R).val := by rw [mul_assoc, Units.mul_inv, mul_one]
    _ = u'.val * compMat Y.charpoly * (u'⁻¹ : GL (Fin n) R).val := by rw [e2]
    _ = u'.val * ((u⁻¹ : GL (Fin n) R).val * (u.val * compMat Y.charpoly)) * (u'⁻¹ : GL (Fin n) R).val := by
      rw [← mul_assoc (u⁻¹ : GL (Fin n) R).val, Units.inv_mul, one_mul]
    _ = u'.val * ((u⁻¹ : GL (Fin n) R).val * (Y * u.val)) * (u'⁻¹ : GL (Fin n) R).val := by rw [e1]
    _ = _ := by simp only [mul_assoc]

end GlobalTheory.ConjLocal
