import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.Dblock.ComapLat

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem comap_mulVec_compact_open : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : Matrix (Fin n) (Fin n) k), IsUnit g → ∀ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧ IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) := by
  intro k _ _ _ _ n g hg A hc ho
  haveI : IsTopologicalRing k := inferInstance
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  have hcont : ∀ m : Matrix (Fin n) (Fin n) k, Continuous (fun x : Fin n → k => m.mulVec x) :=
    fun m => continuous_const.matrix_mulVec continuous_id
  have hset : ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k))
      = (fun x : Fin n → k => g.mulVec x) ⁻¹' (A : Set (Fin n → k)) := rfl
  rw [hset]
  refine ⟨?_, ho.preimage (hcont g)⟩
  have himg : (fun x : Fin n → k => g.mulVec x) ⁻¹' (A : Set (Fin n → k))
      = (fun x : Fin n → k => g⁻¹.mulVec x) '' (A : Set (Fin n → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨g.mulVec x, hx, ?_⟩
      simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hdet, Matrix.one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hdet,
        Matrix.one_mulVec]
      exact hy
  rw [himg]
  exact hc.image (hcont g⁻¹)

end GlobalTheory.CompanionTheory.Dblock.ComapLat
