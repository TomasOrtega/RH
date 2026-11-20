import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.GlCongr

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem blkAt_apply_lemma {n m : ℕ} (x : Fin (n + m)) :
    finSumFinEquiv.symm x =
      if hx : (x : ℕ) < n then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x - n, by omega⟩ := by
  split_ifs with hx
  · exact (Equiv.symm_apply_eq _).2 (Fin.ext (by simp))
  · exact (Equiv.symm_apply_eq _).2 (Fin.ext (by simp; omega))

/- English proof (translation)
Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem blkAt_apply (n N : ℕ) (h : n ≤ N) (g : GL (Fin n) k) (a b : Fin N) :
    ((blkAt k n N h g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) a b =
      if ha : (a : ℕ) < n then (if hb : (b : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨a, ha⟩ ⟨b, hb⟩ else 0)
      else (if a = b then 1 else 0) := by
  simp only [blkAt, blkGL, glCongr, blkHom, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_comp,
    MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]
  simp [reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply, blkAt_apply_lemma]
  split_ifs with ha hb hab <;> simp_all [Fin.ext_iff]
  · omega
  · rw [Matrix.one_apply_ne]
    intro e
    rw [Fin.ext_iff] at e
    simp only at e
    omega

end PositivityTheory.RgUd.Form.U.Asm
