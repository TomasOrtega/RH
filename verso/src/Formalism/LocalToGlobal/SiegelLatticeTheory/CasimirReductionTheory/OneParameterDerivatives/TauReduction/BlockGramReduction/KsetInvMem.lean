import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow

set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kset_inv_mem (I : AutInst) {k : I.Gf} (hk : k ∈ I.Kset) : k⁻¹ ∈ I.Kset := by
  exact (Formalism.UG.stabGL I.Lf).inv_mem hk

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem t4 : LatticeRightInvariant := by
  intro I x y k hk
  ext u
  show (I.fmat (x * (y, k)).2⁻¹) *ᵥ _ ∈ I.Lf ↔ (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
  have hk' : ∀ w, w ∈ I.Lf ↔ I.fmat k⁻¹ *ᵥ w ∈ I.Lf := kset_inv_mem I hk
  have e : I.fmat (x * (y, k)).2⁻¹ = I.fmat k⁻¹ * I.fmat x.2⁻¹ := by
    simp only [AutInst.fmat, Prod.snd_mul, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul]
  rw [e, ← Matrix.mulVec_mulVec]
  exact (hk' _).symm

end Formalism.L2.SG.Pf.Tau
