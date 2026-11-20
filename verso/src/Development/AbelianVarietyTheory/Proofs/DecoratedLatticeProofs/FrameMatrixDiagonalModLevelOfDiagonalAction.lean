import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuProj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameDiag

/- English proof (translation)
Use `show Submodule.span _ _ = Submodule.span _ _`. Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`.

Conclude with `⟨⟨z, hz⟩, rfl⟩`. Introduce and unpack `⟨z, rfl⟩`. Conclude with `⟨z.1, z.2, rfl⟩`.
-/
theorem hatL_eq (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.1, z.2, rfl⟩

/- English proof (translation)
Take `⟨z, hz, rfl⟩` from `GlobalTheory.RowIndex.mem_mL.1 hv`. Establish `hz' : z ∈ Formalism.L2.Herm.hatL (F` using `I.F) I.L := by rw [hatL_eq]; exact hz`. Use `⟨_, (hβ z).1 hz' i, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul]`. Both sides reduce to the same expression.
-/
theorem coord_zmod (I : AutInst) (g : ℕ) {β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : IsFrame β I.L) {v : VA I}
    (hv : v ∈ mL I g) (i : Fin I.n) :
    ZMod' I g ((((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v) i) := by
  obtain ⟨z, hz, rfl⟩ := GlobalTheory.RowIndex.mem_mL.1 hv
  have hz' : z ∈ Formalism.L2.Herm.hatL (F := I.F) I.L := by rw [hatL_eq]; exact hz
  refine ⟨_, (hβ z).1 hz' i, ?_⟩
  rw [Matrix.mulVec_smul]
  rfl

/- English proof (translation)
Introduce `I g b β Y d hβ hY hYi hd`. Establish `hK : Y ∈ I.Kset`. Introduce `y`. Use `⟨fun hy => hY y hy, fun hy => ?_⟩` and prove the remaining obligations. Establish `h` using `hYi _ hy`.

Establish `e : I.fmat Y⁻¹ * I.fmat Y = 1` using `by show (((Y⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) * _ = 1`. Rewrite using `[Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Rewrite `h` using `[Matrix.mulVec_mulVec, e, Matrix.one_mulVec]`. Then use the resulting hypothesis. Take `⟨x, hx⟩` from `(kset_iff I hβ.1 Y).1 hK`. Use `⟨x, hx, fun i j => ?_⟩` and prove the remaining obligations.

Establish `hconj : β⁻¹ * frGL β x * β = intGL I.F I.E I.n x`. Simplify using `only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Use `group`. Rewrite `hconj` using `[hx]`. Use `set col : VA I := fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) l j with hcol`.

Establish `hw : I.fmat Y *ᵥ col - (d j).1 • col ∈ mL I g`. Establish `h1` using `hβ.2 j`. Take `⟨z, hz, hz'⟩` from `GlobalTheory.RowIndex.mem_mL.1 h1`. Establish `h2 : I.fmat Y *ᵥ (col - b j.val) ∈ mL I g`. Rewrite using `[show col - b j.val = _ from hz']`.

Conclude with `Formalism.L2.SG.Pf.unitaryCongruence.mL_mv I hY g le_rfl z hz`. Establish `h3 : (d j).1 • (col - b j.val) ∈ mL I g` using `(mL I g).smul_mem (d j) h1`. Establish `e : I.fmat Y *ᵥ col - (d j).1 • col = (I.fmat Y *ᵥ b j.val - (d j).1 • b j.val) + I.fmat Y *ᵥ (col - b j.val) - (d j).1 • (col - b j.val)`. Rewrite using `[Matrix.mulVec_sub, smul_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `sub_mem (add_mem (hd j) h2) h3`. Establish `key` using `coord_zmod I g hβ.1 hw i`. Use `key using 1` and compare the differences between its conclusion and the goal. Establish `eA : (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ (I.fmat Y *ᵥ col)) i = ((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) i j).1`.

Rewrite using `[Matrix.mulVec_mulVec]`. Use `show ((((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) * I.fmat Y) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))) i j = _`. Rewrite using `[← Units.val_mul, ← Units.val_mul, hconj]`. Both sides reduce to the same expression. Establish `eB : (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ col) i = if i = j then 1 else 0` using `by show (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))) i j = _`.

Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]`. Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, eA, eB, Matrix.sub_apply, Matrix.diagonal_apply]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem diag_mod_in_frame : ∀ (I : AutInst) (g : ℕ) (b : ℕ → VA I) (β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) (Y : I.Gf) (d : Fin I.n → Formalism.L2.Herm.intAf I.F I.E), IsLiftFrame I g b β → (∀ y ∈ I.Lf, I.fmat Y *ᵥ y ∈ I.Lf) → (∀ y ∈ I.Lf, I.fmat Y⁻¹ *ᵥ y ∈ I.Lf) → (∀ j : Fin I.n, I.fmat Y *ᵥ b j.val - (d j).1 • b j.val ∈ mL I g) → ∃ x : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), frGL β x = (Y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∧ ∀ i j, ZMod' I g (((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) - Matrix.diagonal d) i j).1 := by
  intro I g b β Y d hβ hY hYi hd
  have hK : Y ∈ I.Kset := by
    intro y
    refine ⟨fun hy => hY y hy, fun hy => ?_⟩
    have h := hYi _ hy
    have e : I.fmat Y⁻¹ * I.fmat Y = 1 := by
      show (((Y⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) * _ = 1
      rw [Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rwa [Matrix.mulVec_mulVec, e, Matrix.one_mulVec] at h
  obtain ⟨x, hx⟩ := (kset_iff I hβ.1 Y).1 hK
  refine ⟨x, hx, fun i j => ?_⟩
  have hconj : β⁻¹ * frGL β x * β = intGL I.F I.E I.n x := by
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hx] at hconj
  set col : VA I := fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) l j with hcol
  have hw : I.fmat Y *ᵥ col - (d j).1 • col ∈ mL I g := by
    have h1 := hβ.2 j
    obtain ⟨z, hz, hz'⟩ := GlobalTheory.RowIndex.mem_mL.1 h1
    have h2 : I.fmat Y *ᵥ (col - b j.val) ∈ mL I g := by
      rw [show col - b j.val = _ from hz']
      exact Formalism.L2.SG.Pf.unitaryCongruence.mL_mv I hY g le_rfl z hz
    have h3 : (d j).1 • (col - b j.val) ∈ mL I g := (mL I g).smul_mem (d j) h1
    have e : I.fmat Y *ᵥ col - (d j).1 • col =
        (I.fmat Y *ᵥ b j.val - (d j).1 • b j.val) + I.fmat Y *ᵥ (col - b j.val) - (d j).1 • (col - b j.val) := by
      rw [Matrix.mulVec_sub, smul_sub]
      abel
    rw [e]
    exact sub_mem (add_mem (hd j) h2) h3
  have key := coord_zmod I g hβ.1 hw i
  convert key using 1
  have eA : (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ (I.fmat Y *ᵥ col)) i =
      ((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) i j).1 := by
    rw [Matrix.mulVec_mulVec]
    show ((((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) * I.fmat Y) *
      (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))) i j = _
    rw [← Units.val_mul, ← Units.val_mul, hconj]
    rfl
  have eB : (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ col) i =
      if i = j then 1 else 0 := by
    show (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *
      (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))) i j = _
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, eA, eB, Matrix.sub_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    simp
  · simp

end GlobalTheory.FrameDiag

end
