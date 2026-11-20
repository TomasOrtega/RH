import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.EqOneOfUniLevi
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ContinuousProjFInv

noncomputable section

namespace PI.IwaMeasEx.LP

open Matrix NumberField Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.WittLeviSubgroups PI.IwaMeasEx.PD PI.IwaMeasEx.AfT
open scoped TensorProduct

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Both sides reduce to the same expression.
-/
theorem colF_cols : Fr.colF = cols (eW Fr) (frF Fr) := by
  funext r i; rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Both sides reduce to the same expression.
-/
theorem colV_cols (v : InfinitePlace I.F) : Fr.colV v = cols (eW Fr) (Fr.frV v) := by
  funext r i; rfl

/- English proof (translation)
By extensionality, compare the relevant components. Both sides reduce to the same expression.
-/
theorem cT_star {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem gramF : (Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (frF Fr) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
    frF Fr).submatrix (eW Fr) (eW Fr) = (wittJ (J := J) Fr.J0).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  rw [frF, cT_map, ← Matrix.map_mul, ← Matrix.map_mul, submatrix_map]
  congr 1
  exact Gm_sub Fr

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem gramV (v : InfinitePlace I.F) : (Formalism.UG.cT (starRingEnd ℂ) (Fr.frV v) * Formalism.REAL.Jm (I.ε v) *
    Fr.frV v).submatrix (eW Fr) (eW Fr) = (wittJ (J := J) Fr.J0).map (I.φ v) := by
  have hc : ∀ M : Matrix (Fin I.n) (Fin I.n) I.E, (M.map (I.φ v))ᴴ = Mᴴ.map (I.φ v) := fun M =>
    (conjTranspose_map _ (semiconj_phi v)).symm
  have e1 : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← conjTranspose_mul, rrg_P_mul_inv, conjTranspose_one]
  have hJm : Formalism.REAL.Jm (I.ε v) = (I.P v)ᴴ * I.J.map (I.φ v) * I.P v := (I.P_spec v).symm
  have key : (Fr.frV v)ᴴ * Formalism.REAL.Jm (I.ε v) * Fr.frV v = (Gm Fr).map (I.φ v) := by
    calc (Fr.frV v)ᴴ * Formalism.REAL.Jm (I.ε v) * Fr.frV v
        = ((Bm Fr).map (I.φ v))ᴴ * (((I.P v)⁻¹)ᴴ * (I.P v)ᴴ) * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) *
            (Bm Fr).map (I.φ v) := by
          rw [hJm]; simp only [WittFrame.frV, conjTranspose_mul, Matrix.mul_assoc]
      _ = (Gm Fr).map (I.φ v) := by
          rw [e1, rrg_P_mul_inv, hc]; simp only [Gm, Matrix.map_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  rw [cT_star, key, submatrix_map]
  congr 1
  exact Gm_sub Fr

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem alevF : ALev (levW (n₀ := nz I J) c) c.length ((wittJ (J := J) Fr.J0).map (Formalism.UG.inclE (F := I.F) (Af I.F))) :=
  fun q r h => antiLev_wittJ c Fr.J0 q r (fun h' => h (by rw [Matrix.map_apply, h', map_zero]))

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem alevV (v : InfinitePlace I.F) : ALev (levW (n₀ := nz I J) c) c.length ((wittJ (J := J) Fr.J0).map (I.φ v)) :=
  fun q r h => antiLev_wittJ c Fr.J0 q r (fun h' => h (by rw [Matrix.map_apply, h', map_zero]))

variable {Fr c}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem parF {x : I.GA} (hx : x ∈ parA Fr c) : projF I x ∈ parGL (cols (eW Fr) (frF Fr)) (levW c) := by
  rw [← colF_cols]; exact (Subgroup.mem_inf.1 hx).1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem parV {x : I.GA} (hx : x ∈ parA Fr c) (v : InfinitePlace I.F) :
    projV I v x ∈ parGL (cols (eW Fr) (Fr.frV v)) (levW c) := by
  rw [← colV_cols]; exact Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 v

def levF {x : I.GA} (hx : x ∈ parA Fr c) : I.Gf :=
  ⟨levGL (eW Fr) (levW c) (frF_mul Fr) (frFi_mul Fr) (projF I x) (parF hx),
    levGL_unitary (eW Fr) (levW c) (frF_mul Fr) (frFi_mul Fr) (parF hx) _ _ (gramF Fr) (alevF Fr c) x.2.2⟩

def levV {x : I.GA} (hx : x ∈ parA Fr c) (v : InfinitePlace I.F) : Formalism.REAL.UJ (I.ε v) :=
  ⟨levGL (eW Fr) (levW c) (frV_mul Fr v) (frVi_mul Fr v) (projV I v x) (parV hx v), by
    have hU : projV I v x ∈ Formalism.UG.UJ (starRingEnd ℂ) (Formalism.REAL.Jm (I.ε v)) := by
      show Formalism.UG.cT (starRingEnd ℂ) (uMat (x.1 v)) * Formalism.REAL.Jm (I.ε v) * uMat (x.1 v) = Formalism.REAL.Jm (I.ε v)
      rw [cT_star]; exact (x.1 v).2
    have h := levGL_unitary (eW Fr) (levW c) (frV_mul Fr v) (frVi_mul Fr v) (parV hx v) _ _ (gramV Fr v)
      (alevV Fr c v) hU
    have h' : Formalism.UG.cT (starRingEnd ℂ) ((levGL (eW Fr) (levW c) (frV_mul Fr v) (frVi_mul Fr v) (projV I v x)
        (parV hx v) : GL (Fin I.n) ℂ) : Matrix (Fin I.n) (Fin I.n) ℂ) * Formalism.REAL.Jm (I.ε v) *
        ((levGL (eW Fr) (levW c) (frV_mul Fr v) (frVi_mul Fr v) (projV I v x) (parV hx v) : GL (Fin I.n) ℂ) :
          Matrix (Fin I.n) (Fin I.n) ℂ) = Formalism.REAL.Jm (I.ε v) := h
    rw [cT_star] at h'
    exact h'⟩

def levA {x : I.GA} (hx : x ∈ parA Fr c) : I.GA := (fun v => levV hx v, levF hx)

variable (Fr c)

variable {Fr c}

end PI.IwaMeasEx.LP

end
