import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabUMapEqOfRoots
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.RationalFrame

open NumberField Formalism.L2.SG.PoincareInHH

/- English proof (translation)
Unfold `hJ`. Simplify using `only [mulVec_add, mulVec_sum, mulVec_smul, dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul]`.
-/
theorem hJ_lin {n : ℕ} (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (x : Fin n → ℂ) (g : ι → ℂ)
    (y : ι → Fin n → ℂ) (c : ℂ) (w : Fin n → ℂ) :
    hJ ε x (∑ i, g i • y i + c • w) = ∑ i, g i * hJ ε x (y i) + c * hJ ε x w := by
  unfold hJ
  simp only [mulVec_add, mulVec_sum, mulVec_smul, dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Establish `hfr : Formalism.L2.SG.RealObj.frm X u 1 v = Formalism.L2.SG.RealObj.fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))`. Use function extensionality and compare the values at `a`. Simplify using `[Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc]`. Establish `hze : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.eR a)) = 0`. Introduce `a`.

Use `(Cut.hJ_crd X v _ _).trans ?_` and prove the remaining obligations. Establish `h` using `(VS D).herm.eq (X.eX a) (X.zu u)`. Rewrite `h` using `[(X.zu_orth u a).1]`. Rewrite using `[← h]`. Simplify using the standard rewrite rules.

Establish `hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) ≠ 0`. Rewrite using `[HidaSetting.zR, Cut.hJ_crd X v, X.zu_norm]`. Simplify using `only [map_neg, map_natCast, neg_ne_zero, Nat.cast_ne_zero]`. Conclude with `((D.mem u).A.T_prime).ne_zero`. Establish `hfe : ∀ j a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.eR a)) = if a = j then 1 else 0`.

Introduce `j a`. Use `(Cut.hJ_crd X v _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Cut.hT_f_e X]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hfz : ∀ j, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.zR u)) = 0`.

Introduce `j`. Use `(Cut.hJ_crd X v _ _).trans ?_` and prove the remaining obligations. Rewrite using `[(X.zu_orth u j).2]`. Simplify using the standard rewrite rules. Rewrite using `[hfr, Fintype.linearIndependent_iff]`.

Introduce `g hg`. Rewrite `hg` using `[Fin.sum_univ_castSucc]`. Simplify using `only [Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc, Fin.snoc_last] at hg`. Establish `hlast : g (Fin.last _) = 0`. Establish `h` using `congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.zR u))) hg`.

Rewrite `h` using `[hJ_lin]`. Simplify using `only [hze, mul_zero, Finset.sum_const_zero, zero_add] at h`. Unfold `hJ at h`. Simplify using `only [mulVec_zero, dotProduct_zero] at h`. Conclude with `(mul_eq_zero.1 h).resolve_right hzz`.

Introduce `i`. Use `Fin.lastCases hlast (fun j => ?_) i` and prove the remaining obligations. Establish `h` using `congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.fR j))) hg`. Rewrite `h` using `[hJ_lin, hfz]`. Simplify using `only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero] at h`.

Unfold `hJ at h`. Simplify using `only [mulVec_zero, dotProduct_zero] at h`. Conclude with `h`.
-/
theorem frame_linearIndependent (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    LinearIndependent ℂ (Formalism.L2.SG.RealObj.frm X u 1 v) := by
  have hfr : Formalism.L2.SG.RealObj.frm X u 1 v = Formalism.L2.SG.RealObj.fam (fun a => rv X.B.I v (X.eR a))
      (rv X.B.I v (X.zR u)) := by
    funext a
    simp [Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc]
  have hze : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.eR a)) = 0 := by
    intro a
    refine (Cut.hJ_crd X v _ _).trans ?_
    have h := (VS D).herm.eq (X.eX a) (X.zu u)
    rw [(X.zu_orth u a).1] at h
    rw [← h]
    simp
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) ≠ 0 := by
    rw [HidaSetting.zR, Cut.hJ_crd X v, X.zu_norm]
    simp only [map_neg, map_natCast, neg_ne_zero, Nat.cast_ne_zero]
    exact ((D.mem u).A.T_prime).ne_zero
  have hfe : ∀ j a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.eR a)) = if a = j then 1 else 0 := by
    intro j a
    refine (Cut.hJ_crd X v _ _).trans ?_
    rw [Cut.hT_f_e X]
    split_ifs <;> simp
  have hfz : ∀ j, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.zR u)) = 0 := by
    intro j
    refine (Cut.hJ_crd X v _ _).trans ?_
    rw [(X.zu_orth u j).2]
    simp
  rw [hfr, Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_castSucc] at hg
  simp only [Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc, Fin.snoc_last] at hg
  have hlast : g (Fin.last _) = 0 := by
    have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.zR u))) hg
    rw [hJ_lin] at h
    simp only [hze, mul_zero, Finset.sum_const_zero, zero_add] at h
    unfold hJ at h
    simp only [mulVec_zero, dotProduct_zero] at h
    exact (mul_eq_zero.1 h).resolve_right hzz
  intro i
  refine Fin.lastCases hlast (fun j => ?_) i
  have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.fR j))) hg
  rw [hJ_lin, hfz] at h
  simp only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero] at h
  unfold hJ at h
  simp only [mulVec_zero, dotProduct_zero] at h
  exact h

end GlobalTheory.RationalFrame
