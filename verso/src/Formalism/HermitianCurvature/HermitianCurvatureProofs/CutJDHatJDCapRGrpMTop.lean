import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

noncomputable section

/- English proof (translation)
Use function extensionality and compare the values at `j`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[rowsNv, rowsN]`.
-/
theorem vtop_rows (k r : ℕ) (s : Fin (k + 1)) : rowsNv k r (Fin.last r) s = rowsN k r (Fin.last r) s := by
  funext j
  apply Fin.ext
  simp [rowsNv, rowsN]

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg`. Establish `hm : Q.mdim k r (Fin.last r) = k + 1` using `by simp [Q.mdim]`. Establish `hpos : ∀ j, (Q.posL k r (Fin.last r) j).val = r + j.val` using `fun j => by`. Simplify using `[Q.posL]`. Use linear arithmetic over natural numbers and integers.

Establish `hW : Q.wCell k r (Fin.last r) c ∈ Q.Glev k r 0` using `Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _`. Simplify using `only [FNv, Q.resG, Q.QL, Q.grp, Q.tL, Pi.neg_apply, neg_neg]`. Establish `e1 : Q.resG k r (Fin.last r) J c = ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) • (fun g' => J (Q.wCell k r (Fin.last r) c * g'))` using `rfl`. Rewrite using `[e1, Formalism.FourierDecayAlt.P5.chatL_smulC, Pi.smul_apply]`. Use `congr 1`.

Rewrite using `[top_chatL hm _ hpos]`. Unfold `NLv`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian, vtop_rows, vtop_rows]`. Use `congr 1`.

Establish `ez : Q.wCell k r (Fin.last r) c *ᵥ z = z` using `top_wlist_wb c _ z hz`. Establish `eh : herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ bvec (wI k r s)) z = herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z`. Rewrite using `[← Matrix.mulVec_mulVec]`. Use `conv_lhs => rw [← ez]`. Conclude with `Formalism.FourierDecayAlt.P.Qx2.herm_uh hW.1 _ _`.

Establish `es : Q.posL k r (Fin.last r) (Fin.cast hm.symm s) = wI k r s`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[Q.posL, wI]`. Use linear arithmetic over natural numbers and integers. Establish `et : Q.posL k r (Fin.last r) (Fin.cast hm.symm t) = wI k r t`.

Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[Q.posL, wI]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[eh]`. Simplify using `only [Q.ybv, Q.xv, fvec, es, et]`.

Simplify using the standard rewrite rules.
-/
theorem mirror_residue_top_holds : JDRvTop := by
  intro Wp Wq _ _ _ _ k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  have hm : Q.mdim k r (Fin.last r) = k + 1 := by simp [Q.mdim]
  have hpos : ∀ j, (Q.posL k r (Fin.last r) j).val = r + j.val := fun j => by
    simp [Q.posL]; omega
  have hW : Q.wCell k r (Fin.last r) c ∈ Q.Glev k r 0 := Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _
  simp only [FNv, Q.resG, Q.QL, Q.grp, Q.tL, Pi.neg_apply, neg_neg]
  have e1 : Q.resG k r (Fin.last r) J c =
      ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) •
        (fun g' => J (Q.wCell k r (Fin.last r) c * g')) := rfl
  rw [e1, Formalism.FourierDecayAlt.P5.chatL_smulC, Pi.smul_apply]
  congr 1
  rw [top_chatL hm _ hpos]
  unfold NLv
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian, vtop_rows, vtop_rows]
  congr 1
  have ez : Q.wCell k r (Fin.last r) c *ᵥ z = z := top_wlist_wb c _ z hz
  have eh : herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ bvec (wI k r s)) z =
      herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z := by
    rw [← Matrix.mulVec_mulVec]
    conv_lhs => rw [← ez]
    exact Formalism.FourierDecayAlt.P.Qx2.herm_uh hW.1 _ _
  have es : Q.posL k r (Fin.last r) (Fin.cast hm.symm s) = wI k r s := by
    apply Fin.ext; simp [Q.posL, wI]; omega
  have et : Q.posL k r (Fin.last r) (Fin.cast hm.symm t) = wI k r t := by
    apply Fin.ext; simp [Q.posL, wI]; omega
  rw [eh]
  simp only [Q.ybv, Q.xv, fvec, es, et]
  simp

end

end Formalism.FourierDecayAlt.P.CutMP
