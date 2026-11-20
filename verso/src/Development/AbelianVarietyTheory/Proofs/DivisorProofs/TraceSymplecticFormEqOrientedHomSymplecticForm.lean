import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => rfl`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
theorem cA_eq_sigR (D : D7) (z : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig z = Formalism.L2.Theta.cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
Rewrite using `[Finset.sum_comm]`. Rewrite using `[Finset.sum_congr rfl fun k _ => Finset.sum_comm]`. Conclude with `Finset.sum_comm`.
-/
theorem triple_sum_comm_reverse {ι κ μ M : Type} [Fintype ι] [Fintype κ] [Fintype μ] [AddCommMonoid M] (f : ι → κ → μ → M) :
    ∑ i, ∑ k, ∑ l, f i k l = ∑ l, ∑ k, ∑ i, f i k l := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
  exact Finset.sum_comm

/- English proof (translation)
Introduce `D S T JA JB ξ hA hB x y`. Establish `hB' : ∀ j l, ξ * incM D.host.F JB j l = incA D D.host.xi0 * incA D (S.gram⁻¹ j l)`. Introduce `j l`. Establish `h1` using `congrFun (congrFun hB j) l`. Rewrite `h1` using `[Matrix.smul_apply, smul_eq_mul]`.

Rewrite using `[h1]`. Use `show inclR (F := D.host.F) (AF D.host.F) (D.host.xi0 * S.gram⁻¹ j l) = _`. Conclude with `map_mul _ _ _`. Establish `hA' : ∀ i k, incM D.host.F JA i k = incA D (T.gram k i)`. Introduce `i k`.

Substitute `hA` using the available equality. Both sides reduce to the same expression. Unfold `GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens Formalism.IndefR.Datum.symplO Formalism.IndefR.Datum.hO`. Use `congr 1`. Repeatedly rewrite using `[Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[triple_sum_comm_reverse]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hA', cA_eq_sigR]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem symp_eq_symplO : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ x y : Formalism.IndefR.Datum.WO S T,
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
        Formalism.IndefR.Datum.symplO S T x y := by
  intro D S T JA JB ξ hA hB x y
  have hB' : ∀ j l, ξ * incM D.host.F JB j l = incA D D.host.xi0 * incA D (S.gram⁻¹ j l) := by
    intro j l
    have h1 := congrFun (congrFun hB j) l
    rw [Matrix.smul_apply, smul_eq_mul] at h1
    rw [h1]
    show inclR (F := D.host.F) (AF D.host.F) (D.host.xi0 * S.gram⁻¹ j l) = _
    exact map_mul _ _ _
  have hA' : ∀ i k, incM D.host.F JA i k = incA D (T.gram k i) := by
    intro i k; subst hA; rfl
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens Formalism.IndefR.Datum.symplO Formalism.IndefR.Datum.hO
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [triple_sum_comm_reverse]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hA', cA_eq_sigR]
  calc ξ * (x i j * incA D (T.gram k i) * incM D.host.F JB j l * Formalism.L2.Theta.cA D (y k l))
      = x i j * incA D (T.gram k i) * (ξ * incM D.host.F JB j l) * Formalism.L2.Theta.cA D (y k l) := by ring
    _ = _ := by rw [hB']; ring

end GlobalTheory.WeilSchrodinger

end
