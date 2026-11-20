import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionIsAction

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagAction

/- English proof (translation)
Unfold `actG0`. Use `split_ifs with hk`. Use function extensionality and compare the values at `h`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _`.

Simplify using the standard rewrite rules.
-/
theorem act_sum_smul {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (g : Formalism.L2.DIV.G0 L.Pg L.r) {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → GA D V → ℂ) :
    actG0 V β L g (∑ i ∈ s, c i • F i) = ∑ i ∈ s, c i • actG0 V β L g (F i) := by
  unfold actG0
  split_ifs with hk
  · funext h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  · simp

/- English proof (translation)
Introduce `D V β L _ hL c hc F hF`. Establish `hA` using `levelGroupAction_isAction V β L hL F hF`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[act_sum_smul, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun g' _ => ?_` and prove the remaining obligations. Rewrite using `[hA.2 g g', smul_smul]`. Use `_ = ∑ g, ∑ k, (c g * c (g⁻¹ * k)) • actG0 V β L k F := by`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Conclude with `Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun g' => by`.

Simplify using `only [Equiv.coe_mulLeft, inv_mul_cancel_left]`. Use `_ = ∑ k, (∑ g, c g * c (g⁻¹ * k)) • actG0 V β L k F := by`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_smul.symm`. Use `_ = ∑ g, c g • actG0 V β L g F := by`.

Simplify using `only [hc]`.
-/
theorem convIdempotent_act : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) [Fintype (Formalism.L2.DIV.G0 L.Pg L.r)], LiftsExist V β L → ∀ c : Formalism.L2.DIV.G0 L.Pg L.r → ℂ, (∀ g, ∑ a, c a * c (a⁻¹ * g) = c g) → ∀ F : GA D V → ℂ, HasType V β (flag1L L) F → (∑ g, c g • actG0 V β L g (∑ g', c g' • actG0 V β L g' F)) = ∑ g, c g • actG0 V β L g F := by
  intro D V β L _ hL c hc F hF
  have hA := levelGroupAction_isAction V β L hL F hF
  calc (∑ g, c g • actG0 V β L g (∑ g', c g' • actG0 V β L g' F))
      = ∑ g, ∑ g', (c g * c g') • actG0 V β L (g * g') F := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [act_sum_smul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun g' _ => ?_
        rw [hA.2 g g', smul_smul]
    _ = ∑ g, ∑ k, (c g * c (g⁻¹ * k)) • actG0 V β L k F := by
        refine Finset.sum_congr rfl fun g _ => ?_
        exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun g' => by
          simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
    _ = ∑ k, (∑ g, c g * c (g⁻¹ * k)) • actG0 V β L k F := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_smul.symm
    _ = ∑ g, c g • actG0 V β L g F := by
        simp only [hc]

end GlobalTheory.FlagAction
