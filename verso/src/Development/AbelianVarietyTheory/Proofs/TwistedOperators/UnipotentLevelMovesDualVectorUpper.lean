import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BSlotD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

namespace GlobalTheory.SeeConjBwd

open Formalism.L2.SG.Pf.BunEx.Unip Formalism.L2.SG.Pf.unitaryCongruence in

/- English proof (translation)
Introduce `I g r k e0 f0 z0 bw bwd ew h x hx hcx j`. Establish `hm` using `h.mem`. Establish `hcx'` using `Formalism.L2.SG.Pf.unitaryCongruence.cong_inv I g e0 z0 bw hx hcx`. Establish `hw : (I.fmat x - 1) *ᵥ bwd j ∈ I.Lf` using `K_sub_mv I hx (hm.2.2 j).2`. Use `Formalism.L2.SG.Pf.BunEx.Unip.mem_Mo_of (Formalism.L2.SG.Pf.BunEx.Unip.exp h _ hw) ?_` and prove the remaining obligations.

Use `set w := (I.fmat x - 1) *ᵥ bwd j with hwdef`. Unfold `Formalism.L2.SG.Pf.BunEx.Unip.Rc`. Use `add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_` and prove the remaining obligations. Conclude with `span_Mo (sumSpan I _ _ _ (fun a _ => hA_int I (hm.1 a).2 hw) (fun a _ => Or.inl ⟨a, rfl⟩))`. Use `Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (sumZ I g _ _ _ (fun a _ => ?_) (fun a _ => (hm.1 a).2))` and prove the remaining obligations.

Rewrite using `[hwdef, Formalism.L2.SG.Pf.BunEx.Unip.adj]`. Use `Zleft I g (hm.2.2 j).2 ?_ (hcx'.1 a)` and prove the remaining obligations. Introduce and unpack `_ ⟨c, -, rfl⟩`. Conclude with `((h.W j).2.2 c).2.2.1`. Use `Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (Zv I g ?_ hm.2.1)` and prove the remaining obligations.

Rewrite using `[hwdef, Formalism.L2.SG.Pf.BunEx.Unip.adj]`. Use `Zleft I g (hm.2.2 j).2 ?_ hcx'.2.1` and prove the remaining obligations. Introduce and unpack `_ ⟨c, rfl⟩`. Conclude with `((h.W j).2.2 c).2.2.1`. Use `Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (sumZ I g _ _ _ (fun i _ => ?_) (fun i _ => (hm.2.2 i).1))` and prove the remaining obligations.

Establish `e : hA I (bwd i) w = 0`. Rewrite using `[hwdef, Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, bdbd h, sub_zero, h.bwd_w i, h.bwd_w j, Matrix.mulVec_smul]`. Conclude with `hA_sew I h.orth _ _`. Rewrite using `[e]`. Conclude with `Z_zero I g`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hji : j < i`. Conclude with `span_Mo (smul_span I (hA_int I (hm.2.2 i).1 hw) (Or.inr ⟨i, hji, rfl⟩))`. Use `Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (Zv I g ?_ (hm.2.2 i).2)` and prove the remaining obligations. Rewrite using `[hwdef, Formalism.L2.SG.Pf.BunEx.Unip.adj]`.

Use `Zleft I g (hm.2.2 j).2 ?_ (hcx'.2.2 i)` and prove the remaining obligations. Introduce and unpack `_ (⟨c, rfl⟩ | ⟨l, hl, rfl⟩)`. Conclude with `((h.W j).2.2 c).2.2.1`. Establish `hl' : l.1 < i.1` using `hl`. Establish `hlj : j ≠ l` using `fun e => hji (by rw [e]; exact hl')`.

Use `Zsym (h.dual j l)` as an intermediate fact. Rewrite `this` using `[if_neg hlj, map_zero, sub_zero]`. Conclude with `this`.
-/
theorem bwd_move : ∀ (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Af I.F), Formalism.L2.SG.Pf.BunEx.Unip.FH I g e0 f0 z0 bw bwd ew → ∀ x : I.Gf, x ∈ I.Kset → K2cong I g e0 z0 bw x → ∀ j : Fin k, (I.fmat x - 1) *ᵥ bwd j ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo I g (Set.range e0 ∪ bwd '' {l | j < l}) := by
  intro I g r k e0 f0 z0 bw bwd ew h x hx hcx j
  have hm := h.mem
  have hcx' := Formalism.L2.SG.Pf.unitaryCongruence.cong_inv I g e0 z0 bw hx hcx
  have hw : (I.fmat x - 1) *ᵥ bwd j ∈ I.Lf := K_sub_mv I hx (hm.2.2 j).2
  refine Formalism.L2.SG.Pf.BunEx.Unip.mem_Mo_of (Formalism.L2.SG.Pf.BunEx.Unip.exp h _ hw) ?_
  set w := (I.fmat x - 1) *ᵥ bwd j with hwdef
  unfold Formalism.L2.SG.Pf.BunEx.Unip.Rc
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact span_Mo (sumSpan I _ _ _ (fun a _ => hA_int I (hm.1 a).2 hw)
      (fun a _ => Or.inl ⟨a, rfl⟩))
  · refine Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (sumZ I g _ _ _ (fun a _ => ?_) (fun a _ => (hm.1 a).2))
    rw [hwdef, Formalism.L2.SG.Pf.BunEx.Unip.adj]
    refine Zleft I g (hm.2.2 j).2 ?_ (hcx'.1 a)
    rintro _ ⟨c, -, rfl⟩
    exact ((h.W j).2.2 c).2.2.1
  · refine Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (Zv I g ?_ hm.2.1)
    rw [hwdef, Formalism.L2.SG.Pf.BunEx.Unip.adj]
    refine Zleft I g (hm.2.2 j).2 ?_ hcx'.2.1
    rintro _ ⟨c, rfl⟩
    exact ((h.W j).2.2 c).2.2.1
  · refine Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (sumZ I g _ _ _ (fun i _ => ?_) (fun i _ => (hm.2.2 i).1))
    have e : hA I (bwd i) w = 0 := by
      rw [hwdef, Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, bdbd h, sub_zero, h.bwd_w i,
        h.bwd_w j, Matrix.mulVec_smul]
      exact hA_sew I h.orth _ _
    rw [e]; exact Z_zero I g
  · refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hji : j < i
    · exact span_Mo (smul_span I (hA_int I (hm.2.2 i).1 hw) (Or.inr ⟨i, hji, rfl⟩))
    · refine Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (Zv I g ?_ (hm.2.2 i).2)
      rw [hwdef, Formalism.L2.SG.Pf.BunEx.Unip.adj]
      refine Zleft I g (hm.2.2 j).2 ?_ (hcx'.2.2 i)
      rintro _ (⟨c, rfl⟩ | ⟨l, hl, rfl⟩)
      · exact ((h.W j).2.2 c).2.2.1
      · have hl' : l.1 < i.1 := hl
        have hlj : j ≠ l := fun e => hji (by rw [e]; exact hl')
        have := Zsym (h.dual j l)
        rw [if_neg hlj, map_zero, sub_zero] at this
        exact this

end GlobalTheory.SeeConjBwd
