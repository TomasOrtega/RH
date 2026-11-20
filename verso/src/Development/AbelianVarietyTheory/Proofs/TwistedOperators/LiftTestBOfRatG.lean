import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsRationalIffRecord
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsRationalOfRatAt
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

open GlobalTheory.LiftTestCompare GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.LiftRat Formalism.IndefR.Cx Formalism.IndefR.Rat

namespace GlobalTheory.TwistField

section Read

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def readBasis (hU : R.LUnif) (i : Fin D.R.m) :
    Module.Basis (Fin (R.nW i)) ℂ (Tw (twAt D.what₂.embLL A.v0) (R.HW i (sg0 D A)).H) :=
  Module.Basis.mk (Tw.linInd _ ((hU i (sg0 D A)).1 _ _ (Pi.basisFun D.what₂.LL (Fin (R.nW i))).linearIndependent))
    (Tw.span_top _ (span_basis R hU i (sg0 D A))).ge

/- English proof (translation)
Establish `h1 : Tw.mk (twAt D.what₂.embLL A.v0) ((R.FW i).j (sg0 D A) y) = ∑ l, A.v0.embedding (y l) • readBasis R hU i l`. Rewrite using `[j_eq_sum]`. Use `Finset.sum_congr (M := (R.HW i (sg0 D A)).H) rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[readBasis, Module.Basis.mk_apply]`. Use `show _ = cj (twAt D.what₂.embLL A.v0) (A.v0.embedding (y l)) • (R.FW i).j (sg0 D A) (Pi.basisFun D.what₂.LL (Fin (R.nW i)) l)`.

Rewrite using `[emb_eq D.what₂.embLL A.v0, cj_cj]`. Rewrite using `[h1, Module.Basis.coord_apply, Module.Basis.repr_sum_self]`.
-/
theorem readBasis_coord (hU : R.LUnif) (i : Fin D.R.m) (y : Fin (R.nW i) → D.what₂.LL) (k : Fin (R.nW i)) :
    (readBasis R hU i).coord k (Tw.mk (twAt D.what₂.embLL A.v0) ((R.FW i).j (sg0 D A) y)) = A.v0.embedding (y k) := by
  have h1 : Tw.mk (twAt D.what₂.embLL A.v0) ((R.FW i).j (sg0 D A) y) = ∑ l, A.v0.embedding (y l) • readBasis R hU i l := by
    rw [j_eq_sum]
    refine Finset.sum_congr (M := (R.HW i (sg0 D A)).H) rfl fun l _ => ?_
    rw [readBasis, Module.Basis.mk_apply]
    show _ = cj (twAt D.what₂.embLL A.v0) (A.v0.embedding (y l)) •
      (R.FW i).j (sg0 D A) (Pi.basisFun D.what₂.LL (Fin (R.nW i)) l)
    rw [emb_eq D.what₂.embLL A.v0, cj_cj]
  rw [h1, Module.Basis.coord_apply, Module.Basis.repr_sum_self]

end Read

/- English proof (translation)
Introduce `D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F b hU hG`. Rewrite using `[toCx3_liftTestB]`. Introduce `j`. Use `⟨R.toRealDat.nW j, fun k => (readBasis R.toRealDat hU j).coord k, fun w hw => (readBasis R.toRealDat hU j).forall_coord_eq_zero_iff.1 hw, ?_, ?_⟩` and prove the remaining obligations. Introduce `t k x`.

Take `⟨y, hy⟩` from `hG j t x`. Use `⟨y k, ?_⟩` and prove the remaining obligations. Use `show _ = (readBasis R.toRealDat hU j).coord k (Tw.mk (twAt D.what₂.embLL A3.A.v0) (cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.toRealDat.thG j t (R.toRealDat.jV j t x)))`. Rewrite using `[← hy, readBasis_coord]`. Both sides reduce to the same expression.

Introduce `k (l : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b j)))`. Use `⟨R.toRealDat.bL F.lv2 b j l k, ?_⟩` and prove the remaining obligations. Establish `hc : cpt A3.A.v0.embedding (Pi.single l (1 : D.what₂.LL)) = Pi.single l 1`. Use function extensionality and compare the values at `r`. Distinguish the cases in `h : r = l`.

Substitute `h` using the available equality. Simplify using `[cpt]`. Simplify using `[cpt, Pi.single_apply, h]`. Establish `h : Tw.out (s` using `twAt D.what₂.embLL A3.A.v0) (E := (R.toRealDat.HW j (sg0 D A3.A)).H) ((R.toRealDat.toCx F.lv2).w0C b j (Pi.single l 1)) = (R.toRealDat.FW j).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 b j l) := by`. Establish `h0` using `liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 b j (Pi.single l 1)`.

Establish `e1 : ∑ k, (Pi.single l (1 : D.what₂.LL) : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b j)) → D.what₂.LL) k • R.toRealDat.bL F.lv2 b j k = R.toRealDat.bL F.lv2 b j l`. Simplify using `[Pi.single_apply]`. Rewrite `h0` using `[e1]`. Use `Eq.trans ?_ h0` and prove the remaining obligations. Apply the tactic sequence `erw [hc] <;> rfl`.

Use `show _ = (readBasis R.toRealDat hU j).coord k (Tw.mk (twAt D.what₂.embLL A3.A.v0) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.toRealDat.HW j (sg0 D A3.A)).H) ((R.toRealDat.toCx F.lv2).w0C b j (Pi.single l 1))))`. Rewrite using `[h, readBasis_coord]`. Both sides reduce to the same expression.
-/
theorem liftTestB_of_ratG : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool), R.toRealDat.LUnif → GlobalTheory.TwistField.RatG R.toRealDat (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) b := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F b hU hG
  rw [toCx3_liftTestB]
  intro j
  refine ⟨R.toRealDat.nW j, fun k => (readBasis R.toRealDat hU j).coord k,
    fun w hw => (readBasis R.toRealDat hU j).forall_coord_eq_zero_iff.1 hw, ?_, ?_⟩
  · intro t k x
    obtain ⟨y, hy⟩ := hG j t x
    refine ⟨y k, ?_⟩
    show _ = (readBasis R.toRealDat hU j).coord k (Tw.mk (twAt D.what₂.embLL A3.A.v0)
      (cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.toRealDat.thG j t (R.toRealDat.jV j t x)))
    rw [← hy, readBasis_coord]
    rfl
  · intro k (l : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b j)))
    refine ⟨R.toRealDat.bL F.lv2 b j l k, ?_⟩
    have hc : cpt A3.A.v0.embedding (Pi.single l (1 : D.what₂.LL)) = Pi.single l 1 := by
      funext r
      by_cases h : r = l
      · subst h; simp [cpt]
      · simp [cpt, Pi.single_apply, h]
    have h : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.toRealDat.HW j (sg0 D A3.A)).H)
        ((R.toRealDat.toCx F.lv2).w0C b j (Pi.single l 1)) = (R.toRealDat.FW j).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 b j l) := by
      have h0 := liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 b j (Pi.single l 1)
      have e1 : ∑ k, (Pi.single l (1 : D.what₂.LL) : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b j)) → D.what₂.LL) k • R.toRealDat.bL F.lv2 b j k = R.toRealDat.bL F.lv2 b j l := by
        simp [Pi.single_apply]
      rw [e1] at h0
      refine Eq.trans ?_ h0
      erw [hc] <;> rfl
    show _ = (readBasis R.toRealDat hU j).coord k (Tw.mk (twAt D.what₂.embLL A3.A.v0)
      (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.toRealDat.HW j (sg0 D A3.A)).H)
        ((R.toRealDat.toCx F.lv2).w0C b j (Pi.single l 1))))
    rw [h, readBasis_coord]
    rfl

end GlobalTheory.TwistField
