import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatDict
open Formalism.IndefR.Eqv.UI

/- English proof (translation)
Unfold `Formalism.L2.Herm.hatL Formalism.UG.latS Formalism.MainNotions.S.AutInst.Lf Formalism.MainNotions.S.lamAf`. Rewrite using `[Set.image_eq_range]`. Both sides reduce to the same expression.
-/
theorem mem_hatL_iff (D : D7) (V : HSp D) (fr : Frames D V)
    (w : Fin V.rank → D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F) :
    w ∈ Formalism.L2.Herm.hatL (F := D.host.F) fr.Λ ↔ w ∈ (instV fr).Lf := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS Formalism.MainNotions.S.AutInst.Lf Formalism.MainNotions.S.lamAf
  rw [Set.image_eq_range]
  rfl

/- English proof (translation)
Establish `hring : ∀ z : AF D.host.F ⊗[D.host.F] D.host.E, Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) = Formalism.L2.SG.AdBridge.tauF (instV fr) z`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ((Lev.swapAE D).congr_arg (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)`. Consider the case `tmul a b => exact (Formalism.L2.SG.AdBridge.tauF_tmul (instV fr) a b).symm`.

Consider the case `add a b ha hb`. Establish `e1` using `_root_.map_add (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) a b`. Rewrite using `[e1, RingHom.map_add, ha, hb]`. Conclude with `(RingHom.map_add _ _ _).symm`. Rewrite using `[((brg_isBridge fr) x).2]`.

Use extensionality with `i j`. Simplify using `only [Lev.finE, finHom, matHom, Formalism.UG.bc, Formalism.L2.SG.AdBridge.hmat, Formalism.L2.SG.AdBridge.ofHAFin, MonoidHom.comp_apply, Units.coe_map, Matrix.map_apply]`. Conclude with `hring _`.
-/
theorem finE_brg (D : D7) (V : HSp D) (fr : Frames D V) (x : (instV fr).GA) :
    (Lev.finE V (brg fr x)).1 = (instV fr).fmat x.2 := by
  have hring : ∀ z : AF D.host.F ⊗[D.host.F] D.host.E,
      Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) =
        Formalism.L2.SG.AdBridge.tauF (instV fr) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ((Lev.swapAE D).congr_arg (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
    | tmul a b => exact (Formalism.L2.SG.AdBridge.tauF_tmul (instV fr) a b).symm
    | add a b ha hb =>
      have e1 := _root_.map_add (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) a b
      rw [e1, RingHom.map_add, ha, hb]
      exact (RingHom.map_add _ _ _).symm
  rw [((brg_isBridge fr) x).2]
  ext i j
  simp only [Lev.finE, finHom, matHom, Formalism.UG.bc, Formalism.L2.SG.AdBridge.hmat, Formalism.L2.SG.AdBridge.ofHAFin,
    MonoidHom.comp_apply, Units.coe_map, Matrix.map_apply]
  exact hring _

/- English proof (translation)
Introduce `D V fr x`. Unfold `GlobalTheory.SepPer.latAt GlobalTheory.Count.lamX`. Use `congr 1`. Use extensionality with `y`. Rewrite using `[← map_inv (brg fr) x, finE_brg D V fr x⁻¹]`.

Conclude with `mem_hatL_iff D V fr _`.
-/
theorem latAt_brg : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (x : (Formalism.IndefR.Eqv.UI.instV fr).GA), latAt fr.Λ (Formalism.IndefR.Eqv.UI.brg fr x) = GlobalTheory.Count.lamX (Formalism.IndefR.Eqv.UI.instV fr) x := by
  intro D V fr x
  unfold GlobalTheory.SepPer.latAt GlobalTheory.Count.lamX
  congr 1
  ext y
  rw [← map_inv (brg fr) x, finE_brg D V fr x⁻¹]
  exact mem_hatL_iff D V fr _

end GlobalTheory.LatDict
