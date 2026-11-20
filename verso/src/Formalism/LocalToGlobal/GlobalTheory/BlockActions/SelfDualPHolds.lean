import Formalism.LocalToGlobal.GlobalTheory.BlockActions.BrStmt
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial
import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGlob
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

/- English proof (translation)
Introduce a local definition for the expression. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gramP_det_unit (D : D7) : IsUnit (gramP D).det := by
  let _ := D.host.cmStar
  unfold gramP
  rw [Matrix.det_reindex_self]
  exact Formalism.L2.G.gram_det_unit D.sp.cm D.sp.X'

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem isLat_dlP (D : D7) (M : Submodule (𝓞 D.host.E) (Fin (D.R.N D.R.m - 1) → D.host.E)) (hM : Comp.IsLat M) :
    Comp.IsLat (Comp.dl (sigD D) (gramP D) M) := by
  have hL : Submodule.IsLattice D.host.E M := ⟨Module.Finite.iff_fg.1 hM.1, hM.2⟩
  obtain ⟨d, hd, hle⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramP D) (gramP_det_unit D) M hL
  exact ⟨Module.Finite.iff_fg.2 (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.fg_of_le_bnd hd hle),
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.dual_span (sigD D : D.host.E →+* D.host.E) (gramP D) M hL⟩

variable {D : D7} {u : D.what₂.Word}

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem levelLattice_dual_eq_self (K : ClsPTied (D := D) u) : Comp.dl (sigD D) (gramP D) K.lev.Lb = K.lev.Lb := by
  have hS : dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) K.lev.Lb = (K.lev.Lb : Set _) := by
    ext y
    constructor
    · intro hy
      have h := K.lev.Lb_dual y hy
      simpa using h
    · intro hy
      exact K.lev.Lb_int y hy
  unfold Comp.dl
  rw [hS, Submodule.span_eq]

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem classLattice_eq_globalLattice (K : ClsPTied (D := D) u) (c : (D.fm u).clsP) :
    K.lat c = Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb := by
  ext x
  constructor
  · intro hx
    exact (K.y_lat c _).1 (latS_of_mem _ x hx)
  · intro hx
    exact latLocGlob _ _ _ (K.lat c) (K.lat_fin c) x ((K.y_lat c _).2 hx)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem selfDualP_of_formsTiedSym {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf) :
    SelfDualP Tf := by
  intro c
  have hLb : Comp.IsLat Tf.clsP.lev.Lb := ⟨Tf.clsP.lev.Lb_fin, Tf.clsP.lev.Lb_span⟩
  have h1 : Comp.dl (sigD D) (gramP D) (Tf.clsP.lat c) = Tf.clsP.lat c := by
    rw [classLattice_eq_globalLattice, ← Comp.glob_dl (sigD D) (gramP D) (isLat_dlP D) hLb _ (Tf.clsP.y c).2, levelLattice_dual_eq_self]
  rw [← Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_span_dualSet]
  exact congrArg (fun M : Submodule _ _ => (M : Set (Fin (D.R.N D.R.m - 1) → D.host.E))) h1

end Formalism.L2.GlobalTheoryTheory.Br
