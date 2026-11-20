import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterUpdateOfWeakRealisation

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.BigOn.SplitRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lUnif_of_rows (p : PtAt ex Csz) (h : p.Rows) : (R2 p).LUnif := h.prim.unif

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem split_lifts_bijective_base (p : PtAt ex Csz) (h : p.Rows) : ((R2 p).toCx (F2 p)).H5 (F2 p).cr false := by
  have hR := complex_data_conditions_base_level_of_primitive_links h.ok h.sep p.charW h.prim
  have h5 := hR.lifts0.1
  rw [GlobalTheory.CharRealise.toCx3_eq_one p.R p.F p.phsOne] at h5
  exact h5

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem ratTh_of_rows (p : PtAt ex Csz) (h : p.Rows) : ((R2 p).toCx (F2 p)).RATth (F2 p).cr false := by
  have hR := complex_data_conditions_base_level_of_primitive_links h.ok h.sep p.charW h.prim
  have hr := hR.ratTh
  rw [GlobalTheory.CharRealise.toCx3_eq_one p.R p.F p.phsOne] at hr
  exact hr

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem proviso_of_rows (p : PtAt ex Csz) (h : p.Rows) : (lv ((F2 p).fc ((R2 p).toCx (F2 p)).zs) false).Proviso := by
  have hR := complex_data_conditions_base_level_of_primitive_links h.ok h.sep p.charW h.prim
  have hv := hR.proviso0
  rw [GlobalTheory.CharRealise.toCx3_eq_one p.R p.F p.phsOne] at hv
  exact hv

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem baseLinks_of_rows (p : PtAt ex Csz) (h : p.Rows) : BaseLinks (R2 p) (F2 p) :=
  ⟨split_lifts_bijective_base p h, ratTh_of_rows p h, proviso_of_rows p h⟩

/- English proof (translation)
Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem rankRows_of_rows (p : PtAt ex Csz) (h : p.Rows) : RankRows (S2 p) := by
  have hR := complex_data_conditions_base_level_of_primitive_links h.ok h.sep p.charW h.prim
  exact ⟨(indefiniteDataAtBaseLevel hR).D_pos, fun j => (indefiniteDataAtBaseLevel hR).dW_eq (hR.wf false) j⟩

end Point

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem unif_baseLinks_rankRows : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz),
    p.Rows → (R2 p).LUnif ∧ BaseLinks (R2 p) (F2 p) ∧ RankRows (S2 p) :=
  fun _ _ _ _ _ _ _ _ _ _ p h => ⟨lUnif_of_rows p h, baseLinks_of_rows p h, rankRows_of_rows p h⟩

end GlobalTheory.BigOn.SplitRows
