import Formalism.LocalToGlobal.HermitianForms.BothSym
import Formalism.LocalToGlobal.HermitianColumns.FullSym

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Forms

def ColsFullS {D : D7} (C : ColsTiedSym D) :=
  { full : Formalism.L2.Herm.FullTiedS D // full.cols = C.herm }

def ColsExtraTiedS {D : D7} {C : ColsTiedSym D} (Fu : ColsFullS C) {L : SizeData₂ D} {hT : GatTies D}
    {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    (ex : Extra D L hT Gi Gl K Y cX) : Prop :=
  Formalism.L2.Herm.SymmetricExtraCompatibility Fu.1 ex

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ColsExtraTiedS.lev_eq {D : D7} {C : ColsTiedSym D} {Fu : ColsFullS C} {L : SizeData₂ D} {hT : GatTies D}
    {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl K Y cX} (h : ColsExtraTiedS Fu ex) : ex.lev = C.herm.base.lev0 :=
  h.join.lev_eq.trans (congrArg (fun H => H.base.lev0) Fu.2)

/- English proof (translation)
Equip the data with the indicated structure. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem ColsExtraTiedS.piG_lev {D : D7} {C : ColsTiedSym D} {Fu : ColsFullS C} {L : SizeData₂ D} {hT : GatTies D}
    {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl K Y cX} (h : ColsExtraTiedS Fu ex) : PiGLevel D ex.lev ex.errX := by
  letI := D.host.cmStar
  rw [h.join.lev_eq, h.join.errX_eq]
  intro u i v hv
  have key := (Fu.1.levelZeroCompatibility u).splitG_pi i v hv
  rw [Fu.1.piG u D.u₀] at key
  simpa [Formalism.L2.Herm.toErrXS, Formalism.L2.Herm.star_conj, UG.inclE] using key

/- English proof (translation)
Equip the data with the indicated structure. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem ColsExtraTiedS.piT_lev {D : D7} {C : ColsTiedSym D} {Fu : ColsFullS C} {L : SizeData₂ D} {hT : GatTies D}
    {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl K Y cX} (h : ColsExtraTiedS Fu ex) : PiTLevel D ex.lev ex.errX := by
  letI := D.host.cmStar
  rw [h.join.lev_eq, h.join.errX_eq]
  intro u v z hz y
  exact (Fu.1.levelZeroCompatibility u).fM_pi _ _ z hz y

end Formalism.L2.Forms

end
