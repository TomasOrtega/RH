import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.TraceFormCore
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.SymmetricIndices.IndexSym
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.Psplit
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.Ptransl

namespace PositivityTheory.RgUd.TP.Loc.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
The claim follows from `PositivityTheory.RgUd.TP.Loc.Ptf.traceForm k`.
-/
theorem traceForm : TraceForm k := PositivityTheory.RgUd.TP.Loc.Ptf.traceForm k
/- English proof (translation)
The claim follows from `PositivityTheory.RgUd.TP.Loc.Uni.unimod k`.
-/
theorem unimod : TraceForm k → PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) := PositivityTheory.RgUd.TP.Loc.Uni.unimod k
/- English proof (translation)
The claim follows from `PositivityTheory.RgUd.TP.Loc.Psplit.locOff_of k (PositivityTheory.RgUd.TP.Loc.Psplit.split k) (PositivityTheory.RgUd.TP.Loc.Psplit.locChi k)`.
-/
theorem locOff : LocOff k := PositivityTheory.RgUd.TP.Loc.Psplit.locOff_of k (PositivityTheory.RgUd.TP.Loc.Psplit.split k) (PositivityTheory.RgUd.TP.Loc.Psplit.locChi k)
/- English proof (translation)
The claim follows from `PositivityTheory.RgUd.TP.Loc.Psplit.locAll_of k (PositivityTheory.RgUd.TP.Loc.Psplit.split k) (PositivityTheory.RgUd.TP.Loc.Psplit.locChi k)`.
-/
theorem locAll : LocAll k := PositivityTheory.RgUd.TP.Loc.Psplit.locAll_of k (PositivityTheory.RgUd.TP.Loc.Psplit.split k) (PositivityTheory.RgUd.TP.Loc.Psplit.locChi k)
/- English proof (translation)
The claim follows from `PositivityTheory.RgUd.TP.Loc.Ptransl.transl`.
-/
theorem transl : Transl k := PositivityTheory.RgUd.TP.Loc.Ptransl.transl

end PositivityTheory.RgUd.TP.Loc.Final
