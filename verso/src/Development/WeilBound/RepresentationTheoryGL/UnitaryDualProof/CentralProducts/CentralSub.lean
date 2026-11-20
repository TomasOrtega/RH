import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.CentralGenerators.CentralSubGen

namespace PositivityTheory.RgUd.Prod.CSel

/- English proof (translation)
The claim follows from `PositivityTheory.RgUd.Prod.CS.centralSub k`.
-/
theorem centralSub (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    CentralSub k := PositivityTheory.RgUd.Prod.CS.centralSub k

end PositivityTheory.RgUd.Prod.CSel
