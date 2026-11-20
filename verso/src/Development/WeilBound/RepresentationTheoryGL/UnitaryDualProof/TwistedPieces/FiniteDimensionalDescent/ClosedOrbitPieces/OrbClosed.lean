import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.DoubleTransferAlt
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TrOrbB

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `N A _ _ _ hA ρ ρ' h` and use `orbHom_gen k N A hA ρ ρ' h`.
-/
theorem orbHom : Tr.OrbHom k := fun N A _ _ _ hA ρ ρ' h => orbHom_gen k N A hA ρ ρ' h

/- English proof (translation)
Introduce `N r A _ _ _ hA b hb ρ₀` and use `orbClosed_gen N r A hA b hb ρ₀`.
-/
theorem orbClosed : Tr.OrbClosed k := fun N r A _ _ _ hA b hb ρ₀ => orbClosed_gen N r A hA b hb ρ₀

end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
