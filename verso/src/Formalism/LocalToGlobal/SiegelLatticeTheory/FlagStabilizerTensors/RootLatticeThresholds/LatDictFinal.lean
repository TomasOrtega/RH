import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZPfG
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZPfZ
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions

/- English proof (translation)
The claim follows from `latRowLat_of LatDictZ.lattice_genus X u`.
-/
theorem latRowLat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : LatRowLat X u :=
  latRowLat_of LatDictZ.lattice_genus X u

/- English proof (translation)
The claim follows from `latSurj_of LatDictZ.anisotropic_vector_orbit X u`.
-/
theorem latSurj {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : LatSurj X u :=
  latSurj_of LatDictZ.anisotropic_vector_orbit X u

/- English proof (translation)
Introduce `_ X hK u` and use `⟨latRowLat X u, latSurj X u, latInj X u, Formalism.L2.SG.Closed.ClassFin_holds X u hK⟩`.
-/
theorem lattice_steps_hold : LatticeRowBijectionClassFinite := fun _ X hK u =>
  ⟨latRowLat X u, latSurj X u, latInj X u, Formalism.L2.SG.Closed.ClassFin_holds X u hK⟩

/- English proof (translation)
The claim follows from `full_exists_of_lattice_steps h1 lattice_steps_hold h4`.
-/
theorem fullExists_of_TR_Loc (h1 : TRExistsC) (h4 : LocC) : Formalism.L2.SG.Full.FullExists :=
  full_exists_of_lattice_steps h1 lattice_steps_hold h4

end Formalism.L2.SG.Pf
