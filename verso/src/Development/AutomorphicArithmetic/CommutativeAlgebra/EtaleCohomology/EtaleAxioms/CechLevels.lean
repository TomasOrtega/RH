import Mathlib
import Development.EtaleCohomology.EtaleSheaves.CechLevels.Cech0Iso
import Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.LevelsGenOfSpecLim
import Development.EtaleCohomology.EtaleSheaves.CechLevelsGeneration.LevelsOfGen
import Development.EtaleCohomology.EtaleSheaves.SpecLimPf

namespace UpperTheory.Et.CechLevelsEtaleAxioms

/- English proof (translation)
The claim follows from `LateralTheory.E.SpecLimPf.SpecLim_of`.
-/
theorem a0 : LateralTheory.E.LevelsGenPf.SpecLim := LateralTheory.E.SpecLimPf.SpecLim_of
/- English proof (translation)
The claim follows from `LateralTheory.E.LevelsGenPf.LevelsGen_of_specLim a0`.
-/
theorem a1 : LateralTheory.E.LevelsPf.LevelsGen := LateralTheory.E.LevelsGenPf.LevelsGen_of_specLim a0
/- English proof (translation)
The claim follows from `LateralTheory.E.LevelsPf.Levels_of_gen a1`.
-/
theorem a2 : LateralTheory.E.CechLevelsPf.Levels := LateralTheory.E.LevelsPf.Levels_of_gen a1
/- English proof (translation)
The claim follows from `LateralTheory.E.CechLevelsPf.CechLevels_of' a2`.
-/
theorem a3 : LateralTheory.E.t_E1Cut.CechLevels := LateralTheory.E.CechLevelsPf.CechLevels_of' a2

/- English proof (translation)
The claim follows from `a3`.
-/
theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.CechLevels := a3

end UpperTheory.Et.CechLevelsEtaleAxioms
