import Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.QuotCop
import Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.TensCop

namespace LateralTheory.E.LevelsGenPf

/- English proof (translation)
The claim follows from `LevelsGen_of tensCop quotCop hS`.
-/
theorem LevelsGen_of_specLim (hS : SpecLim) : LateralTheory.E.LevelsPf.LevelsGen := LevelsGen_of tensCop quotCop hS

end LateralTheory.E.LevelsGenPf
