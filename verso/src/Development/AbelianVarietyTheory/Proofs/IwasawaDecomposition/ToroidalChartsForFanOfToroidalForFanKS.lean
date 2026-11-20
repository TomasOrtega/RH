import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

namespace GlobalTheory

/- English proof (translation)
Introduce `h` and use `h.toroidalChartsForFan`.
-/
theorem toroidalChartsForFan_of_toroidalForFanKS :
    GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.ToroidalChartsForFan :=
  fun h => h.toroidalChartsForFan

end GlobalTheory
