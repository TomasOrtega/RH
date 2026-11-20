import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt

namespace ReciprocityTheory.ChartRestriction.G.H1

/- English proof (translation)
Introduce `E _ _ _ H V _ _ _ t P`. Use `letI := H.starRing`. Introduce `F _ _ _ k a p`. Conclude with `Geo.Tor.qkAct_exists hG P.D.tau_bimult P.oD a p`.
-/
theorem qkActExists_of (hG : Out.GlobalFnsSt) : QkActExistsStatement := by
  intro E _ _ _ H V _ _ _ t P
  letI := H.starRing
  intro F _ _ _ k a p
  exact Geo.Tor.qkAct_exists hG P.D.tau_bimult P.oD a p

end ReciprocityTheory.ChartRestriction.G.H1
