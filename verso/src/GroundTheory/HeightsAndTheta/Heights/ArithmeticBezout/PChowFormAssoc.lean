import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `F _ n k I g g' hg hg'`. Establish `h1 : g ∣ g'` using `(hg.2 g').mp ((hg'.2 g').mpr dvd_rfl)`. Establish `h2 : g' ∣ g` using `(hg'.2 g).mp ((hg.2 g).mpr dvd_rfl)`. Take `⟨u, hu⟩` from `associated_of_dvd_dvd h1 h2`. Take `⟨c, hc, hcu⟩` from `(isUnit_iff_eq_C_of_isReduced (P := (u : MvPolynomial (Fin k × Fin n) F))).mp u.isUnit`.

Use `⟨c, hc.ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[← hu, hcu, mul_comm]`.
-/
theorem ChowFormAssoc.proof : ChowFormAssoc.Statement := by
  intro F _ n k I g g' hg hg'
  have h1 : g ∣ g' := (hg.2 g').mp ((hg'.2 g').mpr dvd_rfl)
  have h2 : g' ∣ g := (hg'.2 g).mp ((hg.2 g).mpr dvd_rfl)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd h1 h2
  obtain ⟨c, hc, hcu⟩ :=
    (isUnit_iff_eq_C_of_isReduced (P := (u : MvPolynomial (Fin k × Fin n) F))).mp u.isUnit
  refine ⟨c, hc.ne_zero, ?_⟩
  rw [← hu, hcu, mul_comm]

end GroundTheory.Heights₂.Heights
