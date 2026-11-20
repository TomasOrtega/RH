import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem betaH_expand {k : Type} [CommRing k] {d : ℕ} (s : Matrix (Fin d) (Fin d) k) (u φ u' φ' : Fin d → k) :
    betaH k (u, fun i => φ i - s.mulVec u i) (u', fun i => φ' i - s.mulVec u' i) =
      ∑ i, (φ' i * u i - φ i * u' i) + ∑ i, ∑ j, (s j i - s i j) * u i * u' j := by
  have step1 : betaH k (u, fun i => φ i - s.mulVec u i) (u', fun i => φ' i - s.mulVec u' i) =
      ∑ i, (φ' i * u i - φ i * u' i) - ∑ i, ∑ j, s i j * u i * u' j + ∑ i, ∑ j, s i j * u j * u' i := by
    simp only [betaH, Matrix.mulVec, dotProduct]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_mul, sub_mul, Finset.sum_mul, Finset.sum_mul]
    have e1 : ∑ j, s i j * u' j * u i = ∑ j, s i j * u i * u' j := Finset.sum_congr rfl fun j _ => by ring
    rw [e1]; ring
  have step2 : ∑ i, ∑ j, s i j * u j * u' i = ∑ i, ∑ j, s j i * u i * u' j := Finset.sum_comm
  rw [step1, step2]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
