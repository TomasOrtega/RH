import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LinFormOneZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp Xc)

/- English proof (translation)
Introduce `m hm k`. Take `⟨i, -, hi⟩` from `Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)`. Rewrite `hi` using `[C_mul_X_eq_monomial]`. Establish `hmi` using `Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hi)`. Substitute `hmi` using the available equality.

Consider the cases of `k`. Simplify using `[Finsupp.single_apply]`.
-/
theorem isMultiHomog_linForm {n : ℕ} (u : Fin n → ℤ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (fun _ => 1) := by
  classical
  intro m hm k
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at hi
  have hmi := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hi)
  subst hmi
  cases k
  simp [Finsupp.single_apply]

/- English proof (translation)
Introduce `n d P u H hP hu hH hHor`. Take `⟨hK, ⟨hPp, hPh, -⟩, -, hPdim⟩` from `hP`. Take `⟨hHmin, hHrel⟩` from `hH`. Use `hPp` as an intermediate fact. Establish `h1` using `ReciprocityTheory.ChartRestriction.G.Geo.dim_quot_minimal_add_one P H _ hu hHmin`.

Rewrite `h1` using `[hPdim]`. Use `⟨hK, ⟨hHmin.1.1, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_of_mem_minimalPrimes hPh (isMultiHomog_linForm u) hHmin, hHrel⟩, hHor, ReciprocityTheory.ChartRestriction.G.Geo.withBot_eq_of_add_one ?_⟩` and prove the remaining obligations. Rewrite using `[h1, show d + 1 + Fintype.card Unit = d + Fintype.card Unit + 1 by omega]`.
-/
theorem DivSuppHorizontalArithVar.proof : DivSuppHorizontalArithVar.Statement := by
  intro n d P u H hP hu hH hHor
  obtain ⟨hK, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  obtain ⟨hHmin, hHrel⟩ := hH
  have := hPp
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.dim_quot_minimal_add_one P H _ hu hHmin
  rw [hPdim] at h1
  refine ⟨hK, ⟨hHmin.1.1, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_of_mem_minimalPrimes hPh
    (isMultiHomog_linForm u) hHmin, hHrel⟩, hHor,
    ReciprocityTheory.ChartRestriction.G.Geo.withBot_eq_of_add_one ?_⟩
  rw [h1, show d + 1 + Fintype.card Unit = d + Fintype.card Unit + 1 by omega]

end ObjectsChow

end GroundTheory.Heights₂.Heights
