import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.GoodModelLattice
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementK

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.KSum

open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)

/- English proof (translation)
Rewrite using `[Formalism.L2.Th1.F.pSeriesCoeff L 2, if_neg (by norm_num)]`. Use `first`. Consider the case `(simp only [PeriodPair.g₂]; push_cast; ring)`. Consider the case `(unfold PeriodPair.g₂; push_cast; ring)`. Consider the case `(norm_num [PeriodPair.g₂]; ring)`.
-/
theorem coeff_two_pSeries (L : PeriodPair) :
    PowerSeries.coeff 2 (pSeries L) = L.g₂ / 20 := by
  rw [Formalism.L2.Th1.F.pSeriesCoeff L 2, if_neg (by norm_num)]
  first
    | (simp only [PeriodPair.g₂]; push_cast; ring)
    | (unfold PeriodPair.g₂; push_cast; ring)
    | (norm_num [PeriodPair.g₂]; ring)

/- English proof (translation)
Unfold `taylor0`. Rewrite using `[PowerSeries.coeff_mk]`. Establish `hc : IsClosed (L.lattice : Set ℂ)` using `by first`. Consider the case `exact L.isClosed_lattice`. Consider the case `exact PeriodPair.isClosed_lattice L`.

Consider the case `(haveI : DiscreteTopology L.lattice.toAddSubgroup := inferInstanceAs (DiscreteTopology L.lattice)`. Conclude with `AddSubgroup.isClosed_of_discrete (H := L.lattice.toAddSubgroup))`. Establish `hopen : ∀ᶠ w in nhds P, w ∉ L.lattice` using `hc.isOpen_compl.mem_nhds hP`. Establish `hev : deriv L.weierstrassP =ᶠ[nhds P] L.derivWeierstrassP` using `by filter_upwards [hopen] with w hw first`. Consider the case `exact (L.hasDerivAt_weierstrassP hw).deriv`.

Consider the case `exact (PeriodPair.hasDerivAt_weierstrassP L hw).deriv`. Consider the case `exact congrFun L.deriv_weierstrassP w`. Establish `h1 : deriv (fun z => L.weierstrassP (z + P)) = fun w => deriv L.weierstrassP (w + P)`. Use function extensionality and compare the values at `w`. Rewrite using `[deriv_comp_add_const]`.

Establish `h2 : deriv (fun w => deriv L.weierstrassP (w + P)) 0 = 6 * L.weierstrassP P ^ 2 - L.g₂ / 2`. Rewrite using `[deriv_comp_add_const, zero_add, hev.deriv_eq]`. Conclude with `(Formalism.L2.Th1.F.pSecond L P hP).deriv`. Establish `h3 : iteratedDeriv 2 (fun z => L.weierstrassP (z + P)) = deriv (deriv (fun z => L.weierstrassP (z + P)))`. Rewrite using `[iteratedDeriv_succ, iteratedDeriv_one]`.

Rewrite using `[h3, h1, h2, Nat.factorial_two]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_two_shift (L : PeriodPair) (P : ℂ) (hP : P ∉ L.lattice) :
    PowerSeries.coeff 2 (taylor0 (fun z => L.weierstrassP (z + P)))
      = 3 * L.weierstrassP P ^ 2 - L.g₂ / 4 := by
  unfold taylor0
  rw [PowerSeries.coeff_mk]
  have hc : IsClosed (L.lattice : Set ℂ) := by
    first
      | exact L.isClosed_lattice
      | exact PeriodPair.isClosed_lattice L
      | (haveI : DiscreteTopology L.lattice.toAddSubgroup := inferInstanceAs (DiscreteTopology L.lattice)
         exact AddSubgroup.isClosed_of_discrete (H := L.lattice.toAddSubgroup))
  have hopen : ∀ᶠ w in nhds P, w ∉ L.lattice := hc.isOpen_compl.mem_nhds hP
  have hev : deriv L.weierstrassP =ᶠ[nhds P] L.derivWeierstrassP := by
    filter_upwards [hopen] with w hw
    first
      | exact (L.hasDerivAt_weierstrassP hw).deriv
      | exact (PeriodPair.hasDerivAt_weierstrassP L hw).deriv
      | exact congrFun L.deriv_weierstrassP w
  have h1 : deriv (fun z => L.weierstrassP (z + P)) = fun w => deriv L.weierstrassP (w + P) := by
    funext w
    rw [deriv_comp_add_const]
  have h2 : deriv (fun w => deriv L.weierstrassP (w + P)) 0 = 6 * L.weierstrassP P ^ 2 - L.g₂ / 2 := by
    rw [deriv_comp_add_const, zero_add, hev.deriv_eq]
    exact (Formalism.L2.Th1.F.pSecond L P hP).deriv
  have h3 : iteratedDeriv 2 (fun z => L.weierstrassP (z + P)) =
      deriv (deriv (fun z => L.weierstrassP (z + P))) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h3, h1, h2, Nat.factorial_two]
  push_cast
  ring

/- English proof (translation)
Introduce `L α S hα hst hS`. Take `⟨neg, -, -, -, h3⟩` from `Formalism.L2.Th1.F.endoZInstance L α S hα hst hS`. Establish `h4` using `congrArg (PowerSeries.coeff 2) h3`. Rewrite `h4` using `[PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, map_add, map_sum, coeff_two_pSeries]`. Establish `h5 : ∀ P : S, PowerSeries.coeff 2 (taylor0 (fun z => L.weierstrassP (z + (P : ℂ))) - PowerSeries.C (L.weierstrassP (P : ℂ))) = 3 * L.weierstrassP (P : ℂ) ^ 2 - L.g₂ / 4`.

Introduce `P`. Rewrite using `[map_sub, coeff_two_shift L P (hS.1 P P.2).2, PowerSeries.coeff_C]`. Simplify using the standard rewrite rules. Rewrite `h4` using `[Finset.sum_congr rfl (fun P _ => h5 P), Finset.sum_coe_sort S (fun P => 3 * L.weierstrassP P ^ 2 - L.g₂ / 4)]`. Take the linear combination `-h4`.
-/
theorem kappa_sum_holds : KappaSum := by
  intro L α S hα hst hS
  obtain ⟨neg, -, -, -, h3⟩ := Formalism.L2.Th1.F.endoZInstance L α S hα hst hS
  have h4 := congrArg (PowerSeries.coeff 2) h3
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, map_add, map_sum,
    coeff_two_pSeries] at h4
  have h5 : ∀ P : S, PowerSeries.coeff 2
      (taylor0 (fun z => L.weierstrassP (z + (P : ℂ))) - PowerSeries.C (L.weierstrassP (P : ℂ)))
        = 3 * L.weierstrassP (P : ℂ) ^ 2 - L.g₂ / 4 := by
    intro P
    rw [map_sub, coeff_two_shift L P (hS.1 P P.2).2, PowerSeries.coeff_C]
    simp
  rw [Finset.sum_congr rfl (fun P _ => h5 P),
    Finset.sum_coe_sort S (fun P => 3 * L.weierstrassP P ^ 2 - L.g₂ / 4)] at h4
  linear_combination -h4

end Formalism.L2.Th1.B.KSum
