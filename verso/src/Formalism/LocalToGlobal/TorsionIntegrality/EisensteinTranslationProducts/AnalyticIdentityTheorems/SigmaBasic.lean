import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Legendre

noncomputable section
open scoped BigOperators ComplexConjugate
open Filter

namespace Formalism.L2.Th1.F

namespace SigmaBasic

/- English proof (translation)
Unfold `wFactor`. Use `fun_prop`.
-/
lemma differentiable_wFactor (l : ℂ) : Differentiable ℂ (wFactor l) := by
  unfold wFactor
  fun_prop

/- English proof (translation)
Simplify using `[wFactor]`.
-/
lemma wFactor_zero_right (l : ℂ) : wFactor l 0 = 1 := by
  simp [wFactor]

/- English proof (translation)
Simplify using `only [wFactor, neg_div_neg_eq, neg_sq]`.
-/
lemma wFactor_neg_neg (l z : ℂ) : wFactor (-l) (-z) = wFactor l z := by
  simp only [wFactor, neg_div_neg_eq, neg_sq]

/- English proof (translation)
Unfold `wFactor`. Rewrite using `[mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), sub_eq_zero, eq_comm, div_eq_one_iff_eq hl]`.
-/
lemma wFactor_eq_zero_iff {l : ℂ} (hl : l ≠ 0) (z : ℂ) : wFactor l z = 0 ↔ z = l := by
  unfold wFactor
  rw [mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), sub_eq_zero, eq_comm, div_eq_one_iff_eq hl]

/- English proof (translation)
Simplify using `[wFactor]`.
-/
lemma wFactor_zero_left (z : ℂ) : wFactor 0 z = 1 := by
  simp [wFactor]

/- English proof (translation)
Rewrite using `[← differentiableOn_univ]`. Use `TendstoLocallyUniformlyOn.differentiableOn (h L) ?_ isOpen_univ` and prove the remaining obligations. Use `Eventually.of_forall fun s => ?_` and prove the remaining obligations. Use `Differentiable.differentiableOn ?_` and prove the remaining obligations. Introduce `x`.

Conclude with `DifferentiableAt.fun_finset_prod fun l _ => differentiable_wFactor _ x`.
-/
lemma differentiable_tprod (h : SigmaProdLU) (L : PeriodPair) :
    Differentiable ℂ (fun z => ∏' l : L.lattice, wFactor (l : ℂ) z) := by
  rw [← differentiableOn_univ]
  refine TendstoLocallyUniformlyOn.differentiableOn (h L) ?_ isOpen_univ
  refine Eventually.of_forall fun s => ?_
  refine Differentiable.differentiableOn ?_
  intro x
  exact DifferentiableAt.fun_finset_prod fun l _ => differentiable_wFactor _ x

end SigmaBasic

open SigmaBasic

/- English proof (translation)
Introduce `L`. Unfold `wSigma`. Conclude with `differentiable_id.mul (differentiable_tprod h L)`.
-/
theorem sigmaEntire_of (h : SigmaProdLU) : SigmaEntire := by
  intro L
  unfold wSigma
  exact differentiable_id.mul (differentiable_tprod h L)

/- English proof (translation)
Introduce `L z`. Establish `hP : ∏' l : L.lattice, wFactor (l : ℂ) (-z) = ∏' l : L.lattice, wFactor (l : ℂ) z`. Establish `e` using `(Equiv.neg L.lattice).tprod_eq (fun l : L.lattice => wFactor (l : ℂ) (-z))`. Rewrite using `[← e]`. Use `congr 1`.

Use extensionality with `l`. Simplify using `[wFactor_neg_neg]`. Unfold `wSigma`. Rewrite using `[hP]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sigma_odd : SigmaOdd := by
  intro L z
  have hP : ∏' l : L.lattice, wFactor (l : ℂ) (-z) = ∏' l : L.lattice, wFactor (l : ℂ) z := by
    have e := (Equiv.neg L.lattice).tprod_eq (fun l : L.lattice => wFactor (l : ℂ) (-z))
    rw [← e]
    congr 1
    ext l
    simp [wFactor_neg_neg]
  unfold wSigma
  rw [hP]
  ring

/- English proof (translation)
Introduce `L z`. Unfold `wSigma`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Break down `mul_eq_zero.mp h0 with hz | hp` into its components or cases.

Rewrite using `[hz]`. Conclude with `zero_mem _`. Assume the negation of the conclusion as `hz`. Establish `hne : ∀ l : L.lattice, wFactor (l : ℂ) z ≠ 0`. Introduce `l hl`.

Distinguish the cases in `hl0 : (l : ℂ) = 0`. Rewrite `hl` using `[hl0, wFactor_zero_left]`. Conclude with `one_ne_zero hl`. Rewrite `hl` using `[wFactor_eq_zero_iff hl0]`. Conclude with `hz (by rw [hl]; exact l.2)`.

Establish `hs : Summable (fun l : L.lattice => Complex.log (wFactor (l : ℂ) z))`. Use `Complex.summable_log_one_add_of_summable (Summable.of_norm (h L z))` as an intermediate fact. Simplify `this` using `only [add_sub_cancel]`. Rewrite `hp` using `[← Complex.cexp_tsum_eq_tprod hne hs]`. Conclude with `Complex.exp_ne_zero _ hp`.

Introduce `hz`. Distinguish the cases in `hz0 : z = 0`. Rewrite using `[hz0, zero_mul]`. Rewrite using `[tprod_of_exists_eq_zero ⟨⟨z, hz⟩, (wFactor_eq_zero_iff hz0 z).mpr rfl⟩, mul_zero]`.
-/
theorem sigmaZero_of (h : SigmaSummable) : SigmaZero := by
  intro L z
  unfold wSigma
  constructor
  · intro h0
    rcases mul_eq_zero.mp h0 with hz | hp
    · rw [hz]
      exact zero_mem _
    · by_contra hz
      have hne : ∀ l : L.lattice, wFactor (l : ℂ) z ≠ 0 := by
        intro l hl
        by_cases hl0 : (l : ℂ) = 0
        · rw [hl0, wFactor_zero_left] at hl
          exact one_ne_zero hl
        · rw [wFactor_eq_zero_iff hl0] at hl
          exact hz (by rw [hl]; exact l.2)
      have hs : Summable (fun l : L.lattice => Complex.log (wFactor (l : ℂ) z)) := by
        have := Complex.summable_log_one_add_of_summable (Summable.of_norm (h L z))
        simpa only [add_sub_cancel] using this
      rw [← Complex.cexp_tsum_eq_tprod hne hs] at hp
      exact Complex.exp_ne_zero _ hp
  · intro hz
    by_cases hz0 : z = 0
    · rw [hz0, zero_mul]
    · rw [tprod_of_exists_eq_zero ⟨⟨z, hz⟩, (wFactor_eq_zero_iff hz0 z).mpr rfl⟩, mul_zero]

/- English proof (translation)
Introduce `L`. Establish `hP` using `differentiable_tprod h L 0`. Unfold `wSigma`. Rewrite using `[deriv_fun_mul (by fun_prop) hP]`. Simplify using `[wFactor_zero_right]`.
-/
theorem sigmaDerivZero_of (h : SigmaProdLU) : ∀ L : PeriodPair, deriv (wSigma L) 0 = 1 := by
  intro L
  have hP := differentiable_tprod h L 0
  unfold wSigma
  rw [deriv_fun_mul (by fun_prop) hP]
  simp [wFactor_zero_right]

end Formalism.L2.Th1.F
