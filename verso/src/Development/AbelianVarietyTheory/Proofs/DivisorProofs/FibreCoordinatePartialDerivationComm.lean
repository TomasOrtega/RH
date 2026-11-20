import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial

set_option autoImplicit false

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

/- English proof (translation)
Establish `key : ∀ (u v : Tot I g) (p : Tot I g), p ∈ W → (Hol.der u (Hol.der v x)).fn p = fderiv ℂ (fderiv ℂ x.fn) p u v`. Introduce `u v p hp`. Establish `hx : AnalyticAt ℂ x.fn p` using `x.analytic p hp`. Establish `e : (Hol.der v x).fn =ᶠ[nhds p] fun q ↦ fderiv ℂ x.fn q v` using `by filter_upwards [W.isOpen.mem_nhds hp] with q hq using Hol.fn_der v x hq`. Rewrite using `[Hol.fn_der u _ hp, e.fderiv_eq, fderiv_clm_apply hx.fderiv.differentiableAt (differentiableAt_const v)]`.

Simplify using the standard rewrite rules. Use `Hol.ext_fn fun p hp ↦ ?_` and prove the remaining obligations. Establish `hx : AnalyticAt ℂ x.fn p` using `x.analytic p hp`. Establish `hs : IsSymmSndFDerivAt ℂ x.fn p` using `(hx.contDiffAt (n := ⊤)).isSymmSndFDerivAt (by simp)`. Unfold `dw`.

Rewrite using `[key _ _ p hp, key _ _ p hp]`. Conclude with `hs _ _`.
-/
theorem dw_comm (I : Type) [Fintype I] (g : ℕ) (W : Opens (Tot I g)) (a b : Fin g) (x : Hol W) :
    dw a (dw b x) = dw b (dw a x) := by
  have key : ∀ (u v : Tot I g) (p : Tot I g), p ∈ W →
      (Hol.der u (Hol.der v x)).fn p = fderiv ℂ (fderiv ℂ x.fn) p u v := by
    intro u v p hp
    have hx : AnalyticAt ℂ x.fn p := x.analytic p hp
    have e : (Hol.der v x).fn =ᶠ[nhds p] fun q ↦ fderiv ℂ x.fn q v := by
      filter_upwards [W.isOpen.mem_nhds hp] with q hq using Hol.fn_der v x hq
    rw [Hol.fn_der u _ hp, e.fderiv_eq,
      fderiv_clm_apply hx.fderiv.differentiableAt (differentiableAt_const v)]
    simp
  refine Hol.ext_fn fun p hp ↦ ?_
  have hx : AnalyticAt ℂ x.fn p := x.analytic p hp
  have hs : IsSymmSndFDerivAt ℂ x.fn p :=
    (hx.contDiffAt (n := ⊤)).isSymmSndFDerivAt (by simp)
  unfold dw
  rw [key _ _ p hp, key _ _ p hp]
  exact hs _ _

end GlobalTheory.AnPer
