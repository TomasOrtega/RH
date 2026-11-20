import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XSqLimit

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `hI d σ _ SY a₀ ε Q w`. Establish `hCS : ConvergenceSignedStatement` using `hI.1.2.1`. Establish `ht0 : 0 < Q.SW.t₀` using `(Q.SW.reg none).1`. Set `mm : σ × Fin 2 → Option σ` to `fun i => if i.2 = 0 then some i.1 else if i.1 = a₀ then none else some i.1`. Set `c : σ × Fin 2 → ℝ` to `fun i => 1 / 2 * (ε i.1 : ℝ)`.

Establish `hph : ∀ x, 1 / 2 * ∑ a : σ, (ε a : ℝ) * (SY.ph a (Q.q 0 x) + SY.ph a (Q.q 1 x)) = ∑ i : σ × Fin 2, c i * Q.SW.ph (mm i) x`. Introduce `x`. Rewrite using `[Fintype.sum_prod_type, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_two]`.

Establish `e0 : Q.SW.ph (mm (a, 0)) x = SY.ph a (Q.q 0 x)` using `by simp [mm, Q.ph0]`. Establish `e1 : Q.SW.ph (mm (a, 1)) x = SY.ph a (Q.q 1 x)`. Distinguish the cases in `ha : a = a₀`. Substitute `ha` using the available equality. Simplify using `[mm, Q.ph1]`.

Simplify using `[mm, ha, Q.ph0]`. Conclude with `congrFun (Q.base_ph a ha) x`. Rewrite using `[e0, e1]`. Simplify using `only [c]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hphT : ∀ t x, 1 / 2 * ∑ a : σ, (ε a : ℝ) * (SY.phT a t (Q.q 0 x) + SY.phT a t (Q.q 1 x)) = ∑ i : σ × Fin 2, c i * Q.SW.phT (mm i) t x`. Introduce `t x`. Rewrite using `[Fintype.sum_prod_type, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_two]`.

Establish `e0 : Q.SW.phT (mm (a, 0)) t x = SY.phT a t (Q.q 0 x)` using `by simp [mm, Q.phase_some_eq_comp_first_projection]`. Establish `e1 : Q.SW.phT (mm (a, 1)) t x = SY.phT a t (Q.q 1 x)`. Distinguish the cases in `ha : a = a₀`. Substitute `ha` using the available equality. Simplify using `[mm, Q.phase_none_eq_comp_second_projection]`.

Simplify using `[mm, ha, Q.phase_some_eq_comp_first_projection]`. Conclude with `congrFun (Q.base_phT a ha t) x`. Rewrite using `[e0, e1]`. Simplify using `only [c]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hgH : Q.gH = fun x => logNormSec Q.L' Q.v x + (Q.cst + ∑ i, c i * Q.SW.ph (mm i) x)`. Use function extensionality and compare the values at `x`. Simplify using `only [AnSq.gH]`. Rewrite using `[hph]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hgT : ∀ t, Q.gT t = fun x => logNormSec Q.L' Q.v x + (Q.cst + ∑ i, c i * Q.SW.phT (mm i) t x)`. Introduce `t`. Use function extensionality and compare the values at `x`. Simplify using `only [AnSq.gT]`. Rewrite using `[hphT]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨hsI, hsE, hsT⟩` from `PositivityTheory.Xgp.sq_limit.singular_part hI Q w`. Take `⟨hrI, hrT⟩` from `PositivityTheory.Xgp.sq_limit.regular hCS Q.SW w mm c Q.cst ht0`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hgH]`.

Conclude with `PositivityTheory.Xgp.sq_limit.mIntegrable_add' _ _ hsI hrI`. Rewrite using `[hgH, PositivityTheory.Xgp.sq_limit.mInt_add' _ _ hsI hrI]`. Establish `hev : ∀ᶠ t in 𝓝[>] (0:ℝ), mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (logNormSec Q.L' Q.v) + mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (fun x => Q.cst + ∑ i, c i * Q.SW.phT (mm i) t x) = mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (Q.gT t)` using `by filter_upwards [hsE, Ioo_mem_nhdsGT ht0] with t ht htt`. Rewrite using `[hgT t]`. Use `(PositivityTheory.Xgp.sq_limit.mInt_add' _ _ ht ?_).symm` and prove the remaining obligations.

Apply `PositivityTheory.Xgp.sq_limit.mIntegrable_of_continuous` to reduce the goal to its premises. Introduce `i`. Conclude with `ReciprocityTheory.AnForm.M.isPotentialAdd _ _ _ (Q.SW.sing (w i)).1 (ReciprocityTheory.AnForm.M.isPotential_ofFun _ _ ((Q.SW.reg (w i)).2.2 t htt.1 htt.2.le).1)`. Conclude with `continuous_const.add (continuous_finset_sum _ fun i _ => continuous_const.mul (ReciprocityTheory.AnForm.M.projLine_continuous_of_smooth _ ((Q.SW.reg (mm i)).2.2 t htt.1 htt.2.le).1))`. Conclude with `(hsT.add hrT).congr' hev`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.analytic_square_regularized_convergence : Inputs → ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (w : Fin (d + 2) → Option σ), MIntegrable Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH ∧ Tendsto (fun t => mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (Q.gT t)) (𝓝[>] 0) (𝓝 (mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH)) := by
  intro hI d σ _ SY a₀ ε Q w
  classical
  have hCS : ConvergenceSignedStatement := hI.1.2.1
  have ht0 : 0 < Q.SW.t₀ := (Q.SW.reg none).1
  let mm : σ × Fin 2 → Option σ := fun i => if i.2 = 0 then some i.1 else if i.1 = a₀ then none else some i.1
  let c : σ × Fin 2 → ℝ := fun i => 1 / 2 * (ε i.1 : ℝ)
  have hph : ∀ x, 1 / 2 * ∑ a : σ, (ε a : ℝ) * (SY.ph a (Q.q 0 x) + SY.ph a (Q.q 1 x)) = ∑ i : σ × Fin 2, c i * Q.SW.ph (mm i) x := by
    intro x
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_two]
    have e0 : Q.SW.ph (mm (a, 0)) x = SY.ph a (Q.q 0 x) := by simp [mm, Q.ph0]
    have e1 : Q.SW.ph (mm (a, 1)) x = SY.ph a (Q.q 1 x) := by
      by_cases ha : a = a₀
      · subst ha
        simp [mm, Q.ph1]
      · simp [mm, ha, Q.ph0]
        exact congrFun (Q.base_ph a ha) x
    rw [e0, e1]
    simp only [c]
    ring
  have hphT : ∀ t x, 1 / 2 * ∑ a : σ, (ε a : ℝ) * (SY.phT a t (Q.q 0 x) + SY.phT a t (Q.q 1 x)) = ∑ i : σ × Fin 2, c i * Q.SW.phT (mm i) t x := by
    intro t x
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_two]
    have e0 : Q.SW.phT (mm (a, 0)) t x = SY.phT a t (Q.q 0 x) := by simp [mm, Q.phase_some_eq_comp_first_projection]
    have e1 : Q.SW.phT (mm (a, 1)) t x = SY.phT a t (Q.q 1 x) := by
      by_cases ha : a = a₀
      · subst ha
        simp [mm, Q.phase_none_eq_comp_second_projection]
      · simp [mm, ha, Q.phase_some_eq_comp_first_projection]
        exact congrFun (Q.base_phT a ha t) x
    rw [e0, e1]
    simp only [c]
    ring
  have hgH : Q.gH = fun x => logNormSec Q.L' Q.v x + (Q.cst + ∑ i, c i * Q.SW.ph (mm i) x) := by
    funext x
    simp only [AnSq.gH]
    rw [hph]
    ring
  have hgT : ∀ t, Q.gT t = fun x => logNormSec Q.L' Q.v x + (Q.cst + ∑ i, c i * Q.SW.phT (mm i) t x) := by
    intro t
    funext x
    simp only [AnSq.gT]
    rw [hphT]
    ring
  obtain ⟨hsI, hsE, hsT⟩ := PositivityTheory.Xgp.sq_limit.singular_part hI Q w
  obtain ⟨hrI, hrT⟩ := PositivityTheory.Xgp.sq_limit.regular hCS Q.SW w mm c Q.cst ht0
  refine ⟨?_, ?_⟩
  · rw [hgH]
    exact PositivityTheory.Xgp.sq_limit.mIntegrable_add' _ _ hsI hrI
  · rw [hgH, PositivityTheory.Xgp.sq_limit.mInt_add' _ _ hsI hrI]
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (logNormSec Q.L' Q.v) + mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (fun x => Q.cst + ∑ i, c i * Q.SW.phT (mm i) t x) = mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (Q.gT t) := by
      filter_upwards [hsE, Ioo_mem_nhdsGT ht0] with t ht htt
      rw [hgT t]
      refine (PositivityTheory.Xgp.sq_limit.mInt_add' _ _ ht ?_).symm
      apply PositivityTheory.Xgp.sq_limit.mIntegrable_of_continuous
      · intro i
        exact ReciprocityTheory.AnForm.M.isPotentialAdd _ _ _ (Q.SW.sing (w i)).1 (ReciprocityTheory.AnForm.M.isPotential_ofFun _ _ ((Q.SW.reg (w i)).2.2 t htt.1 htt.2.le).1)
      · exact continuous_const.add (continuous_finset_sum _ fun i _ => continuous_const.mul (ReciprocityTheory.AnForm.M.projLine_continuous_of_smooth _ ((Q.SW.reg (mm i)).2.2 t htt.1 htt.2.le).1))
    exact (hsT.add hrT).congr' hev
