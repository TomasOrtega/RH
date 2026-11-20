import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.LeviForms.HomDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

/- English proof (translation)
Set `e : Fin m ≃ {a : Fin N // (a : ℕ) < m}` to `{ toFun := fun i => ⟨Fin.castLE hm i, i.2⟩, invFun := fun a => ⟨a.1, a.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }`. Establish `hdet : (gramHead hd m (cellMat N z)).det = (((cellMat N z)ᴴ * diagonal (fun k => (hd k : ℂ)) * cellMat N z).submatrix (Fin.castLE hm) (Fin.castLE hm)).det`. Rewrite using `[← Matrix.det_submatrix_equiv_self e (gramHead hd m (cellMat N z))]`. Both sides reduce to the same expression. Use `delta GlobalTheory.CompanionTheory.Ar.PB.gramLog ReciprocityTheory.AnForm.P.logDetFlag`.

Rewrite using `[hdet]`.
-/
theorem gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (z : Pairs N → ℂ) :
    gramLog hd m (cellMat N z) = logDetFlag N hd m hm z := by
  let e : Fin m ≃ {a : Fin N // (a : ℕ) < m} :=
    { toFun := fun i => ⟨Fin.castLE hm i, i.2⟩, invFun := fun a => ⟨a.1, a.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hdet : (gramHead hd m (cellMat N z)).det =
      (((cellMat N z)ᴴ * diagonal (fun k => (hd k : ℂ)) * cellMat N z).submatrix
        (Fin.castLE hm) (Fin.castLE hm)).det := by
    rw [← Matrix.det_submatrix_equiv_self e (gramHead hd m (cellMat N z))]
    rfl
  delta GlobalTheory.CompanionTheory.Ar.PB.gramLog ReciprocityTheory.AnForm.P.logDetFlag
  rw [hdet]

/- English proof (translation)
Establish `hE : logDetFlag N hd m hm = fun z => 1 / 2 * Real.log |detGram N hd m hm z|` using `logDetFlag_eq N hd m hm`. Establish `hf : (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) = fun z => 1 / 2 * Real.log (detGram N hd m hm z)`. Use function extensionality and compare the values at `z`. Rewrite using `[gramLog_cellMat N hd m hm z, hE]`. Simplify using `only [Real.log_abs]`.

Rewrite using `[hf]`. Take `⟨hC, h0, -⟩` from `detGram_deriv N hd m hm`. Establish `hne : detGram N hd m hm 0 ≠ 0`. Rewrite using `[h0]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun a _ => hd0 _`.

Conclude with `contDiffAt_const.mul (hC.contDiffAt.log hne)`.
-/
theorem contDiffAt_gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (hd0 : ∀ k, hd k ≠ 0) (m : ℕ) (hm : m ≤ N) :
    ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) 0 := by
  have hE : logDetFlag N hd m hm = fun z => 1 / 2 * Real.log |detGram N hd m hm z| :=
    logDetFlag_eq N hd m hm
  have hf : (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) =
      fun z => 1 / 2 * Real.log (detGram N hd m hm z) := by
    funext z
    rw [gramLog_cellMat N hd m hm z, hE]
    simp only [Real.log_abs]
  rw [hf]
  obtain ⟨hC, h0, -⟩ := detGram_deriv N hd m hm
  have hne : detGram N hd m hm 0 ≠ 0 := by
    rw [h0]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hd0 _
  exact contDiffAt_const.mul (hC.contDiffAt.log hne)

/- English proof (translation)
Establish `hf : (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) = logDetFlag N hd m hm`. Use function extensionality and compare the values at `z`. Conclude with `gramLog_cellMat N hd m hm z`. Rewrite using `[hf]`. Conclude with `homDensity N hd hd0 m hm w`.
-/
theorem levi_gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (hd0 : ∀ k, hd k ≠ 0) (m : ℕ) (hm : m ≤ N)
    (w : Pairs N → ℂ) :
    levi (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) 0 w =
      ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
        hd p.1.2 / (2 * hd p.1.1) * ‖w p‖ ^ 2 else 0 := by
  have hf : (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) = logDetFlag N hd m hm := by
    funext z
    exact gramLog_cellMat N hd m hm z
  rw [hf]
  exact homDensity N hd hd0 m hm w

/- English proof (translation)
Use `delta GlobalTheory.CompanionTheory.Ar.PB.sigForm`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem sigForm_ne_zero (N j : ℕ) (k : Fin N) : sigForm N j k ≠ 0 := by
  delta GlobalTheory.CompanionTheory.Ar.PB.sigForm
  split_ifs <;> norm_num

/- English proof (translation)
Introduce `N j hj i w`. Simplify using `only`. Establish `hs` using `sigForm_ne_zero N j`. Establish `hσ : ∀ k : Fin N, sigForm N j k = if (k : ℕ) < N - j then -1 else 1` using `fun k => rfl`. Establish `G : ∀ m, m ≤ N → ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog (sigForm N j) m (cellMat N z)) 0` using `fun m hm => contDiffAt_gramLog_cellMat N (sigForm N j) hs m hm`.

Establish `Lv : ∀ m, m ≤ N → levi (fun z : Pairs N → ℂ => gramLog (sigForm N j) m (cellMat N z)) 0 w = ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then sigForm N j p.1.2 / (2 * sigForm N j p.1.1) * ‖w p‖ ^ 2 else 0` using `fun m hm => levi_gramLog_cellMat N (sigForm N j) hs m hm w`. Establish `hi` using `i.2`. Distinguish the cases in `hij : (i : ℕ) + 1 ≤ j`. Establish `h1 : N - j + ((i : ℕ) + 1) ≤ N` using `by omega`. Establish `h0 : N - j ≤ N` using `by omega`.

Establish `hfun : (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) = fun z => gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) (cellMat N z) + (-1) * gramLog (sigForm N j) (N - j) (cellMat N z)`. Use function extensionality and compare the values at `z`. Use `delta GlobalTheory.CompanionTheory.Ar.PB.stepPot`. Rewrite using `[if_pos hij]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hfun]`. Use `⟨(G _ h1).add (contDiffAt_const.mul (G _ h0)), ?_⟩` and prove the remaining obligations. Use `(levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) (cellMat N z)) (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j) (cellMat N z)) (-1) (G _ h1) (G _ h0) w).trans ?_` and prove the remaining obligations. Rewrite using `[Lv _ h1, Lv _ h0, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Break down `p with ⟨⟨a, b⟩, hab⟩` into its components or cases. Establish `hab' : (a : ℕ) < b` using `hab`. Establish `ha` using `a.2`. Establish `hb` using `b.2`. Simplify using `only`.

Simplify using `only [hσ]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | norm_num | ring`. Establish `h1 : N - j ≤ N` using `by omega`. Establish `h2 : (i : ℕ) + 1 - j ≤ N` using `by omega`. Establish `hN : N ≤ N` using `le_refl N`.

Establish `hfun : (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) = fun z => (gramLog (sigForm N j) N (cellMat N z) + (-1) * gramLog (sigForm N j) (N - j) (cellMat N z)) + 1 * gramLog (sigForm N j) ((i : ℕ) + 1 - j) (cellMat N z)`. Use function extensionality and compare the values at `z`. Use `delta GlobalTheory.CompanionTheory.Ar.PB.stepPot`. Rewrite using `[if_neg hij]`. Expand and normalize the polynomial expressions, which then agree.

Establish `GA : ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z) + (-1) * gramLog (sigForm N j) (N - j) (cellMat N z)) 0` using `(G _ hN).add (contDiffAt_const.mul (G _ h1))`. Rewrite using `[hfun]`. Use `⟨GA.add (contDiffAt_const.mul (G _ h2)), ?_⟩` and prove the remaining obligations. Use `(levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z) + (-1) * gramLog (sigForm N j) (N - j) (cellMat N z)) (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) ((i : ℕ) + 1 - j) (cellMat N z)) 1 GA (G _ h2) w).trans ?_` and prove the remaining obligations. Rewrite using `[levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z)) (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j) (cellMat N z)) (-1) (G _ hN) (G _ h1) w]`.

Rewrite using `[Lv _ hN, Lv _ h1, Lv _ h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Break down `p with ⟨⟨a, b⟩, hab⟩` into its components or cases. Establish `hab' : (a : ℕ) < b` using `hab`. Establish `ha` using `a.2`.

Establish `hb` using `b.2`. Simplify using `only`. Simplify using `only [hσ]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | norm_num | ring`.
-/
theorem levi_stepPot_cell : ∀ (N j : ℕ), j ≤ N → ∀ (i : Fin N) (w : Pairs N → ℂ), let r : Fin N → ℕ := fun a => if (a : ℕ) < N - j then j + a else a - (N - j); ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 ∧ levi (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 w = ∑ p : Pairs N, if min (r p.1.1) (r p.1.2) ≤ (i : ℕ) ∧ (i : ℕ) < max (r p.1.1) (r p.1.2) then (1 / 2 : ℝ) * ‖w p‖ ^ 2 else 0 := by
  intro N j hj i w
  dsimp only
  have hs := sigForm_ne_zero N j
  have hσ : ∀ k : Fin N, sigForm N j k = if (k : ℕ) < N - j then -1 else 1 := fun k => rfl
  have G : ∀ m, m ≤ N →
      ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog (sigForm N j) m (cellMat N z)) 0 :=
    fun m hm => contDiffAt_gramLog_cellMat N (sigForm N j) hs m hm
  have Lv : ∀ m, m ≤ N → levi (fun z : Pairs N → ℂ => gramLog (sigForm N j) m (cellMat N z)) 0 w =
      ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
        sigForm N j p.1.2 / (2 * sigForm N j p.1.1) * ‖w p‖ ^ 2 else 0 :=
    fun m hm => levi_gramLog_cellMat N (sigForm N j) hs m hm w
  have hi := i.2
  by_cases hij : (i : ℕ) + 1 ≤ j
  · have h1 : N - j + ((i : ℕ) + 1) ≤ N := by omega
    have h0 : N - j ≤ N := by omega
    have hfun : (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) = fun z =>
        gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) (cellMat N z) +
          (-1) * gramLog (sigForm N j) (N - j) (cellMat N z) := by
      funext z
      delta GlobalTheory.CompanionTheory.Ar.PB.stepPot
      rw [if_pos hij]
      ring
    rw [hfun]
    refine ⟨(G _ h1).add (contDiffAt_const.mul (G _ h0)), ?_⟩
    refine (levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j) (cellMat N z)) (-1) (G _ h1) (G _ h0) w).trans ?_
    rw [Lv _ h1, Lv _ h0, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases p with ⟨⟨a, b⟩, hab⟩
    have hab' : (a : ℕ) < b := hab
    have ha := a.2
    have hb := b.2
    dsimp only
    simp only [hσ]
    split_ifs <;> first | (exfalso; omega) | norm_num | ring
  · have h1 : N - j ≤ N := by omega
    have h2 : (i : ℕ) + 1 - j ≤ N := by omega
    have hN : N ≤ N := le_refl N
    have hfun : (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) = fun z =>
        (gramLog (sigForm N j) N (cellMat N z) + (-1) * gramLog (sigForm N j) (N - j) (cellMat N z)) +
          1 * gramLog (sigForm N j) ((i : ℕ) + 1 - j) (cellMat N z) := by
      funext z
      delta GlobalTheory.CompanionTheory.Ar.PB.stepPot
      rw [if_neg hij]
      ring
    have GA : ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z) +
        (-1) * gramLog (sigForm N j) (N - j) (cellMat N z)) 0 :=
      (G _ hN).add (contDiffAt_const.mul (G _ h1))
    rw [hfun]
    refine ⟨GA.add (contDiffAt_const.mul (G _ h2)), ?_⟩
    refine (levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z) +
        (-1) * gramLog (sigForm N j) (N - j) (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) ((i : ℕ) + 1 - j) (cellMat N z)) 1 GA (G _ h2) w).trans ?_
    rw [levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j) (cellMat N z)) (-1) (G _ hN) (G _ h1) w]
    rw [Lv _ hN, Lv _ h1, Lv _ h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases p with ⟨⟨a, b⟩, hab⟩
    have hab' : (a : ℕ) < b := hab
    have ha := a.2
    have hb := b.2
    dsimp only
    simp only [hσ]
    split_ifs <;> first | (exfalso; omega) | norm_num | ring

end GlobalTheory.CompanionTheory.Ar.PB
