import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergySymm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartIbpSymm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergySwap
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergySymmetry

/- English proof (translation)
Establish `h1 : fderiv ℝ (fun y' => f y' - g y') = fun z => fderiv ℝ f z - fderiv ℝ g z`. Use function extensionality and compare the values at `z`. Conclude with `fderiv_sub (hf.differentiable (by norm_num) z) (hg.differentiable (by norm_num) z)`. Establish `hf' : Differentiable ℝ (fderiv ℝ f)` using `(hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)`. Establish `hg' : Differentiable ℝ (fderiv ℝ g)` using `(hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)`.

Establish `h2 : fderiv ℝ (fderiv ℝ (fun y' => f y' - g y')) y = fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ g) y`. Rewrite using `[h1]`. Conclude with `fderiv_sub (hf' y) (hg' y)`. Use extensionality with `i j`. Simplify using `only [cxHessian, h2, _root_.sub_apply, Matrix.sub_apply]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cxHessian_sub {D : ℕ} {f g : (Fin D → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (y : Fin D → ℂ) : cxHessian (fun y' => f y' - g y') y = cxHessian f y - cxHessian g y := by
  have h1 : fderiv ℝ (fun y' => f y' - g y') = fun z => fderiv ℝ f z - fderiv ℝ g z := by
    funext z
    exact fderiv_sub (hf.differentiable (by norm_num) z) (hg.differentiable (by norm_num) z)
  have hf' : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg' : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun y' => f y' - g y')) y =
      fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ g) y := by
    rw [h1]
    exact fderiv_sub (hf' y) (hg' y)
  ext i j
  simp only [cxHessian, h2, _root_.sub_apply, Matrix.sub_apply]
  push_cast
  ring

/- English proof (translation)
Take `⟨M, hM⟩` from `ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)`. Establish `e : ∀ C, mixedDisc (Function.update A k C) = M.toLinearMap A k C` using `fun C => by`. Rewrite using `[MultilinearMap.toLinearMap_apply, hM]`. Both sides reduce to the same expression. Simplify using `only [e, map_sub]`.
-/
theorem mixedDisc_update_sub {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (Function.update A k (X - Y)) =
      mixedDisc (Function.update A k X) - mixedDisc (Function.update A k Y) := by
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  have e : ∀ C, mixedDisc (Function.update A k C) = M.toLinearMap A k C := fun C => by
    rw [MultilinearMap.toLinearMap_apply, hM]
    rfl
  simp only [e, map_sub]

/- English proof (translation)
Establish `key : ∀ h : (Fin D → ℂ) → ℝ, (fun k => cxHessian (Function.update Φ p h k) y) = Function.update (fun k => cxHessian (Φ k) y) p (cxHessian h y)` using `fun h => by`. Use function extensionality and compare the values at `k`. Conclude with `Function.apply_update (fun _ h' => cxHessian h' y) Φ p h k`. Simplify using `only [maDensity, key, cxHessian_sub hf hg y, mixedDisc_update_sub, Complex.sub_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maDensity_update_sub {D : ℕ} (Φ : Fin D → (Fin D → ℂ) → ℝ) (p : Fin D) {f g : (Fin D → ℂ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (y : Fin D → ℂ) :
    maDensity (Function.update Φ p f) y - maDensity (Function.update Φ p g) y =
      maDensity (Function.update Φ p fun y' => f y' - g y') y := by
  have key : ∀ h : (Fin D → ℂ) → ℝ, (fun k => cxHessian (Function.update Φ p h k) y) =
      Function.update (fun k => cxHessian (Φ k) y) p (cxHessian h y) := fun h => by
    funext k
    exact Function.apply_update (fun _ h' => cxHessian h' y) Φ p h k
  simp only [maDensity, key, cxHessian_sub hf hg y, mixedDisc_update_sub, Complex.sub_re]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `only [Function.comp_apply, Fin.cons_succ]`. Rewrite using `[Function.update_of_ne]`.

Introduce `h`. Establish `h'` using `congrArg (Equiv.swap 0 p) h`. Rewrite `h'` using `[Equiv.swap_apply_self, Equiv.swap_apply_right]`. Conclude with `Fin.succ_ne_zero i h'`.
-/
theorem update_comp_swap {α : Type*} {n : ℕ} (Φ : Fin (n + 1) → α) (p : Fin (n + 1)) (f : α) :
    Function.update Φ p f ∘ Equiv.swap 0 p = Fin.cons f (fun i => Φ (Equiv.swap 0 p i.succ)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp only [Function.comp_apply, Fin.cons_succ]
    rw [Function.update_of_ne]
    intro h
    have h' := congrArg (Equiv.swap 0 p) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h'
    exact Fin.succ_ne_zero i h'

end ChartEnergySymmetry

open ChartEnergySymmetry in

/- English proof (translation)
Introduce `e A B C D T p hA hB hC hD hT`. Take `⟨n, rfl⟩ : ∃ n, e = n + 1` from `⟨e - 1, by have := p.pos; omega⟩`. Use `set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p with hσ`. Use `set T' : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ := fun i => T (σ i.succ) with hT'def`. Establish `hT' : ∀ i, (T' i).PosDef` using `fun i => hT _`.

Establish `hpot : ∀ X, (fun j => hermChartPot (Function.update T p X j)) = Function.update (fun j => hermChartPot (T j)) p (hermChartPot X)` using `fun X => by`. Use function extensionality and compare the values at `j`. Conclude with `Function.apply_update (fun _ M => hermChartPot M) T p X j`. Establish `hdiff : ∀ X Y : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ, X.PosDef → Y.PosDef → ∀ y, maDensity (fun j => hermChartPot (Function.update T p X j)) y - maDensity (fun j => hermChartPot (Function.update T p Y j)) y = maDensity (Fin.cons (fun y' => hermChartPot X y' - hermChartPot …`. Introduce `X Y hX hY y`.

Rewrite using `[hpot, hpot, maDensity_update_sub _ _ (ChartEnergySwapHessian.contDiff_hermChartPot X hX) (ChartEnergySwapHessian.contDiff_hermChartPot Y hY), ← Inter.maDensity_comp_perm _ σ, update_comp_swap]`. Repeatedly rewrite using `[hdiff C D hC hD, hdiff A B hA hB]`. Conclude with `hI n A B C D T' hA hB hC hD hT'`.
-/
theorem ChartEnergySymm.proof (hI : ChartIbpSymm.Statement) : ChartEnergySymm.Statement := by
  intro e A B C D T p hA hB hC hD hT
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by have := p.pos; omega⟩
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p with hσ
  set T' : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ := fun i => T (σ i.succ) with hT'def
  have hT' : ∀ i, (T' i).PosDef := fun i => hT _
  have hpot : ∀ X, (fun j => hermChartPot (Function.update T p X j)) =
      Function.update (fun j => hermChartPot (T j)) p (hermChartPot X) := fun X => by
    funext j
    exact Function.apply_update (fun _ M => hermChartPot M) T p X j
  have hdiff : ∀ X Y : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ, X.PosDef → Y.PosDef → ∀ y,
      maDensity (fun j => hermChartPot (Function.update T p X j)) y -
          maDensity (fun j => hermChartPot (Function.update T p Y j)) y =
        maDensity (Fin.cons (fun y' => hermChartPot X y' - hermChartPot Y y')
          fun i => hermChartPot (T' i)) y := by
    intro X Y hX hY y
    rw [hpot, hpot, maDensity_update_sub _ _ (ChartEnergySwapHessian.contDiff_hermChartPot X hX)
      (ChartEnergySwapHessian.contDiff_hermChartPot Y hY), ← Inter.maDensity_comp_perm _ σ, update_comp_swap]
  simp_rw [hdiff C D hC hD, hdiff A B hA hB]
  exact hI n A B C D T' hA hB hC hD hT'

end

end GroundTheory.Heights₂.Heights
