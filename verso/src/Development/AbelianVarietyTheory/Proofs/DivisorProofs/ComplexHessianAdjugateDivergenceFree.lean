import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import ReciprocityTheory.L2DbarEstimates.LeviForms.MacofFderivApplyContDiffOn
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

noncomputable section

namespace GlobalTheory.HessPiola

/- English proof (translation)
Simplify using `only [ReciprocityTheory.L2DbarEstimates.wdb, h.fderiv_eq]`.
-/
theorem wdb_congr {n : ℕ} {f g : V n → ℂ} {y : V n} (h : f =ᶠ[𝓝 y] g) (l : Fin n) :
    ReciprocityTheory.L2DbarEstimates.wdb n l f y = ReciprocityTheory.L2DbarEstimates.wdb n l g y := by
  simp only [ReciprocityTheory.L2DbarEstimates.wdb, h.fderiv_eq]

/- English proof (translation)
Establish `h1 : ContDiffAt ℝ m (fderiv ℝ g) y` using `hg.fderiv_right le_rfl`. Establish `ha : ∀ v, ContDiffAt ℝ m (fun y => fderiv ℝ g y v) y` using `fun v => h1.clm_apply contDiffAt_const`. Establish `: ReciprocityTheory.L2DbarEstimates.wd n j g = fun y => (fderiv ℝ g y (ReciprocityTheory.L2DbarEstimates.bas n j) - Complex.I * fderiv ℝ g y (Complex.I • ReciprocityTheory.L2DbarEstimates.bas n j)) / 2`. Use function extensionality and compare the values at `y`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `((ha _).sub (contDiffAt_const.mul (ha _))).div_const _`.
-/
theorem wd_contDiffAt {n : ℕ} {g : V n → ℂ} {y : V n} {m : WithTop ℕ∞}
    (hg : ContDiffAt ℝ (m + 1) g y) (j : Fin n) :
    ContDiffAt ℝ m (ReciprocityTheory.L2DbarEstimates.wd n j g) y := by
  have h1 : ContDiffAt ℝ m (fderiv ℝ g) y := hg.fderiv_right le_rfl
  have ha : ∀ v, ContDiffAt ℝ m (fun y => fderiv ℝ g y v) y :=
    fun v => h1.clm_apply contDiffAt_const
  have : ReciprocityTheory.L2DbarEstimates.wd n j g = fun y => (fderiv ℝ g y (ReciprocityTheory.L2DbarEstimates.bas n j)
      - Complex.I * fderiv ℝ g y (Complex.I • ReciprocityTheory.L2DbarEstimates.bas n j)) / 2 := by
    funext y; rfl
  rw [this]
  exact ((ha _).sub (contDiffAt_const.mul (ha _))).div_const _

/- English proof (translation)
Establish `h1 : ContDiffAt ℝ m (fderiv ℝ g) y` using `hg.fderiv_right le_rfl`. Establish `ha : ∀ v, ContDiffAt ℝ m (fun y => fderiv ℝ g y v) y` using `fun v => h1.clm_apply contDiffAt_const`. Establish `: ReciprocityTheory.L2DbarEstimates.wdb n j g = fun y => (fderiv ℝ g y (ReciprocityTheory.L2DbarEstimates.bas n j) + Complex.I * fderiv ℝ g y (Complex.I • ReciprocityTheory.L2DbarEstimates.bas n j)) / 2`. Use function extensionality and compare the values at `y`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `((ha _).add (contDiffAt_const.mul (ha _))).div_const _`.
-/
theorem wdb_contDiffAt {n : ℕ} {g : V n → ℂ} {y : V n} {m : WithTop ℕ∞}
    (hg : ContDiffAt ℝ (m + 1) g y) (j : Fin n) :
    ContDiffAt ℝ m (ReciprocityTheory.L2DbarEstimates.wdb n j g) y := by
  have h1 : ContDiffAt ℝ m (fderiv ℝ g) y := hg.fderiv_right le_rfl
  have ha : ∀ v, ContDiffAt ℝ m (fun y => fderiv ℝ g y v) y :=
    fun v => h1.clm_apply contDiffAt_const
  have : ReciprocityTheory.L2DbarEstimates.wdb n j g = fun y => (fderiv ℝ g y (ReciprocityTheory.L2DbarEstimates.bas n j)
      + Complex.I * fderiv ℝ g y (Complex.I • ReciprocityTheory.L2DbarEstimates.bas n j)) / 2 := by
    funext y; rfl
  rw [this]
  exact ((ha _).add (contDiffAt_const.mul (ha _))).div_const _

/- English proof (translation)
Establish `hw : w = ∑ b, w b • (Pi.single b (1 : ℂ) : Fin n → ℂ)`. Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hw]`.

Both sides reduce to the same expression. Use `_ = _ := by simp only [map_sum, map_smul, smul_eq_mul, ReciprocityTheory.L2DbarEstimates.I.macofRow_apply]`.
-/
theorem det_updateRow_expand {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (w : Fin n → ℂ) :
    (M.updateRow i w).det = ∑ b, w b * (M.updateRow i (Pi.single b 1)).det := by
  have hw : w = ∑ b, w b • (Pi.single b (1 : ℂ) : Fin n → ℂ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  calc (M.updateRow i w).det
      = ReciprocityTheory.L2DbarEstimates.I.macofRow M i (∑ b, w b • (Pi.single b (1 : ℂ) : Fin n → ℂ)) := by
        rw [← hw]; rfl
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, ReciprocityTheory.L2DbarEstimates.I.macofRow_apply]

/- English proof (translation)
Use extensionality with `r k`. Simplify using `only [Matrix.updateRow_apply]`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem updateRow_comm' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {i j : Fin n} (h : i ≠ j)
    (e c : Fin n → ℂ) : (M.updateRow i e).updateRow j c = (M.updateRow j c).updateRow i e := by
  ext r k
  simp only [Matrix.updateRow_apply]
  split_ifs <;> simp_all

/- English proof (translation)
Establish `hu3 : ContDiffAt ℝ (2 + 1) u z`. Rewrite using `[show ((2 : WithTop ℕ∞) + 1) = 3 by norm_num]; exact hu`. Establish `hb : ∀ b, ContDiffAt ℝ (1 + 1) (ReciprocityTheory.L2DbarEstimates.wdb D b u) z` using `fun b => by`. Rewrite using `[show ((1 : WithTop ℕ∞) + 1) = 2 by norm_num]; exact wdb_contDiffAt hu3 b`. Establish `hA : ∀ i b, ContDiffAt ℝ 1 (fun x => cHess D u x i b) z` using `fun i b => wd_contDiffAt (hb b) i`.

Establish `hdetC : ∀ (B : V D → Matrix (Fin D) (Fin D) ℂ), (∀ i b, ContDiffAt ℝ 1 (fun x => B x i b) z) → ContDiffAt ℝ 1 (fun x => (B x).det) z`. Introduce `B hB`. Establish `hrow : ContDiffAt ℝ 1 (fun x => (fun i b => B x i b : Fin D → Fin D → ℂ)) z` using `contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun b => hB i b`. Conclude with `(ReciprocityTheory.L2DbarEstimates.I.macofDet D).contDiff.contDiffAt.comp z hrow`. Establish `hBl : ∀ l j i b, ContDiffAt ℝ 1 (fun x => ((cHess D u x).updateRow j (Pi.single l 1)) i b) z`.

Introduce `l j i b`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `only [Matrix.updateRow_self]`. Conclude with `contDiffAt_const`.

Simplify using `only [Matrix.updateRow_ne hij]`. Conclude with `hA i b`. Use `⟨fun l j => ?_, fun j => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.adjugate_apply]`. Conclude with `hdetC _ (hBl l j)`.

Take `⟨c, hc⟩ : ∃ c : Fin D → Fin D → Fin D → ℂ, c = fun l i b => ReciprocityTheory.L2DbarEstimates.wdb D l (fun x => cHess D u x i b) z` from `⟨_, rfl⟩`. Establish `hgerm : ∀ i b, (fun x => cHess D u x i b) =ᶠ[𝓝 z] ReciprocityTheory.L2DbarEstimates.wdb D b (ReciprocityTheory.L2DbarEstimates.wd D i u)`. Introduce `i b`. Use `filter_upwards [hu.eventually (by simp)] with y hy`. Conclude with `ReciprocityTheory.L2DbarEstimates.comm_wd_wdb u y (hy.of_le (by norm_num)) i b`.

Establish `hcs : ∀ l i b, c l i b = c b i l`. Introduce `l i b`. Establish `h2 : ContDiffAt ℝ 2 (ReciprocityTheory.L2DbarEstimates.wd D i u) z` using `wd_contDiffAt hu3 i`. Rewrite using `[hc]`. Simplify using `only`.

Rewrite using `[wdb_congr (hgerm i b), wdb_congr (hgerm i l)]`. Conclude with `ReciprocityTheory.L2DbarEstimates.comm_wdb_wdb _ z h2 l b`. Take `⟨t, ht⟩ : ∃ t : Fin D → Fin D → ℂ, t = fun l i => (((cHess D u z).updateRow j (Pi.single l 1)).updateRow i (if i = j then 0 else c l i)).det` from `⟨_, rfl⟩`. Establish `hterm : ∀ l, dbar (fun x => (cHess D u x).adjugate l j) z (EuclideanSpace.single l 1) = ∑ i, t l i`. Introduce `l`.

Set `B : V D → Matrix (Fin D) (Fin D) ℂ` to `fun w => (cHess D u w).updateRow j (Pi.single l 1)`. Set `B' : Fin D → Fin D → (V D →L[ℝ] ℂ)` to `fun i b => if i = j then 0 else fderiv ℝ (fun x => cHess D u x i b) z`. Establish `hB : ∀ i b, HasFDerivAt (fun w => B w i b) (B' i b) z`. Introduce `i b`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `only [B, B', Matrix.updateRow_self, if_true]`. Conclude with `hasFDerivAt_const _ _`. Simplify using `only [B, B', Matrix.updateRow_ne hij, if_neg hij]`. Conclude with `((hA i b).differentiableAt (by simp)).hasFDerivAt`.

Establish `hfun : (fun w => (cHess D u w).adjugate l j) = fun w => (B w).det`. Use function extensionality and compare the values at `w`. Simplify using `only [B, Matrix.adjugate_apply]`. Establish `key : ∀ i, (1 / 2 : ℂ) • (((B z).updateRow i (fun b => B' i b (EuclideanSpace.single l 1))).det + Complex.I • ((B z).updateRow i (fun b => B' i b (Complex.I • EuclideanSpace.single l 1))).det) = t l i`. Introduce `i`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_smul, map_add, map_smul]`. Simplify using `only [ReciprocityTheory.L2DbarEstimates.I.macofRow_apply]`. Use `_ = t l i := by`. Rewrite using `[ht]`.

Use `show ReciprocityTheory.L2DbarEstimates.I.macofRow (B z) i _ = ReciprocityTheory.L2DbarEstimates.I.macofRow (B z) i _`. Use `congr 1`. Use function extensionality and compare the values at `b`. Distinguish the cases in `hij : i = j`. Simplify using `[B', hij]`.

Simplify using `only [B', hij, if_false, hc, ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.bas, Pi.smul_apply, Pi.add_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun, dbar_apply, ReciprocityTheory.L2DbarEstimates.I.macof_hasFDerivAt_det B z B' hB, ReciprocityTheory.L2DbarEstimates.I.macof_hasFDerivAt_det B z B' hB, Finset.smul_sum, ← Finset.sum_add_distrib, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => key i`. Rewrite using `[Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Rewrite using `[ht]`.

Simplify using `only [if_true]`. Establish `h0 : ReciprocityTheory.L2DbarEstimates.I.macofRow ((cHess D u z).updateRow i (Pi.single l 1)) i 0 = 0` using `map_zero _`. Rewrite `h0` using `[ReciprocityTheory.L2DbarEstimates.I.macofRow_apply]`. Then use the resulting hypothesis. Take `⟨d, hd⟩ : ∃ d : Fin D → Fin D → ℂ, d = fun l b => (((cHess D u z).updateRow j (Pi.single l 1)).updateRow i (Pi.single b 1)).det` from `⟨_, rfl⟩`. Establish `hexp : ∀ l, t l i = ∑ b, c l i b * d l b`.

Introduce `l`. Rewrite using `[ht, hd]`. Simplify using `only [if_neg hij]`. Conclude with `det_updateRow_expand _ i _`. Establish `hanti : ∀ l b, d b l = - d l b`.

Introduce `l b`. Rewrite using `[hd]`. Simplify using `only`. Rewrite using `[← updateRow_comm' _ hij]`. Conclude with `ReciprocityTheory.L2DbarEstimates.I.macof_swap _ hij _ _`.

Simplify using `only [hexp]`. Establish `hS : ∑ l, ∑ b, c l i b * d l b = -(∑ l, ∑ b, c l i b * d l b)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_comm]`. Simplify using `[Finset.sum_neg_distrib]`.

Take the linear combination `hS / 2`.
-/
theorem cHess_adjugate_piola (D : ℕ) (u : V D → ℂ) (z : V D) (hu : ContDiffAt ℝ 3 u z) :
    (∀ l j : Fin D, ContDiffAt ℝ 1 (fun x => (cHess D u x).adjugate l j) z) ∧
      ∀ j : Fin D, ∑ l, dbar (fun x => (cHess D u x).adjugate l j) z
        (EuclideanSpace.single l 1) = 0 := by
  have hu3 : ContDiffAt ℝ (2 + 1) u z := by
    rw [show ((2 : WithTop ℕ∞) + 1) = 3 by norm_num]; exact hu
  have hb : ∀ b, ContDiffAt ℝ (1 + 1) (ReciprocityTheory.L2DbarEstimates.wdb D b u) z := fun b => by
    rw [show ((1 : WithTop ℕ∞) + 1) = 2 by norm_num]; exact wdb_contDiffAt hu3 b
  have hA : ∀ i b, ContDiffAt ℝ 1 (fun x => cHess D u x i b) z :=
    fun i b => wd_contDiffAt (hb b) i
  have hdetC : ∀ (B : V D → Matrix (Fin D) (Fin D) ℂ),
      (∀ i b, ContDiffAt ℝ 1 (fun x => B x i b) z) →
      ContDiffAt ℝ 1 (fun x => (B x).det) z := by
    intro B hB
    have hrow : ContDiffAt ℝ 1 (fun x => (fun i b => B x i b : Fin D → Fin D → ℂ)) z :=
      contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun b => hB i b
    exact (ReciprocityTheory.L2DbarEstimates.I.macofDet D).contDiff.contDiffAt.comp z hrow
  have hBl : ∀ l j i b, ContDiffAt ℝ 1
      (fun x => ((cHess D u x).updateRow j (Pi.single l 1)) i b) z := by
    intro l j i b
    by_cases hij : i = j
    · subst hij; simp only [Matrix.updateRow_self]; exact contDiffAt_const
    · simp only [Matrix.updateRow_ne hij]; exact hA i b
  refine ⟨fun l j => ?_, fun j => ?_⟩
  · simp only [Matrix.adjugate_apply]; exact hdetC _ (hBl l j)

  obtain ⟨c, hc⟩ : ∃ c : Fin D → Fin D → Fin D → ℂ,
      c = fun l i b => ReciprocityTheory.L2DbarEstimates.wdb D l (fun x => cHess D u x i b) z := ⟨_, rfl⟩

  have hgerm : ∀ i b, (fun x => cHess D u x i b) =ᶠ[𝓝 z]
      ReciprocityTheory.L2DbarEstimates.wdb D b (ReciprocityTheory.L2DbarEstimates.wd D i u) := by
    intro i b
    filter_upwards [hu.eventually (by simp)] with y hy
    exact ReciprocityTheory.L2DbarEstimates.comm_wd_wdb u y (hy.of_le (by norm_num)) i b
  have hcs : ∀ l i b, c l i b = c b i l := by
    intro l i b
    have h2 : ContDiffAt ℝ 2 (ReciprocityTheory.L2DbarEstimates.wd D i u) z := wd_contDiffAt hu3 i
    rw [hc]
    dsimp only
    rw [wdb_congr (hgerm i b), wdb_congr (hgerm i l)]
    exact ReciprocityTheory.L2DbarEstimates.comm_wdb_wdb _ z h2 l b
  obtain ⟨t, ht⟩ : ∃ t : Fin D → Fin D → ℂ, t = fun l i =>
      (((cHess D u z).updateRow j (Pi.single l 1)).updateRow i
        (if i = j then 0 else c l i)).det := ⟨_, rfl⟩
  have hterm : ∀ l, dbar (fun x => (cHess D u x).adjugate l j) z (EuclideanSpace.single l 1)
      = ∑ i, t l i := by
    intro l
    let B : V D → Matrix (Fin D) (Fin D) ℂ := fun w => (cHess D u w).updateRow j (Pi.single l 1)
    let B' : Fin D → Fin D → (V D →L[ℝ] ℂ) := fun i b =>
      if i = j then 0 else fderiv ℝ (fun x => cHess D u x i b) z
    have hB : ∀ i b, HasFDerivAt (fun w => B w i b) (B' i b) z := by
      intro i b
      by_cases hij : i = j
      · subst hij
        simp only [B, B', Matrix.updateRow_self, if_true]
        exact hasFDerivAt_const _ _
      · simp only [B, B', Matrix.updateRow_ne hij, if_neg hij]
        exact ((hA i b).differentiableAt (by simp)).hasFDerivAt
    have hfun : (fun w => (cHess D u w).adjugate l j) = fun w => (B w).det := by
      funext w; simp only [B, Matrix.adjugate_apply]
    have key : ∀ i, (1 / 2 : ℂ) • (((B z).updateRow i
          (fun b => B' i b (EuclideanSpace.single l 1))).det
        + Complex.I • ((B z).updateRow i
          (fun b => B' i b (Complex.I • EuclideanSpace.single l 1))).det) = t l i := by
      intro i
      calc _ = ReciprocityTheory.L2DbarEstimates.I.macofRow (B z) i ((1 / 2 : ℂ) •
            ((fun b => B' i b (EuclideanSpace.single l 1))
              + Complex.I • (fun b => B' i b (Complex.I • EuclideanSpace.single l 1)))) := by
            rw [map_smul, map_add, map_smul]
            simp only [ReciprocityTheory.L2DbarEstimates.I.macofRow_apply]
        _ = t l i := by
            rw [ht]
            show ReciprocityTheory.L2DbarEstimates.I.macofRow (B z) i _ = ReciprocityTheory.L2DbarEstimates.I.macofRow (B z) i _
            congr 1
            funext b
            by_cases hij : i = j
            · simp [B', hij]
            · simp only [B', hij, if_false, hc, ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.bas,
                Pi.smul_apply, Pi.add_apply, smul_eq_mul]
              ring
    rw [hfun, dbar_apply, ReciprocityTheory.L2DbarEstimates.I.macof_hasFDerivAt_det B z B' hB,
      ReciprocityTheory.L2DbarEstimates.I.macof_hasFDerivAt_det B z B' hB, Finset.smul_sum,
      ← Finset.sum_add_distrib, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => key i
  rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hij : i = j
  · subst hij
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [ht]
    simp only [if_true]
    have h0 : ReciprocityTheory.L2DbarEstimates.I.macofRow ((cHess D u z).updateRow i (Pi.single l 1)) i 0 = 0 :=
      map_zero _
    rwa [ReciprocityTheory.L2DbarEstimates.I.macofRow_apply] at h0
  · obtain ⟨d, hd⟩ : ∃ d : Fin D → Fin D → ℂ, d = fun l b =>
        (((cHess D u z).updateRow j (Pi.single l 1)).updateRow i (Pi.single b 1)).det :=
      ⟨_, rfl⟩
    have hexp : ∀ l, t l i = ∑ b, c l i b * d l b := by
      intro l
      rw [ht, hd]
      simp only [if_neg hij]
      exact det_updateRow_expand _ i _
    have hanti : ∀ l b, d b l = - d l b := by
      intro l b
      rw [hd]
      dsimp only
      rw [← updateRow_comm' _ hij]
      exact ReciprocityTheory.L2DbarEstimates.I.macof_swap _ hij _ _
    simp only [hexp]
    have hS : ∑ l, ∑ b, c l i b * d l b = -(∑ l, ∑ b, c l i b * d l b) := by
      calc ∑ l, ∑ b, c l i b * d l b = ∑ b, ∑ l, c b i l * d b l := rfl
        _ = ∑ b, ∑ l, -(c l i b * d l b) := Finset.sum_congr rfl fun b _ =>
              Finset.sum_congr rfl fun l _ => by rw [hcs b i l, hanti l b]; ring
        _ = -(∑ l, ∑ b, c l i b * d l b) := by
              rw [Finset.sum_comm]; simp [Finset.sum_neg_distrib]
    linear_combination hS / 2

end GlobalTheory.HessPiola
