import Formalism.LocalToGlobal.AlgebraicTheory.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.JetsLin
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThetaAdditiveHomogeneousHomothety
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz

noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.G (linSub JetsIn JetsIn1)
open Formalism.DworkPowerSeriesWeights (JetsIntegral mfact)
open Formalism.InvariantFactorPaths.G7 (at1)

namespace LinearSubstitutionJets

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single x]`. Simplify using `[scl]`. Introduce `y _ hy`. Simplify using `[scl, Ne.symm hy]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ x) h`.
-/
private theorem sum_C_scl_mul_X {K : Type} [Field K] {p : Type} [Fintype p] [DecidableEq p] (c : K)
    (x : p) :
    (∑ y, MvPowerSeries.C (scl p c x y) * MvPowerSeries.X y : MvPowerSeries p K) =
      MvPowerSeries.C c * MvPowerSeries.X x := by
  rw [Finset.sum_eq_single x]
  · simp [scl]
  · intro y _ hy
    simp [scl, Ne.symm hy]
  · intro h
    exact absurd (Finset.mem_univ x) h

/- English proof (translation)
Unfold `linSub`. Rewrite using `[MvPowerSeries.rescale_eq_subst]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[sum_C_scl_mul_X]`.

Simplify using `[MvPowerSeries.smul_eq_C_mul]`.
-/
theorem linSub_scl {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] (c : K)
    (f : MvPowerSeries n K) :
    linSub (scl n c) f = MvPowerSeries.rescale (fun _ => c) f := by
  unfold linSub
  rw [MvPowerSeries.rescale_eq_subst]
  congr 1
  funext i
  rw [sum_C_scl_mul_X]
  simp [MvPowerSeries.smul_eq_C_mul]

end LinearSubstitutionJets

open LinearSubstitutionJets

/- English proof (translation)
Introduce `K _ _ κ n _ _ _ c r H hr hH`. Establish `hB : ∀ a : K, a ∈ Formalism.G.unitBall K ↔ ‖a‖ ≤ 1` using `fun a => Iff.rfl`. Use `(Formalism.L2.Th1.G.jetsInNorm K n _).mpr ?_` and prove the remaining obligations. Rewrite using `[linSub_scl]`. Take `⟨hC, -, hadd, -, hmul⟩` from `Formalism.L2.Th1.G.jetsRing K (Formalism.G.unitBall K) n`.

Establish `hfac : ∀ k i, JetsIn (Formalism.G.unitBall K) (MvPowerSeries.rescale (fun _ => c) (at1 i (H k i) : MvPowerSeries n K))`. Introduce `k i κ'`. Rewrite using `[MvPowerSeries.coeff_rescale]`. Unfold `at1`. Rewrite using `[PowerSeries.coeff_subst_single, hB]`.

Use `split_ifs with h`. Establish `hm : mfact κ' = (κ' i).factorial` using `by conv_lhs => rw [h]`. Rewrite using `[mfact, Finsupp.prod_single_index (by simp)]`. Establish `hp : (κ'.prod fun _ m => c ^ m) = c ^ (κ' i)` using `by conv_lhs => rw [h]`. Rewrite using `[Finsupp.prod_single_index (by simp)]`.

Rewrite using `[hm, hp]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, norm_mul, norm_mul, norm_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 1 := hH k i (κ' i)`.

Simplify using the standard rewrite rules. Establish `hCr : ∀ k, JetsIn (Formalism.G.unitBall K) (MvPowerSeries.rescale (fun _ => c) (MvPowerSeries.C (r k) : MvPowerSeries n K))`. Introduce `k`. Establish `hres : MvPowerSeries.rescale (fun _ => c) (MvPowerSeries.C (r k) : MvPowerSeries n K) = MvPowerSeries.C (r k)`. Use extensionality with `κ'`.

Rewrite using `[MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[mul_zero]`.

Rewrite using `[hres]`. Conclude with `hC _ ((hB _).mpr (hr k))`. Unfold `Formalism.L2.Th1.E.thetaProd`. Rewrite using `[map_sum]`. Use `Finset.sum_induction _ (JetsIn (Formalism.G.unitBall K)) (fun f g hf hg => hadd f g hf hg) ?_ ?_` and prove the remaining obligations.

Simplify using `using hC 0 (Formalism.G.unitBall K).zero_mem`. Introduce `k _`. Rewrite using `[map_mul, map_prod]`. Conclude with `hmul _ _ (hCr k) (Formalism.L2.Th1.G.HurwitzJetIntegrality.jetsIn_prod Formalism.L2.Th1.G.jetsRing _ _ _ fun i _ => hfac k i)`.
-/
theorem product_scaling_jets : ProdScaleJets := by
  intro K _ _ κ n _ _ _ c r H hr hH
  classical
  have hB : ∀ a : K, a ∈ Formalism.G.unitBall K ↔ ‖a‖ ≤ 1 := fun a => Iff.rfl
  refine (Formalism.L2.Th1.G.jetsInNorm K n _).mpr ?_
  rw [linSub_scl]
  obtain ⟨hC, -, hadd, -, hmul⟩ := Formalism.L2.Th1.G.jetsRing K (Formalism.G.unitBall K) n

  have hfac : ∀ k i, JetsIn (Formalism.G.unitBall K)
      (MvPowerSeries.rescale (fun _ => c) (at1 i (H k i) : MvPowerSeries n K)) := by
    intro k i κ'
    rw [MvPowerSeries.coeff_rescale]
    unfold at1
    rw [PowerSeries.coeff_subst_single, hB]
    split_ifs with h
    · have hm : mfact κ' = (κ' i).factorial := by
        conv_lhs => rw [h]
        rw [mfact, Finsupp.prod_single_index (by simp)]
      have hp : (κ'.prod fun _ m => c ^ m) = c ^ (κ' i) := by
        conv_lhs => rw [h]
        rw [Finsupp.prod_single_index (by simp)]
      rw [hm, hp]
      calc ‖((κ' i).factorial : K) * (c ^ κ' i * PowerSeries.coeff (κ' i) (H k i))‖
          = ‖((κ' i).factorial : K) * PowerSeries.coeff (κ' i) (H k i)‖ * ‖c‖ ^ κ' i := by
            rw [norm_mul, norm_mul, norm_mul, norm_pow]
            ring
        _ ≤ 1 := hH k i (κ' i)
    · simp
  have hCr : ∀ k, JetsIn (Formalism.G.unitBall K)
      (MvPowerSeries.rescale (fun _ => c) (MvPowerSeries.C (r k) : MvPowerSeries n K)) := by
    intro k
    have hres : MvPowerSeries.rescale (fun _ => c) (MvPowerSeries.C (r k) : MvPowerSeries n K) =
        MvPowerSeries.C (r k) := by
      ext κ'
      rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C]
      split_ifs with h
      · subst h
        simp
      · rw [mul_zero]
    rw [hres]
    exact hC _ ((hB _).mpr (hr k))
  unfold Formalism.L2.Th1.E.thetaProd
  rw [map_sum]
  refine Finset.sum_induction _ (JetsIn (Formalism.G.unitBall K)) (fun f g hf hg => hadd f g hf hg) ?_ ?_
  · simpa using hC 0 (Formalism.G.unitBall K).zero_mem
  · intro k _
    rw [map_mul, map_prod]
    exact hmul _ _ (hCr k)
      (Formalism.L2.Th1.G.HurwitzJetIntegrality.jetsIn_prod Formalism.L2.Th1.G.jetsRing _ _ _ fun i _ => hfac k i)

/- English proof (translation)
Introduce `K _ n m _ _ _ _ c A f`. Establish `hS : ∀ {p q : Type} [Fintype p] [Fintype q] (B : p → q → K), MvPowerSeries.HasSubst (fun i => (∑ x, MvPowerSeries.C (B i x) * MvPowerSeries.X x : MvPowerSeries q K))`. Introduce `p q _ _ B`. Conclude with `Formalism.L2.Th1.G.hasSubst_lin B`. Prove the components needed by the constructor for the conclusion.

Unfold `linSub`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply (hS A) (hS (scl m c))]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Use `show linSub (scl m c) (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x) = _`.

Rewrite using `[← Formalism.L2.Th1.G.linSubHom_apply, map_sum]`. Use `Finset.sum_congr rfl (fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSub_C, Formalism.L2.Th1.G.linSub_X, sum_C_scl_mul_X, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Unfold `linSub`.

Rewrite using `[MvPowerSeries.subst_comp_subst_apply (hS (scl n c)) (hS A)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[sum_C_scl_mul_X]`. Use `show linSub A (MvPowerSeries.C c * MvPowerSeries.X i) = _`.

Rewrite using `[← Formalism.L2.Th1.G.linSubHom_apply, map_mul, Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSub_C, Formalism.L2.Th1.G.linSub_X, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem linear_scaling_jets : LinScale := by
  intro K _ n m _ _ _ _ c A f
  have hS : ∀ {p q : Type} [Fintype p] [Fintype q] (B : p → q → K),
      MvPowerSeries.HasSubst
        (fun i => (∑ x, MvPowerSeries.C (B i x) * MvPowerSeries.X x : MvPowerSeries q K)) := by
    intro p q _ _ B
    exact Formalism.L2.Th1.G.hasSubst_lin B
  constructor
  · unfold linSub
    rw [MvPowerSeries.subst_comp_subst_apply (hS A) (hS (scl m c))]
    congr 1
    funext i
    show linSub (scl m c) (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x) = _
    rw [← Formalism.L2.Th1.G.linSubHom_apply, map_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [map_mul, Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSubHom_apply,
      Formalism.L2.Th1.G.linSub_C, Formalism.L2.Th1.G.linSub_X, sum_C_scl_mul_X, map_mul]
    ring
  · unfold linSub
    rw [MvPowerSeries.subst_comp_subst_apply (hS (scl n c)) (hS A)]
    congr 1
    funext i
    rw [sum_C_scl_mul_X]
    show linSub A (MvPowerSeries.C c * MvPowerSeries.X i) = _
    rw [← Formalism.L2.Th1.G.linSubHom_apply, map_mul, Formalism.L2.Th1.G.linSubHom_apply,
      Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSub_C, Formalism.L2.Th1.G.linSub_X, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [map_mul]
    ring

end Formalism.L2.AlgTh
