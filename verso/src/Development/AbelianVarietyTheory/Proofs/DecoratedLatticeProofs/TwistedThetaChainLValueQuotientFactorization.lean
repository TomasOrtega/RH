import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLValuesNonvanishing

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw

/- English proof (translation)
Introduce `D c hc B hB k hk`. Use `set T := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) with hT`. Establish `hrt : D.R.r + 5 ≤ D.R.t` using `D.R.rank_add_five_le`. Establish `hrt' : (D.R.r : ℝ) + 5 ≤ D.R.t` using `by exact_mod_cast hrt`. Establish `hΛ : ∀ i : ℕ, ∃ Λ : ℂ → ℂ, i ∈ Finset.Icc 1 k → Differentiable ℂ Λ ∧ (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd T (fun w => {GlobalTheory.LFun.val (F` using `D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) w}) z) ∧ ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := by`.

Introduce `i`. Distinguish the cases in `hi : i ∈ Finset.Icc 1 k`. Establish `h1` using `(Finset.mem_Icc.1 hi).1`. Establish `h2` using `(Finset.mem_Icc.1 hi).2`. Take `⟨Λ, h⟩` from `GlobalTheory.T.thetaChain_char_quotient_LFunction_entire_ne_zero D c hc i (k + 1) h1 (by omega) (by omega)`.

Conclude with `⟨Λ, fun _ => h⟩`. Conclude with `⟨0, fun h => absurd h hi⟩`. Use `choose Λ hΛ using hΛ`. Use `set A := GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ with hA`. Establish `hAb : GlobalTheory.LFun.Bounded T A D.R.r ((D.R.r : ℝ) / 2)` using `hB.twist fun w _ => by simp [GlobalTheory.LFun.norm_val]`.

Set `z : ℕ → HeightOneSpectrum (𝓞 D.host.E) → ℂˣ` to `fun i => GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)`. Establish `hzc : ∀ i, ∀ y : ℂ, 1 < y.re → GlobalTheory.LFun.Converges T (fun w => {z i w}) y` using `fun i y hy => (GlobalTheory.ChainOnto.bounded_single T (z i) fun w => GlobalTheory.LFun.norm_val _ _).converges (by simpa using hy)`. Set `G : ℂ → ℂ` to `fun x => GlobalTheory.LFun.eulerProd T A (x + 1 / 2) * ∏ i ∈ Finset.Icc 1 k, ∏ l ∈ Finset.range D.R.t, Λ i (x + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l)`. Establish `hEq : ∀ x : ℂ, ((D.R.r : ℝ) + D.R.t + 2) < x.re → G x = GlobalTheory.LFun.LSD D c.S (chainPar c B k) (c.chT (k + 1)) (x + 1 / 2)`. Introduce `x hx`.

Establish `hre : ∀ l : ℕ, l < D.R.t → 1 < (x + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l).re`. Introduce `l hl`. Establish `: (l : ℝ) + 1 ≤ D.R.t` using `by exact_mod_cast hl`. Establish `hr0 : (0 : ℝ) ≤ D.R.r` using `Nat.cast_nonneg _`. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion. Use `show _ = GlobalTheory.LFun.eulerProd T (GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹) (x + 1 / 2)`. Rewrite using `[GlobalTheory.T.thetaLiftChainHeckeParameter_twist_next_target_char D c B k, ← hA, GlobalTheory.ChainOnto.eulerProd_add_segFam T A (Finset.Icc 1 k) z D.R.t (x + 1 / 2) (hAb.converges (by have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _; simp; linarith)) (fun i _ l hl => hzc i _ (h …`. Use `congrArg (GlobalTheory.LFun.eulerProd T A (x + 1 / 2) * ·) (Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun l hl => ?_)` and prove the remaining obligations. Conclude with `(hΛ i hi).2.1 _ (hre l (Finset.mem_range.1 hl))`.

Establish `hU : IsOpen (GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2))` using `GlobalTheory.Cont.isOpen_rightOf _`. Establish `hD : DifferentiableOn ℂ G (GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2))`. Use `DifferentiableOn.mul ?_ (Differentiable.differentiableOn ?_)` and prove the remaining obligations. Use `hAb.differentiableOn.comp (differentiableOn_id.add_const _) fun x hx => ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.Cont.mem_rightOf] at hx`.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Differentiable.fun_finsetProd fun i hi => Differentiable.fun_finsetProd fun l _ => (hΛ i hi).1.comp (by fun_prop)`. Establish `hAn` using `hD.analyticOnNhd hU`. Establish `hmem : ((D.R.t : ℂ) / 2) ∈ GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2)`.

Simplify using `only [GlobalTheory.Cont.mem_rightOf]`. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA0 : GlobalTheory.LFun.Converges T A ((1 + (D.R.t : ℂ)) / 2)`. Use `hAb.converges ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLS : GlobalTheory.LFun.LSD D c.S B (c.μ (k + 1)) ((1 + (D.R.t : ℂ)) / 2) = GlobalTheory.LFun.eulerProd T A ((1 + (D.R.t : ℂ)) / 2)` using `rfl`. Establish `hreidx : ∀ i, ∏ l ∈ Finset.range D.R.t, Λ i ((D.R.t : ℂ) / 2 + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l) = ∏ n ∈ Finset.Icc 1 D.R.t, Λ i n`. Introduce `i`.

Use `Finset.prod_nbij' (fun l => D.R.t - l) (fun n => D.R.t - n) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `l hl`. Simplify using `only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hl ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `n hn`.

Simplify using `only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hn ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `l hl`. Simplify using `only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hl`. Use linear arithmetic over natural numbers and integers.

Introduce `n hn`. Simplify using `only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hn`. Use linear arithmetic over natural numbers and integers. Introduce `l hl`. Establish `hl'` using `Finset.mem_range.1 hl`.

Use `congr 1`. Rewrite using `[Nat.cast_sub hl'.le]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 D.R.t, Λ i n, ?_, ⟨Λ, fun i hi => ⟨(hΛ i hi).1, (hΛ i hi).2.1⟩, rfl⟩, hA0, ?_, ?_⟩` and prove the remaining obligations. Use `Finset.prod_ne_zero_iff.2 fun i hi => Finset.prod_ne_zero_iff.2 fun n hn => ?_` and prove the remaining obligations.

Establish `hn'` using `Finset.mem_Icc.1 hn`. Conclude with `(hΛ i hi).2.2 n hn'.1 hn'.2`. Rewrite using `[hLS]`. Conclude with `hA0.ne_zero`. Use `⟨G, ⟨_, hmem, GlobalTheory.Cont.isRightDomain_rightOf _, hAn.meromorphicOn, (D.R.r : ℝ) + D.R.t + 2, fun x hx => hEq x hx⟩, hAn _ hmem, ?_⟩ show GlobalTheory.LFun.eulerProd T A ((D.R.t : ℂ) / 2 + 1 / 2) * ∏ i ∈ Finset.Icc 1 k, ∏ l ∈ Finset.range D.R.t, Λ i ((D.R.t : ℂ) / 2 + 1 / …` and prove the remaining obligations.

Rewrite using `[hLS, Finset.prod_congr rfl fun i _ => hreidx i]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lFull_holds : ∀ D : D7, LFull D := by
  intro D c hc B hB k hk
  set T := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) with hT
  have hrt : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hrt' : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast hrt
  have hΛ : ∀ i : ℕ, ∃ Λ : ℂ → ℂ, i ∈ Finset.Icc 1 k → Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd T
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := by
    intro i
    by_cases hi : i ∈ Finset.Icc 1 k
    · have h1 := (Finset.mem_Icc.1 hi).1
      have h2 := (Finset.mem_Icc.1 hi).2
      obtain ⟨Λ, h⟩ := GlobalTheory.T.thetaChain_char_quotient_LFunction_entire_ne_zero D c hc i (k + 1) h1 (by omega) (by omega)
      exact ⟨Λ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose Λ hΛ using hΛ
  set A := GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ with hA
  have hAb : GlobalTheory.LFun.Bounded T A D.R.r ((D.R.r : ℝ) / 2) :=
    hB.twist fun w _ => by simp [GlobalTheory.LFun.norm_val]
  let z : ℕ → HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := fun i => GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)
  have hzc : ∀ i, ∀ y : ℂ, 1 < y.re → GlobalTheory.LFun.Converges T (fun w => {z i w}) y := fun i y hy =>
    (GlobalTheory.ChainOnto.bounded_single T (z i) fun w => GlobalTheory.LFun.norm_val _ _).converges (by simpa using hy)
  let G : ℂ → ℂ := fun x => GlobalTheory.LFun.eulerProd T A (x + 1 / 2) *
    ∏ i ∈ Finset.Icc 1 k, ∏ l ∈ Finset.range D.R.t, Λ i (x + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l)
  have hEq : ∀ x : ℂ, ((D.R.r : ℝ) + D.R.t + 2) < x.re →
      G x = GlobalTheory.LFun.LSD D c.S (chainPar c B k) (c.chT (k + 1)) (x + 1 / 2) := by
    intro x hx
    have hre : ∀ l : ℕ, l < D.R.t → 1 < (x + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l).re := by
      intro l hl
      have : (l : ℝ) + 1 ≤ D.R.t := by exact_mod_cast hl
      have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
      simp
      linarith
    show _ = GlobalTheory.LFun.eulerProd T (GlobalTheory.LFun.twist (chainPar c B k)
      (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹) (x + 1 / 2)
    rw [GlobalTheory.T.thetaLiftChainHeckeParameter_twist_next_target_char D c B k, ← hA, GlobalTheory.ChainOnto.eulerProd_add_segFam T A (Finset.Icc 1 k) z D.R.t (x + 1 / 2)
      (hAb.converges (by have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _; simp; linarith))
      (fun i _ l hl => hzc i _ (hre l hl))]
    refine congrArg (GlobalTheory.LFun.eulerProd T A (x + 1 / 2) * ·) (Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun l hl => ?_)
    exact (hΛ i hi).2.1 _ (hre l (Finset.mem_range.1 hl))
  have hU : IsOpen (GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2)) := GlobalTheory.Cont.isOpen_rightOf _
  have hD : DifferentiableOn ℂ G (GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2)) := by
    refine DifferentiableOn.mul ?_ (Differentiable.differentiableOn ?_)
    · refine hAb.differentiableOn.comp (differentiableOn_id.add_const _) fun x hx => ?_
      simp only [GlobalTheory.Cont.mem_rightOf] at hx
      simp
      linarith
    · exact Differentiable.fun_finsetProd fun i hi => Differentiable.fun_finsetProd fun l _ =>
        (hΛ i hi).1.comp (by fun_prop)
  have hAn := hD.analyticOnNhd hU
  have hmem : ((D.R.t : ℂ) / 2) ∈ GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2) := by
    simp only [GlobalTheory.Cont.mem_rightOf]
    simp
    linarith
  have hA0 : GlobalTheory.LFun.Converges T A ((1 + (D.R.t : ℂ)) / 2) := by
    refine hAb.converges ?_
    simp
    linarith
  have hLS : GlobalTheory.LFun.LSD D c.S B (c.μ (k + 1)) ((1 + (D.R.t : ℂ)) / 2) = GlobalTheory.LFun.eulerProd T A ((1 + (D.R.t : ℂ)) / 2) := rfl
  have hreidx : ∀ i, ∏ l ∈ Finset.range D.R.t, Λ i ((D.R.t : ℂ) / 2 + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l) =
      ∏ n ∈ Finset.Icc 1 D.R.t, Λ i n := by
    intro i
    refine Finset.prod_nbij' (fun l => D.R.t - l) (fun n => D.R.t - n) ?_ ?_ ?_ ?_ ?_
    · intro l hl
      simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hl ⊢
      omega
    · intro n hn
      simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hn ⊢
      omega
    · intro l hl
      simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hl
      omega
    · intro n hn
      simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hn
      omega
    · intro l hl
      have hl' := Finset.mem_range.1 hl
      congr 1
      rw [Nat.cast_sub hl'.le]
      ring
  refine ⟨∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 D.R.t, Λ i n, ?_,
    ⟨Λ, fun i hi => ⟨(hΛ i hi).1, (hΛ i hi).2.1⟩, rfl⟩, hA0, ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun i hi => Finset.prod_ne_zero_iff.2 fun n hn => ?_
    have hn' := Finset.mem_Icc.1 hn
    exact (hΛ i hi).2.2 n hn'.1 hn'.2
  · rw [hLS]
    exact hA0.ne_zero
  · refine ⟨G, ⟨_, hmem, GlobalTheory.Cont.isRightDomain_rightOf _, hAn.meromorphicOn,
      (D.R.r : ℝ) + D.R.t + 2, fun x hx => hEq x hx⟩, hAn _ hmem, ?_⟩
    show GlobalTheory.LFun.eulerProd T A ((D.R.t : ℂ) / 2 + 1 / 2) *
      ∏ i ∈ Finset.Icc 1 k, ∏ l ∈ Finset.range D.R.t, Λ i ((D.R.t : ℂ) / 2 + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l) = _
    rw [hLS, Finset.prod_congr rfl fun i _ => hreidx i]
    congr 2
    ring

end GlobalTheory.ChainTw

end
