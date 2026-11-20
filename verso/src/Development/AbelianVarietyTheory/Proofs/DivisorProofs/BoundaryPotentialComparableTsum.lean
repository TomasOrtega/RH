import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSectionSmoothPolydiscStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

namespace GlobalTheory.PoincareLocal

open scoped Classical in

/- English proof (translation)
Establish `h1 : ∀ i, Option.elim (σ i) 0 t = ∑ k, if σ i = some k then t k else 0`. Introduce `i`. Consider the cases of `h : σ i with`. Consider the case `none => simp`. Consider the case `some k0 => simp [Finset.sum_ite_eq]`.

Rewrite using `[Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Use `split_ifs with hk`. Take `⟨i0, hi0⟩` from `hk`. Rewrite using `[Finset.sum_eq_single i0]`.

Simplify using `[hi0]`. Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `hbk`. Conclude with `hb (inj _ _ _ hbk hi0)`.

Simplify using the standard rewrite rules. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[if_neg]`. Introduce `h`.

Conclude with `hk ⟨i, h⟩`.
-/
theorem sum_elim_eq_sum_branches {e m : ℕ} (σ : Fin m → Option (Fin e))
    (inj : ∀ i i' k, σ i = some k → σ i' = some k → i = i') (t : Fin e → ℝ) :
    (∑ i, Option.elim (σ i) 0 t) = ∑ k, if ∃ i, σ i = some k then t k else 0 := by
  have h1 : ∀ i, Option.elim (σ i) 0 t = ∑ k, if σ i = some k then t k else 0 := by
    intro i
    cases h : σ i with
    | none => simp
    | some k0 => simp [Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs with hk
  · obtain ⟨i0, hi0⟩ := hk
    rw [Finset.sum_eq_single i0]
    · simp [hi0]
    · intro b _ hb
      rw [if_neg]
      intro hbk
      exact hb (inj _ _ _ hbk hi0)
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro h
    exact hk ⟨i, h⟩

/- English proof (translation)
Introduce `e X _ A m L s D ψ σ hB hP`. Establish `hfac` using `GlobalTheory.T.normal_section_smooth_polydisc A L s D ψ σ hB hP`. Take `⟨_, _, hinj, hD⟩` from `hP`. Use `choose f hfs hfe using hfac`. Establish `hK : IsCompact (Metric.closedBall (0 : Fin e → ℂ) (1 / 2))` using `isCompact_closedBall _ _`.

Establish `hsub : Metric.closedBall (0 : Fin e → ℂ) (1 / 2) ⊆ Metric.ball 0 1` using `Metric.closedBall_subset_ball (by norm_num)`. Establish `hbd : ∀ i, ∃ B, ∀ z ∈ Metric.closedBall (0 : Fin e → ℂ) (1 / 2), ‖f i z‖ ≤ B` using `fun i => hK.exists_bound_of_continuousOn ((hfs i).continuousOn.mono hsub)`. Use `choose B hBd using hbd`. Use `set M := ∑ i, |B i| with hMdef`. Establish `hM : 0 ≤ M` using `Finset.sum_nonneg (fun i _ => abs_nonneg _)`.

Establish `he2 : 2 ≤ Real.exp 1` using `by linarith [Real.add_one_le_exp (1 : ℝ)]`. Establish `hpi` using `Real.pi_gt_three`. Use `⟨Real.exp 1 + M + 4 * Real.pi + 2, by linarith [Real.exp_pos 1, Real.pi_pos], ?_⟩` and prove the remaining obligations. Introduce `z hz hnot`. Establish `hzc : z ∈ Metric.closedBall (0 : Fin e → ℂ) (1 / 2)` using `Metric.ball_subset_closedBall hz`.

Establish `hz1 : z ∈ Metric.ball (0 : Fin e → ℂ) 1` using `hsub hzc`. Establish `hnD : ∀ i, ψ.symm z ∉ D i` using `fun i h => hnot (Set.mem_iUnion.2 ⟨i, h⟩)`. Establish `hzk : ∀ i k, σ i = some k → z k ≠ 0` using `fun i k h h0 => hnD i ((hD z hz1 i).2 ⟨k, h, h0⟩)`. Establish `hne : ∀ i, normSec (L i) (s i) (ψ.symm z) ≠ 0`. Introduce `i h0`.

Use `hfe i z hz1` as an intermediate fact. Rewrite `this` using `[h0]`. Consider the cases of `h : σ i with`. Consider the case `none`. Simplify using `[h] at this`.

Conclude with `(Real.exp_pos _).ne' this.symm`. Consider the case `some k`. Establish `hk` using `hzk i k h`. Simplify using `[h, hk, Real.exp_ne_zero] at this`. Establish `hlog : ∀ i, Real.log (normSec (L i) (s i) (ψ.symm z) ^ 2) = -(4 * Real.pi) * Option.elim (σ i) 0 (fun k => tOf (z k)) - f i z`.

Introduce `i`. Rewrite using `[hfe i z hz1]`. Consider the cases of `h : σ i with`. Consider the case `none => simp [Real.log_exp]`. Consider the case `some k`.

Establish `hk` using `hzk i k h`. Simplify using `only [Option.elim]`. Rewrite using `[Real.log_mul (pow_pos (norm_pos_iff.2 hk) 2).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow]`. Unfold `tOf`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hr : rTot L s (ψ.symm z) = Real.exp 1 + 4 * Real.pi * ∑ i, Option.elim (σ i) 0 (fun k => tOf (z k)) + ∑ i, f i z`. Unfold `rTot`. Rewrite using `[← Finset.prod_pow, Real.log_prod (fun i _ => pow_ne_zero 2 (hne i))]`.

Simplify using `only [hlog]`. Rewrite using `[Finset.sum_sub_distrib, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Establish `hts : tSum σ z = 1 + ∑ i, Option.elim (σ i) 0 (fun k => tOf (z k))`. Unfold `tSum`.

Rewrite using `[sum_elim_eq_sum_branches σ hinj]`. Establish `hT0 : 0 ≤ ∑ i, Option.elim (σ i) 0 (fun k => tOf (z k))`. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `i _`. Consider the cases of `σ i with`.

Consider the case `none => simp`. Consider the case `some k`. Simplify using `only [Option.elim]`. Unfold `tOf`. Apply `div_nonneg _ (by positivity)` to reduce the goal to its premises.

Rewrite using `[neg_nonneg]`. Apply `Real.log_nonpos (norm_nonneg _)` to reduce the goal to its premises. Rewrite `hz1` using `[mem_ball_zero_iff]`. Conclude with `le_trans (norm_le_pi_norm z k) hz1.le`. Establish `hF : |∑ i, f i z| ≤ M`.

Use `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Use `hBd i z hzc` as an intermediate fact. Rewrite `this` using `[Real.norm_eq_abs]`. Conclude with `this.trans (le_abs_self _)`. Establish `hnn : ∀ i, 0 ≤ normSec (L i) (s i) (ψ.symm z)` using `fun i => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le`.

Establish `hge : Real.exp 1 ≤ rTot L s (ψ.symm z)`. Unfold `rTot`. Establish `hp : 0 < ∏ i, normSec (L i) (s i) (ψ.symm z)` using `Finset.prod_pos (fun i _ => lt_of_le_of_ne (hnn i) (hne i).symm)`. Establish `hp1 : ∏ i, normSec (L i) (s i) (ψ.symm z) ≤ 1` using `Finset.prod_le_one (fun i _ => hnn i) (fun i _ => (hB i).2.2.2 _)`. Establish `: Real.log ((∏ i, normSec (L i) (s i) (ψ.symm z)) ^ 2) ≤ 0` using `Real.log_nonpos (by positivity) (pow_le_one₀ hp.le hp1)`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hts]`. Use `set T := ∑ i, Option.elim (σ i) 0 (fun k => tOf (z k))`. Use `set R := rTot L s (ψ.symm z)`. Use `set F := ∑ i, f i z`.

Establish `hF1` using `(abs_le.1 hF).1`. Establish `hF2` using `(abs_le.1 hF).2`. Prove the components needed by the constructor for the conclusion. Rewrite using `[inv_mul_le_iff₀ (by linarith [Real.exp_pos 1, Real.pi_pos])]`. Establish `h1 : T ≤ R + M` using `by nlinarith`.

Establish `h2 : M ≤ M * R` using `by nlinarith`. Establish `h3 : 0 ≤ (Real.exp 1 + 4 * Real.pi) * R` using `mul_nonneg (by positivity) (by linarith [Real.exp_pos 1])`. Use the polynomial consequences of the given equalities and inequalities. Use polynomial arithmetic with `[mul_nonneg hM hT0, mul_nonneg (Real.exp_pos 1).le hT0, mul_nonneg Real.pi_pos.le hT0]`.
-/
theorem rTot_comparable_tSum : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)),
    IsBoundary A L s D → IsAdaptedPolydisc A D ψ σ → ∃ C : ℝ, 0 < C ∧
      ∀ z ∈ Metric.ball (0 : Fin e → ℂ) (1 / 2), ψ.symm z ∉ ⋃ i, D i →
        C⁻¹ * tSum σ z ≤ rTot L s (ψ.symm z) ∧ rTot L s (ψ.symm z) ≤ C * tSum σ z := by
  intro e X _ A m L s D ψ σ hB hP
  have hfac := GlobalTheory.T.normal_section_smooth_polydisc A L s D ψ σ hB hP
  obtain ⟨_, _, hinj, hD⟩ := hP
  choose f hfs hfe using hfac
  have hK : IsCompact (Metric.closedBall (0 : Fin e → ℂ) (1 / 2)) := isCompact_closedBall _ _
  have hsub : Metric.closedBall (0 : Fin e → ℂ) (1 / 2) ⊆ Metric.ball 0 1 :=
    Metric.closedBall_subset_ball (by norm_num)
  have hbd : ∀ i, ∃ B, ∀ z ∈ Metric.closedBall (0 : Fin e → ℂ) (1 / 2), ‖f i z‖ ≤ B := fun i =>
    hK.exists_bound_of_continuousOn ((hfs i).continuousOn.mono hsub)
  choose B hBd using hbd
  set M := ∑ i, |B i| with hMdef
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpi := Real.pi_gt_three
  refine ⟨Real.exp 1 + M + 4 * Real.pi + 2, by linarith [Real.exp_pos 1, Real.pi_pos], ?_⟩
  intro z hz hnot
  have hzc : z ∈ Metric.closedBall (0 : Fin e → ℂ) (1 / 2) := Metric.ball_subset_closedBall hz
  have hz1 : z ∈ Metric.ball (0 : Fin e → ℂ) 1 := hsub hzc
  have hnD : ∀ i, ψ.symm z ∉ D i := fun i h => hnot (Set.mem_iUnion.2 ⟨i, h⟩)
  have hzk : ∀ i k, σ i = some k → z k ≠ 0 := fun i k h h0 => hnD i ((hD z hz1 i).2 ⟨k, h, h0⟩)
  have hne : ∀ i, normSec (L i) (s i) (ψ.symm z) ≠ 0 := by
    intro i h0
    have := hfe i z hz1
    rw [h0] at this
    cases h : σ i with
    | none =>
      simp [h] at this
      exact (Real.exp_pos _).ne' this.symm
    | some k =>
      have hk := hzk i k h
      simp [h, hk, Real.exp_ne_zero] at this
  have hlog : ∀ i, Real.log (normSec (L i) (s i) (ψ.symm z) ^ 2)
      = -(4 * Real.pi) * Option.elim (σ i) 0 (fun k => tOf (z k)) - f i z := by
    intro i
    rw [hfe i z hz1]
    cases h : σ i with
    | none => simp [Real.log_exp]
    | some k =>
      have hk := hzk i k h
      simp only [Option.elim]
      rw [Real.log_mul (pow_pos (norm_pos_iff.2 hk) 2).ne' (Real.exp_pos _).ne', Real.log_exp,
        Real.log_pow]
      unfold tOf
      push_cast
      field_simp
      ring
  have hr : rTot L s (ψ.symm z) = Real.exp 1
      + 4 * Real.pi * ∑ i, Option.elim (σ i) 0 (fun k => tOf (z k)) + ∑ i, f i z := by
    unfold rTot
    rw [← Finset.prod_pow, Real.log_prod (fun i _ => pow_ne_zero 2 (hne i))]
    simp only [hlog]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hts : tSum σ z = 1 + ∑ i, Option.elim (σ i) 0 (fun k => tOf (z k)) := by
    unfold tSum
    rw [sum_elim_eq_sum_branches σ hinj]
  have hT0 : 0 ≤ ∑ i, Option.elim (σ i) 0 (fun k => tOf (z k)) := by
    apply Finset.sum_nonneg
    intro i _
    cases σ i with
    | none => simp
    | some k =>
      simp only [Option.elim]
      unfold tOf
      apply div_nonneg _ (by positivity)
      rw [neg_nonneg]
      apply Real.log_nonpos (norm_nonneg _)
      rw [mem_ball_zero_iff] at hz1
      exact le_trans (norm_le_pi_norm z k) hz1.le
  have hF : |∑ i, f i z| ≤ M := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have := hBd i z hzc
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have hnn : ∀ i, 0 ≤ normSec (L i) (s i) (ψ.symm z) := fun i =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hge : Real.exp 1 ≤ rTot L s (ψ.symm z) := by
    unfold rTot
    have hp : 0 < ∏ i, normSec (L i) (s i) (ψ.symm z) :=
      Finset.prod_pos (fun i _ => lt_of_le_of_ne (hnn i) (hne i).symm)
    have hp1 : ∏ i, normSec (L i) (s i) (ψ.symm z) ≤ 1 :=
      Finset.prod_le_one (fun i _ => hnn i) (fun i _ => (hB i).2.2.2 _)
    have : Real.log ((∏ i, normSec (L i) (s i) (ψ.symm z)) ^ 2) ≤ 0 :=
      Real.log_nonpos (by positivity) (pow_le_one₀ hp.le hp1)
    linarith
  rw [hts]
  set T := ∑ i, Option.elim (σ i) 0 (fun k => tOf (z k))
  set R := rTot L s (ψ.symm z)
  set F := ∑ i, f i z
  have hF1 := (abs_le.1 hF).1
  have hF2 := (abs_le.1 hF).2
  constructor
  · rw [inv_mul_le_iff₀ (by linarith [Real.exp_pos 1, Real.pi_pos])]
    have h1 : T ≤ R + M := by nlinarith
    have h2 : M ≤ M * R := by nlinarith
    have h3 : 0 ≤ (Real.exp 1 + 4 * Real.pi) * R :=
      mul_nonneg (by positivity) (by linarith [Real.exp_pos 1])
    nlinarith
  · nlinarith [mul_nonneg hM hT0, mul_nonneg (Real.exp_pos 1).le hT0, mul_nonneg Real.pi_pos.le hT0]

end GlobalTheory.PoincareLocal
