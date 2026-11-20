import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermsLatticeBound
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.PointwiseKernelBound
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.AutomorphicBallCount
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutBallCount
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDyadicShellIndex

open NumberField Finset Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.FarTerms

/- English proof (translation)
Use function extensionality and compare the values at `a`. Apply the tactic sequence `by_cases hS : a ∈ S <;> by_cases hF : F a = 0 <;> simp [Set.indicator, hS, hF]`.
-/
private lemma indicator_eq_indicator_inter_support {α : Type} (S : Set α) (F : α → ℝ) :
    S.indicator F = ({a | a ∈ S ∧ F a ≠ 0} : Set α).indicator F := by
  funext a
  by_cases hS : a ∈ S <;> by_cases hF : F a = 0 <;> simp [Set.indicator, hS, hF]

/- English proof (translation)
Take `⟨hs, hle⟩` from `h`. Establish `key` using `indicator_eq_indicator_inter_support S F`. Establish `hT : Summable (({a | a ∈ S ∧ F a ≠ 0} : Set α).indicator F)` using `(summable_subtype_iff_indicator (s := {a | a ∈ S ∧ F a ≠ 0}) (f := F)).1 hs`. Rewrite `hT` using `[← key]`. Use `⟨(summable_subtype_iff_indicator (s := S) (f := F)).2 hT, ?_⟩` and prove the remaining obligations.

Rewrite using `[tsum_subtype S F, key, ← tsum_subtype {a | a ∈ S ∧ F a ≠ 0} F]`. Conclude with `hle`.
-/
theorem summable_of_support {α : Type} (S : Set α) (F : α → ℝ) (C : ℝ)
    (h : Summable (fun γ : {a // a ∈ S ∧ F a ≠ 0} => F γ.1) ∧
      ∑' γ : {a // a ∈ S ∧ F a ≠ 0}, F γ.1 ≤ C) :
    Summable (fun γ : S => F γ.1) ∧ ∑' γ : S, F γ.1 ≤ C := by
  obtain ⟨hs, hle⟩ := h
  have key := indicator_eq_indicator_inter_support S F
  have hT : Summable (({a | a ∈ S ∧ F a ≠ 0} : Set α).indicator F) :=
    (summable_subtype_iff_indicator (s := {a | a ∈ S ∧ F a ≠ 0}) (f := F)).1 hs
  rw [← key] at hT
  refine ⟨(summable_subtype_iff_indicator (s := S) (f := F)).2 hT, ?_⟩
  rw [tsum_subtype S F, key, ← tsum_subtype {a | a ∈ S ∧ F a ≠ 0} F]
  exact hle

/- English proof (translation)
Take `⟨v⟩` from `(inferInstance : Nonempty (InfinitePlace B.I.F))`. Establish `h1 : B.I.qAt v = q` using `(hS v).2`. Establish `h2 : B.I.qAt v ≤ B.I.n` using `by show (Finset.univ.filter fun a => B.I.ε v a = false).card ≤ B.I.n`. Conclude with `(Finset.card_filter_le _ _).trans (by simp)`. Use linear arithmetic over natural numbers and integers.
-/
private lemma one_le_n_of_sigIs_of_one_le_q (B : RowsAut) (p q : ℕ) (hS : SigIs B p q) (hq : 1 ≤ q) :
    1 ≤ B.I.n := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace B.I.F))
  have h1 : B.I.qAt v = q := (hS v).2
  have h2 : B.I.qAt v ≤ B.I.n := by
    show (Finset.univ.filter fun a => B.I.ε v a = false).card ≤ B.I.n
    exact (Finset.card_filter_le _ _).trans (by simp)
  omega

/- English proof (translation)
Introduce `hP B d p q h ep hDS hSig hqm hq1 hGap hep0 hepc hlog hhep hhep2 h120 x`. Establish `hn : 1 ≤ B.I.n` using `one_le_n_of_sigIs_of_one_le_q B p q hSig hq1`. Establish `h120' : 120 * (B.I.n : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h`. Rewrite using `[← hqm]`. Conclude with `h120`.

Take `⟨hdec, hbd, -, -, -, hK, -⟩` from `hP B d p q h hDS hSig hGap h120'`. Rewrite `hdec` using `[← hqm]`. Establish `hdec'` using `hdec hq1`. Establish `hne : ∀ γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, phe B d (x⁻¹ * γ.1 * x) ≠ 0`. Introduce `γ h0`.

Conclude with `γ.2.2 (by simp [h0])`. Establish `hM0 : 0 ≤ (∏ v, d v) * (B.e 1).re` using `(norm_nonneg _).trans (hbd 1)`. Break down `eq_or_lt_of_le hM0 with hM | hM` into its components or cases. Use `haveI : IsEmpty {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} := ⟨fun γ => hne γ (norm_eq_zero.1 (le_antisymm ((hbd _).trans_eq hM.symm) (norm_nonneg _)))⟩`. Use `summable_of_support (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x) (fun a => ‖phe B d (x⁻¹ * a * x)‖) _ ⟨summable_empty, ?_⟩` and prove the remaining obligations.

Rewrite using `[tsum_empty, ← hM]`. Simplify using the standard rewrite rules. Establish `hMne : (∏ v, d v) * (B.e 1).re ≠ 0` using `hM.ne'`. Establish `hA : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor`.

Check the signs of the components of the expression. Establish `hq1r : (1 : ℝ) ≤ q` using `by exact_mod_cast hq1`. Establish `hc : 0 < Real.sqrt (2 * (q : ℝ))` using `Real.sqrt_pos.2 (by linarith)`. Establish `hdist : ∀ (γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}) (v : InfinitePlace B.I.F), 0 ≤ GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v))`. Introduce `γ v`.

Unfold `GlobalTheory.Count.dHS`. Conclude with `Real.sqrt_nonneg _`. Establish `hcount : ∀ r : InfinitePlace B.I.F → ℝ, (∀ v, 0 ≤ r v) → {γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v}.Finite ∧ (({γ : {a // a ∈ GlobalTh …`. Introduce `r hr`. Take `⟨hfin, hcard⟩` from `GlobalTheory.AutBall.autBallCount B.I hn x r hr`.

Establish `hmaps : ∀ γ ∈ {γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v}, (γ.1 : B.I.GA) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCoun …`. Introduce `γ hγ`. Establish `hm : γ.1 ∈ B.I.GFset ∧ ¬ GlobalTheory.Count.IsNear B d ep x γ.1` using `γ.2.1`. Use `show γ.1 ∈ B.I.GFset ∧ (x⁻¹ * γ.1 * x).2 ∈ B.I.Kset ∧ ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v`. Conclude with `⟨hm.1, hK _ (hne γ), hγ⟩`.

Establish `hinj : Set.InjOn (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => γ.1) {γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v …` using `fun a _ b _ hab => Subtype.ext hab`. Use `⟨(hfin.preimage Subtype.val_injective.injOn).subset hmaps, ?_⟩` and prove the remaining obligations. Establish `hle` using `Set.ncard_le_ncard_of_injOn (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => γ.1) hmaps hinj hfin`. Establish `hAB : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x = GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.bigA B.I x` using `rfl`. Rewrite using `[hAB]`.

Conclude with `(Nat.cast_le.2 hle).trans hcard`. Establish `hfar : ∀ γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, ∃ v, ep < GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v))`. Introduce `γ`. Establish `hm : γ.1 ∈ B.I.GFset ∧ ¬ GlobalTheory.Count.IsNear B d ep x γ.1` using `γ.2.1`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `hm.2 (by unfold GlobalTheory.Count.IsNear; exact ⟨hm.1, hne γ, hcon⟩)`. Establish `hw : ∀ γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, 0 ≤ ‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re) ∧ ‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re) ≤ ∏ v, Real.exp (-(h / 8) * min (Glo …`. Introduce `γ`. Use `⟨div_nonneg (norm_nonneg _) hM.le, ?_⟩` and prove the remaining obligations.

Rewrite using `[div_le_iff₀ hM]`. Conclude with `le_of_le_of_eq (hdec' (x⁻¹ * γ.1 * x)) (mul_comm _ _)`. Take `⟨hsum, hle⟩` from `GlobalTheory.sum_over_dyadic_shells {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} (InfinitePlace B.I.F) (fun γ v => GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v))) (fun γ => ‖phe B d (x⁻¹ * γ.1 * x)‖ / ( …`. Establish `hfun : (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => ‖phe B d (x⁻¹ * γ.1 * x)‖) = fun γ => (∏ v, d v) * (B.e 1).re * (‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re))`. Use function extensionality and compare the values at `γ`.

Rewrite using `[mul_div_assoc', mul_comm, mul_div_assoc, div_self hMne, mul_one]`. Establish `hs' : Summable (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => ‖phe B d (x⁻¹ * γ.1 * x)‖)`. Rewrite using `[hfun]`. Conclude with `hsum.mul_left _`. Establish `hle' : ∑' γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, ‖phe B d (x⁻¹ * γ.1 * x)‖ ≤ (∏ v, d v) * (B.e 1).re * GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x * (2 * (B.I.f : …`.

Rewrite using `[hfun, tsum_mul_left]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `summable_of_support (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x) (fun a => ‖phe B d (x⁻¹ * a * x)‖) _ ⟨hs', hle'⟩`.
-/
theorem farBound_of_ptBound : GlobalTheory.Deep.PtBound → GlobalTheory.Deep.FarBound := by
  intro hP B d p q h ep hDS hSig hqm hq1 hGap hep0 hepc hlog hhep hhep2 h120 x
  have hn : 1 ≤ B.I.n := one_le_n_of_sigIs_of_one_le_q B p q hSig hq1
  have h120' : 120 * (B.I.n : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [← hqm]; exact h120
  obtain ⟨hdec, hbd, -, -, -, hK, -⟩ := hP B d p q h hDS hSig hGap h120'
  rw [← hqm] at hdec
  have hdec' := hdec hq1
  have hne : ∀ γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, phe B d (x⁻¹ * γ.1 * x) ≠ 0 := by
    intro γ h0
    exact γ.2.2 (by simp [h0])
  have hM0 : 0 ≤ (∏ v, d v) * (B.e 1).re := (norm_nonneg _).trans (hbd 1)
  rcases eq_or_lt_of_le hM0 with hM | hM
  · haveI : IsEmpty {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} :=
      ⟨fun γ => hne γ (norm_eq_zero.1 (le_antisymm ((hbd _).trans_eq hM.symm) (norm_nonneg _)))⟩
    refine summable_of_support (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x)
      (fun a => ‖phe B d (x⁻¹ * a * x)‖) _ ⟨summable_empty, ?_⟩
    rw [tsum_empty, ← hM]
    simp
  · have hMne : (∏ v, d v) * (B.e 1).re ≠ 0 := hM.ne'
    have hA : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor; positivity
    have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hc : 0 < Real.sqrt (2 * (q : ℝ)) := Real.sqrt_pos.2 (by linarith)
    have hdist : ∀ (γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}) (v : InfinitePlace B.I.F),
        0 ≤ GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) := by
      intro γ v; unfold GlobalTheory.Count.dHS; exact Real.sqrt_nonneg _
    have hcount : ∀ r : InfinitePlace B.I.F → ℝ, (∀ v, 0 ≤ r v) →
        {γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v}.Finite ∧
        (({γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v}.ncard : ℕ) : ℝ) ≤
          GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x * Real.exp (2 * (B.I.n : ℝ) ^ 2 * ∑ v, r v) := by
      intro r hr
      obtain ⟨hfin, hcard⟩ := GlobalTheory.AutBall.autBallCount B.I hn x r hr
      have hmaps : ∀ γ ∈ {γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v},
          (γ.1 : B.I.GA) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.ballSet B.I x r := by
        intro γ hγ
        have hm : γ.1 ∈ B.I.GFset ∧ ¬ GlobalTheory.Count.IsNear B d ep x γ.1 := γ.2.1
        show γ.1 ∈ B.I.GFset ∧ (x⁻¹ * γ.1 * x).2 ∈ B.I.Kset ∧
          ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v
        exact ⟨hm.1, hK _ (hne γ), hγ⟩
      have hinj : Set.InjOn (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => γ.1)
          {γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v} :=
        fun a _ b _ hab => Subtype.ext hab
      refine ⟨(hfin.preimage Subtype.val_injective.injOn).subset hmaps, ?_⟩
      have hle := Set.ncard_le_ncard_of_injOn (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => γ.1) hmaps hinj hfin
      have hAB : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x = GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.bigA B.I x := rfl
      rw [hAB]
      exact (Nat.cast_le.2 hle).trans hcard
    have hfar : ∀ γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, ∃ v, ep < GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) := by
      intro γ
      have hm : γ.1 ∈ B.I.GFset ∧ ¬ GlobalTheory.Count.IsNear B d ep x γ.1 := γ.2.1
      by_contra hcon
      push_neg at hcon
      exact hm.2 (by unfold GlobalTheory.Count.IsNear; exact ⟨hm.1, hne γ, hcon⟩)
    have hw : ∀ γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, 0 ≤ ‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re) ∧
        ‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re) ≤
          ∏ v, Real.exp (-(h / 8) * min (GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ^ 2)
            (GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) / Real.sqrt (2 * (q : ℝ)))) := by
      intro γ
      refine ⟨div_nonneg (norm_nonneg _) hM.le, ?_⟩
      rw [div_le_iff₀ hM]
      exact le_of_le_of_eq (hdec' (x⁻¹ * γ.1 * x)) (mul_comm _ _)
    obtain ⟨hsum, hle⟩ := GlobalTheory.sum_over_dyadic_shells {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} (InfinitePlace B.I.F)
      (fun γ v => GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)))
      (fun γ => ‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re))
      (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x) (2 * (B.I.n : ℝ) ^ 2) h ep (Real.sqrt (2 * (q : ℝ)))
      hA (by positivity) hep0 hc hepc hlog (by linarith) hhep2 hdist hcount hfar hw
    have hfun : (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => ‖phe B d (x⁻¹ * γ.1 * x)‖) =
        fun γ => (∏ v, d v) * (B.e 1).re * (‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re)) := by
      funext γ
      rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hMne, mul_one]
    have hs' : Summable (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => ‖phe B d (x⁻¹ * γ.1 * x)‖) := by
      rw [hfun]; exact hsum.mul_left _
    have hle' : ∑' γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, ‖phe B d (x⁻¹ * γ.1 * x)‖ ≤
        (∏ v, d v) * (B.e 1).re * GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x *
          (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * ep ^ 2 / 16))) := by
      rw [hfun, tsum_mul_left]
      calc _ ≤ (∏ v, d v) * (B.e 1).re * (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x *
              (2 * (Fintype.card (InfinitePlace B.I.F) : ℝ) * 3 ^ Fintype.card (InfinitePlace B.I.F) *
                Real.exp (-(h * ep ^ 2 / 16)))) := mul_le_mul_of_nonneg_left hle hM.le
        _ = _ := by rw [GlobalTheory.Count.FrameMajorant.card_places B.I]; ring
    exact summable_of_support (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x)
      (fun a => ‖phe B d (x⁻¹ * a * x)‖) _ ⟨hs', hle'⟩

end GlobalTheory.FarTerms
