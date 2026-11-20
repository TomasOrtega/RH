import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.LayerBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.KhwEqZeroSharp

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {V : Submodule ℂ M}

/- English proof (translation)
Take `⟨m, hm⟩` from `exists_layer_of_mem_genSub hE hV.2.1 hw`. Take `⟨w₀, hw₀, hw₀μ, ws, hsum, hws⟩` from `layer_khw_decomp hE hU hV.1 hV.2.1 hm hμ`. Use `⟨w₀, hw₀, hw₀μ, m, ws, hsum, fun j => ⟨(hws j).1, fun h0 => ?_⟩⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `khw_layer_succ_bound hE hU hV hc hmono hh hbig (j : ℕ) (hws j).1 (hws j).2.1 h0 (hws j).2.2`. Take `⟨a, b, hab⟩` from `isNCSum_succ_exists h1`.

Use `(gap_gt hab hbig).2` as an intermediate fact. Conclude with `⟨h1, by linarith, h2⟩`.
-/
theorem k_highest_weight_layer_decomp (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {μ : Fin n → ℝ} {w : M}
    (hw : w ∈ genSub E V) (hμ : IsKHWVec ε E μ w) :
    ∃ w₀ ∈ V, IsKHWVec ε E μ w₀ ∧ ∃ m, ∃ ws : Fin m → M, w = w₀ + ∑ j, ws j ∧
      ∀ j : Fin m, ws j ∈ layer ε E V ((j : ℕ) + 1) ∧ (ws j ≠ 0 →
        IsNCSum ε ((j : ℕ) + 1) (μ - lowK ε lam) ∧ 0 < h - n + 1 ∧
        casValK ε (lowK ε lam) + 2 * (((j : ℕ) : ℝ) + 1) * (h - n + 1) ≤ casValK ε μ) := by
  obtain ⟨m, hm⟩ := exists_layer_of_mem_genSub hE hV.2.1 hw
  obtain ⟨w₀, hw₀, hw₀μ, ws, hsum, hws⟩ := layer_khw_decomp hE hU hV.1 hV.2.1 hm hμ
  refine ⟨w₀, hw₀, hw₀μ, m, ws, hsum, fun j => ⟨(hws j).1, fun h0 => ?_⟩⟩
  obtain ⟨h1, h2⟩ := khw_layer_succ_bound hE hU hV hc hmono hh hbig (j : ℕ) (hws j).1
    (hws j).2.1 h0 (hws j).2.2
  obtain ⟨a, b, hab⟩ := isNCSum_succ_exists h1
  have := (gap_gt hab hbig).2
  exact ⟨h1, by linarith, h2⟩

/- English proof (translation)
Take `⟨w₀, hw₀, -, m, ws, hwsum, hws⟩` from `k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hw hμ`. Distinguish the cases in `hall : ∀ j, ws j = 0`. It suffices to derive a contradiction. Establish `hweq : w = w₀`. Rewrite using `[hwsum]`.

Simplify using `[hall]`. Establish `hwV : w ∈ V`. Rewrite using `[hweq]`. Conclude with `hw₀`. Conclude with `hne (khw_weight_eq_of_irr hE hV hwV hw0 hμ)`.

Use `push_neg at hall`. Take `⟨j, hj⟩` from `hall`. Take `⟨h1, h2, h3⟩` from `(hws j).2 hj`. Conclude with `⟨(j : ℕ), h1, h2, h3⟩`.
-/
theorem casimir_gap_at_noncompact_weight (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {μ : Fin n → ℝ} {w : M}
    (hw : w ∈ genSub E V) (hw0 : w ≠ 0) (hμ : IsKHWVec ε E μ w) (hne : μ ≠ lowK ε lam) :
    ∃ j : ℕ, IsNCSum ε (j + 1) (μ - lowK ε lam) ∧ 0 < h - n + 1 ∧
      casValK ε (lowK ε lam) + 2 * ((j : ℝ) + 1) * (h - n + 1) ≤ casValK ε μ := by
  obtain ⟨w₀, hw₀, -, m, ws, hwsum, hws⟩ := k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hw hμ
  by_cases hall : ∀ j, ws j = 0
  · exfalso
    have hweq : w = w₀ := by
      rw [hwsum]
      simp [hall]
    have hwV : w ∈ V := by
      rw [hweq]
      exact hw₀
    exact hne (khw_weight_eq_of_irr hE hV hwV hw0 hμ)
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    obtain ⟨h1, h2, h3⟩ := (hws j).2 hj
    exact ⟨(j : ℕ), h1, h2, h3⟩

/- English proof (translation)
Take `⟨hmono, h, hh, hbig⟩` from `hgap`. Take `⟨w₀, hw₀, -, m, ws, rfl, hws⟩` from `k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hw hμ`. Establish `hzero : ∀ j, ws j = 0`. Introduce `j`. Assume the negation of the conclusion as `hne`.

Take `⟨-, hpos, hle⟩` from `(hws j).2 hne`. Establish `h1 : (0 : ℝ) < 2 * (((j : ℕ) : ℝ) + 1)` using `by positivity`. Establish `h2` using `mul_pos h1 hpos`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify `hw₀` using `[hzero]`.
-/
theorem khw_lowK_mem (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) {w : M} (hw : w ∈ genSub E V) (hμ : IsKHWVec ε E (lowK ε lam) w) :
    w ∈ V := by
  obtain ⟨hmono, h, hh, hbig⟩ := hgap
  obtain ⟨w₀, hw₀, -, m, ws, rfl, hws⟩ := k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hw hμ

  have hzero : ∀ j, ws j = 0 := by
    intro j
    by_contra hne
    obtain ⟨-, hpos, hle⟩ := (hws j).2 hne
    have h1 : (0 : ℝ) < 2 * (((j : ℕ) : ℝ) + 1) := by positivity
    have h2 := mul_pos h1 hpos
    linarith
  simpa [hzero] using hw₀

/- English proof (translation)
Distinguish the cases in `hne : μ = lowK ε lam`. Substitute `hne` using the available equality. Conclude with `le_refl _`. Take `⟨hmono, h, hh, hbig⟩` from `hgap`. Take `⟨j, ⟨γ, -, hsum⟩, -, hle⟩` from `casimir_gap_at_noncompact_weight hE hU hV hc hmono hh hbig hw hw0 hμ hne`.

Establish `hexp : ∀ x : Fin n → ℝ, nsq (x + (2 : ℝ) • rhoC ε) = nsq (x + rhoC ε) + 2 * dot x (rhoC ε) + 3 * nsq (rhoC ε)`. Introduce `x`. Simplify using `only [nsq, dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun a _ => by ring`. Establish `hlin : dot μ (rhoC ε) - dot (lowK ε lam) (rhoC ε) = dot (μ - lowK ε lam) (rhoC ε)`.

Simplify using `only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]`. Establish `hroot : ∀ a b : Fin n, dot (root a b) (rhoC ε) = rhoC ε a - rhoC ε b`. Introduce `a b`. Simplify using `[dot, root, Pi.single_apply, sub_mul, ite_mul, Finset.sum_sub_distrib]`. Establish `hdsum : dot (μ - lowK ε lam) (rhoC ε) = ∑ i, (rhoC ε (γ i).1 - rhoC ε (γ i).2)`.

Rewrite using `[hsum]`. Simplify using `only [dot, Finset.sum_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => hroot _ _`. Establish `hρ : ∀ a, -((n : ℝ) / 2) ≤ rhoC ε a ∧ rhoC ε a ≤ (n : ℝ) / 2`.

Establish `key : ∀ s t : Finset (Fin n), -((n : ℝ) / 2) ≤ ((s.card : ℝ) - t.card) / 2 ∧ ((s.card : ℝ) - t.card) / 2 ≤ (n : ℝ) / 2`. Introduce `s t`. Establish `hs : (s.card : ℝ) ≤ n` using `by exact_mod_cast (card_le_univ s).trans (by simp)`. Establish `ht : (t.card : ℝ) ≤ n` using `by exact_mod_cast (card_le_univ t).trans (by simp)`. Establish `hs0 : (0 : ℝ) ≤ s.card` using `Nat.cast_nonneg _`.

Establish `ht0 : (0 : ℝ) ≤ t.card` using `Nat.cast_nonneg _`. Apply the tactic sequence `constructor <;> linarith`. Introduce `a`. Conclude with `key _ _`. Establish `hterm : ∀ i : Fin (j + 1), -(n : ℝ) ≤ rhoC ε (γ i).1 - rhoC ε (γ i).2`.

Introduce `i`. Take `⟨h1, -⟩` from `hρ (γ i).1`. Take `⟨-, h2⟩` from `hρ (γ i).2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdot : -(((j : ℝ) + 1) * n) ≤ dot (μ - lowK ε lam) (rhoC ε)`.

Rewrite using `[hdsum]`. Establish `hc : ∑ _i : Fin (j + 1), (-(n : ℝ)) = -(((j : ℝ) + 1) * n)`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← hc]`. Conclude with `Finset.sum_le_sum fun i _ => hterm i`. Establish `hprod : 0 ≤ ((j : ℝ) + 1) * (h - 2 * n + 1)`. Establish `: (0 : ℝ) ≤ j` using `Nat.cast_nonneg j`. Conclude with `mul_nonneg (by linarith) (by linarith)`.

Simplify using `only [casValK] at hle`. Establish `e1` using `hexp μ`. Establish `e2` using `hexp (lowK ε lam)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem vogan_min (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) {μ : Fin n → ℝ} {w : M} (hw : w ∈ genSub E V) (hw0 : w ≠ 0)
    (hμ : IsKHWVec ε E μ w) :
    nsq (lowK ε lam + (2 : ℝ) • rhoC ε) ≤ nsq (μ + (2 : ℝ) • rhoC ε) := by
  by_cases hne : μ = lowK ε lam
  · subst hne
    exact le_refl _
  obtain ⟨hmono, h, hh, hbig⟩ := hgap
  obtain ⟨j, ⟨γ, -, hsum⟩, -, hle⟩ := casimir_gap_at_noncompact_weight hE hU hV hc hmono hh hbig hw hw0 hμ hne
  have hexp : ∀ x : Fin n → ℝ, nsq (x + (2 : ℝ) • rhoC ε) =
      nsq (x + rhoC ε) + 2 * dot x (rhoC ε) + 3 * nsq (rhoC ε) := by
    intro x
    simp only [nsq, dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hlin : dot μ (rhoC ε) - dot (lowK ε lam) (rhoC ε) = dot (μ - lowK ε lam) (rhoC ε) := by
    simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hroot : ∀ a b : Fin n, dot (root a b) (rhoC ε) = rhoC ε a - rhoC ε b := by
    intro a b
    simp [dot, root, Pi.single_apply, sub_mul, ite_mul, Finset.sum_sub_distrib]
  have hdsum : dot (μ - lowK ε lam) (rhoC ε) = ∑ i, (rhoC ε (γ i).1 - rhoC ε (γ i).2) := by
    rw [hsum]
    simp only [dot, Finset.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => hroot _ _

  have hρ : ∀ a, -((n : ℝ) / 2) ≤ rhoC ε a ∧ rhoC ε a ≤ (n : ℝ) / 2 := by
    have key : ∀ s t : Finset (Fin n),
        -((n : ℝ) / 2) ≤ ((s.card : ℝ) - t.card) / 2 ∧ ((s.card : ℝ) - t.card) / 2 ≤ (n : ℝ) / 2 := by
      intro s t
      have hs : (s.card : ℝ) ≤ n := by exact_mod_cast (card_le_univ s).trans (by simp)
      have ht : (t.card : ℝ) ≤ n := by exact_mod_cast (card_le_univ t).trans (by simp)
      have hs0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
      have ht0 : (0 : ℝ) ≤ t.card := Nat.cast_nonneg _
      constructor <;> linarith
    intro a
    exact key _ _
  have hterm : ∀ i : Fin (j + 1), -(n : ℝ) ≤ rhoC ε (γ i).1 - rhoC ε (γ i).2 := by
    intro i
    obtain ⟨h1, -⟩ := hρ (γ i).1
    obtain ⟨-, h2⟩ := hρ (γ i).2
    linarith
  have hdot : -(((j : ℝ) + 1) * n) ≤ dot (μ - lowK ε lam) (rhoC ε) := by
    rw [hdsum]
    have hc : ∑ _i : Fin (j + 1), (-(n : ℝ)) = -(((j : ℝ) + 1) * n) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [← hc]
    exact Finset.sum_le_sum fun i _ => hterm i
  have hprod : 0 ≤ ((j : ℝ) + 1) * (h - 2 * n + 1) := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    exact mul_nonneg (by linarith) (by linarith)
  simp only [casValK] at hle
  have e1 := hexp μ
  have e2 := hexp (lowK ε lam)
  linarith

/- English proof (translation)
Take `⟨hmono, h, hh, hbig⟩` from `hgap`. Establish `hn : (0 : ℝ) < h - n + 1`. Establish `: (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmon : Monotone (layer ε E V)`.

Use `monotone_nat_of_le_succ fun k => ?_` and prove the remaining obligations. Simplify using `only [layer]`. Conclude with `le_sup_left`. Use `⟨⌈(casValK ε μ - casValK ε (lowK ε lam)) / (2 * (h - n + 1))⌉₊, fun w hw hμ => ?_⟩` and prove the remaining obligations. Take `⟨w₀, hw₀, -, m, ws, rfl, hws⟩` from `k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hw hμ`.

Use `add_mem (hmon (Nat.zero_le _) (show w₀ ∈ layer ε E V 0 from hw₀)) (_root_.sum_mem fun j _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hj : ws j = 0`. Rewrite using `[hj]`. Conclude with `zero_mem _`. Take `⟨hmem, hrest⟩` from `hws j`.

Take `⟨-, -, hle⟩` from `hrest hj`. Use `hmon ?_ hmem` and prove the remaining obligations. Establish `hq : (((j : ℕ) : ℝ) + 1) ≤ (casValK ε μ - casValK ε (lowK ε lam)) / (2 * (h - n + 1))`. Rewrite using `[le_div_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hq'` using `hq.trans (Nat.le_ceil _)`. Conclude with `hq'` after adjusting the coercions.
-/
theorem khw_mem_layer (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) (μ : Fin n → ℝ) :
    ∃ k : ℕ, ∀ w ∈ genSub E V, IsKHWVec ε E μ w → w ∈ layer ε E V k := by
  obtain ⟨hmono, h, hh, hbig⟩ := hgap
  have hn : (0 : ℝ) < h - n + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hmon : Monotone (layer ε E V) := by
    refine monotone_nat_of_le_succ fun k => ?_
    simp only [layer]
    exact le_sup_left
  refine ⟨⌈(casValK ε μ - casValK ε (lowK ε lam)) / (2 * (h - n + 1))⌉₊, fun w hw hμ => ?_⟩
  obtain ⟨w₀, hw₀, -, m, ws, rfl, hws⟩ := k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hw hμ
  refine add_mem (hmon (Nat.zero_le _) (show w₀ ∈ layer ε E V 0 from hw₀))
    (_root_.sum_mem fun j _ => ?_)
  by_cases hj : ws j = 0
  · rw [hj]
    exact zero_mem _
  · obtain ⟨hmem, hrest⟩ := hws j
    obtain ⟨-, -, hle⟩ := hrest hj
    refine hmon ?_ hmem

    have hq : (((j : ℕ) : ℝ) + 1) ≤ (casValK ε μ - casValK ε (lowK ε lam)) / (2 * (h - n + 1)) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hq' := hq.trans (Nat.le_ceil _)
    exact_mod_cast hq'

/- English proof (translation)
Take `⟨k, hk⟩` from `khw_mem_layer hE hU hV hc hgap μ`. Take `⟨hfd, hks, -, -⟩` from `hV`. Establish `hcl : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V`. Introduce `a b v hv`. Rewrite `hv`, the goal using `[genSub, Submodule.mem_sInf]`.

Conclude with `fun T hT => hT.2 a b v (hv T hT)`. Establish `hgen : ∀ j, layer ε E V j ≤ genSub E V`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`.

Simplify using `only [layer]`. Rewrite using `[genSub]`. Conclude with `le_sInf fun T hT => hT.1`. Consider the case `succ j ih`. Simplify using `only [layer]`.

Use `sup_le ih (iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_)` and prove the remaining obligations. Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce `v hv`. Conclude with `hcl a b v (ih hv)`. Conclude with `⟨layer ε E V k, finiteDimensional_layer hfd k, hgen k, layer_kStable hE hks k, hk⟩`.
-/
theorem admissible (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) (μ : Fin n → ℝ) :
    ∃ S : Submodule ℂ M, FiniteDimensional ℂ S ∧ S ≤ genSub E V ∧ IsKStableSub ε E S ∧
      ∀ w ∈ genSub E V, IsKHWVec ε E μ w → w ∈ S := by
  obtain ⟨k, hk⟩ := khw_mem_layer hE hU hV hc hgap μ
  obtain ⟨hfd, hks, -, -⟩ := hV
  have hcl : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := by
    intro a b v hv
    rw [genSub, Submodule.mem_sInf] at hv ⊢
    exact fun T hT => hT.2 a b v (hv T hT)
  have hgen : ∀ j, layer ε E V j ≤ genSub E V := by
    intro j
    induction j with
    | zero =>
      simp only [layer]
      rw [genSub]
      exact le_sInf fun T hT => hT.1
    | succ j ih =>
      simp only [layer]
      refine sup_le ih (iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_)
      rw [Submodule.map_le_iff_le_comap]
      intro v hv
      exact hcl a b v (ih hv)
  exact ⟨layer ε E V k, finiteDimensional_layer hfd k, hgen k, layer_kStable hE hks k, hk⟩

end Unitary

end ReciprocityTheory.ChartRestriction.DS.G2
