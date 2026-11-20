import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoversOfLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.WtSz

open GlobalTheory.CompHS

/- English proof (translation)
The claim follows from `|((ofGaps a g j : ℤ) : ℝ)| ≤ 2 * ∑ k ∈ Finset.range N, |(g k : ℝ)| := by have key : ∀ b, b ≤ N ∨ True → ∑ k ∈ Finset.range b, |(g k : ℝ)| ≤ ∑ k ∈ Finset.range N, |(g k : ℝ)| := by intro b _ rcases le_total b N with h | h · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range …`.
-/
theorem abs_ofGaps_le {N : ℕ} (a : ℕ) (g : ℕ → ℤ) (hg : ∀ k, N ≤ k → g k = 0) (j : Fin N) :
    |((ofGaps a g j : ℤ) : ℝ)| ≤ 2 * ∑ k ∈ Finset.range N, |(g k : ℝ)| := by
  have key : ∀ b, b ≤ N ∨ True → ∑ k ∈ Finset.range b, |(g k : ℝ)| ≤ ∑ k ∈ Finset.range N, |(g k : ℝ)| := by
    intro b _
    rcases le_total b N with h | h
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h) (fun _ _ _ => abs_nonneg _)
    · rw [← Finset.sum_range_add_sum_Ico _ h]
      have : ∑ k ∈ Finset.Ico N b, |(g k : ℝ)| = 0 :=
        Finset.sum_eq_zero fun k hk => by simp [hg k (Finset.mem_Ico.1 hk).1]
      rw [this, add_zero]
  have h1 := key a (Or.inr trivial)
  have h2 := key j (Or.inl j.2.le)
  unfold ofGaps
  push_cast
  calc |∑ k ∈ Finset.range a, (g k : ℝ) - ∑ k ∈ Finset.range j, (g k : ℝ)|
      ≤ |∑ k ∈ Finset.range a, (g k : ℝ)| + |∑ k ∈ Finset.range j, (g k : ℝ)| := abs_sub _ _
    _ ≤ ∑ k ∈ Finset.range a, |(g k : ℝ)| + ∑ k ∈ Finset.range j, |(g k : ℝ)| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := by linarith

/- English proof (translation)
Set `e : ℕ → ℝ` to `fun k => if h : k < N then |(w ⟨k, h⟩ : ℝ)| else 0`. Establish `he : ∑ j, |(w j : ℝ)| = ∑ k ∈ Finset.range N, e k`. Rewrite using `[← Fin.sum_univ_eq_sum_range]`. Simplify using `[e]`. Establish `hb : ∀ k, |(gap w k : ℝ)| ≤ e k + e (k + 1)`.

Introduce `k`. Unfold `gap`. Distinguish the cases in `h : k + 1 < N`. Simplify using `only [dif_pos h, e, dif_pos (show k < N by omega)]`. Use `push_cast`.

Conclude with `abs_sub _ _`. Simplify using `only [dif_neg h]`. Apply the tactic sequence `have : 0 ≤ e k := by simp only [e]; split_ifs <;> simp`. Apply the tactic sequence `have : 0 ≤ e (k+1) := by simp only [e]; split_ifs <;> simp`. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs : ∑ k ∈ Finset.range N, e (k + 1) ≤ ∑ k ∈ Finset.range N, e k`. Use `Finset.sum_range_succ' e N` as an intermediate fact. Establish `h2` using `Finset.sum_range_succ e N`. Establish `hN : e N = 0` using `by simp [e]`.

Apply the tactic sequence `have h0 : 0 ≤ e 0 := by simp only [e]; split_ifs <;> simp`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_abs_gap_le {N : ℕ} (w : Fin N → ℤ) :
    ∑ k ∈ Finset.range N, |(gap w k : ℝ)| ≤ 2 * ∑ j, |(w j : ℝ)| := by
  let e : ℕ → ℝ := fun k => if h : k < N then |(w ⟨k, h⟩ : ℝ)| else 0
  have he : ∑ j, |(w j : ℝ)| = ∑ k ∈ Finset.range N, e k := by
    rw [← Fin.sum_univ_eq_sum_range]; simp [e]
  have hb : ∀ k, |(gap w k : ℝ)| ≤ e k + e (k + 1) := by
    intro k
    unfold gap
    by_cases h : k + 1 < N
    · simp only [dif_pos h, e, dif_pos (show k < N by omega)]
      push_cast
      exact abs_sub _ _
    · simp only [dif_neg h]
      have : 0 ≤ e k := by simp only [e]; split_ifs <;> simp
      have : 0 ≤ e (k+1) := by simp only [e]; split_ifs <;> simp
      simp; linarith
  have hs : ∑ k ∈ Finset.range N, e (k + 1) ≤ ∑ k ∈ Finset.range N, e k := by
    have := Finset.sum_range_succ' e N
    have h2 := Finset.sum_range_succ e N
    have hN : e N = 0 := by simp [e]
    have h0 : 0 ≤ e 0 := by simp only [e]; split_ifs <;> simp
    linarith
  calc ∑ k ∈ Finset.range N, |(gap w k : ℝ)| ≤ ∑ k ∈ Finset.range N, (e k + e (k + 1)) := Finset.sum_le_sum fun k _ => hb k
    _ ≤ _ := by rw [Finset.sum_add_distrib, he]; linarith

/- English proof (translation)
Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `h1 : ((x / n : ℤ) : ℝ) * n ≤ x`. Use `Int.ediv_mul_le x hn.ne'` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `h2 : (x : ℝ) < ((x / n : ℤ) : ℝ) * n + n`.

Use `Int.lt_ediv_add_one_mul_self x hn` as an intermediate fact. Establish `h3 : (x : ℝ) < ((x / n + 1 : ℤ) : ℝ) * n` using `by exact_mod_cast this`. Move the coercions through the operations in `at h3`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[abs_le]`.

Prove the components needed by the constructor for the conclusion. Establish `: -|(x:ℝ)| ≤ x` using `neg_abs_le _`. Establish `: ((x / n : ℤ) : ℝ) > (x : ℝ) / n - 1`. Rewrite using `[gt_iff_lt, sub_lt_iff_lt_add, div_lt_iff₀ hn']`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: (x:ℝ)/n ≥ -|(x:ℝ)|/n`. Apply `div_le_div_of_nonneg_right _ hn'.le` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: -|(x:ℝ)|/n = -(|(x:ℝ)|/n)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: ((x / n : ℤ) : ℝ) ≤ (x : ℝ) / n` using `by rw [le_div_iff₀ hn']; exact h1`. Establish `: (x:ℝ)/n ≤ |(x:ℝ)|/n` using `div_le_div_of_nonneg_right (le_abs_self _) hn'.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem abs_ediv_le (x n : ℤ) (hn : 0 < n) : |((x / n : ℤ) : ℝ)| ≤ |(x : ℝ)| / n + 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ((x / n : ℤ) : ℝ) * n ≤ x := by
    have := Int.ediv_mul_le x hn.ne'; exact_mod_cast this
  have h2 : (x : ℝ) < ((x / n : ℤ) : ℝ) * n + n := by
    have := Int.lt_ediv_add_one_mul_self x hn
    have h3 : (x : ℝ) < ((x / n + 1 : ℤ) : ℝ) * n := by exact_mod_cast this
    push_cast at h3; linarith
  rw [abs_le]
  constructor
  · have : -|(x:ℝ)| ≤ x := neg_abs_le _
    have : ((x / n : ℤ) : ℝ) > (x : ℝ) / n - 1 := by
      rw [gt_iff_lt, sub_lt_iff_lt_add, div_lt_iff₀ hn']; linarith
    have : (x:ℝ)/n ≥ -|(x:ℝ)|/n := by
      apply div_le_div_of_nonneg_right _ hn'.le; linarith
    have : -|(x:ℝ)|/n = -(|(x:ℝ)|/n) := by ring
    linarith
  · have : ((x / n : ℤ) : ℝ) ≤ (x : ℝ) / n := by rw [le_div_iff₀ hn']; exact h1
    have : (x:ℝ)/n ≤ |(x:ℝ)|/n := div_le_div_of_nonneg_right (le_abs_self _) hn'.le
    linarith

end GlobalTheory.CovTop.WtSz

namespace GlobalTheory.CovTop.WtSz

open GlobalTheory.CompHS

/- English proof (translation)
Apply the tactic sequence `unfold gap; split_ifs <;> ring`.
-/
theorem gap_sub_const {N : ℕ} (w : Fin N → ℤ) (c : ℤ) (k : ℕ) : gap (fun j => w j - c) k = gap w k := by
  unfold gap; split_ifs <;> ring

/- English proof (translation)
Unfold `gap; rw [dif_neg (by omega)]`.
-/
theorem gap_eq_zero {N : ℕ} (w : Fin N → ℤ) {k : ℕ} (hk : N ≤ k) : gap w k = 0 := by
  unfold gap; rw [dif_neg (by omega)]

/- English proof (translation)
Establish `hT' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `hsum : ∑ k ∈ Finset.range N, |(gap v k : ℝ)| ≤ 2 * ∑ j, |(w j : ℝ)| + N * B`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Use `_ ≤ _ := by linarith [sum_abs_gap_le w]`.

Establish `hG : ∑ k ∈ Finset.range N, |((gap v k / n : ℤ) : ℝ)| ≤ (2 * ∑ j, |(w j : ℝ)| + N * B) / n + N`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Use `_ ≤ _ := by gcongr`. Establish `hent : ∀ j, |(floorGaps a n v j : ℝ)| ≤ 2 * ((2 * ∑ j, |(w j : ℝ)| + N * B) / n + N)`.

Introduce `j`. Use `(abs_ofGaps_le a (fun k => gap v k / n) (fun k hk => ?_) j).trans ?_` and prove the remaining obligations. Simplify using `[gap_eq_zero v hk]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_abs_floorGaps_le {N : ℕ} (v w : Fin N → ℤ) (n : ℤ) (hn : 0 < n) (B : ℝ) (a : ℕ)
    (hgv : ∀ k, |(gap v k : ℝ)| ≤ |(gap w k : ℝ)| + B) :
    ∑ j, |(floorGaps a n v j : ℝ)| ≤ 2 * N * ((2 * ∑ j, |(w j : ℝ)| + N * B) / n + N) := by
  have hT' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ k ∈ Finset.range N, |(gap v k : ℝ)| ≤ 2 * ∑ j, |(w j : ℝ)| + N * B := by
    calc ∑ k ∈ Finset.range N, |(gap v k : ℝ)| ≤ ∑ k ∈ Finset.range N, (|(gap w k : ℝ)| + B) :=
          Finset.sum_le_sum fun k _ => hgv k
      _ = ∑ k ∈ Finset.range N, |(gap w k : ℝ)| + N * B := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := by linarith [sum_abs_gap_le w]
  have hG : ∑ k ∈ Finset.range N, |((gap v k / n : ℤ) : ℝ)| ≤ (2 * ∑ j, |(w j : ℝ)| + N * B) / n + N := by
    calc ∑ k ∈ Finset.range N, |((gap v k / n : ℤ) : ℝ)| ≤ ∑ k ∈ Finset.range N, (|(gap v k : ℝ)| / n + 1) :=
          Finset.sum_le_sum fun k _ => abs_ediv_le _ _ hn
      _ = (∑ k ∈ Finset.range N, |(gap v k : ℝ)|) / n + N := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      _ ≤ _ := by gcongr
  have hent : ∀ j, |(floorGaps a n v j : ℝ)| ≤ 2 * ((2 * ∑ j, |(w j : ℝ)| + N * B) / n + N) := by
    intro j
    refine (abs_ofGaps_le a (fun k => gap v k / n) (fun k hk => ?_) j).trans ?_
    · simp [gap_eq_zero v hk]
    · linarith
  calc ∑ j, |(floorGaps a n v j : ℝ)| ≤ ∑ _j : Fin N, 2 * ((2 * ∑ j, |(w j : ℝ)| + N * B) / n + N) :=
        Finset.sum_le_sum fun j _ => hent j
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/- English proof (translation)
Establish `hg : ∀ k, |((gap v k - n * (gap v k / n) : ℤ) : ℝ)| ≤ n - 1`. Introduce `k`. Rewrite using `[← Int.emod_def]`. Establish `h0` using `Int.emod_nonneg (gap v k) hn.ne'`. Establish `h1` using `Int.emod_lt_of_pos (gap v k) hn`.

Rewrite using `[abs_of_nonneg (by exact_mod_cast h0)]`. Establish `: gap v k % n ≤ n - 1` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hent : ∀ j, |(remGaps a n v j : ℝ)| ≤ 2 * (N * ((n : ℝ) - 1))`. Introduce `j`.

Use `(abs_ofGaps_le a (fun k => gap v k - n * (gap v k / n)) (fun k hk => ?_) j).trans ?_` and prove the remaining obligations. Simplify using `[gap_eq_zero v hk]`. Use `gcongr`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_abs_remGaps_le {N : ℕ} (v : Fin N → ℤ) (n : ℤ) (hn : 0 < n) (a : ℕ) :
    ∑ j, |(remGaps a n v j : ℝ)| ≤ 2 * N * N * (n - 1) := by
  have hg : ∀ k, |((gap v k - n * (gap v k / n) : ℤ) : ℝ)| ≤ n - 1 := by
    intro k
    rw [← Int.emod_def]
    have h0 := Int.emod_nonneg (gap v k) hn.ne'
    have h1 := Int.emod_lt_of_pos (gap v k) hn
    rw [abs_of_nonneg (by exact_mod_cast h0)]
    have : gap v k % n ≤ n - 1 := by omega
    exact_mod_cast this
  have hent : ∀ j, |(remGaps a n v j : ℝ)| ≤ 2 * (N * ((n : ℝ) - 1)) := by
    intro j
    refine (abs_ofGaps_le a (fun k => gap v k - n * (gap v k / n)) (fun k hk => ?_) j).trans ?_
    · simp [gap_eq_zero v hk]
    · gcongr
      calc ∑ k ∈ Finset.range N, |((gap v k - n * (gap v k / n) : ℤ) : ℝ)|
          ≤ ∑ _k ∈ Finset.range N, ((n : ℝ) - 1) := Finset.sum_le_sum fun k _ => hg k
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ∑ j, |(remGaps a n v j : ℝ)| ≤ ∑ _j : Fin N, 2 * (N * ((n : ℝ) - 1)) :=
        Finset.sum_le_sum fun j _ => hent j
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

/- English proof (translation)
Unfold `WtPar.T₁`. Check the signs of the components of the expression.
-/
theorem T₁_pos (P : WtPar Dw) : 0 < P.T₁ := by unfold WtPar.T₁; positivity

/- English proof (translation)
Use `sum_abs_floorGaps_le _ w _ (T₁_pos P) _ _ fun k => ?_` and prove the remaining obligations. Distinguish the cases in `h : k + 1 < Dw.p + Dw.q`. Rewrite using `[P.gap_uMinus_sub_kap τ h]`. Establish `hu' : P.u τ = fun j => w j - c` using `funext hu`. Rewrite using `[hu', gap_sub_const]`.

Use `push_cast`. Use `(abs_add_le _ _).trans (add_le_add le_rfl ?_)` and prove the remaining obligations. Establish `hN : (0:ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Move the coercions through the operations in `at hN ⊢`. Use `split_ifs`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show -(P.c₀ : ℝ) - (2 * ((Dw.p : ℝ) + Dw.q) - 2) = -((P.c₀ : ℝ) + (2 * ((Dw.p : ℝ) + Dw.q) - 2)) by ring, abs_neg]`. Conclude with `abs_add_le _ _`. Use `_ ≤ _ := by`. Establish `: |2 * ((Dw.p : ℝ) + Dw.q) - 2| ≤ 2 * ((Dw.p : ℝ) + Dw.q) + 2`.

Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`. Combine the linear equalities and inequalities to obtain the conclusion. Evaluate the numerical expressions. Combine the linear relations using `[abs_nonneg (P.c₀ : ℝ)]`. Establish `: gap ((P.uMinus - FlagTan.kap Dw) τ) k = 0` using `by unfold gap; rw [dif_neg h]`.

Rewrite using `[this]`. Simplify using `only [Int.cast_zero, abs_zero]`. Establish `: (0:ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Check the signs of the components of the expression.
-/
theorem sum_abs_u₁_le (P : WtPar Dw) (τ : Psi H) (w : Fin (Dw.p + Dw.q) → ℤ) (c : ℤ)
    (hu : ∀ j, P.u τ j = w j - c) :
    ∑ j, |(P.u₁ τ j : ℝ)| ≤ 2 * (Dw.p + Dw.q : ℕ) * ((2 * ∑ j, |(w j : ℝ)| +
      (Dw.p + Dw.q : ℕ) * (|(P.c₀ : ℝ)| + 2 * (Dw.p + Dw.q : ℕ) + 2)) / P.T₁ + (Dw.p + Dw.q : ℕ)) := by
  refine sum_abs_floorGaps_le _ w _ (T₁_pos P) _ _ fun k => ?_
  by_cases h : k + 1 < Dw.p + Dw.q
  · rw [P.gap_uMinus_sub_kap τ h]
    have hu' : P.u τ = fun j => w j - c := funext hu
    rw [hu', gap_sub_const]
    push_cast
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    have hN : (0:ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast at hN ⊢
    split_ifs
    · calc |-(P.c₀ : ℝ) - (2 * ((Dw.p : ℝ) + Dw.q) - 2)| ≤ |(P.c₀ : ℝ)| + |2 * ((Dw.p : ℝ) + Dw.q) - 2| := by
            rw [show -(P.c₀ : ℝ) - (2 * ((Dw.p : ℝ) + Dw.q) - 2) = -((P.c₀ : ℝ) + (2 * ((Dw.p : ℝ) + Dw.q) - 2)) by ring,
              abs_neg]
            exact abs_add_le _ _
        _ ≤ _ := by
            have : |2 * ((Dw.p : ℝ) + Dw.q) - 2| ≤ 2 * ((Dw.p : ℝ) + Dw.q) + 2 := by
              rw [abs_le]; constructor <;> linarith
            linarith
    · norm_num; linarith [abs_nonneg (P.c₀ : ℝ)]
  · have : gap ((P.uMinus - FlagTan.kap Dw) τ) k = 0 := by unfold gap; rw [dif_neg h]
    rw [this]; simp only [Int.cast_zero, abs_zero]
    have : (0:ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := Nat.cast_nonneg _
    positivity

/- English proof (translation)
Establish `h` using `sum_abs_remGaps_le ((P.uMinus - FlagTan.kap Dw) τ) P.T₁ (T₁_pos P) P.a`. Establish `hT : (P.T₁ : ℝ) - 1 = (P.T + FlagTan.dimFlag Dw : ℕ)` using `by unfold WtPar.T₁; push_cast; ring`. Rewrite `h` using `[hT]`. Conclude with `h`.
-/
theorem sum_abs_rem_le (P : WtPar Dw) (τ : Psi H) :
    ∑ j, |(P.rem τ j : ℝ)| ≤ 2 * (Dw.p + Dw.q : ℕ) * (Dw.p + Dw.q : ℕ) * (P.T + FlagTan.dimFlag Dw : ℕ) := by
  have h := sum_abs_remGaps_le ((P.uMinus - FlagTan.kap Dw) τ) P.T₁ (T₁_pos P) P.a
  have hT : (P.T₁ : ℝ) - 1 = (P.T + FlagTan.dimFlag Dw : ℕ) := by unfold WtPar.T₁; push_cast; ring
  rw [hT] at h
  exact h

end GlobalTheory.CovTop.WtSz

namespace GlobalTheory.CovTop.WtSz

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Take `⟨Z, hZ⟩ : ∃ Z, Z = f * r * L` from `⟨_, rfl⟩`. Rewrite `hPP`, the goal using `[← hZ]`. Establish `hfr : 8 ≤ f * r` using `by nlinarith`. Establish `hZ80 : 80 ≤ Z` using `by rw [hZ]; nlinarith`. Establish `hZ1 : 1 ≤ Z` using `by linarith`.

Establish `hfZ : f ≤ Z` using `by rw [hZ]; nlinarith`. Establish `hrZ : r ≤ Z` using `by rw [hZ]; nlinarith`. Establish `hfrZ : f * r ≤ Z` using `by rw [hZ]; nlinarith`. Establish `hZpow : ∀ n m : ℕ, n ≤ m → Z ^ n ≤ Z ^ m` using `fun n m h => pow_le_pow_right₀ hZ1 h`. Establish `hPP1 : 1 ≤ PP` using `le_trans (one_le_pow₀ hZ1) hPP`.

Establish `hPPZ : Z ^ 12 ≤ PP` using `hPP`. Establish `hb0 : 0 < b` using `lt_of_lt_of_le (by positivity) hb`. Establish `hkap9 : PP ^ 9 ≤ kap`. Establish `: PP * PP ^ 9 ≤ PP * kap` using `by nlinarith [pow_succ' PP 9]`. Conclude with `le_of_mul_le_mul_left this (by linarith)`.

Establish `hPPpow : ∀ n m : ℕ, n ≤ m → PP ^ n ≤ PP ^ m` using `fun n m h => pow_le_pow_right₀ hPP1 h`. Establish `hB : f * r * (c + 2 * r + 2) ≤ kap`. Establish `h1 : f * r * (c + 2 * r + 2) ≤ f * r * (26 * f ^ 2 * r ^ 4)`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Establish `: 2 * r + 2 ≤ 4 * f ^ 2 * r ^ 4`.

Establish `: r ≤ r ^ 4` using `by nlinarith [pow_le_pow_right₀ hr (show 1 ≤ 4 by norm_num), pow_one r]`. Establish `: 1 ≤ f ^ 2` using `by nlinarith`. Establish `: r ^ 4 ≤ f ^ 2 * r ^ 4` using `by nlinarith [pow_pos (by linarith : (0:ℝ) < r) 4]`. Use polynomial arithmetic with `[pow_pos (by linarith : (0:ℝ) < r) 4]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2 : f * r * (26 * f ^ 2 * r ^ 4) ≤ 26 * Z ^ 5`. Establish `: f * r * (f ^ 2 * r ^ 4) ≤ Z ^ 5`. Establish `e : f * r * (f ^ 2 * r ^ 4) = (f * r) ^ 3 * r ^ 2` using `by ring`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : 26 * Z ^ 5 ≤ Z ^ 12`. Establish `: 26 ≤ Z ^ 7` using `by nlinarith [hZpow 1 7 (by norm_num), pow_one Z]`. Establish `e : Z ^ 12 = Z ^ 7 * Z ^ 5` using `by ring`. Rewrite using `[e]; nlinarith [pow_pos (by linarith : (0:ℝ) < Z) 5]`.

Use polynomial arithmetic with `[hPPpow 1 9 (by norm_num), pow_one PP]`. Establish `hT3 : T ≤ 2 * PP ^ 3`. Establish `h1 : (f * r ^ 2) ^ 2 * r ≤ Z ^ 5`. Establish `e : (f * r ^ 2) ^ 2 * r = (f * r) ^ 2 * r ^ 3` using `by ring`. Rewrite using `[e]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : Z ^ 5 ≤ PP` using `(hZpow 5 12 (by norm_num)).trans hPPZ`. Establish `h3 : PP ^ 2 * ((f * r ^ 2) ^ 2 * r) ≤ PP ^ 2 * PP` using `by gcongr; linarith`. Establish `h4 : 1 ≤ PP ^ 3` using `one_le_pow₀ hPP1`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hT0 : 0 < T` using `by linarith`. Establish `hT₁ : T ≤ T + D + 1` using `by linarith`. Establish `hU1 : 2 * r * ((2 * kap + f * r * (c + 2 * r + 2)) / (T + D + 1) + f * r) ≤ 6 * r * (kap / T) + 2 * f * r ^ 2`. Establish `hkap0 : 0 ≤ kap` using `le_trans (by positivity) hkap9`. Establish `: (2 * kap + f * r * (c + 2 * r + 2)) / (T + D + 1) ≤ 3 * kap / T`.

Rewrite using `[div_le_div_iff₀ (by linarith) hT0]`. Use the polynomial consequences of the given equalities and inequalities. Establish `e : 3 * kap / T = 3 * (kap / T)` using `by ring`. Use the polynomial consequences of the given equalities and inequalities. Establish `hq0 : 0 ≤ kap / T` using `div_nonneg (le_trans (by positivity) hkap9) hT0.le`.

Establish `hfL : 12 ≤ f * L ^ 2` using `by nlinarith`. Establish `hfr2 : 0 ≤ f * r ^ 2` using `by positivity`. Establish `hZsq : Z ^ 2 = (f * L ^ 2) * (f * r ^ 2)` using `by rw [hZ]; ring`. Establish `hmul : 12 * (f * r ^ 2) ≤ (f * L ^ 2) * (f * r ^ 2)` using `mul_le_mul_of_nonneg_right hfL hfr2`. Establish `hZ2 : 2 * f * r ^ 2 ≤ Z ^ 2`.

Rewrite using `[hZsq]`. Establish `: 0 ≤ f * r ^ 2` using `hfr2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h6r : 6 * r ≤ Z ^ 2 / 2`. Establish `: r ≤ f * r ^ 2` using `by nlinarith`.

Rewrite using `[hZsq]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hR : f * (2 * r * r * (T + D)) ≤ Z ^ 2 / 2 * (kap / T)`. Establish `h1 : f * (2 * r * r * (T + D)) ≤ 4 * f * r ^ 2 * T` using `by nlinarith [mul_pos (by linarith : (0:ℝ) < f) (by linarith : (0:ℝ) < r)]`. Establish `h2 : 4 * f * r ^ 2 * T ≤ kap / T`.

Rewrite using `[le_div_iff₀ hT0]`. Establish `hT2 : T * T ≤ 4 * PP ^ 6` using `by nlinarith`. Establish `h16 : 16 * f * r ^ 2 ≤ PP`. Establish `: 16 * f * r ^ 2 ≤ Z ^ 12`. Establish `: f * r ^ 2 ≤ Z ^ 3`.

Combine the equalities or inequalities in the displayed calculation. Establish `: 16 ≤ Z ^ 9` using `by nlinarith [hZpow 1 9 (by norm_num), pow_one Z]`. Establish `e : Z ^ 12 = Z ^ 9 * Z ^ 3` using `by ring`. Rewrite using `[e]; nlinarith [pow_pos (by linarith : (0:ℝ) < Z) 3, mul_pos (by linarith : (0:ℝ) < f) (by positivity : (0:ℝ) < r ^ 2)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: 4 * f * r ^ 2 * T * T ≤ 4 * f * r ^ 2 * (4 * PP ^ 6)`. Establish `: 0 ≤ 4 * f * r ^ 2` using `by positivity`. Rewrite using `[mul_assoc (4 * f * r ^ 2)]`. Conclude with `mul_le_mul_of_nonneg_left hT2 this`. Establish `: 4 * f * r ^ 2 * (4 * PP ^ 6) ≤ PP * PP ^ 6` using `by nlinarith [pow_pos (by linarith : (0:ℝ) < PP) 6]`.

Establish `: PP * PP ^ 6 ≤ PP ^ 9` using `by rw [← pow_succ']; exact hPPpow 7 9 (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : kap / T ≤ Z ^ 2 / 2 * (kap / T)`. Establish `: 1 ≤ Z ^ 2 / 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `a1 : 6 * r * (kap / T) ≤ Z ^ 2 / 2 * (kap / T)` using `mul_le_mul_of_nonneg_right h6r hq0`. Establish `a2 : Z ^ 2 / 2 * (kap / T) ≤ Z ^ 2 * (kap / T)` using `mul_le_mul_of_nonneg_right (by nlinarith) hq0`. Establish `e : Z ^ 2 * (kap / T + 1) = Z ^ 2 * (kap / T) + Z ^ 2` using `by ring`. Rewrite using `[e]`.

Use `⟨by linarith, by linarith⟩` and prove the remaining obligations.
-/
theorem arith (f r L PP b kap T D c : ℝ) (hf : 8 ≤ f) (hr : 1 ≤ r) (hL : 10 ≤ L)
    (hPP : (f * r * L) ^ 12 ≤ PP) (hb : PP ^ 10 ≤ b) (hk : b ≤ PP * kap) (hT1 : 1 ≤ T) (hD0 : 0 ≤ D) (hDT : D ≤ T)
    (hTup : T ≤ PP ^ 2 * (f * r ^ 2) ^ 2 * r + 1) (hc0 : 0 ≤ c) (hc : c ≤ 22 * f ^ 2 * r ^ 4) :
    2 * r * ((2 * kap + f * r * (c + 2 * r + 2)) / (T + D + 1) + f * r) ≤ (f * r * L) ^ 2 * (kap / T + 1) ∧
    2 * r * ((2 * kap + f * r * (c + 2 * r + 2)) / (T + D + 1) + f * r) + f * (2 * r * r * (T + D)) ≤
      (f * r * L) ^ 2 * (kap / T + 1) := by
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = f * r * L := ⟨_, rfl⟩
  rw [← hZ] at hPP ⊢
  have hfr : 8 ≤ f * r := by nlinarith
  have hZ80 : 80 ≤ Z := by rw [hZ]; nlinarith
  have hZ1 : 1 ≤ Z := by linarith
  have hfZ : f ≤ Z := by rw [hZ]; nlinarith
  have hrZ : r ≤ Z := by rw [hZ]; nlinarith
  have hfrZ : f * r ≤ Z := by rw [hZ]; nlinarith
  have hZpow : ∀ n m : ℕ, n ≤ m → Z ^ n ≤ Z ^ m := fun n m h => pow_le_pow_right₀ hZ1 h
  have hPP1 : 1 ≤ PP := le_trans (one_le_pow₀ hZ1) hPP
  have hPPZ : Z ^ 12 ≤ PP := hPP

  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hkap9 : PP ^ 9 ≤ kap := by
    have : PP * PP ^ 9 ≤ PP * kap := by nlinarith [pow_succ' PP 9]
    exact le_of_mul_le_mul_left this (by linarith)
  have hPPpow : ∀ n m : ℕ, n ≤ m → PP ^ n ≤ PP ^ m := fun n m h => pow_le_pow_right₀ hPP1 h

  have hB : f * r * (c + 2 * r + 2) ≤ kap := by
    have h1 : f * r * (c + 2 * r + 2) ≤ f * r * (26 * f ^ 2 * r ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 2 * r + 2 ≤ 4 * f ^ 2 * r ^ 4 := by
        have : r ≤ r ^ 4 := by nlinarith [pow_le_pow_right₀ hr (show 1 ≤ 4 by norm_num), pow_one r]
        have : 1 ≤ f ^ 2 := by nlinarith
        have : r ^ 4 ≤ f ^ 2 * r ^ 4 := by nlinarith [pow_pos (by linarith : (0:ℝ) < r) 4]
        nlinarith [pow_pos (by linarith : (0:ℝ) < r) 4]
      linarith
    have h2 : f * r * (26 * f ^ 2 * r ^ 4) ≤ 26 * Z ^ 5 := by
      have : f * r * (f ^ 2 * r ^ 4) ≤ Z ^ 5 := by
        have e : f * r * (f ^ 2 * r ^ 4) = (f * r) ^ 3 * r ^ 2 := by ring
        rw [e]
        calc (f * r) ^ 3 * r ^ 2 ≤ Z ^ 3 * Z ^ 2 := by gcongr
          _ = Z ^ 5 := by ring
      linarith
    have h3 : 26 * Z ^ 5 ≤ Z ^ 12 := by
      have : 26 ≤ Z ^ 7 := by nlinarith [hZpow 1 7 (by norm_num), pow_one Z]
      have e : Z ^ 12 = Z ^ 7 * Z ^ 5 := by ring
      rw [e]; nlinarith [pow_pos (by linarith : (0:ℝ) < Z) 5]
    nlinarith [hPPpow 1 9 (by norm_num), pow_one PP]

  have hT3 : T ≤ 2 * PP ^ 3 := by
    have h1 : (f * r ^ 2) ^ 2 * r ≤ Z ^ 5 := by
      have e : (f * r ^ 2) ^ 2 * r = (f * r) ^ 2 * r ^ 3 := by ring
      rw [e]
      calc (f * r) ^ 2 * r ^ 3 ≤ Z ^ 2 * Z ^ 3 := by gcongr
        _ = Z ^ 5 := by ring
    have h2 : Z ^ 5 ≤ PP := (hZpow 5 12 (by norm_num)).trans hPPZ
    have h3 : PP ^ 2 * ((f * r ^ 2) ^ 2 * r) ≤ PP ^ 2 * PP := by gcongr; linarith
    have h4 : 1 ≤ PP ^ 3 := one_le_pow₀ hPP1
    nlinarith
  have hT0 : 0 < T := by linarith
  have hT₁ : T ≤ T + D + 1 := by linarith

  have hU1 : 2 * r * ((2 * kap + f * r * (c + 2 * r + 2)) / (T + D + 1) + f * r) ≤ 6 * r * (kap / T) + 2 * f * r ^ 2 := by
    have hkap0 : 0 ≤ kap := le_trans (by positivity) hkap9
    have : (2 * kap + f * r * (c + 2 * r + 2)) / (T + D + 1) ≤ 3 * kap / T := by
      rw [div_le_div_iff₀ (by linarith) hT0]
      nlinarith
    have e : 3 * kap / T = 3 * (kap / T) := by ring
    nlinarith
  have hq0 : 0 ≤ kap / T := div_nonneg (le_trans (by positivity) hkap9) hT0.le
  have hfL : 12 ≤ f * L ^ 2 := by nlinarith
  have hfr2 : 0 ≤ f * r ^ 2 := by positivity
  have hZsq : Z ^ 2 = (f * L ^ 2) * (f * r ^ 2) := by rw [hZ]; ring
  have hmul : 12 * (f * r ^ 2) ≤ (f * L ^ 2) * (f * r ^ 2) := mul_le_mul_of_nonneg_right hfL hfr2
  have hZ2 : 2 * f * r ^ 2 ≤ Z ^ 2 := by
    rw [hZsq]; have : 0 ≤ f * r ^ 2 := hfr2; linarith
  have h6r : 6 * r ≤ Z ^ 2 / 2 := by
    have : r ≤ f * r ^ 2 := by nlinarith
    rw [hZsq]; linarith

  have hR : f * (2 * r * r * (T + D)) ≤ Z ^ 2 / 2 * (kap / T) := by
    have h1 : f * (2 * r * r * (T + D)) ≤ 4 * f * r ^ 2 * T := by nlinarith [mul_pos (by linarith : (0:ℝ) < f) (by linarith : (0:ℝ) < r)]
    have h2 : 4 * f * r ^ 2 * T ≤ kap / T := by
      rw [le_div_iff₀ hT0]
      have hT2 : T * T ≤ 4 * PP ^ 6 := by nlinarith
      have h16 : 16 * f * r ^ 2 ≤ PP := by
        have : 16 * f * r ^ 2 ≤ Z ^ 12 := by
          have : f * r ^ 2 ≤ Z ^ 3 := by
            calc f * r ^ 2 ≤ Z * Z ^ 2 := by gcongr
              _ = Z ^ 3 := by ring
          have : 16 ≤ Z ^ 9 := by nlinarith [hZpow 1 9 (by norm_num), pow_one Z]
          have e : Z ^ 12 = Z ^ 9 * Z ^ 3 := by ring
          rw [e]; nlinarith [pow_pos (by linarith : (0:ℝ) < Z) 3, mul_pos (by linarith : (0:ℝ) < f) (by positivity : (0:ℝ) < r ^ 2)]
        linarith
      have : 4 * f * r ^ 2 * T * T ≤ 4 * f * r ^ 2 * (4 * PP ^ 6) := by
        have : 0 ≤ 4 * f * r ^ 2 := by positivity
        rw [mul_assoc (4 * f * r ^ 2)]; exact mul_le_mul_of_nonneg_left hT2 this
      have : 4 * f * r ^ 2 * (4 * PP ^ 6) ≤ PP * PP ^ 6 := by nlinarith [pow_pos (by linarith : (0:ℝ) < PP) 6]
      have : PP * PP ^ 6 ≤ PP ^ 9 := by rw [← pow_succ']; exact hPPpow 7 9 (by norm_num)
      linarith
    have h3 : kap / T ≤ Z ^ 2 / 2 * (kap / T) := by
      have : 1 ≤ Z ^ 2 / 2 := by nlinarith
      nlinarith
    linarith
  have a1 : 6 * r * (kap / T) ≤ Z ^ 2 / 2 * (kap / T) := mul_le_mul_of_nonneg_right h6r hq0
  have a2 : Z ^ 2 / 2 * (kap / T) ≤ Z ^ 2 * (kap / T) := mul_le_mul_of_nonneg_right (by nlinarith) hq0
  have e : Z ^ 2 * (kap / T + 1) = Z ^ 2 * (kap / T) + Z ^ 2 := by ring
  rw [e]
  refine ⟨by linarith, by linarith⟩

end GlobalTheory.CovTop.WtSz

namespace GlobalTheory.CovTop.WtSz

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `set P : WtPar (dat p i) := ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ with hP`. Establish `hN : (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r` using `by rw [hW.sig.2.2]`. Establish `hcard : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f` using `by rw [← Nat.card_eq_fintype_card, hW.card]`. Establish `hRk : D.R.k ≤ D.R.r ∧ 1 ≤ D.R.m ∧ 1 ≤ D.R.r`. Use `D.R.two_le_m` as an intermediate fact.

Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers. Establish `hDim : CompHt.dimFlag (dat p i) = FlagTan.dimFlag (dat p i)` using `GlobalTheory.CompHS.dimFlag_eq _`. Take `⟨⟨u1, hu1⟩, hq⟩` from `hS.2.2.2.2.2.2 hi`. Establish `hT3` using `(hq u1 hu1).1`.

Rewrite `hT3` using `[hDim]`. Establish `hc` using `cZero_spec D ((i : ℕ) + 1)`. Establish `hc0 : (0 : ℝ) ≤ (cZero D ((i : ℕ) + 1) : ℝ)` using `by exact_mod_cast hc.2.1`. Establish `hc1 : (cZero D ((i : ℕ) + 1) : ℝ) ≤ 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4` using `by exact_mod_cast hc.2.2`. Establish `hPPx` using `hH.poly.2.1`.

Establish `hroom` using `hH.room`. Establish `hZ12` using `hH.ppLow`. Establish `hPP0 : 0 ≤ PP` using `le_trans (by unfold zBase; positivity) hZ12`. Establish `hroom' : (L.sc.x ^ A') ^ (10 : ℕ) ≤ L.sc.b`. Use `Real.rpow_natCast (L.sc.x ^ A') 10` as an intermediate fact.

Move the coercions through the operations in `at this`. Rewrite `hroom` using `[this]`. Then use the resulting hypothesis. Establish `hb10 : PP ^ 10 ≤ L.sc.b` using `(pow_le_pow_left₀ hPP0 hPPx 10).trans hroom'`. Establish `hTup : (lenT p i PP : ℝ) ≤ PP ^ 2 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 * D.R.r + 1`. Establish `hd : (CompHt.dimFlag (dat p i) : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2`.

Rewrite using `[hW.dim]`. Establish `: D.R.r.choose 2 ≤ D.R.r ^ 2`. Rewrite using `[Nat.choose_two_right, sq]`. Conclude with `(Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))`. Conclude with `Nat.mul_le_mul_left _ this` after adjusting the coercions.

Establish `hm : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast hRk.2.1`. Establish `hk : (D.R.k : ℝ) ≤ D.R.r` using `by exact_mod_cast hRk.1`. Establish `hx : 0 ≤ PP ^ 2 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)` using `by positivity`. Establish `h1` using `Nat.ceil_lt_add_one hx`. Establish `h2 : PP ^ 2 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) ≤ PP ^ 2 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 * D.R.r`.

Rewrite using `[div_le_iff₀ (by linarith)]`. Establish `a : (CompHt.dimFlag (dat p i) : ℝ) ^ 2 ≤ ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2` using `pow_le_pow_left₀ (by positivity) hd 2`. Establish `b : PP ^ 2 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) ≤ PP ^ 2 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 * D.R.r` using `by gcongr`. Establish `c : 0 ≤ PP ^ 2 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 * D.R.r` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Unfold `lenT`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA` using `arith (D.R.f : ℝ) (D.R.r : ℝ) L.sc.L PP L.sc.b (kap p i) (lenT p i PP : ℝ) (FlagTan.dimFlag (dat p i) : ℝ) (cZero D ((i : ℕ) + 1) : ℝ) (by exact_mod_cast hH.f8) (by exact_mod_cast hRk.2.2) hH.big.2.1 (by unfold zBase at hZ12; exact hZ12) hb10 hS.2.2.2.2.2.1 (by exact_mod_cast (sh …`. Establish `hZ : zBase L = (D.R.f : ℝ) * D.R.r * L.sc.L` using `rfl`. Rewrite using `[hZ]`.

Establish `hT₁ : (P.T₁ : ℝ) = (lenT p i PP : ℝ) + (FlagTan.dimFlag (dat p i) : ℝ) + 1`. Simplify using `[WtPar.T₁, hP]`. Establish `hS1 : ∑ τ, ∑ j, |(P.u₁ τ j : ℝ)| ≤ 2 * (D.R.r : ℝ) * ((2 * kap p i + D.R.f * D.R.r * ((cZero D ((i : ℕ) + 1) : ℝ) + 2 * D.R.r + 2)) / ((lenT p i PP : ℝ) + (FlagTan.dimFlag (dat p i) : ℝ) + 1) + D.R.f * D.R.r)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hN, hT₁, show P.c₀ = cZero D ((i : ℕ) + 1) from rfl, abs_of_nonneg hc0]`.

Simplify using `only [mul_add, add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]`. Rewrite using `[show kap p i = ∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)| from rfl]`. Expand and normalize the polynomial expressions, which then agree. Establish `hS2 : ∑ τ, ∑ j, |(P.rem τ j : ℝ)| ≤ D.R.f * (2 * D.R.r * D.R.r * ((lenT p i PP : ℝ) + FlagTan.dimFlag (dat p i)))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, hN]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hS3 : ∑ τ, ∑ j, |(P.u₂ τ j : ℝ)| ≤ ∑ τ, ∑ j, |(P.u₁ τ j : ℝ)| + ∑ τ, ∑ j, |(P.rem τ j : ℝ)|`. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Establish `: (P.u₂ τ j : ℝ) = (P.u₁ τ j : ℝ) + (P.rem τ j : ℝ)`. Simplify using `[WtPar.u₂]`.

Rewrite using `[this]`. Conclude with `abs_add_le _ _`. Introduce `la hla`. Break down `hla with rfl | rfl` into its components or cases. Conclude with `hS1.trans hA.1`.

Conclude with `hS3.trans (by linarith [hA.2])`.
-/
theorem at_pt (PP A A' : ℝ) (hi : (i : ℕ) + 1 < D.R.m) (hS : SizeAt p i PP A) (hH : HostNum D L PP A' 10)
    (hW : WtNum p i PP) :
    ∀ la ∈ ({(⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁,
      (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂} : Set (AllWt.Weight (dat p i))),
      ∑ τ, ∑ k, |(la τ k : ℝ)| ≤ zBase L ^ 2 * (kap p i / lenT p i PP + 1) := by
  set P : WtPar (dat p i) := ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ with hP
  have hN : (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r := by rw [hW.sig.2.2]
  have hcard : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by rw [← Nat.card_eq_fintype_card, hW.card]
  have hRk : D.R.k ≤ D.R.r ∧ 1 ≤ D.R.m ∧ 1 ≤ D.R.r := by
    have := D.R.two_le_m; unfold Ranks.r; omega
  have hDim : CompHt.dimFlag (dat p i) = FlagTan.dimFlag (dat p i) := GlobalTheory.CompHS.dimFlag_eq _
  obtain ⟨⟨u1, hu1⟩, hq⟩ := hS.2.2.2.2.2.2 hi
  have hT3 := (hq u1 hu1).1
  rw [hDim] at hT3
  have hc := cZero_spec D ((i : ℕ) + 1)
  have hc0 : (0 : ℝ) ≤ (cZero D ((i : ℕ) + 1) : ℝ) := by exact_mod_cast hc.2.1
  have hc1 : (cZero D ((i : ℕ) + 1) : ℝ) ≤ 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 := by exact_mod_cast hc.2.2

  have hPPx := hH.poly.2.1
  have hroom := hH.room
  have hZ12 := hH.ppLow
  have hPP0 : 0 ≤ PP := le_trans (by unfold zBase; positivity) hZ12
  have hroom' : (L.sc.x ^ A') ^ (10 : ℕ) ≤ L.sc.b := by
    have := Real.rpow_natCast (L.sc.x ^ A') 10
    push_cast at this
    rwa [this] at hroom
  have hb10 : PP ^ 10 ≤ L.sc.b := (pow_le_pow_left₀ hPP0 hPPx 10).trans hroom'

  have hTup : (lenT p i PP : ℝ) ≤ PP ^ 2 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 * D.R.r + 1 := by
    have hd : (CompHt.dimFlag (dat p i) : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by
      rw [hW.dim]
      have : D.R.r.choose 2 ≤ D.R.r ^ 2 := by
        rw [Nat.choose_two_right, sq]; exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      exact_mod_cast Nat.mul_le_mul_left _ this
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast hRk.2.1
    have hk : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hRk.1
    have hx : 0 ≤ PP ^ 2 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by positivity
    have h1 := Nat.ceil_lt_add_one hx
    have h2 : PP ^ 2 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) ≤
        PP ^ 2 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 * D.R.r := by
      rw [div_le_iff₀ (by linarith)]
      have a : (CompHt.dimFlag (dat p i) : ℝ) ^ 2 ≤ ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hd 2
      have b : PP ^ 2 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) ≤ PP ^ 2 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 * D.R.r := by
        gcongr
      have c : 0 ≤ PP ^ 2 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 * D.R.r := by positivity
      nlinarith
    unfold lenT
    linarith
  have hA := arith (D.R.f : ℝ) (D.R.r : ℝ) L.sc.L PP L.sc.b (kap p i) (lenT p i PP : ℝ) (FlagTan.dimFlag (dat p i) : ℝ)
    (cZero D ((i : ℕ) + 1) : ℝ) (by exact_mod_cast hH.f8) (by exact_mod_cast hRk.2.2) hH.big.2.1 (by unfold zBase at hZ12; exact hZ12)
    hb10 hS.2.2.2.2.2.1 (by exact_mod_cast (show 1 ≤ lenT p i PP by omega)) (by positivity)
    (by exact_mod_cast (show FlagTan.dimFlag (dat p i) ≤ lenT p i PP by omega)) hTup hc0 hc1
  have hZ : zBase L = (D.R.f : ℝ) * D.R.r * L.sc.L := rfl
  rw [hZ]

  have hT₁ : (P.T₁ : ℝ) = (lenT p i PP : ℝ) + (FlagTan.dimFlag (dat p i) : ℝ) + 1 := by
    simp [WtPar.T₁, hP]
  have hS1 : ∑ τ, ∑ j, |(P.u₁ τ j : ℝ)| ≤ 2 * (D.R.r : ℝ) * ((2 * kap p i + D.R.f * D.R.r *
      ((cZero D ((i : ℕ) + 1) : ℝ) + 2 * D.R.r + 2)) / ((lenT p i PP : ℝ) + (FlagTan.dimFlag (dat p i) : ℝ) + 1) +
      D.R.f * D.R.r) := by
    calc ∑ τ, ∑ j, |(P.u₁ τ j : ℝ)| ≤ ∑ τ, 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) *
          ((2 * ∑ j, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ j : ℝ)| + (((dat p i).p + (dat p i).q : ℕ) : ℝ) *
            (|(P.c₀ : ℝ)| + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) + 2)) / P.T₁ + (((dat p i).p + (dat p i).q : ℕ) : ℝ)) :=
          Finset.sum_le_sum fun τ _ => sum_abs_u₁_le P τ _ (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ)
            (fun j => rfl)
      _ = _ := by
          rw [hN, hT₁, show P.c₀ = cZero D ((i : ℕ) + 1) from rfl, abs_of_nonneg hc0]
          simp only [mul_add, add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
            Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
          rw [show kap p i = ∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)| from rfl]
          ring
  have hS2 : ∑ τ, ∑ j, |(P.rem τ j : ℝ)| ≤ D.R.f * (2 * D.R.r * D.R.r * ((lenT p i PP : ℝ) + FlagTan.dimFlag (dat p i))) := by
    calc ∑ τ, ∑ j, |(P.rem τ j : ℝ)| ≤ ∑ _τ : Psi p.T.Q.H, 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) *
          (((dat p i).p + (dat p i).q : ℕ) : ℝ) * ((P.T + FlagTan.dimFlag (dat p i) : ℕ) : ℝ) :=
          Finset.sum_le_sum fun τ _ => sum_abs_rem_le P τ
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, hN]
          push_cast; rfl
  have hS3 : ∑ τ, ∑ j, |(P.u₂ τ j : ℝ)| ≤ ∑ τ, ∑ j, |(P.u₁ τ j : ℝ)| + ∑ τ, ∑ j, |(P.rem τ j : ℝ)| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun τ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have : (P.u₂ τ j : ℝ) = (P.u₁ τ j : ℝ) + (P.rem τ j : ℝ) := by
      simp [WtPar.u₂]
    rw [this]; exact abs_add_le _ _
  intro la hla
  rcases hla with rfl | rfl
  · exact hS1.trans hA.1
  · exact hS3.trans (by linarith [hA.2])

end GlobalTheory.CovTop.WtSz

namespace GlobalTheory.CovTop.WtSz

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hS`. Establish `hL : Lifts fun Fm x _ ι p i PP _ => (∃ A, SizeAt p i PP A) ∧ (∃ A, HostNum (Fm.D x ι) (Fm.L x ι) PP A 10) ∧ WtNum p i PP`. Use `Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and hS (Formalism.MainNotions.Closed.and (GlobalTheory.CovTop.Sizes.hostN 10) GlobalTheory.CovTop.WtShape.wtN)) fun Fm CH _ h => ?_` and prove the remaining obligations. Take `⟨⟨C1, _, a1, ha1⟩, ⟨C2, _, a2, ha2⟩, ⟨C3, _, a3, ha3⟩⟩` from `h`. Conclude with `⟨0, le_rfl, max a1 (max a2 a3), fun x hx hle ι p hp i => ⟨⟨C1, ha1 x hx ((le_max_left _ _).trans hle) ι p hp i⟩, ⟨C2, ha2 x hx (((le_max_left _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩, ha3 x hx (((le_max_right _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩⟩`.

Conclude with `CovSz.covers_of_lifts hL fun Fm x hx ι p i _ _ h hi _ _ => at_pt p i _ h.1.choose h.2.1.choose hi h.1.choose_spec h.2.1.choose_spec h.2.2`.
-/
theorem wts_le : Size → Covers fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂} : Set (AllWt.Weight (dat p i))), ∑ τ, ∑ k, |(la τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i PP + 1) := by
  intro hS
  have hL : Lifts fun Fm x _ ι p i PP _ => (∃ A, SizeAt p i PP A) ∧ (∃ A, HostNum (Fm.D x ι) (Fm.L x ι) PP A 10) ∧
      WtNum p i PP := by
    refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and hS (Formalism.MainNotions.Closed.and (GlobalTheory.CovTop.Sizes.hostN 10) GlobalTheory.CovTop.WtShape.wtN))
      fun Fm CH _ h => ?_
    obtain ⟨⟨C1, _, a1, ha1⟩, ⟨C2, _, a2, ha2⟩, ⟨C3, _, a3, ha3⟩⟩ := h
    exact ⟨0, le_rfl, max a1 (max a2 a3), fun x hx hle ι p hp i =>
      ⟨⟨C1, ha1 x hx ((le_max_left _ _).trans hle) ι p hp i⟩,
        ⟨C2, ha2 x hx (((le_max_left _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩,
        ha3 x hx (((le_max_right _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩⟩
  exact CovSz.covers_of_lifts hL fun Fm x hx ι p i _ _ h hi _ _ =>
    at_pt p i _ h.1.choose h.2.1.choose hi h.1.choose_spec h.2.1.choose_spec h.2.2

end GlobalTheory.CovTop.WtSz
