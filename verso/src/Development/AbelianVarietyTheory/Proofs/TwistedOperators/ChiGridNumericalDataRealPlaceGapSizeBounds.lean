import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridReal

open GlobalTheory.SignedHC

/- English proof (translation)
Introduce `D large₂ hS τ`. Take `⟨⟨Pm, -, -⟩, -, -, hm44, -, -, -, -, -, -, -, hSb, hpos, -⟩` from `hS`. Use `set G := GlobalTheory.ChiGrid.num D 1 τ with hG`. Establish `hk : G.k = D.R.k` using `rfl`. Establish `hm : G.m = D.R.m` using `rfl`.

Establish `hga : G.ga = GlobalTheory.ChiGrid.gap D 1` using `rfl`. Take `⟨hv0, hb0, -⟩` from `GridData.ofHCParam_spec (D.hc τ) (GlobalTheory.ChiGrid.sLen D) (GlobalTheory.ChiGrid.gap D 1) (GlobalTheory.ChiGrid.cen D 1 τ)`. Establish `hv : ∀ i : Fin (D.R.k - 1), (((D.hc τ).v i : ℚ) : ℝ) = ((G.v (i.1 + 2) : ℤ) : ℝ)`. Introduce `i`. Establish `e : (D.hc τ).v i = ((G.v (i.1 + 2) : ℤ) : ℚ)` using `hv0 i`.

Rewrite using `[e, Rat.cast_intCast]`. Establish `hb : ∀ l : Fin D.R.m, (((D.hc τ).b l : ℚ) : ℝ) = ((G.b (l.1 + 1) : ℤ) : ℝ)`. Introduce `l`. Establish `e : (D.hc τ).b l = ((G.b (l.1 + 1) : ℤ) : ℚ)` using `hb0 l`. Rewrite using `[e, Rat.cast_intCast]`.

Establish `hm2` using `D.R.two_le_m`. Establish `hmk` using `D.R.m_add_three_le_k`. Establish `hr6 : 6 ≤ D.R.r` using `by unfold Ranks.r; omega`. Use `set X : ℝ := (D.R.r : ℝ) + 1 with hX`. Establish `hX7 : 7 ≤ X`.

Establish `: (6 : ℝ) ≤ D.R.r` using `by exact_mod_cast hr6`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX3 : 0 ≤ X ^ 3` using `by positivity`. Establish `hgapS : (2 : ℝ) ≤ Formalism.BasicNotions.LevelStarExponents.gapS D Pm.Cgap`. Unfold `Formalism.BasicNotions.LevelStarExponents.gapS`.

Establish `h1 : 0 ≤ Pm.Cgap * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4`. Use `Pm.Cgap_pos` as an intermediate fact. Check the signs of the components of the expression. Establish `hN : (2 : ℝ) ≤ (D.R.N D.R.m : ℝ)`. Establish `: 2 ≤ D.R.N D.R.m` using `by unfold Ranks.N; exact le_trans (by omega) (Nat.le_add_right _ _)`.

Conclude with `this` after adjusting the coercions. Establish `hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10` using `one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ D.R.m))`. Use the polynomial consequences of the given equalities and inequalities. Establish `hgap : 1000 * X ^ 3 ≤ (G.ga : ℝ)`. Establish `hB` using `((GlobalTheory.ChiGrid.gapBound_iff D 1 (GlobalTheory.ChiGrid.gap D 1)).2 le_rfl).1`.

Establish `hn : ((GlobalTheory.ChiGrid.nRk D : ℕ) : ℝ) = X` using `by unfold GlobalTheory.ChiGrid.nRk; push_cast; rfl`. Rewrite `hB` using `[hn]`. Establish `h1 : 0 ≤ (1 : ℝ) * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 3` using `by positivity`. Establish `h2 : 0 ≤ (1 : ℝ) * X ^ 3 * Real.sqrt (GlobalTheory.ChiGrid.cloudLen D)`. Use `Real.sqrt_nonneg (GlobalTheory.ChiGrid.cloudLen D : ℝ)` as an intermediate fact.

Check the signs of the components of the expression. Establish `h4 : (1000 : ℝ) ≤ X ^ 4`. Establish `: (7 : ℝ) ^ 4 ≤ X ^ 4` using `pow_le_pow_left₀ (by norm_num) hX7 4`. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h7 : 1000 * X ^ 3 ≤ X ^ 7`. Establish `: X ^ 7 = X ^ 4 * X ^ 3` using `by ring`. Rewrite using `[this]`. Conclude with `mul_le_mul_of_nonneg_right h4 hX3`. Rewrite using `[hga]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX1 : (1 : ℝ) ≤ 1000 * X ^ 3`. Establish `: (1 : ℝ) ≤ X ^ 3` using `one_le_pow₀ (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hga0 : (0 : ℝ) ≤ (G.ga : ℝ)` using `by positivity`.

Establish `hSb' : large₂.Sc + ((D.R.m : ℝ) + 1) * (G.ga : ℝ) + 1 / 2 ≤ large₂.sc.b` using `by rw [hga]; exact hSb`. Establish `hSc` using `large₂.Sc_pos`. Establish `hbga : (G.ga : ℝ) ≤ large₂.sc.b`. Establish `: (G.ga : ℝ) ≤ ((D.R.m : ℝ) + 1) * (G.ga : ℝ)`. Establish `: (0 : ℝ) ≤ (D.R.m : ℝ)` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb1 : (1 : ℝ) ≤ large₂.sc.b` using `by linarith`. Establish `hbsq : large₂.sc.b ≤ large₂.sc.b ^ 2` using `by nlinarith`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb1, ?_⟩` and prove the remaining obligations.

Introduce `i hi1 hi2`. Take `⟨a, rfl⟩` from `Nat.exists_eq_add_of_le' hi1`. Establish `hlt : a + 1 < D.R.k - 1` using `by rw [hk] at hi2; omega`. Establish `h` using `(Pm.sig_gaps τ).1 a hlt`. Establish `e` using `hv ⟨a, by omega⟩`.

Establish `e'` using `hv ⟨a + 1, hlt⟩`. Move the coercions through the operations in `at h`. Simplify using `only at e e'`. Rewrite `h` using `[e, e']`. Establish `: ((G.v (a + 2 + 1) : ℤ) : ℝ) + 2 ≤ ((G.v (a + 2) : ℤ) : ℝ)`.

Rewrite using `[show a + 2 + 1 = a + 1 + 2 by omega]; linarith`. Conclude with `this` after adjusting the coercions. Establish `h` using `(Pm.sig_gaps τ).2.1 (by omega) (by omega)`. Establish `e` using `hv ⟨D.R.k - 2, by omega⟩`. Establish `e'` using `hb ⟨0, by omega⟩`.

Move the coercions through the operations in `at h`. Simplify using `only at e e'`. Rewrite `h` using `[e, e']`. Rewrite using `[hk, show D.R.k = D.R.k - 2 + 2 by omega]`. Establish `: (2 : ℝ) ≤ ((G.v (D.R.k - 2 + 2) : ℤ) : ℝ) + ((G.b (0 + 1) : ℤ) : ℝ)` using `by linarith`.

Conclude with `this` after adjusting the coercions. Introduce `l hl1 hl2`. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le' hl1`. Establish `hlt : j + 1 < D.R.m` using `by rw [hm] at hl2; omega`. Establish `h` using `(Pm.nodes_gap τ j hlt).1`.

Establish `hf` using `Pm.heightBound_ge_rank_cubic`. Establish `e` using `hb ⟨j + 1, hlt⟩`. Establish `e'` using `hb ⟨j, by omega⟩`. Move the coercions through the operations in `at h`. Simplify using `only at e e'`.

Rewrite `h` using `[e, e']`. Establish `hY : 10 * X ≤ (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1)`. Establish `h44 : (44 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm44`. Establish `hk0 : (0 : ℝ) ≤ D.R.k` using `by positivity`. Establish `ht0 : (0 : ℝ) ≤ D.R.t` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hY3 : (10 * X) ^ 3 ≤ ((D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1)) ^ 3` using `pow_le_pow_left₀ (by linarith) hY 3`. Establish `ht0 : (0 : ℝ) ≤ D.R.t` using `by positivity`. Establish `: ((G.b (j + 1) : ℤ) : ℝ) + 1000 * X ^ 3 ≤ ((G.b (j + 1 + 1) : ℤ) : ℝ)` using `by nlinarith`. Conclude with `this`.

Conclude with `hgap`. Establish `h` using `(large₂.cloud_v τ ⟨D.R.k - 2, by omega⟩).1`. Rewrite `h` using `[hv]`. Simplify using `only at h`. Rewrite using `[hk, show D.R.k = D.R.k - 2 + 2 by omega]`.

Conclude with `h` after adjusting the coercions. Establish `h` using `(hpos τ ⟨0, by omega⟩).1`. Establish `e` using `hb ⟨0, by omega⟩`. Establish `h' : (0 : ℝ) < (((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ)` using `by exact_mod_cast h`. Rewrite `h'` using `[e]`.

Conclude with `h'` after adjusting the coercions. Establish `h` using `(large₂.cloud_v τ ⟨0, by omega⟩).2`. Rewrite `h` using `[hv]`. Simplify using `only [zero_add] at h`. Establish `e : (((G.a 0 : ℚ)) : ℝ) = ((G.v 2 : ℤ) : ℝ) + 1 / 2 + ((D.R.m : ℝ) + 1) * (G.ga : ℝ)`.

Unfold `GridData.a`. Rewrite using `[hm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h` using `large₂.b_le τ ⟨D.R.m - 1, by omega⟩`. Rewrite `h` using `[hb]`. Simplify using `only at h`. Rewrite using `[hm, show D.R.m = D.R.m - 1 + 1 by omega]`.

Conclude with `h`. Establish `h8 : 8 * X ≤ 1000 * X ^ 3`. Establish `hX2 : (1 : ℝ) ≤ X ^ 2` using `one_le_pow₀ (by linarith)`. Establish `: X ^ 3 = X * X ^ 2` using `by ring`. Establish `hXX : X ≤ X ^ 3` using `by rw [this]; nlinarith`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb4 : large₂.sc.b ≤ large₂.sc.b ^ 4`. Establish `: large₂.sc.b ^ 4 = large₂.sc.b * large₂.sc.b ^ 3` using `by ring`. Rewrite using `[this]`. Establish `: (1 : ℝ) ≤ large₂.sc.b ^ 3` using `one_le_pow₀ hb1`.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem num_real_bounds : ∀ (D : D7) (large₂ : SizeData₂ D), SizeRows large₂ → ∀ τ : D.what₂.Tau, (∀ i, 2 ≤ i → i < (GlobalTheory.ChiGrid.num D 1 τ).k → (GlobalTheory.ChiGrid.num D 1 τ).v (i + 1) + 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v i) ∧ 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k + (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (∀ l, 1 ≤ l → l < (GlobalTheory.ChiGrid.num D 1 τ).m → ((GlobalTheory.ChiGrid.num D 1 τ).b l : ℝ) + 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).b (l + 1)) ∧ 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).ga ∧ 0 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k ∧ 0 < (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (((GlobalTheory.ChiGrid.num D 1 τ).a 0 : ℚ) : ℝ) ≤ large₂.sc.b ^ 2 ∧ ((GlobalTheory.ChiGrid.num D 1 τ).b (GlobalTheory.ChiGrid.num D 1 τ).m : ℝ) ≤ large₂.sc.b ^ 2 ∧ 1 ≤ large₂.sc.b ∧ 8 * ((D.R.r : ℝ) + 1) ≤ large₂.sc.b ^ 4 := by
  intro D large₂ hS τ
  obtain ⟨⟨Pm, -, -⟩, -, -, hm44, -, -, -, -, -, -, -, hSb, hpos, -⟩ := hS
  set G := GlobalTheory.ChiGrid.num D 1 τ with hG
  have hk : G.k = D.R.k := rfl
  have hm : G.m = D.R.m := rfl
  have hga : G.ga = GlobalTheory.ChiGrid.gap D 1 := rfl
  obtain ⟨hv0, hb0, -⟩ := GridData.ofHCParam_spec (D.hc τ) (GlobalTheory.ChiGrid.sLen D) (GlobalTheory.ChiGrid.gap D 1)
    (GlobalTheory.ChiGrid.cen D 1 τ)
  have hv : ∀ i : Fin (D.R.k - 1), (((D.hc τ).v i : ℚ) : ℝ) = ((G.v (i.1 + 2) : ℤ) : ℝ) := by
    intro i
    have e : (D.hc τ).v i = ((G.v (i.1 + 2) : ℤ) : ℚ) := hv0 i
    rw [e, Rat.cast_intCast]
  have hb : ∀ l : Fin D.R.m, (((D.hc τ).b l : ℚ) : ℝ) = ((G.b (l.1 + 1) : ℤ) : ℝ) := by
    intro l
    have e : (D.hc τ).b l = ((G.b (l.1 + 1) : ℤ) : ℚ) := hb0 l
    rw [e, Rat.cast_intCast]
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hr6 : 6 ≤ D.R.r := by unfold Ranks.r; omega
  set X : ℝ := (D.R.r : ℝ) + 1 with hX
  have hX7 : 7 ≤ X := by
    have : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
    linarith
  have hX3 : 0 ≤ X ^ 3 := by positivity

  have hgapS : (2 : ℝ) ≤ Formalism.BasicNotions.LevelStarExponents.gapS D Pm.Cgap := by
    unfold Formalism.BasicNotions.LevelStarExponents.gapS
    have h1 : 0 ≤ Pm.Cgap * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 := by
      have := Pm.Cgap_pos; positivity
    have hN : (2 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      have : 2 ≤ D.R.N D.R.m := by unfold Ranks.N; exact le_trans (by omega) (Nat.le_add_right _ _)
      exact_mod_cast this
    have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ D.R.m))
    nlinarith

  have hgap : 1000 * X ^ 3 ≤ (G.ga : ℝ) := by
    have hB := ((GlobalTheory.ChiGrid.gapBound_iff D 1 (GlobalTheory.ChiGrid.gap D 1)).2 le_rfl).1
    have hn : ((GlobalTheory.ChiGrid.nRk D : ℕ) : ℝ) = X := by unfold GlobalTheory.ChiGrid.nRk; push_cast; rfl
    rw [hn] at hB
    have h1 : 0 ≤ (1 : ℝ) * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 3 := by positivity
    have h2 : 0 ≤ (1 : ℝ) * X ^ 3 * Real.sqrt (GlobalTheory.ChiGrid.cloudLen D) := by
      have := Real.sqrt_nonneg (GlobalTheory.ChiGrid.cloudLen D : ℝ); positivity
    have h4 : (1000 : ℝ) ≤ X ^ 4 := by
      have : (7 : ℝ) ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX7 4
      norm_num at this; linarith
    have h7 : 1000 * X ^ 3 ≤ X ^ 7 := by
      have : X ^ 7 = X ^ 4 * X ^ 3 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right h4 hX3
    rw [hga]; linarith
  have hX1 : (1 : ℝ) ≤ 1000 * X ^ 3 := by
    have : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ (by linarith)
    linarith

  have hga0 : (0 : ℝ) ≤ (G.ga : ℝ) := by positivity
  have hSb' : large₂.Sc + ((D.R.m : ℝ) + 1) * (G.ga : ℝ) + 1 / 2 ≤ large₂.sc.b := by rw [hga]; exact hSb
  have hSc := large₂.Sc_pos
  have hbga : (G.ga : ℝ) ≤ large₂.sc.b := by
    have : (G.ga : ℝ) ≤ ((D.R.m : ℝ) + 1) * (G.ga : ℝ) := by
      have : (0 : ℝ) ≤ (D.R.m : ℝ) := by positivity
      nlinarith
    linarith
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith
  have hbsq : large₂.sc.b ≤ large₂.sc.b ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb1, ?_⟩
  ·
    intro i hi1 hi2
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hi1
    have hlt : a + 1 < D.R.k - 1 := by rw [hk] at hi2; omega
    have h := (Pm.sig_gaps τ).1 a hlt
    have e := hv ⟨a, by omega⟩
    have e' := hv ⟨a + 1, hlt⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    have : ((G.v (a + 2 + 1) : ℤ) : ℝ) + 2 ≤ ((G.v (a + 2) : ℤ) : ℝ) := by
      rw [show a + 2 + 1 = a + 1 + 2 by omega]; linarith
    exact_mod_cast this
  ·
    have h := (Pm.sig_gaps τ).2.1 (by omega) (by omega)
    have e := hv ⟨D.R.k - 2, by omega⟩
    have e' := hb ⟨0, by omega⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    rw [hk, show D.R.k = D.R.k - 2 + 2 by omega]
    have : (2 : ℝ) ≤ ((G.v (D.R.k - 2 + 2) : ℤ) : ℝ) + ((G.b (0 + 1) : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  ·
    intro l hl1 hl2
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hl1
    have hlt : j + 1 < D.R.m := by rw [hm] at hl2; omega
    have h := (Pm.nodes_gap τ j hlt).1
    have hf := Pm.heightBound_ge_rank_cubic
    have e := hb ⟨j + 1, hlt⟩
    have e' := hb ⟨j, by omega⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    have hY : 10 * X ≤ (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1) := by
      have h44 : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm44
      have hk0 : (0 : ℝ) ≤ D.R.k := by positivity
      have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
      nlinarith
    have hY3 : (10 * X) ^ 3 ≤ ((D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1)) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hY 3
    have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
    have : ((G.b (j + 1) : ℤ) : ℝ) + 1000 * X ^ 3 ≤ ((G.b (j + 1 + 1) : ℤ) : ℝ) := by nlinarith
    exact this
  · exact hgap
  ·
    have h := (large₂.cloud_v τ ⟨D.R.k - 2, by omega⟩).1
    rw [hv] at h
    simp only at h
    rw [hk, show D.R.k = D.R.k - 2 + 2 by omega]
    exact_mod_cast h
  ·
    have h := (hpos τ ⟨0, by omega⟩).1
    have e := hb ⟨0, by omega⟩
    have h' : (0 : ℝ) < (((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast h
    rw [e] at h'
    exact_mod_cast h'
  ·
    have h := (large₂.cloud_v τ ⟨0, by omega⟩).2
    rw [hv] at h
    simp only [zero_add] at h
    have e : (((G.a 0 : ℚ)) : ℝ) = ((G.v 2 : ℤ) : ℝ) + 1 / 2 + ((D.R.m : ℝ) + 1) * (G.ga : ℝ) := by
      unfold GridData.a; rw [hm]; push_cast; ring
    rw [e]; linarith
  ·
    have h := large₂.b_le τ ⟨D.R.m - 1, by omega⟩
    rw [hb] at h
    simp only at h
    rw [hm, show D.R.m = D.R.m - 1 + 1 by omega]
    exact h
  ·
    have h8 : 8 * X ≤ 1000 * X ^ 3 := by
      have hX2 : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ (by linarith)
      have : X ^ 3 = X * X ^ 2 := by ring
      have hXX : X ≤ X ^ 3 := by rw [this]; nlinarith
      linarith
    have hb4 : large₂.sc.b ≤ large₂.sc.b ^ 4 := by
      have : large₂.sc.b ^ 4 = large₂.sc.b * large₂.sc.b ^ 3 := by ring
      rw [this]
      have : (1 : ℝ) ≤ large₂.sc.b ^ 3 := one_le_pow₀ hb1
      nlinarith
    linarith

end GlobalTheory.GridReal
