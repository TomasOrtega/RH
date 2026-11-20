import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

/- English proof (translation)
Establish `hfr : 12 ≤ f * r` using `by nlinarith`. Establish `hrf : r ≤ f * r` using `by nlinarith`. Take `⟨F, hF⟩ : ∃ F, F = f * r` from `⟨_, rfl⟩`. Rewrite `hfr`, `hrf`, `hs` using `[← hF]`. Establish `hFn : F ≤ F * n` using `by nlinarith`.

Establish `hnF : n ≤ F * n` using `by nlinarith`. Establish `hs3 : 13 ≤ s` using `by linarith`. Establish `hAs : A ≤ s` using `by linarith`. Establish `hns : n ≤ s` using `by linarith`. Establish `hFns : F * n ≤ s` using `by linarith`.

Establish `hZ : 24 ≤ F * L` using `by nlinarith`. Establish `hLZ : L ≤ F * L` using `by nlinarith`. Establish `hrL : r * L ≤ F * L` using `by nlinarith`. Establish `hZs : 24 ≤ F * L * s` using `by nlinarith`. Establish `h1 : r * L * A ≤ F * L * s` using `mul_le_mul hrL hAs hA (by linarith)`.

Establish `h2 : L * A ≤ F * L * s` using `mul_le_mul hLZ hAs hA (by linarith)`. Establish `h3 : F * L * n ≤ F * L * s` using `mul_le_mul_of_nonneg_left hns (by linarith)`. Establish `hLs : 0 ≤ L * s` using `by positivity`. Establish `hM0 : 0 ≤ M` using `by linarith`. Establish `hMs : M * 13 ≤ M * s` using `mul_le_mul_of_nonneg_left hs3 hM0`.

Establish `hlams : 0 ≤ lam * s` using `by positivity`. Establish `hlps : 0 ≤ lp * s` using `by positivity`. Establish `h4 : 12 * (lam * s) ≤ F * (lam * s)` using `mul_le_mul_of_nonneg_right hfr hlams`. Establish `h5 : 12 * (lp * s) ≤ F * (lp * s)` using `mul_le_mul_of_nonneg_right hfr hlps`. Establish `e : (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s = 1040 * (F * L * s) + 3 * (L * s) + 2 * (M * s) + 2 * (F * (lam * s)) + 4 * (F * (lp * s))`.

Rewrite using `[hF]`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : 400 * (f * r * L) * s = 400 * (F * L * s)` using `by rw [hF]; ring`. Establish `e2 : 200 * f * r * n * L = 200 * (F * L * n)` using `by rw [hF]; ring`. Establish `e3 : 3 * f * r * n * L = 3 * (F * L * n)` using `by rw [hF]; ring`.

Establish `e4 : 140 * r * L * A = 140 * (r * L * A)` using `by ring`. Establish `e5 : 10 * L * A = 10 * (L * A)` using `by ring`. Establish `e6 : 2 * (lam + 2 * lp) * s = 2 * (lam * s) + 4 * (lp * s)` using `by ring`. Establish `e7 : (lam + 2 * lp) * s = lam * s + 2 * (lp * s)` using `by ring`. Rewrite using `[e, e1, e2, e3, e4, e5, e6, e7]`.

Use `⟨by linarith, by linarith, by linarith⟩` and prove the remaining obligations.
-/
theorem gc_arith (f r L A n s lam lp a b M : ℝ) (hf : 2 ≤ f) (hr : 6 ≤ r) (hL : 2 ≤ L) (hA : 0 ≤ A)
    (hn : 1 ≤ n) (hs : A + f * r * n + 1 ≤ s) (hlam : 0 ≤ lam) (hlp : 0 ≤ lp) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : a + b ≤ M) :
    (140 * r * L * A + 10 * L * A + 200 * f * r * n * L ≤ 400 * (f * r * L) * s) ∧
    (2 * (lam + 2 * lp) * s + 400 * (f * r * L) * s + lam * s ≤
      (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s) ∧
    ((lam + 2 * lp) * s + (400 * (f * r * L) * s + 3 * f * r * n * L + 5 * a + b + 2) ≤
      (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s) := by
  have hfr : 12 ≤ f * r := by nlinarith
  have hrf : r ≤ f * r := by nlinarith
  obtain ⟨F, hF⟩ : ∃ F, F = f * r := ⟨_, rfl⟩
  rw [← hF] at hfr hrf hs
  have hFn : F ≤ F * n := by nlinarith
  have hnF : n ≤ F * n := by nlinarith
  have hs3 : 13 ≤ s := by linarith
  have hAs : A ≤ s := by linarith
  have hns : n ≤ s := by linarith
  have hFns : F * n ≤ s := by linarith
  have hZ : 24 ≤ F * L := by nlinarith
  have hLZ : L ≤ F * L := by nlinarith
  have hrL : r * L ≤ F * L := by nlinarith
  have hZs : 24 ≤ F * L * s := by nlinarith
  have h1 : r * L * A ≤ F * L * s := mul_le_mul hrL hAs hA (by linarith)
  have h2 : L * A ≤ F * L * s := mul_le_mul hLZ hAs hA (by linarith)
  have h3 : F * L * n ≤ F * L * s := mul_le_mul_of_nonneg_left hns (by linarith)
  have hLs : 0 ≤ L * s := by positivity
  have hM0 : 0 ≤ M := by linarith
  have hMs : M * 13 ≤ M * s := mul_le_mul_of_nonneg_left hs3 hM0
  have hlams : 0 ≤ lam * s := by positivity
  have hlps : 0 ≤ lp * s := by positivity
  have h4 : 12 * (lam * s) ≤ F * (lam * s) := mul_le_mul_of_nonneg_right hfr hlams
  have h5 : 12 * (lp * s) ≤ F * (lp * s) := mul_le_mul_of_nonneg_right hfr hlps
  have e : (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s =
      1040 * (F * L * s) + 3 * (L * s) + 2 * (M * s) + 2 * (F * (lam * s)) + 4 * (F * (lp * s)) := by
    rw [hF]; ring
  have e1 : 400 * (f * r * L) * s = 400 * (F * L * s) := by rw [hF]; ring
  have e2 : 200 * f * r * n * L = 200 * (F * L * n) := by rw [hF]; ring
  have e3 : 3 * f * r * n * L = 3 * (F * L * n) := by rw [hF]; ring
  have e4 : 140 * r * L * A = 140 * (r * L * A) := by ring
  have e5 : 10 * L * A = 10 * (L * A) := by ring
  have e6 : 2 * (lam + 2 * lp) * s = 2 * (lam * s) + 4 * (lp * s) := by ring
  have e7 : (lam + 2 * lp) * s = lam * s + 2 * (lp * s) := by ring
  rw [e, e1, e2, e3, e4, e5, e6, e7]
  refine ⟨by linarith, by linarith, by linarith⟩

/- English proof (translation)
Unfold `lamStar`. Establish `h1 : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1)`. Use `Real.log_natCast_nonneg (D.host.g 0 * D.host.g 1)` as an intermediate fact. Simplify `this` using `only [Nat.cast_mul]`. Establish `h2 : 0 ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d)`.

Use `Real.log_natCast_nonneg (D.R.f ^ 2 * D.host.q * D.host.d)` as an intermediate fact. Establish `e : 4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d = ((D.R.f ^ 2 * D.host.q * D.host.d : ℕ) : ℝ)` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lamStar_nonneg_nat (D : D7) : 0 ≤ lamStar D := by
  unfold lamStar
  have h1 : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by
    have := Real.log_natCast_nonneg (D.host.g 0 * D.host.g 1)
    simpa only [Nat.cast_mul] using this
  have h2 : 0 ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) := by
    have := Real.log_natCast_nonneg (D.R.f ^ 2 * D.host.q * D.host.d)
    have e : 4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d =
        ((D.R.f ^ 2 * D.host.q * D.host.d : ℕ) : ℝ) := by push_cast; ring
    rw [e]; exact this
  linarith

/- English proof (translation)
Introduce `D B large₂ j w p hL hn`. Establish `hf : (2 : ℝ) ≤ D.R.f`. Establish `: 2 ≤ D.R.f`. Unfold `Ranks.f Ranks.n`. Use `And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions. Establish `hr : (6 : ℝ) ≤ D.R.r`. Establish `: 6 ≤ D.R.r`. Unfold `Ranks.r`.

Use `D.R.two_le_m` as an intermediate fact. Use `D.R.m_add_three_le_k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions. Establish `hA : 0 ≤ absA w` using `by unfold absA; positivity`.

Establish `hn' : (1 : ℝ) ≤ w.n` using `by exact_mod_cast hn`. Establish `hs : absA w + (D.R.f : ℝ) * D.R.r * w.n + 1 ≤ w.size`. Unfold `WeightFamilies.Wt.size absA`. Establish `hm : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ)` using `by exact_mod_cast le_max_right _ _`. Establish `h0 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n` using `by positivity`.

Establish `: (D.R.f : ℝ) * D.R.r * w.n ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ)`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hm h0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb : 0 ≤ Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO`. Apply `div_nonneg _ (Nat.cast_nonneg _)` to reduce the goal to its premises.

Rewrite using `[Real.log_abs]`. Conclude with `Real.log_intCast_nonneg _`. Unfold `WeightAlgebra.Gc Zb`. Conclude with `gc_arith _ _ _ _ _ _ _ _ _ _ _ hf hr hL hA hn' hs (lamStar_nonneg_nat D) (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg _) hb (le_max_left _ _)`.
-/
theorem sup_bounds_le_Gc : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (p : ℕ), 2 ≤ large₂.sc.L → 0 < w.n → (140 * D.R.r * large₂.sc.L * absA w + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L ≤ 400 * Zb D large₂ * w.size) ∧ (2 * (lamStar D + 2 * Real.log p) * w.size + 400 * Zb D large₂ * w.size + lamStar D * w.size ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) ∧ ((lamStar D + 2 * Real.log p) * w.size + (400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO + 2) ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) := by
  intro D B large₂ j w p hL hn
  have hf : (2 : ℝ) ≤ D.R.f := by
    have : 2 ≤ D.R.f := by
      unfold Ranks.f Ranks.n
      have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity)
      omega
    exact_mod_cast this
  have hr : (6 : ℝ) ≤ D.R.r := by
    have : 6 ≤ D.R.r := by
      unfold Ranks.r
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      omega
    exact_mod_cast this
  have hA : 0 ≤ absA w := by unfold absA; positivity
  have hn' : (1 : ℝ) ≤ w.n := by exact_mod_cast hn
  have hs : absA w + (D.R.f : ℝ) * D.R.r * w.n + 1 ≤ w.size := by
    unfold WeightFamilies.Wt.size absA
    have hm : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n := by positivity
    have : (D.R.f : ℝ) * D.R.r * w.n ≤
        (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hm h0]
    linarith
  have hb : 0 ≤ Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    rw [Real.log_abs]
    exact Real.log_intCast_nonneg _
  unfold WeightAlgebra.Gc Zb
  exact gc_arith _ _ _ _ _ _ _ _ _ _ _ hf hr hL hA hn' hs (lamStar_nonneg_nat D)
    (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg _) hb (le_max_left _ _)

end GlobalTheory.RunIn
