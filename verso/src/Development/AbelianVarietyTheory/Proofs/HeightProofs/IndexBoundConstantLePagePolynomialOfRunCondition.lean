import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie

set_option autoImplicit false

namespace GlobalTheory.FinalJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

/- English proof (translation)
Establish `hZ1 : (1 : ℝ) ≤ Z` using `by linarith`. Establish `hZ0 : (0 : ℝ) ≤ Z` using `by linarith`. Establish `hC0 : (0 : ℝ) ≤ C` using `by linarith`. Establish `hu0 : (0 : ℝ) ≤ u` using `by linarith`. Establish `h34 : u ^ 3 ≤ 16 * Z ^ 5` using `(pow_le_pow_right₀ hu1 (by norm_num)).trans hu`.

Establish `hZ2 : (4000000 : ℝ) ≤ Z ^ 2` using `by nlinarith`. Establish `hW0 : 0 ≤ C * Z ^ 10` using `by positivity`. Establish `hW : 4000000 * (C * Z ^ 10) ≤ C * Z ^ 12`. Combine the equalities or inequalities in the displayed calculation. Establish `hk : ∀ k : ℕ, k ≤ 10 → Z ^ k ≤ C * Z ^ 10` using `fun k hk => (pow_le_pow_right₀ hZ1 hk).trans (le_mul_of_one_le_left (by positivity) hC)`.

Use `max_le ?_ (max_le ?_ ?_)` and prove the remaining obligations. Establish `hpi : Real.pi ≤ 4` using `Real.pi_le_four`. Establish `hpi0 : 0 ≤ Real.pi` using `Real.pi_pos.le`. Combine the equalities or inequalities in the displayed calculation. Establish `a1 : u ^ 4 * n ≤ (16 * Z ^ 5) * (C * Z ^ 4)` using `by gcongr`.

Establish `a2 : C * Z ^ 9 ≤ C * Z ^ 10` using `mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ1 (by norm_num)) hC0`. Establish `a3` using `hk 5 (by norm_num)`. Establish `a4 : (16 * Z ^ 5) * (C * Z ^ 4) = 16 * (C * Z ^ 9)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `a1 : r * u ^ 3 ≤ Z * (16 * Z ^ 5)` using `by gcongr`.

Establish `a3` using `hk 6 (by norm_num)`. Establish `a4 : Z * (16 * Z ^ 5) = 16 * Z ^ 6` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem indexBound_threeTerm_constant_le_real (n m4 u r C Z : ℝ) (hZ : 2000 ≤ Z) (hC : 1 ≤ C) (hn0 : 0 ≤ n) (hn : n ≤ C * Z ^ 4)
    (hm0 : 0 ≤ m4) (hm : m4 ≤ Z) (hu1 : 1 ≤ u) (hu : u ^ 4 ≤ 16 * Z ^ 5) (hr : r ≤ Z) :
    max (16200 * Real.pi * n * m4 * u ^ 4) (max (u ^ 4 * n + 2 * u ^ 3) (r * u ^ 3)) ≤ C * Z ^ 12 := by
  have hZ1 : (1 : ℝ) ≤ Z := by linarith
  have hZ0 : (0 : ℝ) ≤ Z := by linarith
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have h34 : u ^ 3 ≤ 16 * Z ^ 5 := (pow_le_pow_right₀ hu1 (by norm_num)).trans hu
  have hZ2 : (4000000 : ℝ) ≤ Z ^ 2 := by nlinarith
  have hW0 : 0 ≤ C * Z ^ 10 := by positivity
  have hW : 4000000 * (C * Z ^ 10) ≤ C * Z ^ 12 := by
    calc 4000000 * (C * Z ^ 10) ≤ Z ^ 2 * (C * Z ^ 10) := mul_le_mul_of_nonneg_right hZ2 hW0
      _ = C * Z ^ 12 := by ring
  have hk : ∀ k : ℕ, k ≤ 10 → Z ^ k ≤ C * Z ^ 10 := fun k hk =>
    (pow_le_pow_right₀ hZ1 hk).trans (le_mul_of_one_le_left (by positivity) hC)
  refine max_le ?_ (max_le ?_ ?_)
  · have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
    calc 16200 * Real.pi * n * m4 * u ^ 4 ≤ 16200 * 4 * (C * Z ^ 4) * Z * (16 * Z ^ 5) := by gcongr
      _ = 1036800 * (C * Z ^ 10) := by ring
      _ ≤ C * Z ^ 12 := by linarith
  · have a1 : u ^ 4 * n ≤ (16 * Z ^ 5) * (C * Z ^ 4) := by gcongr
    have a2 : C * Z ^ 9 ≤ C * Z ^ 10 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ1 (by norm_num)) hC0
    have a3 := hk 5 (by norm_num)
    have a4 : (16 * Z ^ 5) * (C * Z ^ 4) = 16 * (C * Z ^ 9) := by ring
    linarith
  · have a1 : r * u ^ 3 ≤ Z * (16 * Z ^ 5) := by gcongr
    have a3 := hk 6 (by norm_num)
    have a4 : Z * (16 * Z ^ 5) = 16 * Z ^ 6 := by ring
    linarith

/- English proof (translation)
Introduce `D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 _ hP`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, hnW, -, -, -, -, -, -, -, -, -, -, -, -, -, hd⟩` from `hP.hyp.2.1`. Rewrite `hd` using `[hP.tie.1]`. Establish `hA : 12 ≤ A2` using `hP.tie.2.2.2.2.2`. Take `⟨hC, hCZ, -, -, -, -, -, -, h12, -⟩` from `hd`.

Establish `e : Zb D large₂ = zBase large₂` using `rfl`. Rewrite `hCZ`, `h12` using `[e]`. Establish `hZ : 2000 ≤ zBase large₂`. Establish `h1 : (1000 : ℝ) ^ 20 ≤ C2 ^ 20` using `pow_le_pow_left₀ (by norm_num) hC 20`. Establish `h2 : (2000 : ℝ) ≤ 1000 ^ 20` using `by norm_num`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL : 1 ≤ large₂.sc.L`. Unfold `Scale.L`. Conclude with `Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le`. Establish `hfr : (D.R.f : ℝ) * D.R.r ≤ zBase large₂`.

Unfold `zBase`. Conclude with `le_mul_of_one_le_right (by positivity) hL`. Establish `hm1 : (1 : ℝ) ≤ (D.R.m : ℝ)`. Establish `: 1 ≤ D.R.m` using `by have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions.

Establish `hr1 : (1 : ℝ) ≤ (D.R.r : ℝ)`. Establish `: 1 ≤ D.R.r` using `by unfold Ranks.r; have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions. Establish `hf8 : (8 : ℝ) ≤ (D.R.f : ℝ)` using `by exact_mod_cast D.eight_le_f`. Establish `hf : (D.R.f : ℝ) ≤ zBase large₂` using `(le_mul_of_one_le_right (by positivity) hr1).trans hfr`.

Establish `hr : (D.R.r : ℝ) ≤ zBase large₂` using `(le_mul_of_one_le_left (by positivity) (by linarith)).trans hfr`. Establish `hm : (D.R.m : ℝ) ^ 4 ≤ zBase large₂` using `(lift_index_pow_four_le_degree hP.page).trans hf`. Establish `hu1 : 1 ≤ 2 * (D.R.f : ℝ) * (D.R.m : ℝ)` using `by nlinarith`. Establish `hu : (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤ 16 * zBase large₂ ^ 5`. Combine the equalities or inequalities in the displayed calculation.

Establish `key` using `indexBound_threeTerm_constant_le_real (nW : ℝ) ((D.R.m : ℝ) ^ 4) (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) (D.R.r : ℝ) C2 (zBase large₂) hZ (by linarith) (Nat.cast_nonneg _) (hnW.trans h12) (by positivity) hm hu1 hu hr`. Establish `hZA : zBase large₂ ^ (12 : ℕ) ≤ zBase large₂ ^ A2`. Combine the equalities or inequalities in the displayed calculation. Unfold `flipOneThree WeightFamilies.PPv`. Conclude with `key.trans (mul_le_mul_of_nonneg_left hZA (by linarith))`.
-/
theorem indexBoundConstant_le_pagePolynomial_of_runConditions : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), InR D j → PageRun large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → flipOneThree D nW ≤ WeightFamilies.PPv D large₂ C2 A2 := by
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 _ hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hnW, -, -, -, -, -, -, -, -, -, -, -, -, -, hd⟩ := hP.hyp.2.1
  rw [hP.tie.1] at hd
  have hA : 12 ≤ A2 := hP.tie.2.2.2.2.2
  obtain ⟨hC, hCZ, -, -, -, -, -, -, h12, -⟩ := hd
  have e : Zb D large₂ = zBase large₂ := rfl
  rw [e] at hCZ h12
  have hZ : 2000 ≤ zBase large₂ := by
    have h1 : (1000 : ℝ) ^ 20 ≤ C2 ^ 20 := pow_le_pow_left₀ (by norm_num) hC 20
    have h2 : (2000 : ℝ) ≤ 1000 ^ 20 := by norm_num
    linarith
  have hL : 1 ≤ large₂.sc.L := by
    unfold Scale.L; exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hfr : (D.R.f : ℝ) * D.R.r ≤ zBase large₂ := by
    unfold zBase
    exact le_mul_of_one_le_right (by positivity) hL
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hf8 : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
  have hf : (D.R.f : ℝ) ≤ zBase large₂ := (le_mul_of_one_le_right (by positivity) hr1).trans hfr
  have hr : (D.R.r : ℝ) ≤ zBase large₂ := (le_mul_of_one_le_left (by positivity) (by linarith)).trans hfr
  have hm : (D.R.m : ℝ) ^ 4 ≤ zBase large₂ := (lift_index_pow_four_le_degree hP.page).trans hf
  have hu1 : 1 ≤ 2 * (D.R.f : ℝ) * (D.R.m : ℝ) := by nlinarith
  have hu : (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤ 16 * zBase large₂ ^ 5 := by
    calc (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 = 16 * ((D.R.f : ℝ) ^ 4 * (D.R.m : ℝ) ^ 4) := by ring
      _ ≤ 16 * (zBase large₂ ^ 4 * zBase large₂) := by gcongr
      _ = 16 * zBase large₂ ^ 5 := by ring
  have key := indexBound_threeTerm_constant_le_real (nW : ℝ) ((D.R.m : ℝ) ^ 4) (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) (D.R.r : ℝ) C2 (zBase large₂) hZ
    (by linarith) (Nat.cast_nonneg _) (hnW.trans h12) (by positivity) hm hu1 hu hr
  have hZA : zBase large₂ ^ (12 : ℕ) ≤ zBase large₂ ^ A2 := by
    calc zBase large₂ ^ (12 : ℕ) = zBase large₂ ^ ((12 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ zBase large₂ ^ A2 := Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast hA)
  unfold flipOneThree WeightFamilies.PPv
  exact key.trans (mul_le_mul_of_nonneg_left hZA (by linarith))

end GlobalTheory.FinalJoin
