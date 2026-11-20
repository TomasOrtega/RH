import Formalism.HermitianCurvature.BigCellVanishingOfCommute

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Introduce `r i a _ hai`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem fibre_chain_expansion : C6.FibChainExp := by
  intro r i a _ hai; nlinarith

/- English proof (translation)
Introduce `r i hi`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem fibre_expansion_identity : C6.FibExpText := by
  intro r i hi; nlinarith

/- English proof (translation)
Introduce `h`. Use `h 0 0` as an intermediate fact. Evaluate the numerical expressions using `at this`.
-/
theorem fibre_expansion_zero_fails : C6.FibExpZeroFails := by
  intro h; have := h 0 0; norm_num at this

/- English proof (translation)
Introduce `Cb CV hCb`. Use `⟨Cb ^ 2 + 3 * Cb + 6 * CV + 1, ?_⟩` and prove the remaining obligations. Introduce `r n N o κ As A₀ hr hn h1 h2 ho hκ hA`. Unfold `C6.AV C6.mmV`. Use `push_cast`.

Establish `hx : (1:ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hxy : 2 * (r:ℝ) + 2 ≤ n` using `by exact_mod_cast hn`. Establish `h1' : (N:ℝ) * (n:ℝ) ^ 2 ≤ As` using `by exact_mod_cast h1`. Establish `h2' : (n:ℝ) ^ 3 ≤ As` using `by exact_mod_cast h2`. Establish `hV : (0:ℝ) ≤ CV` using `by positivity`.

Establish `hN : (0:ℝ) ≤ N` using `by positivity`. Establish `hy : (1:ℝ) ≤ n` using `by linarith`. Establish `hn2 : (n:ℝ) ^ 2 ≤ As` using `le_trans (by nlinarith) h2'`. Establish `hn1 : (n:ℝ) ≤ As` using `le_trans (by nlinarith) hn2`. Establish `hR3 : ((r:ℝ) + 1) ^ 3 ≤ As` using `le_trans (pow_le_pow_left₀ (by positivity) (by linarith) 3) h2'`.

Establish `hr3 : (r:ℝ) ^ 3 ≤ As` using `le_trans (pow_le_pow_left₀ (by positivity) (by linarith) 3) hR3`. Establish `hNn : (N:ℝ) * n ≤ As` using `le_trans (mul_le_mul_of_nonneg_left (by nlinarith) hN) h1'`. Establish `ho' : (o:ℝ) ≤ Cb * As`. Combine the equalities or inequalities in the displayed calculation. Establish `hAs0 : (0:ℝ) ≤ As` using `le_trans (by positivity) hn1`.

Use `set P : ℝ := ((r:ℝ) + 1) ^ 4 * As with hP`. Establish `hR4 : (1:ℝ) ≤ ((r:ℝ) + 1) ^ 4` using `one_le_pow₀ (by linarith)`. Establish `hP1 : (As:ℝ) ≤ P` using `by nlinarith`. Establish `hRR : (r:ℝ) + 1 ≤ ((r:ℝ) + 1) ^ 4`. Combine the equalities or inequalities in the displayed calculation.

Establish `hP2 : ((r:ℝ) + 1) * As ≤ P` using `mul_le_mul_of_nonneg_right hRR hAs0`. Establish `hx4 : (r:ℝ) ^ 4 ≤ ((r:ℝ) + 1) ^ 4` using `pow_le_pow_left₀ (by positivity) (by linarith) 4`. Establish `hP3 : (r:ℝ) ^ 4 * n ≤ P` using `mul_le_mul hx4 hn1 (by positivity) (by positivity)`. Establish `hP4 : (r:ℝ) * n ^ 2 ≤ P` using `mul_le_mul (by linarith) hn2 (by positivity) (by positivity)`. Establish `hx2 : (r:ℝ) ^ 2 ≤ ((r:ℝ) + 1) ^ 4`.

Combine the equalities or inequalities in the displayed calculation. Establish `hP5 : (r:ℝ) ^ 5 ≤ P`. Establish `: (r:ℝ) ^ 5 = (r:ℝ) ^ 2 * (r:ℝ) ^ 3` using `by ring`. Rewrite using `[this]; exact mul_le_mul hx2 hr3 (by positivity) (by positivity)`. Establish `hP6 : ((r:ℝ) + 1) * ((r:ℝ) ^ 2 + 1) ≤ P`.

Establish `: ((r:ℝ) + 1) * ((r:ℝ) ^ 2 + 1) ≤ ((r:ℝ) + 1) ^ 3` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hκ' : (κ:ℝ) ≤ Cb ^ 2 * P`. Establish `a1 : (κ:ℝ) ≤ Cb * ((r:ℝ) + 1) * (Cb * As)` using `le_trans hκ (mul_le_mul_of_nonneg_left ho' (by positivity))`. Establish `a2 : Cb * ((r:ℝ) + 1) * (Cb * As) = Cb ^ 2 * (((r:ℝ) + 1) * As)` using `by ring`.

Rewrite `a1` using `[a2]`. Conclude with `le_trans a1 (mul_le_mul_of_nonneg_left hP2 (by positivity))`. Establish `hoR : ((r:ℝ) + 1) * o ≤ Cb * P`. Combine the equalities or inequalities in the displayed calculation. Establish `hP0 : 0 ≤ P` using `by positivity`.

Establish `e1 : (r:ℝ) * (CV * ((r:ℝ) ^ 3 * n + (n:ℝ) ^ 2 + (r:ℝ) ^ 4)) = CV * ((r:ℝ) ^ 4 * n) + CV * ((r:ℝ) * n ^ 2) + CV * (r:ℝ) ^ 5` using `by ring`. Establish `e2 : 3 * ((r:ℝ) + 1) * (CV * ((r:ℝ) ^ 2 + 1) + o) = 3 * CV * (((r:ℝ) + 1) * ((r:ℝ) ^ 2 + 1)) + 3 * (((r:ℝ) + 1) * o)` using `by ring`. Rewrite using `[e1, e2]`. Use `mul_le_mul_of_nonneg_left hP3 hV` as an intermediate fact. Use `mul_le_mul_of_nonneg_left hP4 hV` as an intermediate fact.

Use `mul_le_mul_of_nonneg_left hP5 hV` as an intermediate fact. Use `mul_le_mul_of_nonneg_left hP6 (by positivity : (0:ℝ) ≤ 3 * CV)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem c6_budgetArith_proof : C6.BudgetArith := by
  intro Cb CV hCb
  refine ⟨Cb ^ 2 + 3 * Cb + 6 * CV + 1, ?_⟩
  intro r n N o κ As A₀ hr hn h1 h2 ho hκ hA
  unfold C6.AV C6.mmV
  push_cast
  have hx : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hxy : 2 * (r:ℝ) + 2 ≤ n := by exact_mod_cast hn
  have h1' : (N:ℝ) * (n:ℝ) ^ 2 ≤ As := by exact_mod_cast h1
  have h2' : (n:ℝ) ^ 3 ≤ As := by exact_mod_cast h2
  have hV : (0:ℝ) ≤ CV := by positivity
  have hN : (0:ℝ) ≤ N := by positivity
  have hy : (1:ℝ) ≤ n := by linarith
  have hn2 : (n:ℝ) ^ 2 ≤ As := le_trans (by nlinarith) h2'
  have hn1 : (n:ℝ) ≤ As := le_trans (by nlinarith) hn2
  have hR3 : ((r:ℝ) + 1) ^ 3 ≤ As := le_trans (pow_le_pow_left₀ (by positivity) (by linarith) 3) h2'
  have hr3 : (r:ℝ) ^ 3 ≤ As := le_trans (pow_le_pow_left₀ (by positivity) (by linarith) 3) hR3
  have hNn : (N:ℝ) * n ≤ As := le_trans (mul_le_mul_of_nonneg_left (by nlinarith) hN) h1'
  have ho' : (o:ℝ) ≤ Cb * As := by
    calc (o:ℝ) ≤ Cb * N * n := ho
      _ = Cb * (N * n) := by ring
      _ ≤ Cb * As := mul_le_mul_of_nonneg_left hNn hCb
  have hAs0 : (0:ℝ) ≤ As := le_trans (by positivity) hn1
  set P : ℝ := ((r:ℝ) + 1) ^ 4 * As with hP
  have hR4 : (1:ℝ) ≤ ((r:ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)
  have hP1 : (As:ℝ) ≤ P := by nlinarith
  have hRR : (r:ℝ) + 1 ≤ ((r:ℝ) + 1) ^ 4 := by
    calc (r:ℝ) + 1 = ((r:ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hP2 : ((r:ℝ) + 1) * As ≤ P := mul_le_mul_of_nonneg_right hRR hAs0
  have hx4 : (r:ℝ) ^ 4 ≤ ((r:ℝ) + 1) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hP3 : (r:ℝ) ^ 4 * n ≤ P := mul_le_mul hx4 hn1 (by positivity) (by positivity)
  have hP4 : (r:ℝ) * n ^ 2 ≤ P := mul_le_mul (by linarith) hn2 (by positivity) (by positivity)
  have hx2 : (r:ℝ) ^ 2 ≤ ((r:ℝ) + 1) ^ 4 := by
    calc (r:ℝ) ^ 2 ≤ ((r:ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hP5 : (r:ℝ) ^ 5 ≤ P := by
    have : (r:ℝ) ^ 5 = (r:ℝ) ^ 2 * (r:ℝ) ^ 3 := by ring
    rw [this]; exact mul_le_mul hx2 hr3 (by positivity) (by positivity)
  have hP6 : ((r:ℝ) + 1) * ((r:ℝ) ^ 2 + 1) ≤ P := by
    have : ((r:ℝ) + 1) * ((r:ℝ) ^ 2 + 1) ≤ ((r:ℝ) + 1) ^ 3 := by nlinarith
    linarith
  have hκ' : (κ:ℝ) ≤ Cb ^ 2 * P := by
    have a1 : (κ:ℝ) ≤ Cb * ((r:ℝ) + 1) * (Cb * As) :=
      le_trans hκ (mul_le_mul_of_nonneg_left ho' (by positivity))
    have a2 : Cb * ((r:ℝ) + 1) * (Cb * As) = Cb ^ 2 * (((r:ℝ) + 1) * As) := by ring
    rw [a2] at a1
    exact le_trans a1 (mul_le_mul_of_nonneg_left hP2 (by positivity))
  have hoR : ((r:ℝ) + 1) * o ≤ Cb * P := by
    calc ((r:ℝ) + 1) * o ≤ ((r:ℝ) + 1) * (Cb * As) := mul_le_mul_of_nonneg_left ho' (by positivity)
      _ = Cb * (((r:ℝ) + 1) * As) := by ring
      _ ≤ Cb * P := mul_le_mul_of_nonneg_left hP2 hCb
  have hP0 : 0 ≤ P := by positivity
  have e1 : (r:ℝ) * (CV * ((r:ℝ) ^ 3 * n + (n:ℝ) ^ 2 + (r:ℝ) ^ 4)) =
      CV * ((r:ℝ) ^ 4 * n) + CV * ((r:ℝ) * n ^ 2) + CV * (r:ℝ) ^ 5 := by ring
  have e2 : 3 * ((r:ℝ) + 1) * (CV * ((r:ℝ) ^ 2 + 1) + o) =
      3 * CV * (((r:ℝ) + 1) * ((r:ℝ) ^ 2 + 1)) + 3 * (((r:ℝ) + 1) * o) := by ring
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left hP3 hV
  have := mul_le_mul_of_nonneg_left hP4 hV
  have := mul_le_mul_of_nonneg_left hP5 hV
  have := mul_le_mul_of_nonneg_left hP6 (by positivity : (0:ℝ) ≤ 3 * CV)
  nlinarith

/- English proof (translation)
Introduce `c₃ Cb hc hCb`. Use `⟨c₃ * Cb + 2 * c₃ + 3 * Cb + 4, ?_⟩` and prove the remaining obligations. Introduce `r n N o As A₀ hr hn h1 h2 ho hA`. Establish `hx : (1:ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hxy : 2 * (r:ℝ) + 2 ≤ n` using `by exact_mod_cast hn`.

Establish `h1' : (N:ℝ) * (n:ℝ) ^ 2 ≤ As` using `by exact_mod_cast h1`. Establish `h2' : (n:ℝ) ^ 3 ≤ As` using `by exact_mod_cast h2`. Establish `hN : (0:ℝ) ≤ N` using `by positivity`. Establish `hy : (1:ℝ) ≤ n` using `by linarith`. Establish `hn2 : (n:ℝ) ^ 2 ≤ As` using `le_trans (by nlinarith) h2'`.

Establish `hn1 : (n:ℝ) ≤ As` using `le_trans (by nlinarith) hn2`. Establish `hA1 : (1:ℝ) ≤ As` using `le_trans hy hn1`. Establish `hNn : (N:ℝ) * n ≤ As` using `le_trans (mul_le_mul_of_nonneg_left (by nlinarith) hN) h1'`. Establish `ho' : (o:ℝ) ≤ Cb * As`. Combine the equalities or inequalities in the displayed calculation.

Use `set P : ℝ := ((r:ℝ) + 1) ^ 4 * As with hP`. Establish `hAs0 : (0:ℝ) ≤ As` using `by linarith`. Establish `q2 : ((r:ℝ) + 1) ^ 2 ≤ ((r:ℝ) + 1) ^ 4` using `pow_le_pow_right₀ (by linarith) (by norm_num)`. Establish `q3 : ((r:ℝ) + 1) ^ 3 ≤ ((r:ℝ) + 1) ^ 4` using `pow_le_pow_right₀ (by linarith) (by norm_num)`. Establish `q1 : ((r:ℝ) + 1) ≤ ((r:ℝ) + 1) ^ 4`.

Combine the equalities or inequalities in the displayed calculation. Establish `hR4 : (1:ℝ) ≤ ((r:ℝ) + 1) ^ 4` using `one_le_pow₀ (by linarith)`. Establish `p1 : ((r:ℝ) + 1) ^ 2 * o ≤ Cb * P`. Combine the equalities or inequalities in the displayed calculation. Establish `p2 : ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n) ≤ P`.

Establish `: (r:ℝ) * n ≤ ((r:ℝ) + 1) * As` using `mul_le_mul (by linarith) hn1 (by positivity) (by positivity)`. Combine the equalities or inequalities in the displayed calculation. Establish `p3 : ((r:ℝ) + 1) ^ 2 ≤ P`. Combine the equalities or inequalities in the displayed calculation. Establish `p4 : ((r:ℝ) + 1) * o ≤ Cb * P`.

Combine the equalities or inequalities in the displayed calculation. Establish `p5 : ((r:ℝ) + 1) ≤ P`. Combine the equalities or inequalities in the displayed calculation. Establish `hP0 : 0 ≤ P` using `by positivity`. Establish `e : c₃ * ((r:ℝ) + 1) ^ 2 * ((o:ℝ) + r * n + 1) = c₃ * (((r:ℝ) + 1) ^ 2 * o) + c₃ * (((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n)) + c₃ * ((r:ℝ) + 1) ^ 2` using `by ring`.

Establish `e' : 3 * ((r:ℝ) + 1) * ((o:ℝ) + 1) = 3 * (((r:ℝ) + 1) * o) + 3 * ((r:ℝ) + 1)` using `by ring`. Rewrite using `[e, e']`. Use `mul_le_mul_of_nonneg_left p1 hc` as an intermediate fact. Use `mul_le_mul_of_nonneg_left p2 hc` as an intermediate fact. Use `mul_le_mul_of_nonneg_left p3 hc` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem big_cell_threshold : C6.BigCellVanishingThreshold := by
  intro c₃ Cb hc hCb
  refine ⟨c₃ * Cb + 2 * c₃ + 3 * Cb + 4, ?_⟩
  intro r n N o As A₀ hr hn h1 h2 ho hA
  have hx : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hxy : 2 * (r:ℝ) + 2 ≤ n := by exact_mod_cast hn
  have h1' : (N:ℝ) * (n:ℝ) ^ 2 ≤ As := by exact_mod_cast h1
  have h2' : (n:ℝ) ^ 3 ≤ As := by exact_mod_cast h2
  have hN : (0:ℝ) ≤ N := by positivity
  have hy : (1:ℝ) ≤ n := by linarith
  have hn2 : (n:ℝ) ^ 2 ≤ As := le_trans (by nlinarith) h2'
  have hn1 : (n:ℝ) ≤ As := le_trans (by nlinarith) hn2
  have hA1 : (1:ℝ) ≤ As := le_trans hy hn1
  have hNn : (N:ℝ) * n ≤ As := le_trans (mul_le_mul_of_nonneg_left (by nlinarith) hN) h1'
  have ho' : (o:ℝ) ≤ Cb * As := by
    calc (o:ℝ) ≤ Cb * N * n := ho
      _ = Cb * (N * n) := by ring
      _ ≤ Cb * As := mul_le_mul_of_nonneg_left hNn hCb
  set P : ℝ := ((r:ℝ) + 1) ^ 4 * As with hP
  have hAs0 : (0:ℝ) ≤ As := by linarith
  have q2 : ((r:ℝ) + 1) ^ 2 ≤ ((r:ℝ) + 1) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have q3 : ((r:ℝ) + 1) ^ 3 ≤ ((r:ℝ) + 1) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have q1 : ((r:ℝ) + 1) ≤ ((r:ℝ) + 1) ^ 4 := by
    calc (r:ℝ) + 1 = ((r:ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hR4 : (1:ℝ) ≤ ((r:ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)

  have p1 : ((r:ℝ) + 1) ^ 2 * o ≤ Cb * P := by
    calc ((r:ℝ) + 1) ^ 2 * o ≤ ((r:ℝ) + 1) ^ 4 * (Cb * As) := mul_le_mul q2 ho' (by positivity) (by positivity)
      _ = Cb * P := by rw [hP]; ring
  have p2 : ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n) ≤ P := by
    have : (r:ℝ) * n ≤ ((r:ℝ) + 1) * As := mul_le_mul (by linarith) hn1 (by positivity) (by positivity)
    calc ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n) ≤ ((r:ℝ) + 1) ^ 2 * (((r:ℝ) + 1) * As) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ((r:ℝ) + 1) ^ 3 * As := by ring
      _ ≤ P := mul_le_mul_of_nonneg_right q3 hAs0
  have p3 : ((r:ℝ) + 1) ^ 2 ≤ P := by
    calc ((r:ℝ) + 1) ^ 2 = ((r:ℝ) + 1) ^ 2 * 1 := by ring
      _ ≤ ((r:ℝ) + 1) ^ 4 * As := mul_le_mul q2 hA1 (by norm_num) (by positivity)
  have p4 : ((r:ℝ) + 1) * o ≤ Cb * P := by
    calc ((r:ℝ) + 1) * o ≤ ((r:ℝ) + 1) ^ 4 * (Cb * As) := mul_le_mul q1 ho' (by positivity) (by positivity)
      _ = Cb * P := by rw [hP]; ring
  have p5 : ((r:ℝ) + 1) ≤ P := by
    calc ((r:ℝ) + 1) = ((r:ℝ) + 1) * 1 := by ring
      _ ≤ ((r:ℝ) + 1) ^ 4 * As := mul_le_mul q1 hA1 (by norm_num) (by positivity)
  have hP0 : 0 ≤ P := by positivity
  have e : c₃ * ((r:ℝ) + 1) ^ 2 * ((o:ℝ) + r * n + 1) =
      c₃ * (((r:ℝ) + 1) ^ 2 * o) + c₃ * (((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n)) + c₃ * ((r:ℝ) + 1) ^ 2 := by ring
  have e' : 3 * ((r:ℝ) + 1) * ((o:ℝ) + 1) = 3 * (((r:ℝ) + 1) * o) + 3 * ((r:ℝ) + 1) := by ring
  rw [e, e']
  have := mul_le_mul_of_nonneg_left p1 hc
  have := mul_le_mul_of_nonneg_left p2 hc
  have := mul_le_mul_of_nonneg_left p3 hc
  nlinarith

end Formalism.FourierDecayAlt.P
