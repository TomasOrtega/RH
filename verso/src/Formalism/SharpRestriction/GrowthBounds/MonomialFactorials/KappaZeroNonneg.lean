import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

/- English proof (translation)
Establish `hA0 : 0 ≤ 3 * (s + 2) * r ^ 2 * L` using `by positivity`. Establish `hB0 : 0 ≤ N * (r + 1) ^ 2 * L`. Establish `: 0 ≤ N` using `by linarith`. Check the signs of the components of the expression. Establish `hA : 3 * (s + 2) * r ^ 2 * L ≤ 9 * (N * (r + 1) ^ 2 * L)`.

Establish `h1 : s + 2 ≤ 3 * N` using `by linarith`. Establish `h2 : r ^ 2 ≤ (r + 1) ^ 2` using `by nlinarith`. Establish `h3 : (s + 2) * r ^ 2 ≤ (3 * N) * (r + 1) ^ 2` using `mul_le_mul h1 h2 (by positivity) (by linarith)`. Establish `h4` using `mul_le_mul_of_nonneg_right h3 hL`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `htA : t * (3 * (s + 2) * r ^ 2 * L) ≤ N * (9 * (N * (r + 1) ^ 2 * L))` using `mul_le_mul (by linarith) hA hA0 (by linarith)`. Establish `k1` using `mul_le_mul_of_nonneg_left htA (sq_nonneg Y)`. Establish `hYCM : 0 ≤ Y * CM` using `mul_nonneg (by linarith) hCM`. Establish `k2` using `mul_le_mul_of_nonneg_left htA hYCM`. Establish `k3` using `mul_le_mul_of_nonneg_left hA hYCM`.

Establish `k4 : 10 * (s + 1) * (r + 1) * L ≤ 20 * (N * (r + 1) ^ 2 * L)`. Establish `h1 : s + 1 ≤ 2 * N` using `by linarith`. Establish `h2 : r + 1 ≤ (r + 1) ^ 2` using `by nlinarith`. Establish `h3 : (s + 1) * (r + 1) ≤ (2 * N) * (r + 1) ^ 2` using `mul_le_mul h1 h2 (by linarith) (by linarith)`. Establish `h4` using `mul_le_mul_of_nonneg_right h3 hL`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hY2 : Y ≤ Y ^ 2` using `by nlinarith`. Establish `h5` using `mul_le_mul_of_nonneg_left hN (sq_nonneg Y)`. Establish `hYN : Y * N ≤ Y ^ 2 * N` using `mul_le_mul_of_nonneg_right hY2 (by linarith)`. Establish `hY1 : Y ≤ Y ^ 2 * N` using `by linarith`.

Establish `h1P : 1 ≤ Y ^ 2 * N` using `by nlinarith`. Establish `hc0 : 0 ≤ CM * (9 * (N * (r + 1) ^ 2 * L))` using `mul_nonneg hCM (by linarith)`. Establish `m1` using `mul_le_mul_of_nonneg_left hYN hc0`. Establish `m2` using `mul_le_mul_of_nonneg_left hY1 hc0`. Establish `m3` using `mul_le_mul_of_nonneg_left h1P (by linarith : (0:ℝ) ≤ 20 * (N * (r + 1) ^ 2 * L))`.

Establish `hP0 : 0 ≤ Y ^ 2 * N * (N * (r + 1) ^ 2 * L)` using `mul_nonneg (by linarith) hB0`. Establish `m4` using `mul_le_mul_of_nonneg_right (by linarith : 29 + 18 * CM ≤ C) hP0`. Combine the linear relations using `[k1, k2, k3, k4, m1, m2, m3, m4]`.
-/
theorem depth_num (Y N s t r L CM C : ℝ) (hY : 1 ≤ Y) (hN : 1 ≤ N) (hs0 : 0 ≤ s) (hs : s ≤ N) (ht0 : 0 ≤ t)
    (ht : t ≤ s) (hr : 0 ≤ r) (hL : 0 ≤ L) (hCM : 0 ≤ CM) (hC : 18 * (1 + CM) + 20 ≤ C) :
    Y * (t * (Y * (3 * (s + 2) * r ^ 2 * L) + CM * (3 * (s + 2) * r ^ 2 * L)) + CM * (3 * (s + 2) * r ^ 2 * L)) +
      10 * (s + 1) * (r + 1) * L ≤ C * Y ^ 2 * N ^ 2 * (r + 1) ^ 2 * L := by
  have hA0 : 0 ≤ 3 * (s + 2) * r ^ 2 * L := by positivity
  have hB0 : 0 ≤ N * (r + 1) ^ 2 * L := by
    have : 0 ≤ N := by linarith
    positivity
  have hA : 3 * (s + 2) * r ^ 2 * L ≤ 9 * (N * (r + 1) ^ 2 * L) := by
    have h1 : s + 2 ≤ 3 * N := by linarith
    have h2 : r ^ 2 ≤ (r + 1) ^ 2 := by nlinarith
    have h3 : (s + 2) * r ^ 2 ≤ (3 * N) * (r + 1) ^ 2 := mul_le_mul h1 h2 (by positivity) (by linarith)
    have h4 := mul_le_mul_of_nonneg_right h3 hL
    linarith
  have htA : t * (3 * (s + 2) * r ^ 2 * L) ≤ N * (9 * (N * (r + 1) ^ 2 * L)) :=
    mul_le_mul (by linarith) hA hA0 (by linarith)
  have k1 := mul_le_mul_of_nonneg_left htA (sq_nonneg Y)
  have hYCM : 0 ≤ Y * CM := mul_nonneg (by linarith) hCM
  have k2 := mul_le_mul_of_nonneg_left htA hYCM
  have k3 := mul_le_mul_of_nonneg_left hA hYCM
  have k4 : 10 * (s + 1) * (r + 1) * L ≤ 20 * (N * (r + 1) ^ 2 * L) := by
    have h1 : s + 1 ≤ 2 * N := by linarith
    have h2 : r + 1 ≤ (r + 1) ^ 2 := by nlinarith
    have h3 : (s + 1) * (r + 1) ≤ (2 * N) * (r + 1) ^ 2 := mul_le_mul h1 h2 (by linarith) (by linarith)
    have h4 := mul_le_mul_of_nonneg_right h3 hL
    linarith
  have hY2 : Y ≤ Y ^ 2 := by nlinarith
  have h5 := mul_le_mul_of_nonneg_left hN (sq_nonneg Y)
  have hYN : Y * N ≤ Y ^ 2 * N := mul_le_mul_of_nonneg_right hY2 (by linarith)
  have hY1 : Y ≤ Y ^ 2 * N := by linarith
  have h1P : 1 ≤ Y ^ 2 * N := by nlinarith
  have hc0 : 0 ≤ CM * (9 * (N * (r + 1) ^ 2 * L)) := mul_nonneg hCM (by linarith)
  have m1 := mul_le_mul_of_nonneg_left hYN hc0
  have m2 := mul_le_mul_of_nonneg_left hY1 hc0
  have m3 := mul_le_mul_of_nonneg_left h1P (by linarith : (0:ℝ) ≤ 20 * (N * (r + 1) ^ 2 * L))
  have hP0 : 0 ≤ Y ^ 2 * N * (N * (r + 1) ^ 2 * L) := mul_nonneg (by linarith) hB0
  have m4 := mul_le_mul_of_nonneg_right (by linarith : 29 + 18 * CM ≤ C) hP0
  linarith [k1, k2, k3, k4, m1, m2, m3, m4]

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

/- English proof (translation)
Establish `hmR : (4 : ℝ) ≤ (X.L.m : ℝ)` using `by exact_mod_cast hF.m4`. Use polynomial arithmetic with `[hF.p_ge]`.
-/
theorem p25 (hF : HIFacts C0 X) : (25 : ℝ) ≤ (X.L.p : ℝ) := by
  have hmR : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hF.m4
  nlinarith [hF.p_ge]

/- English proof (translation)
Unfold `lgA`. Establish `h : 0 ≤ Real.logb (X.p : ℝ) (8 * (X.L.a : ℝ) + X.r)`. Unfold `Real.logb`. Apply `div_nonneg` to reduce the goal to its premises. Establish `h'` using `Real.log_natCast_nonneg (8 * X.L.a + X.r)`.

Move the coercions through the operations in `at h'`. Conclude with `h'`. Conclude with `Real.log_natCast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lgA_ge_one_facts (hF : HIFacts C0 X) : 1 ≤ lgA X.p X.L.a X.r := by
  unfold lgA
  have h : 0 ≤ Real.logb (X.p : ℝ) (8 * (X.L.a : ℝ) + X.r) := by
    unfold Real.logb
    apply div_nonneg
    · have h' := Real.log_natCast_nonneg (8 * X.L.a + X.r)
      push_cast at h'
      exact h'
    · exact Real.log_natCast_nonneg _
  linarith

/- English proof (translation)
Unfold `kappaZeroExponent`. Establish `h : 0 ≤ Real.logb (X.p : ℝ) (X.L.a : ℝ)` using `div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)`. Conclude with `mul_nonneg (by positivity) h`.
-/
theorem kap0A_nonneg_of_hiFacts (hF : HIFacts C0 X) : 0 ≤ kappaZeroExponent X.p X.L.a X.Nt X.r := by
  unfold kappaZeroExponent
  have h : 0 ≤ Real.logb (X.p : ℝ) (X.L.a : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  exact mul_nonneg (by positivity) h

/- English proof (translation)
Establish `hF` using `hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH`. Establish `hY : (1 : ℝ) ≤ X.L.Y` using `hH.1.1`. Establish `hN : (1 : ℝ) ≤ (X.N₁ : ℝ)` using `by exact_mod_cast hH.1.2.2.2.2.2.1`. Establish `hs : (X.s : ℝ) ≤ (X.N₁ : ℝ)` using `by exact_mod_cast (hH.1.2.2.2.2.1 X.j).2`. Establish `ht : ((X.S C0 CE1 CE2).t : ℝ) ≤ (X.s : ℝ)`.

Establish `: (X.S C0 CE1 CE2).t ≤ X.s` using `Nat.sub_le _ _`. Conclude with `this` after adjusting the coercions. Establish `hL` using `lgA_ge_one_facts hF`. Establish `hL0 : 0 ≤ lgA X.p X.L.a X.r` using `by linarith`. Establish `hk` using `kap0A_nonneg_of_hiFacts hF`.

Prove the components needed by the constructor for the conclusion. Unfold `D1r kapS`. Check the signs of the components of the expression. Establish `h` using `depth_num X.L.Y X.N₁ X.s ((X.S C0 CE1 CE2).t : ℝ) X.r (lgA X.p X.L.a X.r) CM C hY hN (Nat.cast_nonneg _) hs (Nat.cast_nonneg _) ht (Nat.cast_nonneg _) hL0 hCM hC`. Unfold `D1r kapS levelPassageLoss depthD`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem restDepth_proved {CYb Cde Ck CD Cb Cc : ℝ} (CM C : ℝ) (hCYb : 1 ≤ CYb) (hCM : 0 ≤ CM)
    (hC : 18 * (1 + CM) + 20 ≤ C) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : RestDepth C0 CE1 CE2 X CM C := by
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
  have hY : (1 : ℝ) ≤ X.L.Y := hH.1.1
  have hN : (1 : ℝ) ≤ (X.N₁ : ℝ) := by exact_mod_cast hH.1.2.2.2.2.2.1
  have hs : (X.s : ℝ) ≤ (X.N₁ : ℝ) := by exact_mod_cast (hH.1.2.2.2.2.1 X.j).2
  have ht : ((X.S C0 CE1 CE2).t : ℝ) ≤ (X.s : ℝ) := by
    have : (X.S C0 CE1 CE2).t ≤ X.s := Nat.sub_le _ _
    exact_mod_cast this
  have hL := lgA_ge_one_facts hF
  have hL0 : 0 ≤ lgA X.p X.L.a X.r := by linarith
  have hk := kap0A_nonneg_of_hiFacts hF
  constructor
  · unfold D1r kapS
    positivity
  · have h := depth_num X.L.Y X.N₁ X.s ((X.S C0 CE1 CE2).t : ℝ) X.r (lgA X.p X.L.a X.r) CM C hY hN (Nat.cast_nonneg _) hs
      (Nat.cast_nonneg _) ht (Nat.cast_nonneg _) hL0 hCM hC
    unfold D1r kapS levelPassageLoss depthD
    linarith

end Formalism.MainNotions.G.SymmetricFormBlocks

end
