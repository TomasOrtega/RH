import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DminusLeBeS
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNonzeroModUniformiser
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FrameZeroStrictMono
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DistAddTwoLeOfSameVec
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.AdmissibleSmallRatio

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

/- English proof (translation)
Introduce `p n' r K _ _ _ X hX hLa hk j b hA`. Establish `hV` using `hX.valid`. Establish `B` using `basics hX`. Establish `hr : 0 < r` using `NeZero.pos r`. Establish `hp0 : (0 : ℝ) < p` using `by linarith [B.p1]`.

Establish `hp2 : 2 ≤ p` using `hX.prime.two_le`. Establish `h41` using `(top_count_lower_bounds 1088 (by norm_num) p n' r K X hX hLa hk).1`. Establish `ha0 : 0 < X.a` using `by have := TE.four_hundred_sixteen_le_a hX; linarith`. Establish `hL1 : 1 ≤ X.L₁`. Assume the negation of the conclusion as `h`.

Establish `h0 : X.L₁ = 0` using `by omega`. Establish `hP2` using `hX.P2`. Rewrite `hP2` using `[h0]`. Establish `e1 : (p : ℝ) ^ (((0 : ℕ) : ℤ) - 1) = (p : ℝ)⁻¹` using `by simp`. Rewrite `hP2` using `[e1]`.

Establish `e2 : (p : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ B.p1`. Establish `e3 : (1 : ℝ) ≤ 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2`. Establish `k5` using `B.k5`. Unfold `Dat.k at k5`. Establish `a1 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2` using `by nlinarith`.

Establish `a2 : (1 : ℝ) ≤ X.Y ^ 2` using `by nlinarith [B.Y1]`. Establish `a3` using `B.Ns1`. Establish `a4 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ)` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hP2 : 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2 ≤ (p : ℝ) ^ (X.L₁ - 1)`. Establish `h` using `hX.P2`. Establish `e : ((X.L₁ : ℤ) - 1) = ((X.L₁ - 1 : ℕ) : ℤ)` using `by omega`. Rewrite `h` using `[e, zpow_natCast]`. Conclude with `h`.

Use `set D1 := X.F.dist j (X.F.fr j 0) with hD1`. Use `set s := (X.F.letters j).filter (· < X.F.fr j 0) with hs`. Establish `hfr0 : X.F.fr j 0 ∈ X.F.letters j` using `k_fr_mem_letters X.F hV j hr`. Establish `hD1c` using `TE.dist_cast hfr0`. Establish `hU1 : ∀ x ∈ s, D1 + X.L₁ + 1 ≤ X.F.dist j x`.

Introduce `x hx`. Establish `hne : s.Nonempty` using `⟨x, hx⟩`. Establish `hmax` using `Finset.max'_mem s hne`. Take `⟨hm1, hm2⟩` from `Finset.mem_filter.mp hmax`. Establish `hgap` using `hV.2.2.2.2.2.2.1 j |>.2.2 (s.max' hne) hm1 hm2 (fun z hz hzlt => Finset.le_max' s z (Finset.mem_filter.mpr ⟨hz, hzlt⟩))`.

Establish `hle` using `Finset.le_max' s x hx`. Establish `hxc` using `TE.dist_cast (Finset.mem_filter.mp hx).1`. Use linear arithmetic over natural numbers and integers. Establish `hA1 : (X.beS p K j (X.restr j b) : ℝ) ≤ 4 * X.a / (p : ℝ) ^ (X.Rj p K j + D1 + X.L₁ + 1)`. Unfold `Dat.beS`.

Use `push_cast`. Establish `h1 : ∀ x ∈ s, (X.Bdeg p K j (X.restr j b) x : ℝ) ≤ 2 * X.a / (p : ℝ) ^ X.Rj p K j * (1 / (p : ℝ) ^ X.F.dist j x)`. Introduce `x hx`. Take `⟨hx1, hx2⟩` from `Finset.mem_filter.mp hx`. Establish `b1` using `(TE.Bdeg_bounds hX hk h41 j b hA x hx1 hx2).2`.

Establish `b2` using `(TE.c_bounds hX h41 j x hx1).2.2`. Use `le_trans b1 ?_` and prove the remaining obligations. Rewrite using `[pow_add]`. Establish `hq1 : (0 : ℝ) < (p : ℝ) ^ X.F.dist j x` using `by positivity`. Establish `hq2 : (0 : ℝ) < (p : ℝ) ^ X.Rj p K j` using `by positivity`.

Rewrite using `[div_mul_div_comm, mul_one, mul_comm ((p : ℝ) ^ X.Rj p K j)]`. Conclude with `div_le_div_of_nonneg_right b2 (by positivity)`. Use `le_trans (Finset.sum_le_sum h1) ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`. Establish `hinj : Set.InjOn (X.F.dist j) (s : Set ℤ)`.

Introduce `x hx y hy hxy`. Establish `c1` using `TE.dist_cast (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1`. Establish `c2` using `TE.dist_cast (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1`. Establish `: (X.F.dist j x : ℤ) = (X.F.dist j y : ℤ)` using `by exact_mod_cast hxy`. Use linear arithmetic over natural numbers and integers.

Establish `h2 : ∑ x ∈ s, (1 / (p : ℝ) ^ X.F.dist j x) = ∑ D ∈ s.image (X.F.dist j), (1 / (p : ℝ) ^ D)` using `(Finset.sum_image (f := fun D : ℕ => 1 / (p : ℝ) ^ D) hinj).symm`. Establish `h3` using `Formalism.InvariantFactorPaths.BranchingDimensions.geometricSumDistinct p (D1 + X.L₁ + 1) (s.image (X.F.dist j)) hp2 (by`. Introduce `D hD`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp hD`. Conclude with `hU1 x hx)`.

Rewrite using `[h2]`. Establish `hc : 0 ≤ 2 * X.a / (p : ℝ) ^ X.Rj p K j` using `by positivity`. Use `le_trans (mul_le_mul_of_nonneg_left h3 hc) ?_` and prove the remaining obligations. Rewrite using `[div_mul_div_comm, ← pow_add]`. Establish `e : X.Rj p K j + (D1 + X.L₁ + 1) = X.Rj p K j + D1 + X.L₁ + 1` using `by ring`.

Rewrite using `[e]`. Apply `le_of_eq` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree. Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) := by`. Establish `hm : X.F.fr j (r - 1) < X.F.fr (j + 1) (r - 1)` using `eFr_strictMono hV (by omega : j < j + 1)`.

Conclude with `⟨(X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1)).toNat, Int.toNat_of_nonneg (by omega)⟩`. Establish `hdist : X.F.dist (j + 1) (X.F.fr j 0) = D1 + d`. Establish `: ((X.F.dist (j + 1) (X.F.fr j 0) : ℕ) : ℤ) = X.F.fr (j + 1) (r - 1) - X.F.fr j 0`. Unfold `Frames.dist`. Conclude with `Int.toNat_of_nonneg (by omega)`.

Use linear arithmetic over natural numbers and integers. Establish `hB1 : X.a / (8 * p * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) < (p : ℝ) ^ X.Rj p K (j + 1)`. Establish `h` using `lt_pow_Rj hX (j + 1)`. Unfold `Tj at h`. Rewrite `h` using `[add_sub_cancel_right, hdist, pow_add ((p : ℝ)) D1 d, pow_succ ((p : ℝ)) (X.Rj p K (j + 1))]`.

Unfold `Dat.k at h`. Establish `hden : 0 < 8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)`. Establish `k5` using `B.k5`. Unfold `Dat.k at k5`. Use `B.Ns1` as an intermediate fact.

Use `B.Y1` as an intermediate fact. Check the signs of the components of the expression. Rewrite `h` using `[div_lt_iff₀ hden]`. Establish `hden2 : 0 < 8 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)`. Establish `e : 8 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) = (p : ℝ) * (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d))` using `by ring`.

Rewrite using `[e]`. Conclude with `mul_pos hp0 hden`. Rewrite using `[div_lt_iff₀ hden2]`. Combine the equalities or inequalities in the displayed calculation. Establish `hcore` using `(Formalism.InvariantFactorPaths.BranchingDimensions.admissibleSmallRatio p (r + K) X.Ns D1 X.L₁ (X.Rj p K j) (X.Rj p K (j + 1)) X.a X.Y ((p : ℝ) ^ d) (X.beS p K j (X.restr j b) : ℝ) hp2 (by omega) (by have := B.Ns1; exact_mod_cast this) B.Y1 ha0 (by positivity) hL1 hA1 hB1 hP2).2 …`.

Establish `hexp` using `Rj_add_first_frame_gap_le_last_frame_gap_add_Rj_succ hX j`. Establish `hmono : X.F.fr (j - 1) 0 ≤ X.F.fr j 0` using `(mem_letters_bounds hfr0).1`. Establish `hQ : ((X.Qc p K j : ℕ) : ℝ) = (p : ℝ) ^ d * (p : ℝ) ^ X.Rj p K (j + 1) / (p : ℝ) ^ X.Rj p K j`. Unfold `Dat.Qc`. Rewrite using `[eq_div_iff (by positivity)]`.

Use `push_cast`. Rewrite using `[← pow_add, ← pow_add]`. Use `congr 1`. Establish `: (((X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ)).toNat : ℕ) : ℤ) = X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ)` using `Int.toNat_of_nonneg (by omega)`. Use linear arithmetic over natural numbers and integers.

Rewrite `hcore` using `[← hQ]`. Establish `hQpos : (0 : ℝ) < ((X.Qc p K j : ℕ) : ℝ)`. Rewrite using `[hQ]`. Check the signs of the components of the expression. Rewrite `hcore` using `[div_le_div_iff₀ hQpos (by have := B.Y1; positivity)]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem beta_ratio_bound : BetaRatioBound 1088 := by
  intro p n' r K _ _ _ X hX hLa hk j b hA
  classical
  have hV := hX.valid
  have B := basics hX
  have hr : 0 < r := NeZero.pos r
  have hp0 : (0 : ℝ) < p := by linarith [B.p1]
  have hp2 : 2 ≤ p := hX.prime.two_le
  have h41 := (top_count_lower_bounds 1088 (by norm_num) p n' r K X hX hLa hk).1
  have ha0 : 0 < X.a := by have := TE.four_hundred_sixteen_le_a hX; linarith

  have hL1 : 1 ≤ X.L₁ := by
    by_contra h
    have h0 : X.L₁ = 0 := by omega
    have hP2 := hX.P2
    rw [h0] at hP2
    have e1 : (p : ℝ) ^ (((0 : ℕ) : ℤ) - 1) = (p : ℝ)⁻¹ := by simp
    rw [e1] at hP2
    have e2 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ B.p1
    have e3 : (1 : ℝ) ≤ 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2 := by
      have k5 := B.k5
      unfold Dat.k at k5
      have a1 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 := by nlinarith
      have a2 : (1 : ℝ) ≤ X.Y ^ 2 := by nlinarith [B.Y1]
      have a3 := B.Ns1
      have a4 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) := by nlinarith
      nlinarith
    linarith
  have hP2 : 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2 ≤ (p : ℝ) ^ (X.L₁ - 1) := by
    have h := hX.P2
    have e : ((X.L₁ : ℤ) - 1) = ((X.L₁ - 1 : ℕ) : ℤ) := by omega
    rw [e, zpow_natCast] at h
    exact h
  set D1 := X.F.dist j (X.F.fr j 0) with hD1
  set s := (X.F.letters j).filter (· < X.F.fr j 0) with hs
  have hfr0 : X.F.fr j 0 ∈ X.F.letters j := k_fr_mem_letters X.F hV j hr
  have hD1c := TE.dist_cast hfr0

  have hU1 : ∀ x ∈ s, D1 + X.L₁ + 1 ≤ X.F.dist j x := by
    intro x hx
    have hne : s.Nonempty := ⟨x, hx⟩
    have hmax := Finset.max'_mem s hne
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hmax
    have hgap := hV.2.2.2.2.2.2.1 j |>.2.2 (s.max' hne) hm1 hm2 (fun z hz hzlt =>
      Finset.le_max' s z (Finset.mem_filter.mpr ⟨hz, hzlt⟩))
    have hle := Finset.le_max' s x hx
    have hxc := TE.dist_cast (Finset.mem_filter.mp hx).1
    omega

  have hA1 : (X.beS p K j (X.restr j b) : ℝ) ≤ 4 * X.a / (p : ℝ) ^ (X.Rj p K j + D1 + X.L₁ + 1) := by
    unfold Dat.beS
    push_cast
    have h1 : ∀ x ∈ s, (X.Bdeg p K j (X.restr j b) x : ℝ) ≤
        2 * X.a / (p : ℝ) ^ X.Rj p K j * (1 / (p : ℝ) ^ X.F.dist j x) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      have b1 := (TE.Bdeg_bounds hX hk h41 j b hA x hx1 hx2).2
      have b2 := (TE.c_bounds hX h41 j x hx1).2.2
      refine le_trans b1 ?_
      rw [pow_add]
      have hq1 : (0 : ℝ) < (p : ℝ) ^ X.F.dist j x := by positivity
      have hq2 : (0 : ℝ) < (p : ℝ) ^ X.Rj p K j := by positivity
      rw [div_mul_div_comm, mul_one, mul_comm ((p : ℝ) ^ X.Rj p K j)]
      exact div_le_div_of_nonneg_right b2 (by positivity)
    refine le_trans (Finset.sum_le_sum h1) ?_
    rw [← Finset.mul_sum]
    have hinj : Set.InjOn (X.F.dist j) (s : Set ℤ) := by
      intro x hx y hy hxy
      have c1 := TE.dist_cast (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1
      have c2 := TE.dist_cast (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1
      have : (X.F.dist j x : ℤ) = (X.F.dist j y : ℤ) := by exact_mod_cast hxy
      omega
    have h2 : ∑ x ∈ s, (1 / (p : ℝ) ^ X.F.dist j x) = ∑ D ∈ s.image (X.F.dist j), (1 / (p : ℝ) ^ D) :=
      (Finset.sum_image (f := fun D : ℕ => 1 / (p : ℝ) ^ D) hinj).symm
    have h3 := Formalism.InvariantFactorPaths.BranchingDimensions.geometricSumDistinct p (D1 + X.L₁ + 1) (s.image (X.F.dist j)) hp2 (by
      intro D hD
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hD
      exact hU1 x hx)
    rw [h2]
    have hc : 0 ≤ 2 * X.a / (p : ℝ) ^ X.Rj p K j := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left h3 hc) ?_
    rw [div_mul_div_comm, ← pow_add]
    have e : X.Rj p K j + (D1 + X.L₁ + 1) = X.Rj p K j + D1 + X.L₁ + 1 := by ring
    rw [e]
    apply le_of_eq
    ring

  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) := by
    have hm : X.F.fr j (r - 1) < X.F.fr (j + 1) (r - 1) := eFr_strictMono hV (by omega : j < j + 1)
    exact ⟨(X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1)).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hdist : X.F.dist (j + 1) (X.F.fr j 0) = D1 + d := by
    have : ((X.F.dist (j + 1) (X.F.fr j 0) : ℕ) : ℤ) = X.F.fr (j + 1) (r - 1) - X.F.fr j 0 := by
      unfold Frames.dist
      exact Int.toNat_of_nonneg (by omega)
    omega
  have hB1 : X.a / (8 * p * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) <
      (p : ℝ) ^ X.Rj p K (j + 1) := by
    have h := lt_pow_Rj hX (j + 1)
    unfold Tj at h
    rw [add_sub_cancel_right, hdist, pow_add ((p : ℝ)) D1 d, pow_succ ((p : ℝ)) (X.Rj p K (j + 1))] at h
    unfold Dat.k at h
    have hden : 0 < 8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) := by
      have k5 := B.k5
      unfold Dat.k at k5
      have := B.Ns1
      have := B.Y1
      positivity
    rw [div_lt_iff₀ hden] at h
    have hden2 : 0 < 8 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) := by
      have e : 8 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) =
          (p : ℝ) * (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) := by ring
      rw [e]; exact mul_pos hp0 hden
    rw [div_lt_iff₀ hden2]
    calc X.a < (p : ℝ) ^ X.Rj p K (j + 1) * (p : ℝ) *
          (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) := h
      _ = _ := by ring
  have hcore := (Formalism.InvariantFactorPaths.BranchingDimensions.admissibleSmallRatio p (r + K) X.Ns D1 X.L₁ (X.Rj p K j) (X.Rj p K (j + 1)) X.a X.Y
    ((p : ℝ) ^ d) (X.beS p K j (X.restr j b) : ℝ) hp2 (by omega)
    (by have := B.Ns1; exact_mod_cast this) B.Y1 ha0 (by positivity) hL1 hA1 hB1 hP2).2.2

  have hexp := Rj_add_first_frame_gap_le_last_frame_gap_add_Rj_succ hX j
  have hmono : X.F.fr (j - 1) 0 ≤ X.F.fr j 0 := (mem_letters_bounds hfr0).1
  have hQ : ((X.Qc p K j : ℕ) : ℝ) = (p : ℝ) ^ d * (p : ℝ) ^ X.Rj p K (j + 1) / (p : ℝ) ^ X.Rj p K j := by
    unfold Dat.Qc
    rw [eq_div_iff (by positivity)]
    push_cast
    rw [← pow_add, ← pow_add]
    congr 1
    have : (((X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ)).toNat : ℕ) : ℤ) =
        X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ) :=
      Int.toNat_of_nonneg (by omega)
    omega
  rw [← hQ] at hcore
  have hQpos : (0 : ℝ) < ((X.Qc p K j : ℕ) : ℝ) := by
    rw [hQ]; positivity
  rw [div_le_div_iff₀ hQpos (by have := B.Y1; positivity)] at hcore
  linarith

end Formalism.MainNotions.SelectionLemmas.Pf
