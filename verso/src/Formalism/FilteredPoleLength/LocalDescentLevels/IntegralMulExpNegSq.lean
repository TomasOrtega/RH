import Formalism.FilteredPoleLength.ReducedBasisBounds.TransvectionIsometry

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset MeasureTheory Filter Topology Set

/- English proof (translation)
Conclude with `pow_le_pow_left₀ hx hxy n`.
-/
private theorem pow_le_pow_left_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    x ^ n ≤ y ^ n := by
  exact pow_le_pow_left₀ hx hxy n

/- English proof (translation)
Introduce `D rr hr`. Break down `Nat.eq_zero_or_pos D with hD | hD` into its components or cases. Substitute `hD show volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) rr) = _` using the available equality. Establish `hb : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) rr = Set.univ`. Use extensionality with `z`.

Simplify using `only [mem_ball_zero_iff, Set.mem_univ, iff_true]`. Establish `hz : ‖z‖ = 0`. Rewrite using `[EuclideanSpace.norm_eq]`. Simplify using the standard rewrite rules. Rewrite using `[hz]`.

Conclude with `hr`. Establish `hpar : parallelepiped (EuclideanSpace.basisFun (Fin 0) ℝ) = Set.univ`. Use extensionality with `z`. Simplify using `only [Set.mem_univ, iff_true]`. Establish `hz : z = 0`.

Rewrite using `[← norm_eq_zero, EuclideanSpace.norm_eq]`. Simplify using the standard rewrite rules. Rewrite using `[hz, mem_parallelepiped_iff]`. Conclude with `⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩`. Rewrite using `[hb, ← hpar, OrthonormalBasis.volume_parallelepiped]`.

Simplify using the standard rewrite rules. Establish `: Nonempty (Fin (2 * D))` using `⟨⟨0, by omega⟩⟩`. Rewrite using `[EuclideanSpace.volume_ball, Fintype.card_fin]`. Establish `hg : Real.Gamma (((2 * D : ℕ) : ℝ) / 2 + 1) = (D.factorial : ℝ)`. Rewrite using `[show ((2 * D : ℕ) : ℝ) / 2 + 1 = (D : ℝ) + 1 by push_cast; ring]`.

Conclude with `Real.Gamma_nat_eq_factorial D`. Establish `hs : Real.sqrt Real.pi ^ (2 * D) = Real.pi ^ D`. Rewrite using `[pow_mul, Real.sq_sqrt Real.pi_pos.le]`. Rewrite using `[hg, hs, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity)]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ballVolume : BallVolume := by
  intro D rr hr
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    show volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) rr) = _
    have hb : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) rr = Set.univ := by
      ext z
      simp only [mem_ball_zero_iff, Set.mem_univ, iff_true]
      have hz : ‖z‖ = 0 := by
        rw [EuclideanSpace.norm_eq]
        simp
      rw [hz]
      exact hr
    have hpar : parallelepiped (EuclideanSpace.basisFun (Fin 0) ℝ) = Set.univ := by
      ext z
      simp only [Set.mem_univ, iff_true]
      have hz : z = 0 := by
        rw [← norm_eq_zero, EuclideanSpace.norm_eq]
        simp
      rw [hz, mem_parallelepiped_iff]
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
    rw [hb, ← hpar, OrthonormalBasis.volume_parallelepiped]
    simp
  have : Nonempty (Fin (2 * D)) := ⟨⟨0, by omega⟩⟩
  rw [EuclideanSpace.volume_ball, Fintype.card_fin]
  have hg : Real.Gamma (((2 * D : ℕ) : ℝ) / 2 + 1) = (D.factorial : ℝ) := by
    rw [show ((2 * D : ℕ) : ℝ) / 2 + 1 = (D : ℝ) + 1 by push_cast; ring]
    exact Real.Gamma_nat_eq_factorial D
  have hs : Real.sqrt Real.pi ^ (2 * D) = Real.pi ^ D := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [hg, hs, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/- English proof (translation)
The claim follows from `Real.exp_le_exp.mpr (by nlinarith)`.
-/
private theorem exp_neg_sq_div_sixteen_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.exp (-t ^ 2 / 16) ≤ Real.exp (-s ^ 2 / 16) :=
  Real.exp_le_exp.mpr (by nlinarith)

/- English proof (translation)
Establish `hs0 : 0 < s` using `lt_of_lt_of_le hR0 hs`. Take `⟨u, hu⟩ : ∃ u : ℝ, u = (t ^ 2 - s ^ 2) / 16` from `⟨_, rfl⟩`. Establish `hu0 : 0 ≤ u` using `by rw [hu]; nlinarith`. Take `⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (u / 2)` from `⟨_, rfl⟩`. Establish `hE2 : E ^ 2 = Real.exp u`.

Rewrite using `[show E ^ 2 = E * E by ring, hE, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hfs : Real.exp (-s ^ 2 / 16) = Real.exp (-t ^ 2 / 16) * E ^ 2`. Rewrite using `[hE2, ← Real.exp_add]`.

Use `congr 1`. Rewrite using `[hu]`. Expand and normalize the polynomial expressions, which then agree. Establish `hK : 0 < 2 * (g : ℝ) + 1` using `by positivity`. Take `⟨v, hv⟩ : ∃ v : ℝ, v = u / (2 * (g : ℝ) + 1)` from `⟨_, rfl⟩`.

Establish `hv0 : 0 ≤ v` using `by rw [hv]; exact div_nonneg hu0 hK.le`. Establish `hvK : v * (2 * (g : ℝ) + 1) = u` using `by rw [hv]; field_simp`. Establish `hR2 : R0 ^ 2 ≤ s ^ 2` using `by nlinarith`. Establish `ht2 : t ^ 2 ≤ s ^ 2 * (1 + v)`. Establish `h16 : 16 * (2 * (g : ℝ) + 1) ≤ s ^ 2` using `le_trans hg hR2`.

Establish `htu : t ^ 2 = s ^ 2 + 16 * u` using `by rw [hu]; ring`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h16 hv0]`. Establish `hP : ∀ x : ℝ, (3 * x / R0) ^ (2 * g) = ((3 / R0) ^ 2 * x ^ 2) ^ g`. Introduce `x`. Rewrite using `[pow_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hBt : (3 * t / R0) ^ (2 * g) ≤ (3 * s / R0) ^ (2 * g) * E`. Rewrite using `[hP t, hP s]`. Establish `h1 : (3 / R0) ^ 2 * t ^ 2 ≤ ((3 / R0) ^ 2 * s ^ 2) * (1 + v)`.

Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left ht2 (sq_nonneg _)`. Establish `h2 : ((3 / R0) ^ 2 * t ^ 2) ^ g ≤ (((3 / R0) ^ 2 * s ^ 2) * (1 + v)) ^ g` using `pow_le_pow_left_of_nonneg (by positivity) h1 g`. Establish `h3 : (1 + v) ^ g ≤ E`. Establish `hexp : (1 + v) ^ g ≤ (Real.exp v) ^ g` using `pow_le_pow_left_of_nonneg (by linarith) (by linarith [Real.add_one_le_exp v]) g`.

Establish `hnat : (Real.exp v) ^ g = Real.exp (g * v)`. Conclude with `(Real.exp_nat_mul v g).symm`. Establish `hle : Real.exp (g * v) ≤ E`. Rewrite using `[hE]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `hft : 0 ≤ Real.exp (-t ^ 2 / 16)` using `(Real.exp_pos _).le`. Establish `hBs : 0 ≤ (3 * s / R0) ^ (2 * g)` using `by rw [hP s]; positivity`.

Rewrite using `[hfs]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hBt hft, mul_nonneg (mul_nonneg hBs hft) (sq_nonneg (E - 1))]`.
-/
private theorem gaussian_tail_pow_mul_exp_le {g : ℕ} {R0 s t : ℝ} (hR0 : 0 < R0)
    (hg : 16 * (2 * (g : ℝ) + 1) ≤ R0 ^ 2) (hs : R0 ≤ s) (hst : s ≤ t) :
    (2 * (3 * t / R0) ^ (2 * g) - (3 * s / R0) ^ (2 * g)) * Real.exp (-t ^ 2 / 16) ≤
      (3 * s / R0) ^ (2 * g) * Real.exp (-s ^ 2 / 16) := by
  have hs0 : 0 < s := lt_of_lt_of_le hR0 hs
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (t ^ 2 - s ^ 2) / 16 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; nlinarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (u / 2) := ⟨_, rfl⟩
  have hE2 : E ^ 2 = Real.exp u := by
    rw [show E ^ 2 = E * E by ring, hE, ← Real.exp_add]
    congr 1
    ring
  have hfs : Real.exp (-s ^ 2 / 16) = Real.exp (-t ^ 2 / 16) * E ^ 2 := by
    rw [hE2, ← Real.exp_add]
    congr 1
    rw [hu]
    ring
  have hK : 0 < 2 * (g : ℝ) + 1 := by positivity
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = u / (2 * (g : ℝ) + 1) := ⟨_, rfl⟩
  have hv0 : 0 ≤ v := by rw [hv]; exact div_nonneg hu0 hK.le
  have hvK : v * (2 * (g : ℝ) + 1) = u := by rw [hv]; field_simp
  have hR2 : R0 ^ 2 ≤ s ^ 2 := by nlinarith
  have ht2 : t ^ 2 ≤ s ^ 2 * (1 + v) := by
    have h16 : 16 * (2 * (g : ℝ) + 1) ≤ s ^ 2 := le_trans hg hR2
    have htu : t ^ 2 = s ^ 2 + 16 * u := by rw [hu]; ring
    nlinarith [mul_le_mul_of_nonneg_left h16 hv0]
  have hP : ∀ x : ℝ, (3 * x / R0) ^ (2 * g) = ((3 / R0) ^ 2 * x ^ 2) ^ g := by
    intro x
    rw [pow_mul]
    congr 1
    ring
  have hBt : (3 * t / R0) ^ (2 * g) ≤ (3 * s / R0) ^ (2 * g) * E := by
    rw [hP t, hP s]
    have h1 : (3 / R0) ^ 2 * t ^ 2 ≤ ((3 / R0) ^ 2 * s ^ 2) * (1 + v) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ht2 (sq_nonneg _)
    have h2 : ((3 / R0) ^ 2 * t ^ 2) ^ g ≤ (((3 / R0) ^ 2 * s ^ 2) * (1 + v)) ^ g :=
      pow_le_pow_left_of_nonneg (by positivity) h1 g
    have h3 : (1 + v) ^ g ≤ E := by
      have hexp : (1 + v) ^ g ≤ (Real.exp v) ^ g :=
        pow_le_pow_left_of_nonneg (by linarith) (by linarith [Real.add_one_le_exp v]) g
      have hnat : (Real.exp v) ^ g = Real.exp (g * v) := by
        exact (Real.exp_nat_mul v g).symm
      have hle : Real.exp (g * v) ≤ E := by
        rw [hE]
        apply Real.exp_le_exp.mpr
        nlinarith
      linarith
    calc ((3 / R0) ^ 2 * t ^ 2) ^ g ≤ (((3 / R0) ^ 2 * s ^ 2) * (1 + v)) ^ g := h2
      _ = ((3 / R0) ^ 2 * s ^ 2) ^ g * (1 + v) ^ g := mul_pow _ _ _
      _ ≤ ((3 / R0) ^ 2 * s ^ 2) ^ g * E := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hft : 0 ≤ Real.exp (-t ^ 2 / 16) := (Real.exp_pos _).le
  have hBs : 0 ≤ (3 * s / R0) ^ (2 * g) := by rw [hP s]; positivity
  rw [hfs]
  nlinarith [mul_le_mul_of_nonneg_right hBt hft, mul_nonneg (mul_nonneg hBs hft) (sq_nonneg (E - 1))]

/- English proof (translation)
Introduce `ι h g R0 hR0 hg hlow hcount`. Establish `claim : ∀ S : Finset ι, ∀ M : ℝ, R0 ≤ M → (∀ i ∈ S, h i ≤ M) → ∑ i ∈ S, Real.exp (-(h i) ^ 2 / 16) ≤ 2 * (3 * R0 / R0) ^ (2 * g) * Real.exp (-R0 ^ 2 / 16) - 2 * (3 * M / R0) ^ (2 * g) * Real.exp (-M ^ 2 / 16) + (S.card : ℝ) * Real.exp (-M ^ 2 / 16)`. Introduce `S`. Use `Finset.induction_on_max_value h S ?_ ?_` and prove the remaining obligations. Introduce `M hM _`.

Establish `k` using `gaussian_tail_pow_mul_exp_le hR0 hg le_rfl hM`. Establish `hfa : Real.exp (-M ^ 2 / 16) ≤ Real.exp (-R0 ^ 2 / 16)` using `exp_neg_sq_div_sixteen_antitone hR0.le hM`. Establish `hB0 : 0 ≤ (3 * R0 / R0) ^ (2 * g)` using `pow_nonneg (div_nonneg (by linarith) hR0.le) _`. Simplify using `only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul, add_zero]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hfa hB0]`.

Introduce `a S haS hmax ih M hM hSM`. Establish `hxR : R0 ≤ h a` using `hlow a`. Establish `hxM : h a ≤ M` using `hSM a (Finset.mem_insert_self a S)`. Establish `ih'` using `ih (h a) hxR hmax`. Establish `hins : ∀ i ∈ insert a S, h i ≤ h a`.

Introduce `i hi`. Break down `Finset.mem_insert.mp hi with hia | hi'` into its components or cases. Rewrite using `[hia]`. Conclude with `hmax i hi'`. Establish `hcard` using `hcount (h a) hxR (insert a S) hins`.

Establish `hc : (insert a S).card = S.card + 1` using `by first`. Consider the case `exact Finset.card_insert_of_notMem haS`. Consider the case `exact Finset.card_insert_of_not_mem haS`. Consider the case `simp [haS]`. Rewrite `hcard` using `[hc]`.

Rewrite using `[Finset.sum_insert haS, hc]`. Move the coercions through the operations in `at hcard ⊢`. Establish `k` using `gaussian_tail_pow_mul_exp_le hR0 hg hxR hxM`. Establish `hfa : Real.exp (-M ^ 2 / 16) ≤ Real.exp (-(h a) ^ 2 / 16)` using `exp_neg_sq_div_sixteen_antitone (hR0.le.trans hxR) hxM`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hcard (sub_nonneg.mpr hfa)]`.

Establish `hG0 : (3 * R0 / R0) ^ (2 * g) = (9 : ℝ) ^ g`. Rewrite using `[show 3 * R0 / R0 = (3 : ℝ) by field_simp, pow_mul]`. Evaluate the numerical expressions. Establish `hpos : ∀ i, 0 ≤ h i` using `fun i => hR0.le.trans (hlow i)`. Establish `hsum : ∀ S : Finset ι, ∑ i ∈ S, Real.exp (-(h i) ^ 2 / 16) ≤ 2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16)`.

Introduce `S`. Establish `hM0 : R0 ≤ R0 + ∑ j ∈ S, h j` using `le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hpos j)`. Establish `hMi : ∀ i ∈ S, h i ≤ R0 + ∑ j ∈ S, h j` using `fun i hi => (Finset.single_le_sum (fun j _ => hpos j) hi).trans (le_add_of_nonneg_left hR0.le)`. Establish `c1` using `claim S _ hM0 hMi`. Establish `c2` using `hcount _ hM0 S hMi`.

Establish `hBM : 0 ≤ (3 * (R0 + ∑ j ∈ S, h j) / R0) ^ (2 * g)` using `pow_nonneg (div_nonneg (by linarith) hR0.le) _`. Establish `hfM` using `(Real.exp_pos (-(R0 + ∑ j ∈ S, h j) ^ 2 / 16)).le`. Rewrite `c1` using `[hG0]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right c2 hfM, mul_nonneg hBM hfM]`. Establish `hnn : ∀ i, 0 ≤ Real.exp (-(h i) ^ 2 / 16)` using `fun i => (Real.exp_pos _).le`.

Establish `hsm : Summable (fun i => Real.exp (-(h i) ^ 2 / 16))` using `summable_of_sum_le hnn hsum`. Use `⟨hsm, ?_⟩` and prove the remaining obligations. Conclude with `Real.tsum_le_of_sum_le hnn hsum`.
-/
theorem gaussian_tail_bound : GaussianTailBound := by
  intro ι h g R0 hR0 hg hlow hcount
  classical
  have claim : ∀ S : Finset ι, ∀ M : ℝ, R0 ≤ M → (∀ i ∈ S, h i ≤ M) →
      ∑ i ∈ S, Real.exp (-(h i) ^ 2 / 16) ≤
        2 * (3 * R0 / R0) ^ (2 * g) * Real.exp (-R0 ^ 2 / 16)
          - 2 * (3 * M / R0) ^ (2 * g) * Real.exp (-M ^ 2 / 16)
          + (S.card : ℝ) * Real.exp (-M ^ 2 / 16) := by
    intro S
    refine Finset.induction_on_max_value h S ?_ ?_
    · intro M hM _
      have k := gaussian_tail_pow_mul_exp_le hR0 hg le_rfl hM
      have hfa : Real.exp (-M ^ 2 / 16) ≤ Real.exp (-R0 ^ 2 / 16) :=
        exp_neg_sq_div_sixteen_antitone hR0.le hM
      have hB0 : 0 ≤ (3 * R0 / R0) ^ (2 * g) :=
        pow_nonneg (div_nonneg (by linarith) hR0.le) _
      simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul, add_zero]
      nlinarith [mul_le_mul_of_nonneg_left hfa hB0]
    · intro a S haS hmax ih M hM hSM
      have hxR : R0 ≤ h a := hlow a
      have hxM : h a ≤ M := hSM a (Finset.mem_insert_self a S)
      have ih' := ih (h a) hxR hmax
      have hins : ∀ i ∈ insert a S, h i ≤ h a := by
        intro i hi
        rcases Finset.mem_insert.mp hi with hia | hi'
        · rw [hia]
        · exact hmax i hi'
      have hcard := hcount (h a) hxR (insert a S) hins
      have hc : (insert a S).card = S.card + 1 := by
        first
          | exact Finset.card_insert_of_notMem haS
          | exact Finset.card_insert_of_not_mem haS
          | simp [haS]
      rw [hc] at hcard
      rw [Finset.sum_insert haS, hc]
      push_cast at hcard ⊢
      have k := gaussian_tail_pow_mul_exp_le hR0 hg hxR hxM
      have hfa : Real.exp (-M ^ 2 / 16) ≤ Real.exp (-(h a) ^ 2 / 16) :=
        exp_neg_sq_div_sixteen_antitone (hR0.le.trans hxR) hxM
      nlinarith [mul_le_mul_of_nonneg_right hcard (sub_nonneg.mpr hfa)]
  have hG0 : (3 * R0 / R0) ^ (2 * g) = (9 : ℝ) ^ g := by
    rw [show 3 * R0 / R0 = (3 : ℝ) by field_simp, pow_mul]
    norm_num
  have hpos : ∀ i, 0 ≤ h i := fun i => hR0.le.trans (hlow i)
  have hsum : ∀ S : Finset ι, ∑ i ∈ S, Real.exp (-(h i) ^ 2 / 16) ≤
      2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16) := by
    intro S
    have hM0 : R0 ≤ R0 + ∑ j ∈ S, h j :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hpos j)
    have hMi : ∀ i ∈ S, h i ≤ R0 + ∑ j ∈ S, h j := fun i hi =>
      (Finset.single_le_sum (fun j _ => hpos j) hi).trans (le_add_of_nonneg_left hR0.le)
    have c1 := claim S _ hM0 hMi
    have c2 := hcount _ hM0 S hMi
    have hBM : 0 ≤ (3 * (R0 + ∑ j ∈ S, h j) / R0) ^ (2 * g) :=
      pow_nonneg (div_nonneg (by linarith) hR0.le) _
    have hfM := (Real.exp_pos (-(R0 + ∑ j ∈ S, h j) ^ 2 / 16)).le
    rw [hG0] at c1
    nlinarith [mul_le_mul_of_nonneg_right c2 hfM, mul_nonneg hBM hfM]
  have hnn : ∀ i, 0 ≤ Real.exp (-(h i) ^ 2 / 16) := fun i => (Real.exp_pos _).le
  have hsm : Summable (fun i => Real.exp (-(h i) ^ 2 / 16)) := summable_of_sum_le hnn hsum
  refine ⟨hsm, ?_⟩
  exact Real.tsum_le_of_sum_le hnn hsum

end Formalism.LatticeBaseChangeAlt
