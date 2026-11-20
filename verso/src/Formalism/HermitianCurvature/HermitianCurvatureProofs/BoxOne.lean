import Formalism.HermitianCurvature.Statement
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd

namespace Formalism.FourierDecayAlt.P.BoxOne

open NumberField Finset

/- English proof (translation)
Use `set M := T.sup (fun k => Finset.univ.sup k) + 1 with hM`. Establish `hsub : T ⊆ Fintype.piFinset (fun _ : ι => Finset.range M)`. Introduce `k hk`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `i`.

Rewrite using `[Finset.mem_range, hM, Nat.lt_succ_iff]`. Conclude with `(Finset.le_sup (f := k) (Finset.mem_univ i)).trans (Finset.le_sup (f := fun k => Finset.univ.sup k) hk)`. Establish `hgeom : ∑ n ∈ Finset.range M, q ^ n ≤ 1 / (1 - q)`. Establish `h` using `geom_sum_Ico_le_of_lt_one (m := 0) (n := M) hq0 hq1`. Rewrite `h` using `[← Finset.range_eq_Ico, pow_zero]`. Then use the resulting hypothesis.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_univ_sum]`. Use `_ ≤ ∏ _i : ι, (1 / (1 - q)) := Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun n _ => pow_nonneg hq0 n) (fun _ _ => hgeom)`. Use `_ = (1 / (1 - q)) ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]`.
-/
theorem geom_prod_sum_le {ι : Type} [Fintype ι] (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (T : Finset (ι → ℕ)) :
    ∑ k ∈ T, ∏ i, q ^ (k i) ≤ (1 / (1 - q)) ^ Fintype.card ι := by
  classical
  set M := T.sup (fun k => Finset.univ.sup k) + 1 with hM
  have hsub : T ⊆ Fintype.piFinset (fun _ : ι => Finset.range M) := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range, hM, Nat.lt_succ_iff]
    exact (Finset.le_sup (f := k) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun k => Finset.univ.sup k) hk)
  have hgeom : ∑ n ∈ Finset.range M, q ^ n ≤ 1 / (1 - q) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := M) hq0 hq1
    rwa [← Finset.range_eq_Ico, pow_zero] at h
  calc ∑ k ∈ T, ∏ i, q ^ (k i)
      ≤ ∑ k ∈ Fintype.piFinset (fun _ : ι => Finset.range M), ∏ i, q ^ (k i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => Finset.prod_nonneg fun i _ => pow_nonneg hq0 _)
    _ = ∏ i : ι, ∑ n ∈ Finset.range M, q ^ n := by
        rw [Finset.prod_univ_sum]
    _ ≤ ∏ _i : ι, (1 / (1 - q)) :=
        Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun n _ => pow_nonneg hq0 n)
          (fun _ _ => hgeom)
    _ = (1 / (1 - q)) ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Apply `Finset.prod_le_prod (fun w _ => le_min zero_le_one (Real.rpow_nonneg (div_nonneg (hx w).le (by positivity)) _))` to reduce the goal to its premises. Introduce `w _`. Establish `hpos : 0 < x w / w l` using `div_pos (hx w) (InfinitePlace.pos_iff.2 hl0)`. Rewrite using `[Formalism.SA.P.min_one_rpow _ _ hpos hK, ← Formalism.SA.P.pow_rpow_comm (1 / 2 : ℝ) Kx (by norm_num)]`. Apply `Real.rpow_le_rpow (le_min zero_le_one hpos.le) _ hK` to reduce the goal to its premises.

Establish `hu : 0 < w l / x w` using `div_pos (InfinitePlace.pos_iff.2 hl0) (hx w)`. Use `Formalism.SA.P.min_one_inv_le (w l / x w) hu` as an intermediate fact. Rewrite `this` using `[one_div_div]`. Then use the resulting hypothesis.
-/
theorem term_le (x : InfinitePlace E → ℝ) (hx : ∀ w, 0 < x w) (Kx : ℝ) (hK : 0 ≤ Kx) (l : E)
    (hl0 : l ≠ 0) :
    ∏ w, min 1 ((x w / w l) ^ Kx) ≤ ∏ w, ((1 / 2 : ℝ) ^ Kx) ^ (Nat.log 2 ⌊w l / x w⌋₊) := by
  apply Finset.prod_le_prod (fun w _ => le_min zero_le_one
    (Real.rpow_nonneg (div_nonneg (hx w).le (by positivity)) _))
  intro w _
  have hpos : 0 < x w / w l := div_pos (hx w) (InfinitePlace.pos_iff.2 hl0)
  rw [Formalism.SA.P.min_one_rpow _ _ hpos hK, ← Formalism.SA.P.pow_rpow_comm (1 / 2 : ℝ) Kx (by norm_num)]
  apply Real.rpow_le_rpow (le_min zero_le_one hpos.le) _ hK
  have hu : 0 < w l / x w := div_pos (InfinitePlace.pos_iff.2 hl0) (hx w)
  have := Formalism.SA.P.min_one_inv_le (w l / x w) hu
  rwa [one_div_div] at this

end Formalism.FourierDecayAlt.P.BoxOne

namespace Formalism.FourierDecayAlt.P

open NumberField Finset

/- English proof (translation)
Introduce `Kx hKx`. Use `set p : ℝ := (1 / 2 : ℝ) ^ Kx with hp`. Use `set q : ℝ := 4 * p with hq`. Establish `hp0 : 0 < p` using `by rw [hp]; positivity`. Establish `hp1 : p < 1 / 4`.

Establish `h` using `Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hKx`. Rewrite `h` using `[show ((1 / 2 : ℝ) ^ (2 : ℝ)) = 1 / 4 by rw [Real.rpow_two]; norm_num]`. Conclude with `h`. Establish `hq0 : 0 ≤ q` using `by rw [hq]; linarith`. Establish `hq1 : q < 1` using `by rw [hq]; linarith`.

Use `⟨400 * (1 / (1 - q)), ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ b hb x hx hX S hS`. Use `set f := Fintype.card (InfinitePlace E) with hf`. Use `set N : ℝ := (FractionalIdeal.absNorm b : ℝ) with hN`. Establish `hNpos : 0 < N` using `Formalism.SA.P.absNorm_pos b hb`.

Use `set X := ∏ w, x w with hXdef`. Establish `hX0 : 0 ≤ X` using `Finset.prod_nonneg fun w _ => (hx w).le`. Establish `hX2 : X ^ 2 ≤ N`. Combine the equalities or inequalities in the displayed calculation. Set `kv : E → InfinitePlace E → ℕ` to `fun l w => Nat.log 2 ⌊w l / x w⌋₊`.

Establish `hfib : ∀ k ∈ S.image kv, ∑ l ∈ S with kv l = k, ∏ w, min 1 ((x w / w l) ^ Kx) ≤ (400 : ℝ) ^ f * ∏ w, q ^ (k w)`. Introduce `k _`. Use `set B := ∏ w, p ^ (k w) with hB`. Establish `hB0 : 0 ≤ B` using `Finset.prod_nonneg fun w _ => pow_nonneg hp0.le _`. Establish `hterm : ∀ l ∈ S.filter (fun l => kv l = k), ∏ w, min 1 ((x w / w l) ^ Kx) ≤ B`.

Introduce `l hl`. Rewrite `hl` using `[Finset.mem_filter]`. Take `⟨hlS, hlk⟩` from `hl`. Rewrite using `[hB, ← hlk]`. Conclude with `Formalism.FourierDecayAlt.P.BoxOne.term_le x hx Kx (by linarith) l (hS l hlS).2`.

Establish `hcard : (((S.filter (fun l => kv l = k)).card : ℕ) : ℝ) ≤ (100 : ℝ) ^ f * (∏ w, (2 ^ (k w + 1) * x w) ^ 2) / N`. Apply `Formalism.SA.P.card_box_le b hb (fun w => 2 ^ (k w + 1) * x w) (fun w => by have := hx w; positivity)` to reduce the goal to its premises. Introduce `l hl`. Rewrite `hl` using `[Finset.mem_filter]`. Take `⟨hlS, hlk⟩` from `hl`.

Use `⟨(hS l hlS).1, (hS l hlS).2, fun w => ?_⟩` and prove the remaining obligations. Use `Formalism.SA.P.nat_log_floor_upper (w l / x w) (div_nonneg (by positivity) (hx w).le)` as an intermediate fact. Rewrite `this` using `[div_lt_iff₀ (hx w)]`. Rewrite using `[← hlk]`. Conclude with `this`.

Establish `hpt : ∀ w, (2 ^ (k w + 1) * x w) ^ 2 * p ^ (k w) = 4 * x w ^ 2 * q ^ (k w)`. Introduce `w`. Rewrite using `[hq, mul_pow (4 : ℝ) p (k w), show (4 : ℝ) ^ (k w) = (2 ^ (k w)) ^ 2 by rw [sq, ← mul_pow]; norm_num]`. Expand and normalize the polynomial expressions, which then agree. Establish `hid : (∏ w, (2 ^ (k w + 1) * x w) ^ 2) * B = 4 ^ f * X ^ 2 * ∏ w, q ^ (k w)`.

Rewrite using `[hB, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun w _ => hpt w), Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hf, Finset.prod_pow]`. Establish `hQ0 : 0 ≤ ∏ w, q ^ (k w)` using `Finset.prod_nonneg fun w _ => pow_nonneg hq0 _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_mul_eq_mul_div, mul_assoc, hid]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ (100 : ℝ) ^ f * 4 ^ f * (∏ w, q ^ (k w)) * 1 := mul_le_mul_of_nonneg_left ((div_le_one hNpos).2 hX2) (by positivity)`. Use `_ = (400 : ℝ) ^ f * ∏ w, q ^ (k w) := by`. Rewrite using `[show (400 : ℝ) ^ f = 100 ^ f * 4 ^ f by rw [← mul_pow]; norm_num]; ring`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := kv) (t := S.image kv) (fun l hl => Finset.mem_image_of_mem kv hl)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem box_weights_sum_to_one : Formalism.FourierDecayAlt.BoxSumOne := by
  intro Kx hKx
  set p : ℝ := (1 / 2 : ℝ) ^ Kx with hp
  set q : ℝ := 4 * p with hq
  have hp0 : 0 < p := by rw [hp]; positivity
  have hp1 : p < 1 / 4 := by
    have h := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hKx
    rw [show ((1 / 2 : ℝ) ^ (2 : ℝ)) = 1 / 4 by rw [Real.rpow_two]; norm_num] at h
    exact h
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  have hq1 : q < 1 := by rw [hq]; linarith
  refine ⟨400 * (1 / (1 - q)), ?_⟩
  intro E _ _ _ b hb x hx hX S hS
  classical
  set f := Fintype.card (InfinitePlace E) with hf
  set N : ℝ := (FractionalIdeal.absNorm b : ℝ) with hN
  have hNpos : 0 < N := Formalism.SA.P.absNorm_pos b hb
  set X := ∏ w, x w with hXdef
  have hX0 : 0 ≤ X := Finset.prod_nonneg fun w _ => (hx w).le
  have hX2 : X ^ 2 ≤ N := by
    calc X ^ 2 ≤ (√N) ^ 2 := pow_le_pow_left₀ hX0 hX 2
      _ = N := Real.sq_sqrt hNpos.le
  let kv : E → InfinitePlace E → ℕ := fun l w => Nat.log 2 ⌊w l / x w⌋₊
  have hfib : ∀ k ∈ S.image kv, ∑ l ∈ S with kv l = k, ∏ w, min 1 ((x w / w l) ^ Kx) ≤
      (400 : ℝ) ^ f * ∏ w, q ^ (k w) := by
    intro k _
    set B := ∏ w, p ^ (k w) with hB
    have hB0 : 0 ≤ B := Finset.prod_nonneg fun w _ => pow_nonneg hp0.le _
    have hterm : ∀ l ∈ S.filter (fun l => kv l = k), ∏ w, min 1 ((x w / w l) ^ Kx) ≤ B := by
      intro l hl
      rw [Finset.mem_filter] at hl
      obtain ⟨hlS, hlk⟩ := hl
      rw [hB, ← hlk]
      exact Formalism.FourierDecayAlt.P.BoxOne.term_le x hx Kx (by linarith) l (hS l hlS).2
    have hcard : (((S.filter (fun l => kv l = k)).card : ℕ) : ℝ) ≤
        (100 : ℝ) ^ f * (∏ w, (2 ^ (k w + 1) * x w) ^ 2) / N := by
      apply Formalism.SA.P.card_box_le b hb (fun w => 2 ^ (k w + 1) * x w)
        (fun w => by have := hx w; positivity)
      intro l hl
      rw [Finset.mem_filter] at hl
      obtain ⟨hlS, hlk⟩ := hl
      refine ⟨(hS l hlS).1, (hS l hlS).2, fun w => ?_⟩
      have := Formalism.SA.P.nat_log_floor_upper (w l / x w) (div_nonneg (by positivity) (hx w).le)
      rw [div_lt_iff₀ (hx w)] at this
      rw [← hlk]; exact this
    have hpt : ∀ w, (2 ^ (k w + 1) * x w) ^ 2 * p ^ (k w) = 4 * x w ^ 2 * q ^ (k w) := by
      intro w
      rw [hq, mul_pow (4 : ℝ) p (k w), show (4 : ℝ) ^ (k w) = (2 ^ (k w)) ^ 2 by rw [sq, ← mul_pow]; norm_num]
      ring
    have hid : (∏ w, (2 ^ (k w + 1) * x w) ^ 2) * B = 4 ^ f * X ^ 2 * ∏ w, q ^ (k w) := by
      rw [hB, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun w _ => hpt w),
        Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ← hf, Finset.prod_pow]
    have hQ0 : 0 ≤ ∏ w, q ^ (k w) := Finset.prod_nonneg fun w _ => pow_nonneg hq0 _
    calc ∑ l ∈ S with kv l = k, ∏ w, min 1 ((x w / w l) ^ Kx)
        ≤ (S.filter (fun l => kv l = k)).card • B := Finset.sum_le_card_nsmul _ _ _ hterm
      _ = ((S.filter (fun l => kv l = k)).card : ℝ) * B := by rw [nsmul_eq_mul]
      _ ≤ (100 : ℝ) ^ f * (∏ w, (2 ^ (k w + 1) * x w) ^ 2) / N * B :=
          mul_le_mul_of_nonneg_right hcard hB0
      _ = (100 : ℝ) ^ f * 4 ^ f * (∏ w, q ^ (k w)) * (X ^ 2 / N) := by
          rw [div_mul_eq_mul_div, mul_assoc, hid]; ring
      _ ≤ (100 : ℝ) ^ f * 4 ^ f * (∏ w, q ^ (k w)) * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hNpos).2 hX2) (by positivity)
      _ = (400 : ℝ) ^ f * ∏ w, q ^ (k w) := by
          rw [show (400 : ℝ) ^ f = 100 ^ f * 4 ^ f by rw [← mul_pow]; norm_num]; ring
  rw [← Finset.sum_fiberwise_of_maps_to (g := kv) (t := S.image kv)
    (fun l hl => Finset.mem_image_of_mem kv hl)]
  calc ∑ k ∈ S.image kv, ∑ l ∈ S with kv l = k, ∏ w, min 1 ((x w / w l) ^ Kx)
      ≤ ∑ k ∈ S.image kv, (400 : ℝ) ^ f * ∏ w, q ^ (k w) := Finset.sum_le_sum hfib
    _ = (400 : ℝ) ^ f * ∑ k ∈ S.image kv, ∏ w, q ^ (k w) := by rw [Finset.mul_sum]
    _ ≤ (400 : ℝ) ^ f * (1 / (1 - q)) ^ f :=
        mul_le_mul_of_nonneg_left (Formalism.FourierDecayAlt.P.BoxOne.geom_prod_sum_le q hq0 hq1 _) (by positivity)
    _ = (400 * (1 / (1 - q))) ^ f := by rw [mul_pow]

end Formalism.FourierDecayAlt.P
