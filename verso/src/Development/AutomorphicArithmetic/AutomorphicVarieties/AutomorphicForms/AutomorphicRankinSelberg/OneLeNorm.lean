import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open Set

namespace UpperTheory.V.Af.Rs

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx (funext h)`. Establish `h1 : (1 : ℝ) ≤ ‖x i‖`.

Rewrite using `[Int.norm_eq_abs]`. Conclude with `Int.one_le_abs hi` after adjusting the coercions. Conclude with `h1.trans (norm_le_pi_norm x i)`.
-/
private lemma one_le_norm {x : Fin 2 → ℤ} (hx : x ≠ 0) : 1 ≤ ‖x‖ := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  have h1 : (1 : ℝ) ≤ ‖x i‖ := by
    rw [Int.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hi
  exact h1.trans (norm_le_pi_norm x i)

/- English proof (translation)
Take `⟨-, -, h3, -, -, h6⟩` from `hB s hs`. Establish `him0 : 0 < z.im` using `z.im_pos`. Establish `him : 1 / 2 < z.im`. Use `ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Rewrite using `[h3]`. Simplify using the standard rewrite rules. Establish `hn` using `one_le_norm hx`.

Establish `hpos : 0 < ‖x‖` using `by linarith`. Establish `e1 : ‖x‖ ^ (-(2 * s)) ≤ ‖x‖ ^ (-2 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hn (by linarith [hs.1])`. Establish `e2 : ‖x‖ * ‖x‖ ^ (-3 : ℝ) = ‖x‖ ^ (-2 : ℝ)`. Rewrite using `[show (-2 : ℝ) = 1 + (-3) by norm_num, Real.rpow_add hpos, Real.rpow_one]`. Establish `hp : 0 ≤ ‖x‖ ^ (-2 : ℝ)` using `Real.rpow_nonneg hpos.le _`.

Establish `hq : 4 * z.im ^ 2 ≤ 8 * z.im ^ 3`. Use polynomial arithmetic with `[mul_pos (pow_pos him0 2) (by linarith : (0 : ℝ) < 2 * z.im - 1)]`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma ker_le (hB : KerBd) {s : ℝ} (hs : s ∈ Icc (1 : ℝ) 2) {z : UpperHalfPlane}
    (hz : z ∈ ModularGroup.fd) (x : Fin 2 → ℤ) :
    ker s x z ≤ 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := by
  obtain ⟨-, -, h3, -, -, h6⟩ := hB s hs
  have him0 : 0 < z.im := z.im_pos
  have him : 1 / 2 < z.im := by
    have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
    nlinarith
  by_cases hx : x = 0
  · subst hx
    rw [h3]
    simp
  · have hn := one_le_norm hx
    have hpos : 0 < ‖x‖ := by linarith
    have e1 : ‖x‖ ^ (-(2 * s)) ≤ ‖x‖ ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith [hs.1])
    have e2 : ‖x‖ * ‖x‖ ^ (-3 : ℝ) = ‖x‖ ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = 1 + (-3) by norm_num, Real.rpow_add hpos, Real.rpow_one]
    have hp : 0 ≤ ‖x‖ ^ (-2 : ℝ) := Real.rpow_nonneg hpos.le _
    have hq : 4 * z.im ^ 2 ≤ 8 * z.im ^ 3 := by
      nlinarith [mul_pos (pow_pos him0 2) (by linarith : (0 : ℝ) < 2 * z.im - 1)]
    calc ker s x z ≤ 4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s)) := h6 x z hz
      _ ≤ 4 * z.im ^ 2 * ‖x‖ ^ (-2 : ℝ) := by gcongr
      _ ≤ 8 * z.im ^ 3 * ‖x‖ ^ (-2 : ℝ) := mul_le_mul_of_nonneg_right hq hp
      _ = 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := by rw [← e2]; ring

/- English proof (translation)
The claim follows from `|ker s x z - ker s x' z| ≤ C * ‖x - x'‖ * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x'‖ ^ (-3 : ℝ)) := by obtain ⟨C, hC0, hC⟩ := hD refine ⟨max C 8, hC0.trans (le_max_left _ _), ?_⟩ intro s hs x x' z hz obtain ⟨-, h2, h3, -⟩ := hB s hs have h0 : ‖(0 : Fin 2 → ℤ)‖ ^ (-3 : ℝ) = 0 := by rw [nor …`.
-/
private lemma diff_le (hB : KerBd) (hD : KerDiff) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (1 : ℝ) 2,
    ∀ x x' : Fin 2 → ℤ, ∀ z ∈ ModularGroup.fd,
    |ker s x z - ker s x' z| ≤ C * ‖x - x'‖ * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x'‖ ^ (-3 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := hD
  refine ⟨max C 8, hC0.trans (le_max_left _ _), ?_⟩
  intro s hs x x' z hz
  obtain ⟨-, h2, h3, -⟩ := hB s hs
  have h0 : ‖(0 : Fin 2 → ℤ)‖ ^ (-3 : ℝ) = 0 := by
    rw [norm_zero]
    exact Real.zero_rpow (by norm_num)
  by_cases hx : x = 0
  · by_cases hx' : x' = 0
    · subst hx hx'
      rw [h3, sub_self, abs_zero]
      positivity
    · subst hx
      rw [h3, zero_sub, abs_neg, abs_of_nonneg (h2 _ _), zero_sub, norm_neg, h0, zero_add]
      calc ker s x' z ≤ 8 * ‖x'‖ * z.im ^ 3 * ‖x'‖ ^ (-3 : ℝ) := ker_le hB hs hz x'
        _ ≤ max C 8 * ‖x'‖ * z.im ^ 3 * ‖x'‖ ^ (-3 : ℝ) := by
          gcongr
          exact le_max_right _ _
  · by_cases hx' : x' = 0
    · subst hx'
      rw [h3, sub_zero, abs_of_nonneg (h2 _ _), sub_zero, h0, add_zero]
      calc ker s x z ≤ 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := ker_le hB hs hz x
        _ ≤ max C 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := by
          gcongr
          exact le_max_right _ _
    · refine (hC s hs x x' hx hx' z hz).trans ?_
      gcongr
      exact le_max_left _ _

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
/- English proof (translation)
Introduce `hB hD hW L _`. Take `⟨C, hC0, hC⟩` from `diff_le hB hD`. Establish `hS : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-3 : ℝ)` using `hW.1 3 (by norm_num)`. Use `set S := ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-3 : ℝ) with hSdef`. Use `⟨C * L * (2 * S), ?_⟩` and prove the remaining obligations.

Introduce `v v' s hs z hz`. Establish `hs' : s ∈ Icc (1 : ℝ) 2` using `⟨hs.1.le, hs.2⟩`. Take `⟨-, h2, -, -, -, h6⟩` from `hB s hs'`. Establish `him : 0 < z.im` using `z.im_pos`. Set `a : Fin 2 → ℤ` to `fun i => ((v' i - v i : ZMod L).val : ℤ)`.

Establish `hcls : ∀ x, cls L (x + a) = v' ↔ cls L x = v`. Introduce `x`. Establish `e : cls L (x + a) = cls L x + (v' - v)`. Use function extensionality and compare the values at `i`. Simplify using `[cls, a, ZMod.natCast_zmod_val]`.

Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take the linear combination `h`. Introduce `h`.

Take the linear combination `h`. Establish `ha : ‖a‖ ≤ L`. Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_` and prove the remaining obligations. Simplify using `only [a, Int.norm_eq_abs]`. Rewrite using `[Int.cast_natCast, abs_of_nonneg (by positivity)]`.

Conclude with `(ZMod.val_lt _).le` after adjusting the coercions. Establish `hker : Summable fun x : Fin 2 → ℤ => ker s x z`. Use `Summable.of_nonneg_of_le (fun x => h2 x z) (fun x => h6 x z hz) ?_` and prove the remaining obligations. Conclude with `(hW.1 (2 * s) (by linarith [hs.1])).mul_left _`. Establish `hker' : Summable fun x : Fin 2 → ℤ => ker s (x + a) z` using `(Equiv.addRight a).summable_iff.mpr hker`.

Establish `hS' : Summable fun x : Fin 2 → ℤ => ‖x + a‖ ^ (-3 : ℝ)` using `(Equiv.addRight a).summable_iff.mpr hS`. Use `set g : (Fin 2 → ℤ) → ℝ := fun x => if cls L x = v then ker s x z else 0 with hg`. Use `set g' : (Fin 2 → ℤ) → ℝ := fun x => if cls L x = v then ker s (x + a) z else 0 with hg'`. Establish `hgs : Summable g`. Use `Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hker` and prove the remaining obligations.

Simplify using `only [hg] split_ifs exacts [h2 x z, le_rfl]`. Simplify using `only [hg] split_ifs exacts [le_rfl, h2 x z]`. Establish `hgs' : Summable g'`. Use `Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hker'` and prove the remaining obligations. Simplify using `only [hg'] split_ifs exacts [h2 _ z, le_rfl]`.

Simplify using `only [hg'] split_ifs exacts [le_rfl, h2 _ z]`. Establish `hZ : Zc L v s z = ∑' x, g x` using `rfl`. Establish `hZ' : Zc L v' s z = ∑' x, g' x` using `by show (∑' x, if cls L x = v' then ker s x z else 0) = _`. Rewrite using `[← (Equiv.addRight a).tsum_eq (fun x => if cls L x = v' then ker s x z else 0)]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `only [Equiv.coe_addRight, hg', hcls]`. Establish `hd : ∀ x, |g x - g' x| ≤ C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ))`. Introduce `x`. Establish `hnn : 0 ≤ C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ))` using `by positivity`.

Simplify using `only [hg, hg']`. Use `split_ifs`. Establish `e : ‖x - (x + a)‖ = ‖a‖` using `by simp`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`.

Use `gcongr`. Simplify using `using hnn`. Establish `hh : Summable fun x : Fin 2 → ℤ => C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ))` using `(hS.add hS').mul_left _`. Establish `hshift : ∑' x : Fin 2 → ℤ, ‖x + a‖ ^ (-3 : ℝ) = S` using `(Equiv.addRight a).tsum_eq (fun x => ‖x‖ ^ (-3 : ℝ))`. Establish `hsum : ∑' x : Fin 2 → ℤ, C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) = C * L * z.im ^ 3 * (2 * S)`.

Rewrite using `[tsum_mul_left, hS.tsum_add hS', hshift]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hZ, hZ', ← hgs.tsum_sub hgs']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[abs_le]`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[← tsum_neg]`. Conclude with `Summable.tsum_le_tsum (fun x => neg_le_of_abs_le (hd x)) hh.neg (hgs.sub hgs')`. Conclude with `Summable.tsum_le_tsum (fun x => le_of_abs_le (hd x)) (hgs.sub hgs') hh`. Use `_ = C * L * z.im ^ 3 * (2 * S) := hsum`.

Use `_ = C * L * (2 * S) * z.im ^ 3 := by ring`.
-/
theorem UpperTheory.V.Af.Rs.zDiff :
    UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.KerDiff → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZDiff := by
  intro hB hD hW L _
  obtain ⟨C, hC0, hC⟩ := diff_le hB hD
  have hS : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-3 : ℝ) := hW.1 3 (by norm_num)
  set S := ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-3 : ℝ) with hSdef
  refine ⟨C * L * (2 * S), ?_⟩
  intro v v' s hs z hz
  have hs' : s ∈ Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨-, h2, -, -, -, h6⟩ := hB s hs'
  have him : 0 < z.im := z.im_pos
  let a : Fin 2 → ℤ := fun i => ((v' i - v i : ZMod L).val : ℤ)
  have hcls : ∀ x, cls L (x + a) = v' ↔ cls L x = v := by
    intro x
    have e : cls L (x + a) = cls L x + (v' - v) := by
      funext i
      simp [cls, a, ZMod.natCast_zmod_val]
    rw [e]
    constructor
    · intro h
      linear_combination h
    · intro h
      linear_combination h
  have ha : ‖a‖ ≤ L := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    simp only [a, Int.norm_eq_abs]
    rw [Int.cast_natCast, abs_of_nonneg (by positivity)]
    exact_mod_cast (ZMod.val_lt _).le
  have hker : Summable fun x : Fin 2 → ℤ => ker s x z := by
    refine Summable.of_nonneg_of_le (fun x => h2 x z) (fun x => h6 x z hz) ?_
    exact (hW.1 (2 * s) (by linarith [hs.1])).mul_left _
  have hker' : Summable fun x : Fin 2 → ℤ => ker s (x + a) z :=
    (Equiv.addRight a).summable_iff.mpr hker
  have hS' : Summable fun x : Fin 2 → ℤ => ‖x + a‖ ^ (-3 : ℝ) :=
    (Equiv.addRight a).summable_iff.mpr hS
  set g : (Fin 2 → ℤ) → ℝ := fun x => if cls L x = v then ker s x z else 0 with hg
  set g' : (Fin 2 → ℤ) → ℝ := fun x => if cls L x = v then ker s (x + a) z else 0 with hg'
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hker
    · simp only [hg]
      split_ifs
      exacts [h2 x z, le_rfl]
    · simp only [hg]
      split_ifs
      exacts [le_rfl, h2 x z]
  have hgs' : Summable g' := by
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hker'
    · simp only [hg']
      split_ifs
      exacts [h2 _ z, le_rfl]
    · simp only [hg']
      split_ifs
      exacts [le_rfl, h2 _ z]
  have hZ : Zc L v s z = ∑' x, g x := rfl
  have hZ' : Zc L v' s z = ∑' x, g' x := by
    show (∑' x, if cls L x = v' then ker s x z else 0) = _
    rw [← (Equiv.addRight a).tsum_eq (fun x => if cls L x = v' then ker s x z else 0)]
    congr 1
    funext x
    simp only [Equiv.coe_addRight, hg', hcls]
  have hd : ∀ x, |g x - g' x| ≤ C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by
    intro x
    have hnn : 0 ≤ C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by positivity
    simp only [hg, hg']
    split_ifs
    · have e : ‖x - (x + a)‖ = ‖a‖ := by simp
      calc |ker s x z - ker s (x + a) z|
          ≤ C * ‖x - (x + a)‖ * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) :=
            hC s hs' x (x + a) z hz
        _ ≤ C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by
            rw [e]
            gcongr
    · simpa using hnn
  have hh : Summable fun x : Fin 2 → ℤ =>
      C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) :=
    (hS.add hS').mul_left _
  have hshift : ∑' x : Fin 2 → ℤ, ‖x + a‖ ^ (-3 : ℝ) = S :=
    (Equiv.addRight a).tsum_eq (fun x => ‖x‖ ^ (-3 : ℝ))
  have hsum : ∑' x : Fin 2 → ℤ, C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ))
      = C * L * z.im ^ 3 * (2 * S) := by
    rw [tsum_mul_left, hS.tsum_add hS', hshift]
    ring
  rw [hZ, hZ', ← hgs.tsum_sub hgs']
  calc |∑' x, (g x - g' x)|
      ≤ ∑' x : Fin 2 → ℤ, C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by
        rw [abs_le]
        constructor
        · rw [← tsum_neg]
          exact Summable.tsum_le_tsum (fun x => neg_le_of_abs_le (hd x)) hh.neg (hgs.sub hgs')
        · exact Summable.tsum_le_tsum (fun x => le_of_abs_le (hd x)) (hgs.sub hgs') hh
    _ = C * L * z.im ^ 3 * (2 * S) := hsum
    _ = C * L * (2 * S) * z.im ^ 3 := by ring
