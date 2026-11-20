import Mathlib
import Formalism.PeriodIntegrals.LongWeylElementSquare
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaussianUniqueness.MulMApply

noncomputable section

open Matrix

namespace PI.SwBig.GU

variable {k r : ℕ}

/- English proof (translation)
Use `show ∑ j, g x j * (PI.SwBig.bvec i : Fin (2 * r + k + 1) → ℂ) j = g x i`. Simplify using `[PI.SwBig.bvec, Pi.single_apply]`.
-/
theorem mulVec_bvec (g : Mat k r) (i x : Fin (2 * r + k + 1)) : (g *ᵥ bvec i) x = g x i := by
  show ∑ j, g x j * (PI.SwBig.bvec i : Fin (2 * r + k + 1) → ℂ) j = g x i
  simp [PI.SwBig.bvec, Pi.single_apply]

/- English proof (translation)
Establish `key : ∀ i, m *ᵥ PI.SwBig.bvec i = PI.SwBig.bvec i → m x i = (1 : PI.SwBig.Mat k r) x i`. Introduce `i hi`. Establish `h` using `congrFun hi x`. Rewrite `h` using `[mulVec_bvec]`. Rewrite using `[h, Matrix.one_apply]`.

Simplify using `[PI.SwBig.bvec, Pi.single_apply]`. Take `⟨_, hfix⟩` from `hm`. Distinguish the cases in `h1 : y.val < r`. Establish `e : PI.SwBig.eI k r ⟨y.val, h1⟩ = y` using `Fin.ext rfl`. Establish `h` using `key _ (hfix ⟨y.val, h1⟩).1`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis. Establish `h2 : r + k < y.val`. Assume the negation of the conclusion as `h2`. Apply `hy` to reduce the goal to its premises. Unfold `lv`.

Rewrite using `[if_neg h1, if_pos (show y.val ≤ r + k by omega)]`. Establish `hyl` using `y.isLt`. Establish `hlt : 2 * r + k - y.val < r` using `by omega`. Establish `e : PI.SwBig.esI k r ⟨2 * r + k - y.val, hlt⟩ = y` using `Fin.ext (by show 2 * r + k - (2 * r + k - y.val) = y.val; omega)`. Establish `h` using `key _ (hfix ⟨2 * r + k - y.val, hlt⟩).2`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem UWb_col {m : Mat k r} (hm : m ∈ UWb k r) (x y : Fin (2 * r + k + 1)) (hy : lv k r y ≠ r) :
    m x y = (1 : Mat k r) x y := by
  have key : ∀ i, m *ᵥ PI.SwBig.bvec i = PI.SwBig.bvec i → m x i = (1 : PI.SwBig.Mat k r) x i := by
    intro i hi
    have h := congrFun hi x
    rw [mulVec_bvec] at h
    rw [h, Matrix.one_apply]
    simp [PI.SwBig.bvec, Pi.single_apply]
  obtain ⟨_, hfix⟩ := hm
  by_cases h1 : y.val < r
  · have e : PI.SwBig.eI k r ⟨y.val, h1⟩ = y := Fin.ext rfl
    have h := key _ (hfix ⟨y.val, h1⟩).1
    rwa [e] at h
  · have h2 : r + k < y.val := by
      by_contra h2
      apply hy
      unfold lv
      rw [if_neg h1, if_pos (show y.val ≤ r + k by omega)]
    have hyl := y.isLt
    have hlt : 2 * r + k - y.val < r := by omega
    have e : PI.SwBig.esI k r ⟨2 * r + k - y.val, hlt⟩ = y :=
      Fin.ext (by show 2 * r + k - (2 * r + k - y.val) = y.val; omega)
    have h := key _ (hfix ⟨2 * r + k - y.val, hlt⟩).2
    rwa [e] at h

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Conclude with `h (Matrix.one_apply_ne hne)`.
-/
private theorem eq_of_one_apply_ne_zero {x y : Fin (2 * r + k + 1)} (h : (1 : PI.SwBig.Mat k r) x y ≠ 0) : x = y := by
  by_contra hne
  exact h (Matrix.one_apply_ne hne)

/- English proof (translation)
Rewrite using `[lv_sg]`. Use `lv_le x` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem lv_sg_ne_of_lv_ne {x : Fin (2 * r + k + 1)} (hx : lv k r x ≠ r) :
    lv k r (sg k r x) ≠ r := by
  rw [lv_sg]
  have := lv_le x
  omega

/- English proof (translation)
Rewrite using `[(inv_of_UH hg).1, Hpk_eq, mul_M_apply, M_mul_apply]`. Simplify using `only [sg_sg, sn_sg, Matrix.conjTranspose_apply]`.
-/
private theorem inv_apply_sg_sg_of_mem_UH {g : PI.SwBig.Mat k r} (hg : g ∈ PI.SwBig.UH (PI.SwBig.Hpk k r))
    (x y : Fin (2 * r + k + 1)) :
    g⁻¹ (sg k r y) (sg k r x) = sn k r y * star (g x y) * sn k r x := by
  rw [(inv_of_UH hg).1, Hpk_eq, mul_M_apply, M_mul_apply]
  simp only [sg_sg, sn_sg, Matrix.conjTranspose_apply]

/- English proof (translation)
Establish `hl : m⁻¹ * m = 1` using `(inv_of_UH hm.1).2.1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl (fun j _ => by rw [UWb_col hm j y hy])`. Use `_ = (1 : PI.SwBig.Mat k r) x y := by rw [hl]`.
-/
private theorem inv_apply_eq_one_apply_of_mem_UWb_of_lv_right_ne {m : PI.SwBig.Mat k r} (hm : m ∈ PI.SwBig.UWb k r)
    (x y : Fin (2 * r + k + 1)) (hy : lv k r y ≠ r) : m⁻¹ x y = (1 : PI.SwBig.Mat k r) x y := by
  have hl : m⁻¹ * m = 1 := (inv_of_UH hm.1).2.1
  calc m⁻¹ x y = (m⁻¹ * 1) x y := by rw [Matrix.mul_one]
    _ = (m⁻¹ * m) x y := by
        simp only [Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun j _ => by rw [UWb_col hm j y hy])
    _ = (1 : PI.SwBig.Mat k r) x y := by rw [hl]

/- English proof (translation)
Establish `h` using `inv_apply_sg_sg_of_mem_UH hm.1 x y`. Rewrite `h` using `[inv_apply_eq_one_apply_of_mem_UWb_of_lv_right_ne hm _ _ (lv_sg_ne_of_lv_ne hx)]`. Distinguish the cases in `hxy : x = y`. Substitute `hxy` using the available equality. Rewrite `h` using `[Matrix.one_apply_eq]`.

Establish `h2 : star (m x x) = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sn_mul_self, one_mul]`. Use `_ = sn k r x * star (m x x) * sn k r x := by ring`. Use `_ = 1 := h.symm`.

Establish `h3` using `congrArg star h2`. Rewrite `h3` using `[star_star, star_one]`. Rewrite using `[h3, Matrix.one_apply_eq]`. Establish `hw : sg k r y ≠ sg k r x` using `fun e => hxy (sg_inj e).symm`. Rewrite `h` using `[Matrix.one_apply_ne hw]`.

Rewrite using `[Matrix.one_apply_ne hxy]`. Break down `mul_eq_zero.1 h.symm with h' | h'` into its components or cases. Break down `mul_eq_zero.1 h' with h'' | h''` into its components or cases. Conclude with `absurd h'' (sn_ne_zero y)`. Conclude with `star_eq_zero.1 h''`.

Conclude with `absurd h' (sn_ne_zero x)`.
-/
private theorem apply_eq_one_apply_of_mem_UWb_of_lv_left_ne {m : PI.SwBig.Mat k r} (hm : m ∈ PI.SwBig.UWb k r)
    (x y : Fin (2 * r + k + 1)) (hx : lv k r x ≠ r) : m x y = (1 : PI.SwBig.Mat k r) x y := by
  have h := inv_apply_sg_sg_of_mem_UH hm.1 x y
  rw [inv_apply_eq_one_apply_of_mem_UWb_of_lv_right_ne hm _ _ (lv_sg_ne_of_lv_ne hx)] at h
  by_cases hxy : x = y
  · subst hxy
    rw [Matrix.one_apply_eq] at h
    have h2 : star (m x x) = 1 := by
      calc star (m x x) = (sn k r x * sn k r x) * star (m x x) := by
            rw [sn_mul_self, one_mul]
        _ = sn k r x * star (m x x) * sn k r x := by ring
        _ = 1 := h.symm
    have h3 := congrArg star h2
    rw [star_star, star_one] at h3
    rw [h3, Matrix.one_apply_eq]
  · have hw : sg k r y ≠ sg k r x := fun e => hxy (sg_inj e).symm
    rw [Matrix.one_apply_ne hw] at h
    rw [Matrix.one_apply_ne hxy]
    rcases mul_eq_zero.1 h.symm with h' | h'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact absurd h'' (sn_ne_zero y)
      · exact star_eq_zero.1 h''
    · exact absurd h' (sn_ne_zero x)

/- English proof (translation)
Introduce `x y hxy`. Use `show lv k r x = lv k r y`. Distinguish the cases in `hx : lv k r x = r`. Distinguish the cases in `hy : lv k r y = r`. Rewrite using `[hx, hy]`.

Rewrite `hxy` using `[UWb_col hm x y hy]`. Rewrite using `[eq_of_one_apply_ne_zero hxy]`. Rewrite `hxy` using `[apply_eq_one_apply_of_mem_UWb_of_lv_left_ne hm x y hx]`. Rewrite using `[eq_of_one_apply_ne_zero hxy]`.
-/
theorem UWb_supp {m : Mat k r} (hm : m ∈ UWb k r) : Supp m (fun a b => a = b) := by
  intro x y hxy
  show lv k r x = lv k r y
  by_cases hx : lv k r x = r
  · by_cases hy : lv k r y = r
    · rw [hx, hy]
    · rw [UWb_col hm x y hy] at hxy
      rw [eq_of_one_apply_ne_zero hxy]
  · rw [apply_eq_one_apply_of_mem_UWb_of_lv_left_ne hm x y hx] at hxy
    rw [eq_of_one_apply_ne_zero hxy]

/- English proof (translation)
Unfold `lv`. Apply the tactic sequence `split_ifs <;> omega`.
-/
private theorem lv_cases (x : Fin (2 * r + k + 1)) :
    (x.val < r ∧ lv k r x = x.val) ∨ (r ≤ x.val ∧ x.val ≤ r + k ∧ lv k r x = r) ∨
      (r + k < x.val ∧ lv k r x = x.val - k) := by
  unfold lv
  split_ifs <;> omega

/- English proof (translation)
Introduce `x y hxy`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hj : lv k r j ≤ lv k r x`. Rewrite using `[hA x j hj]`.

Distinguish the cases in `hxj : x = j`. Substitute `hxj` using the available equality. Rewrite using `[hB x y hxy]`. Rewrite using `[Matrix.one_apply_ne hxj, zero_mul, zero_mul]`. Establish `hjy : lv k r y ≤ lv k r j` using `by omega`.

Rewrite using `[hB j y hjy]`. Establish `hne : j ≠ y`. Introduce and unpack `rfl`. Conclude with `hj hxy`. Establish `hne' : x ≠ j`.

Introduce and unpack `rfl`. Conclude with `hj le_rfl`. Rewrite using `[Matrix.one_apply_ne hne, Matrix.one_apply_ne hne', mul_zero, mul_zero]`. Use `_ = ((1 : PI.SwBig.Mat k r) * 1) x y := Matrix.mul_apply.symm`. Use `_ = (1 : PI.SwBig.Mat k r) x y := by rw [Matrix.mul_one]`.
-/
private theorem mul_apply_eq_one_apply_of_lv_le {A B : PI.SwBig.Mat k r}
    (hA : ∀ x y, lv k r y ≤ lv k r x → A x y = (1 : PI.SwBig.Mat k r) x y)
    (hB : ∀ x y, lv k r y ≤ lv k r x → B x y = (1 : PI.SwBig.Mat k r) x y) :
    ∀ x y, lv k r y ≤ lv k r x → (A * B) x y = (1 : PI.SwBig.Mat k r) x y := by
  intro x y hxy
  calc (A * B) x y = ∑ j, A x j * B j y := Matrix.mul_apply
    _ = ∑ j, (1 : PI.SwBig.Mat k r) x j * (1 : PI.SwBig.Mat k r) j y := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hj : lv k r j ≤ lv k r x
        · rw [hA x j hj]
          by_cases hxj : x = j
          · subst hxj
            rw [hB x y hxy]
          · rw [Matrix.one_apply_ne hxj, zero_mul, zero_mul]
        · have hjy : lv k r y ≤ lv k r j := by omega
          rw [hB j y hjy]
          have hne : j ≠ y := by
            rintro rfl
            exact hj hxy
          have hne' : x ≠ j := by
            rintro rfl
            exact hj le_rfl
          rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hne', mul_zero, mul_zero]
    _ = ((1 : PI.SwBig.Mat k r) * 1) x y := Matrix.mul_apply.symm
    _ = (1 : PI.SwBig.Mat k r) x y := by rw [Matrix.mul_one]

/- English proof (translation)
Introduce `X Y hXY`. Establish `h` using `inv_apply_sg_sg_of_mem_UH hg (sg k r Y) (sg k r X)`. Rewrite `h` using `[sg_sg, sg_sg]`. Establish `hlX` using `lv_le (k := k) (r := r) X`. Establish `hlY` using `lv_le (k := k) (r := r) Y`.

Rewrite using `[h, hU (sg k r Y) (sg k r X) (by rw [lv_sg, lv_sg]; omega)]`. Distinguish the cases in `hxy : X = Y`. Substitute `hxy` using the available equality. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq, star_one, mul_one, sn_mul_self]`. Establish `hw : sg k r Y ≠ sg k r X` using `fun e => hxy (sg_inj e).symm`.

Rewrite using `[Matrix.one_apply_ne hw, Matrix.one_apply_ne hxy, star_zero, mul_zero, zero_mul]`.
-/
private theorem inv_apply_eq_one_apply_of_mem_UH_of_lv_le {g : PI.SwBig.Mat k r} (hg : g ∈ PI.SwBig.UH (PI.SwBig.Hpk k r))
    (hU : ∀ x y, lv k r y ≤ lv k r x → g x y = (1 : PI.SwBig.Mat k r) x y) :
    ∀ x y, lv k r y ≤ lv k r x → g⁻¹ x y = (1 : PI.SwBig.Mat k r) x y := by
  intro X Y hXY
  have h := inv_apply_sg_sg_of_mem_UH hg (sg k r Y) (sg k r X)
  rw [sg_sg, sg_sg] at h
  have hlX := lv_le (k := k) (r := r) X
  have hlY := lv_le (k := k) (r := r) Y
  rw [h, hU (sg k r Y) (sg k r X) (by rw [lv_sg, lv_sg]; omega)]
  by_cases hxy : X = Y
  · subst hxy
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, star_one, mul_one, sn_mul_self]
  · have hw : sg k r Y ≠ sg k r X := fun e => hxy (sg_inj e).symm
    rw [Matrix.one_apply_ne hw, Matrix.one_apply_ne hxy, star_zero, mul_zero, zero_mul]

/- English proof (translation)
It suffices to establish `H : ∀ n, ∀ x y, lv k r y = n → n ≤ L → n ≤ lv k r x → g⁻¹ x y = (1 : PI.SwBig.Mat k r) x y by`. Introduce `x y h1 h2`. Conclude with `H _ x y rfl h1 h2`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`.

Consider the case `_ n ih`. Introduce `x y hyn hnL hnx`. Establish `e : (g⁻¹ * g) x y = (1 : PI.SwBig.Mat k r) x y` using `by rw [hgi]`. Rewrite `e` using `[Matrix.mul_apply, Finset.sum_eq_single y]`. Rewrite `e` using `[hg y y (by omega) le_rfl, Matrix.one_apply_eq, mul_one]`. Then use the resulting hypothesis.

Introduce `j _ hjy`. Distinguish the cases in `hj : lv k r y ≤ lv k r j`. Rewrite using `[hg j y (by omega) hj, Matrix.one_apply_ne hjy, mul_zero]`. Establish `hlt : lv k r j < n` using `by omega`. Establish `hxj : x ≠ j`.

Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Rewrite using `[ih (lv k r j) hlt x j rfl (by omega) (by omega), Matrix.one_apply_ne hxj, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ y) h`.
-/
private theorem inv_apply_eq_one_apply_of_lv_le_bound {g : PI.SwBig.Mat k r} (hgi : g⁻¹ * g = 1) (L : ℕ)
    (hg : ∀ x y, lv k r y ≤ L → lv k r y ≤ lv k r x → g x y = (1 : PI.SwBig.Mat k r) x y) :
    ∀ x y, lv k r y ≤ L → lv k r y ≤ lv k r x → g⁻¹ x y = (1 : PI.SwBig.Mat k r) x y := by
  suffices H : ∀ n, ∀ x y, lv k r y = n → n ≤ L → n ≤ lv k r x →
      g⁻¹ x y = (1 : PI.SwBig.Mat k r) x y by
    intro x y h1 h2
    exact H _ x y rfl h1 h2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hyn hnL hnx
    have e : (g⁻¹ * g) x y = (1 : PI.SwBig.Mat k r) x y := by rw [hgi]
    rw [Matrix.mul_apply, Finset.sum_eq_single y] at e
    · rwa [hg y y (by omega) le_rfl, Matrix.one_apply_eq, mul_one] at e
    · intro j _ hjy
      by_cases hj : lv k r y ≤ lv k r j
      · rw [hg j y (by omega) hj, Matrix.one_apply_ne hjy, mul_zero]
      · have hlt : lv k r j < n := by omega
        have hxj : x ≠ j := by
          rintro rfl
          omega
        rw [ih (lv k r j) hlt x j rfl (by omega) (by omega), Matrix.one_apply_ne hxj, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ y) h

/- English proof (translation)
Take `⟨hU, h1, h2⟩` from `hg`. Establish `low : ∀ x y, lv k r y ≤ r → lv k r y ≤ lv k r x → g x y = (1 : PI.SwBig.Mat k r) x y`. Introduce `x y hy hxy`. Break down `lv_cases y with ⟨hy1, hly⟩ | ⟨hy1, hy2, hly⟩ | ⟨hy1, hly⟩` into its components or cases. Establish `e : PI.SwBig.eI k r ⟨y.val, hy1⟩ = y` using `Fin.ext rfl`.

Establish `hx : y.val ≤ x.val`. Apply the tactic sequence `rcases lv_cases x with h | h | h <;> omega`. Establish `h3` using `h1 ⟨y.val, hy1⟩ x hx`. Rewrite `h3` using `[e]`. Rewrite using `[h3, Matrix.one_apply]`.

Establish `hx : r ≤ x.val`. Apply the tactic sequence `rcases lv_cases x with h | h | h <;> omega`. Rewrite using `[h2 x y hy1 hy2 hx, Matrix.one_apply]`. Use linear arithmetic over natural numbers and integers. Introduce `x y hxy`.

Distinguish the cases in `hy : lv k r y ≤ r`. Conclude with `low x y hy hxy`. Establish `hinv` using `inv_apply_eq_one_apply_of_lv_le_bound (inv_of_UH hU).2.1 r low`. Establish `h` using `inv_apply_sg_sg_of_mem_UH hU x y`. Establish `hlx` using `lv_le (k := k) (r := r) x`.

Rewrite `h` using `[hinv (sg k r y) (sg k r x) (by rw [lv_sg]; omega) (by rw [lv_sg, lv_sg]; omega)]`. Distinguish the cases in `hxe : x = y`. Substitute `hxe` using the available equality. Rewrite `h` using `[Matrix.one_apply_eq]`. Establish `h4 : star (g x x) = 1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sn_mul_self, one_mul]`. Use `_ = sn k r x * star (g x x) * sn k r x := by ring`. Use `_ = 1 := h.symm`. Establish `h5` using `congrArg star h4`.

Rewrite `h5` using `[star_star, star_one]`. Rewrite using `[h5, Matrix.one_apply_eq]`. Establish `hw : sg k r y ≠ sg k r x` using `fun e => hxe (sg_inj e).symm`. Rewrite `h` using `[Matrix.one_apply_ne hw]`. Rewrite using `[Matrix.one_apply_ne hxe]`.

Break down `mul_eq_zero.1 h.symm with h' | h'` into its components or cases. Break down `mul_eq_zero.1 h' with h'' | h''` into its components or cases. Conclude with `absurd h'' (sn_ne_zero y)`. Conclude with `star_eq_zero.1 h''`. Conclude with `absurd h' (sn_ne_zero x)`.
-/
private theorem apply_eq_one_apply_of_mem_Nset_of_lv_le {g : PI.SwBig.Mat k r} (hg : g ∈ PI.SwBig.Nset k r) :
    ∀ x y, lv k r y ≤ lv k r x → g x y = (1 : PI.SwBig.Mat k r) x y := by
  obtain ⟨hU, h1, h2⟩ := hg
  have low : ∀ x y, lv k r y ≤ r → lv k r y ≤ lv k r x → g x y = (1 : PI.SwBig.Mat k r) x y := by
    intro x y hy hxy
    rcases lv_cases y with ⟨hy1, hly⟩ | ⟨hy1, hy2, hly⟩ | ⟨hy1, hly⟩
    · have e : PI.SwBig.eI k r ⟨y.val, hy1⟩ = y := Fin.ext rfl
      have hx : y.val ≤ x.val := by
        rcases lv_cases x with h | h | h <;> omega
      have h3 := h1 ⟨y.val, hy1⟩ x hx
      rw [e] at h3
      rw [h3, Matrix.one_apply]
    · have hx : r ≤ x.val := by
        rcases lv_cases x with h | h | h <;> omega
      rw [h2 x y hy1 hy2 hx, Matrix.one_apply]
    · omega
  intro x y hxy
  by_cases hy : lv k r y ≤ r
  · exact low x y hy hxy
  · have hinv := inv_apply_eq_one_apply_of_lv_le_bound (inv_of_UH hU).2.1 r low
    have h := inv_apply_sg_sg_of_mem_UH hU x y
    have hlx := lv_le (k := k) (r := r) x
    rw [hinv (sg k r y) (sg k r x) (by rw [lv_sg]; omega) (by rw [lv_sg, lv_sg]; omega)] at h
    by_cases hxe : x = y
    · subst hxe
      rw [Matrix.one_apply_eq] at h
      have h4 : star (g x x) = 1 := by
        calc star (g x x) = (sn k r x * sn k r x) * star (g x x) := by
              rw [sn_mul_self, one_mul]
          _ = sn k r x * star (g x x) * sn k r x := by ring
          _ = 1 := h.symm
      have h5 := congrArg star h4
      rw [star_star, star_one] at h5
      rw [h5, Matrix.one_apply_eq]
    · have hw : sg k r y ≠ sg k r x := fun e => hxe (sg_inj e).symm
      rw [Matrix.one_apply_ne hw] at h
      rw [Matrix.one_apply_ne hxe]
      rcases mul_eq_zero.1 h.symm with h' | h'
      · rcases mul_eq_zero.1 h' with h'' | h''
        · exact absurd h'' (sn_ne_zero y)
        · exact star_eq_zero.1 h''
      · exact absurd h' (sn_ne_zero x)

/- English proof (translation)
Use `⟨fun y => if h : y.val < r then c ⟨y.val, h⟩ else if h2 : y.val ≤ r + k then 1 else (star (c ⟨2 * r + k - y.val, by omega⟩))⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [PI.SwBig.bigCell, M, sg, PI.SwBig.esI, Fin.ext_iff, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Introduce `a`.

Simplify using `[PI.SwBig.eI]`. Introduce `hc z dsimp only split_ifs`. Conclude with `hc _`. Conclude with `one_ne_zero`. Conclude with `inv_ne_zero (star_ne_zero.2 (hc _))`.
-/
private theorem exists_bigCell_eq_M (c : Fin r → ℂ) :
    ∃ f : Fin (2 * r + k + 1) → ℂ, PI.SwBig.bigCell k r c 1 = M k r f ∧
      (∀ a, f (PI.SwBig.eI k r a) = c a) ∧ ((∀ a, c a ≠ 0) → ∀ z, f z ≠ 0) := by
  refine ⟨fun y => if h : y.val < r then c ⟨y.val, h⟩ else if h2 : y.val ≤ r + k then 1
    else (star (c ⟨2 * r + k - y.val, by omega⟩))⁻¹, ?_, ?_, ?_⟩
  · ext i j
    simp only [PI.SwBig.bigCell, M, sg, PI.SwBig.esI, Fin.ext_iff, Matrix.one_apply]
    split_ifs <;> first | rfl | omega
  · intro a
    simp [PI.SwBig.eI]
  · intro hc z
    dsimp only
    split_ifs
    · exact hc _
    · exact one_ne_zero
    · exact inv_ne_zero (star_ne_zero.2 (hc _))

/- English proof (translation)
Establish `hl : ∀ x y, 2 * r ≤ lv k r x + lv k r y → (n * W₁) x y = W₁ x y`. Introduce `x y hxy`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hj : W₁ j y = 0`.

Rewrite using `[hj, mul_zero, mul_zero]`. Use `h₁ j y hj` as an intermediate fact. Rewrite using `[hn x j (by omega)]`. Use `_ = ((1 : PI.SwBig.Mat k r) * W₁) x y := Matrix.mul_apply.symm`. Use `_ = W₁ x y := by rw [Matrix.one_mul]`.

Establish `hr : ∀ x y, lv k r x + lv k r y ≤ 2 * r → (W₂ * u) x y = W₂ x y`. Introduce `x y hxy`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hj : W₂ x j = 0`.

Rewrite using `[hj, zero_mul, zero_mul]`. Use `h₂ x j hj` as an intermediate fact. Rewrite using `[hu j y (by omega)]`. Use `_ = (W₂ * (1 : PI.SwBig.Mat k r)) x y := Matrix.mul_apply.symm`. Use `_ = W₂ x y := by rw [Matrix.mul_one]`.

Establish `heq : W₁ = W₂`. Use extensionality with `x y`. Distinguish the cases in `hs : lv k r x + lv k r y = 2 * r`. Establish `e` using `hl x y hs.ge`. Rewrite `e` using `[h, hr x y hs.le]`.

Conclude with `e.symm`. Establish `e1 : W₁ x y = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hs (h₁ x y hne)`. Establish `e2 : W₂ x y = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `hs (h₂ x y hne)`. Rewrite using `[e1, e2]`. Use `⟨heq, ?_⟩` and prove the remaining obligations. Use extensionality with `x y`.

Distinguish the cases in `hs : 2 * r ≤ lv k r x + lv k r y`. Conclude with `hl x y hs`. Rewrite using `[h, hr x y (by omega), heq]`.
-/
private theorem W_eq_and_mul_W_eq_of_mul_eq_mul_of_lv_sum {n u W₁ W₂ : PI.SwBig.Mat k r}
    (hn : ∀ x y, lv k r y ≤ lv k r x → n x y = (1 : PI.SwBig.Mat k r) x y)
    (hu : ∀ x y, lv k r y ≤ lv k r x → u x y = (1 : PI.SwBig.Mat k r) x y)
    (h₁ : ∀ x y, W₁ x y ≠ 0 → lv k r x + lv k r y = 2 * r)
    (h₂ : ∀ x y, W₂ x y ≠ 0 → lv k r x + lv k r y = 2 * r)
    (h : n * W₁ = W₂ * u) : W₁ = W₂ ∧ n * W₁ = W₁ := by
  have hl : ∀ x y, 2 * r ≤ lv k r x + lv k r y → (n * W₁) x y = W₁ x y := by
    intro x y hxy
    calc (n * W₁) x y = ∑ j, n x j * W₁ j y := Matrix.mul_apply
      _ = ∑ j, (1 : PI.SwBig.Mat k r) x j * W₁ j y := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          by_cases hj : W₁ j y = 0
          · rw [hj, mul_zero, mul_zero]
          · have := h₁ j y hj
            rw [hn x j (by omega)]
      _ = ((1 : PI.SwBig.Mat k r) * W₁) x y := Matrix.mul_apply.symm
      _ = W₁ x y := by rw [Matrix.one_mul]
  have hr : ∀ x y, lv k r x + lv k r y ≤ 2 * r → (W₂ * u) x y = W₂ x y := by
    intro x y hxy
    calc (W₂ * u) x y = ∑ j, W₂ x j * u j y := Matrix.mul_apply
      _ = ∑ j, W₂ x j * (1 : PI.SwBig.Mat k r) j y := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          by_cases hj : W₂ x j = 0
          · rw [hj, zero_mul, zero_mul]
          · have := h₂ x j hj
            rw [hu j y (by omega)]
      _ = (W₂ * (1 : PI.SwBig.Mat k r)) x y := Matrix.mul_apply.symm
      _ = W₂ x y := by rw [Matrix.mul_one]
  have heq : W₁ = W₂ := by
    ext x y
    by_cases hs : lv k r x + lv k r y = 2 * r
    · have e := hl x y hs.ge
      rw [h, hr x y hs.le] at e
      exact e.symm
    · have e1 : W₁ x y = 0 := by
        by_contra hne
        exact hs (h₁ x y hne)
      have e2 : W₂ x y = 0 := by
        by_contra hne
        exact hs (h₂ x y hne)
      rw [e1, e2]
  refine ⟨heq, ?_⟩
  ext x y
  by_cases hs : 2 * r ≤ lv k r x + lv k r y
  · exact hl x y hs
  · rw [h, hr x y (by omega), heq]

/- English proof (translation)
Introduce `x y hxy`. Rewrite `hxy` using `[M_mul_apply]`. Establish `h2 : m (sg k r x) y ≠ 0` using `fun h0 => hxy (by rw [h0, mul_zero])`. Establish `e : lv k r (sg k r x) = lv k r y` using `UWb_supp hm (sg k r x) y h2`. Rewrite `e` using `[lv_sg]`.

Use `lv_le (k := k) (r := r) x` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem lv_add_lv_eq_of_M_mul_apply_ne_zero {m : PI.SwBig.Mat k r} (hm : m ∈ PI.SwBig.UWb k r)
    (f : Fin (2 * r + k + 1) → ℂ) :
    ∀ x y, (M k r f * m) x y ≠ 0 → lv k r x + lv k r y = 2 * r := by
  intro x y hxy
  rw [M_mul_apply] at hxy
  have h2 : m (sg k r x) y ≠ 0 := fun h0 => hxy (by rw [h0, mul_zero])
  have e : lv k r (sg k r x) = lv k r y := UWb_supp hm (sg k r x) y h2
  rw [lv_sg] at e
  have := lv_le (k := k) (r := r) x
  omega

/- English proof (translation)
Use extensionality with `x y`. Establish `e` using `congrFun (congrFun h (sg k r x)) y`. Rewrite `e` using `[M_mul_apply, M_mul_apply, sg_sg]`. Conclude with `mul_left_cancel₀ (hf x) e`.
-/
private theorem eq_of_M_mul_eq_M_mul_of_ne_zero {f : Fin (2 * r + k + 1) → ℂ} (hf : ∀ z, f z ≠ 0)
    {A A' : PI.SwBig.Mat k r} (h : M k r f * A = M k r f * A') : A = A' := by
  ext x y
  have e := congrFun (congrFun h (sg k r x)) y
  rw [M_mul_apply, M_mul_apply, sg_sg] at e
  exact mul_left_cancel₀ (hf x) e

/- English proof (translation)
Establish `h' : n * M k r f = M k r f`. Use `congrArg (· * m⁻¹) h` as an intermediate fact. Simplify using `only [Matrix.mul_assoc, hm, Matrix.mul_one] at this`. Conclude with `this`. Use extensionality with `x y`.

Establish `e` using `congrFun (congrFun h' x) (sg k r y)`. Rewrite `e` using `[mul_M_apply, sg_sg]`. Establish `e2 : M k r f x (sg k r y) = (1 : PI.SwBig.Mat k r) x y * f (sg k r y)`. Simplify using `only [M, sg_sg, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite `e` using `[e2]`. Conclude with `mul_right_cancel₀ (hf _) e`.
-/
private theorem eq_one_of_mul_M_mul_eq {f : Fin (2 * r + k + 1) → ℂ} (hf : ∀ z, f z ≠ 0)
    {n m : PI.SwBig.Mat k r} (hm : m * m⁻¹ = 1) (h : n * (M k r f * m) = M k r f * m) : n = 1 := by
  have h' : n * M k r f = M k r f := by
    have := congrArg (· * m⁻¹) h
    simp only [Matrix.mul_assoc, hm, Matrix.mul_one] at this
    exact this
  ext x y
  have e := congrFun (congrFun h' x) (sg k r y)
  rw [mul_M_apply, sg_sg] at e
  have e2 : M k r f x (sg k r y) = (1 : PI.SwBig.Mat k r) x y * f (sg k r y) := by
    simp only [M, sg_sg, Matrix.one_apply]
    split_ifs <;> simp
  rw [e2] at e
  exact mul_right_cancel₀ (hf _) e

/- English proof (translation)
Introduce `k r n₁ n₂ m₁ m₂ u₁ u₂ c₁ c₂ hn₁ hn₂ hm₁ hm₂ hu₁ hu₂ hc h`. Take `⟨_, hn₂l, hn₂r⟩` from `inv_of_UH hn₂.1`. Take `⟨_, hu₁l, hu₁r⟩` from `inv_of_UH hu₁.1`. Take `⟨_, hu₂l, hu₂r⟩` from `inv_of_UH hu₂.1`. Take `⟨_, hm₁l, hm₁r⟩` from `inv_of_UH hm₁.1`.

Take `⟨f₁, hB₁, hf₁, hf₁nz⟩` from `exists_bigCell_eq_M (k := k) c₁`. Take `⟨f₂, hB₂, hf₂, -⟩` from `exists_bigCell_eq_M (k := k) c₂`. Rewrite `h` using `[hB₁, hB₂]`. Establish `key : (n₂⁻¹ * n₁) * (M k r f₁ * m₁) = (M k r f₂ * m₂) * (u₂⁻¹ * u₁)`. Use `congrArg (fun X => n₂⁻¹ * X * u₁) h` as an intermediate fact.

Simplify using `only [Matrix.mul_assoc] at this ⊢`. Rewrite `this` using `[hu₁l, Matrix.mul_one, ← Matrix.mul_assoc n₂⁻¹ n₂, hn₂l, Matrix.one_mul]`. Conclude with `this`. Take `⟨heq, hnW⟩` from `W_eq_and_mul_W_eq_of_mul_eq_mul_of_lv_sum (mul_apply_eq_one_apply_of_lv_le (inv_apply_eq_one_apply_of_mem_UH_of_lv_le hn₂.1 (apply_eq_one_apply_of_mem_Nset_of_lv_le hn₂)) (apply_eq_one_apply_of_mem_Nset_of_lv_le hn₁)) (mul_apply_eq_one_apply_of_lv_le (inv_apply_eq_one_apply_of_me …`. Establish `hc12 : c₁ = c₂`.

Use function extensionality and compare the values at `a`. Establish `e` using `congrFun (congrFun heq (PI.SwBig.esI k r a)) (PI.SwBig.eI k r a)`. Establish `ha` using `a.isLt`. Establish `hs : sg k r (PI.SwBig.esI k r a) = PI.SwBig.eI k r a`. Apply `Fin.ext` to reduce the goal to its premises.

Use `show (if r ≤ 2 * r + k - a.val ∧ 2 * r + k - a.val ≤ r + k then 2 * r + k - a.val else 2 * r + k - (2 * r + k - a.val)) = a.val`. Apply the tactic sequence `split <;> omega`. Establish `hl : lv k r (PI.SwBig.eI k r a) ≠ r`. Establish `e4 : lv k r (PI.SwBig.eI k r a) = a.val`. Unfold `lv`.

Rewrite using `[if_pos (show (PI.SwBig.eI k r a).val < r from a.isLt)]`. Both sides reduce to the same expression. Use linear arithmetic over natural numbers and integers. Rewrite `e` using `[M_mul_apply, M_mul_apply, hs, UWb_col hm₁ _ _ hl, UWb_col hm₂ _ _ hl, hf₁, hf₂, Matrix.one_apply_eq, mul_one, mul_one]`. Conclude with `e`.

Establish `hfnz : ∀ z, f₁ z ≠ 0` using `hf₁nz (by rw [hc12]; exact hc)`. Establish `hMM : M k r f₂ = M k r f₁` using `by rw [← hB₁, ← hB₂, hc12]`. Rewrite `heq`, `key` using `[hMM]`. Establish `hm : m₁ = m₂` using `eq_of_M_mul_eq_M_mul_of_ne_zero hfnz heq`. Rewrite `key` using `[← hm]`.

Establish `hn : n₂⁻¹ * n₁ = 1` using `eq_one_of_mul_M_mul_eq hfnz hm₁r hnW`. Establish `hu : u₂⁻¹ * u₁ = 1`. Establish `e : M k r f₁ * m₁ * (u₂⁻¹ * u₁) = M k r f₁ * m₁ * 1`. Rewrite using `[Matrix.mul_one, ← key, hnW]`. Simplify using `only [Matrix.mul_assoc] at e`.

Establish `e2` using `eq_of_M_mul_eq_M_mul_of_ne_zero hfnz e`. Establish `e3` using `congrArg (m₁⁻¹ * ·) e2`. Simplify using `only [← Matrix.mul_assoc, hm₁l, Matrix.one_mul] at e3`. Conclude with `e3`. Use `⟨?_, hc12, hm, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gaussUniq_main : GaussUniq := by
  intro k r n₁ n₂ m₁ m₂ u₁ u₂ c₁ c₂ hn₁ hn₂ hm₁ hm₂ hu₁ hu₂ hc h
  obtain ⟨_, hn₂l, hn₂r⟩ := inv_of_UH hn₂.1
  obtain ⟨_, hu₁l, hu₁r⟩ := inv_of_UH hu₁.1
  obtain ⟨_, hu₂l, hu₂r⟩ := inv_of_UH hu₂.1
  obtain ⟨_, hm₁l, hm₁r⟩ := inv_of_UH hm₁.1
  obtain ⟨f₁, hB₁, hf₁, hf₁nz⟩ := exists_bigCell_eq_M (k := k) c₁
  obtain ⟨f₂, hB₂, hf₂, -⟩ := exists_bigCell_eq_M (k := k) c₂
  rw [hB₁, hB₂] at h
  have key : (n₂⁻¹ * n₁) * (M k r f₁ * m₁) = (M k r f₂ * m₂) * (u₂⁻¹ * u₁) := by
    have := congrArg (fun X => n₂⁻¹ * X * u₁) h
    simp only [Matrix.mul_assoc] at this ⊢
    rw [hu₁l, Matrix.mul_one, ← Matrix.mul_assoc n₂⁻¹ n₂, hn₂l, Matrix.one_mul] at this
    exact this
  obtain ⟨heq, hnW⟩ := W_eq_and_mul_W_eq_of_mul_eq_mul_of_lv_sum
    (mul_apply_eq_one_apply_of_lv_le (inv_apply_eq_one_apply_of_mem_UH_of_lv_le hn₂.1 (apply_eq_one_apply_of_mem_Nset_of_lv_le hn₂)) (apply_eq_one_apply_of_mem_Nset_of_lv_le hn₁))
    (mul_apply_eq_one_apply_of_lv_le (inv_apply_eq_one_apply_of_mem_UH_of_lv_le hu₂.1 (apply_eq_one_apply_of_mem_Nset_of_lv_le hu₂)) (apply_eq_one_apply_of_mem_Nset_of_lv_le hu₁))
    (lv_add_lv_eq_of_M_mul_apply_ne_zero hm₁ f₁) (lv_add_lv_eq_of_M_mul_apply_ne_zero hm₂ f₂) key
  have hc12 : c₁ = c₂ := by
    funext a
    have e := congrFun (congrFun heq (PI.SwBig.esI k r a)) (PI.SwBig.eI k r a)
    have ha := a.isLt
    have hs : sg k r (PI.SwBig.esI k r a) = PI.SwBig.eI k r a := by
      apply Fin.ext
      show (if r ≤ 2 * r + k - a.val ∧ 2 * r + k - a.val ≤ r + k then 2 * r + k - a.val
        else 2 * r + k - (2 * r + k - a.val)) = a.val
      split <;> omega
    have hl : lv k r (PI.SwBig.eI k r a) ≠ r := by
      have e4 : lv k r (PI.SwBig.eI k r a) = a.val := by
        unfold lv
        rw [if_pos (show (PI.SwBig.eI k r a).val < r from a.isLt)]
        rfl
      omega
    rw [M_mul_apply, M_mul_apply, hs, UWb_col hm₁ _ _ hl, UWb_col hm₂ _ _ hl, hf₁, hf₂,
      Matrix.one_apply_eq, mul_one, mul_one] at e
    exact e
  have hfnz : ∀ z, f₁ z ≠ 0 := hf₁nz (by rw [hc12]; exact hc)
  have hMM : M k r f₂ = M k r f₁ := by rw [← hB₁, ← hB₂, hc12]
  rw [hMM] at heq key
  have hm : m₁ = m₂ := eq_of_M_mul_eq_M_mul_of_ne_zero hfnz heq
  rw [← hm] at key
  have hn : n₂⁻¹ * n₁ = 1 := eq_one_of_mul_M_mul_eq hfnz hm₁r hnW
  have hu : u₂⁻¹ * u₁ = 1 := by
    have e : M k r f₁ * m₁ * (u₂⁻¹ * u₁) = M k r f₁ * m₁ * 1 := by
      rw [Matrix.mul_one, ← key, hnW]
    simp only [Matrix.mul_assoc] at e
    have e2 := eq_of_M_mul_eq_M_mul_of_ne_zero hfnz e
    have e3 := congrArg (m₁⁻¹ * ·) e2
    simp only [← Matrix.mul_assoc, hm₁l, Matrix.one_mul] at e3
    exact e3
  refine ⟨?_, hc12, hm, ?_⟩
  · calc n₁ = n₂ * (n₂⁻¹ * n₁) := by rw [← Matrix.mul_assoc, hn₂r, Matrix.one_mul]
      _ = n₂ := by rw [hn, Matrix.mul_one]
  · calc u₁ = u₂ * (u₂⁻¹ * u₁) := by rw [← Matrix.mul_assoc, hu₂r, Matrix.one_mul]
      _ = u₂ := by rw [hu, Matrix.mul_one]

end PI.SwBig.GU
