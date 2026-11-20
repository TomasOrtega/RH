import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

namespace ReciprocityTheory.AnForm.A

open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval

noncomputable section

section TMax
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- English proof (translation)
The claim follows from `Finset.le_sup' t (Finset.mem_univ i)`.
-/
lemma le_tmax (t : ι → ℝ) (i : ι) : t i ≤ tmax t := Finset.le_sup' t (Finset.mem_univ i)

/- English proof (translation)
The claim follows from `Finset.sup'_le _ _ (fun i _ => h i)`.
-/
lemma tmax_le {t : ι → ℝ} {c : ℝ} (h : ∀ i, t i ≤ c) : tmax t ≤ c := Finset.sup'_le _ _ (fun i _ => h i)

/- English proof (translation)
Take `⟨i, -, hi⟩` from `Finset.exists_mem_eq_sup' Finset.univ_nonempty t`. Conclude with `⟨i, hi⟩`.
-/
lemma exists_tmax (t : ι → ℝ) : ∃ i, tmax t = t i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty t
  exact ⟨i, hi⟩

/- English proof (translation)
The claim follows from `tmax_le (fun i => (h i).trans (le_tmax t i))`.
-/
lemma tmax_mono {s t : ι → ℝ} (h : s ≤ t) : tmax s ≤ tmax t := tmax_le (fun i => (h i).trans (le_tmax t i))

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `tmax_le fun j => by show t j + c ≤ tmax t + c`. Combine the linear relations using `[le_tmax t j]`. Take `⟨i, hi⟩` from `exists_tmax t`. Rewrite using `[hi]`.

Conclude with `le_tmax (fun j => t j + c) i`.
-/
lemma tmax_add_const (t : ι → ℝ) (c : ℝ) : tmax (fun j => t j + c) = tmax t + c := by
  apply le_antisymm
  · exact tmax_le fun j => by
      show t j + c ≤ tmax t + c
      linarith [le_tmax t j]
  · obtain ⟨i, hi⟩ := exists_tmax t
    rw [hi]
    exact le_tmax (fun j => t j + c) i

/- English proof (translation)
The claim follows from `le_antisymm (tmax_le h) (le_tmax t i)`.
-/
lemma tmax_eq_of_forall_le {t : ι → ℝ} {i : ι} (h : ∀ j, t j ≤ t i) : tmax t = t i := le_antisymm (tmax_le h) (le_tmax t i)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `tmax_le fun j => ?_ show c * t j ≤ c * tmax t` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left (le_tmax t j) hc`. Take `⟨i, hi⟩` from `exists_tmax t`. Rewrite using `[hi]`.

Conclude with `le_tmax (c • t) i`.
-/
lemma tmax_smul (t : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) : tmax (c • t) = c * tmax t := by
  apply le_antisymm
  · refine tmax_le fun j => ?_
    show c * t j ≤ c * tmax t
    exact mul_le_mul_of_nonneg_left (le_tmax t j) hc
  · obtain ⟨i, hi⟩ := exists_tmax t
    rw [hi]
    exact le_tmax (c • t) i

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_tmax s`. Rewrite using `[hi]`. Establish `h1` using `le_tmax t i`. Establish `h2 : ‖(s - t) i‖ ≤ ‖s - t‖` using `norm_le_pi_norm (s - t) i`. Rewrite `h2` using `[Pi.sub_apply, Real.norm_eq_abs]`.

Establish `h3` using `le_abs_self (s i - t i)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma tmax_sub_le_norm (s t : ι → ℝ) : tmax s - tmax t ≤ ‖s - t‖ := by
  obtain ⟨i, hi⟩ := exists_tmax s
  rw [hi]
  have h1 := le_tmax t i
  have h2 : ‖(s - t) i‖ ≤ ‖s - t‖ := norm_le_pi_norm (s - t) i
  rw [Pi.sub_apply, Real.norm_eq_abs] at h2
  have h3 := le_abs_self (s i - t i)
  linarith

/- English proof (translation)
Rewrite using `[abs_sub_le_iff]`. Use `⟨tmax_sub_le_norm s t, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_sub_rev]`. Conclude with `tmax_sub_le_norm t s`.
-/
lemma abs_tmax_sub_le (s t : ι → ℝ) : |tmax s - tmax t| ≤ ‖s - t‖ := by
  rw [abs_sub_le_iff]
  refine ⟨tmax_sub_le_norm s t, ?_⟩
  rw [norm_sub_rev]
  exact tmax_sub_le_norm t s

/- English proof (translation)
The claim follows from `LipschitzWith.of_dist_le_mul fun s t => by rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] exact abs_tmax_sub_le s t`.
-/
lemma lipschitz_tmax : LipschitzWith 1 (tmax : (ι → ℝ) → ℝ) := LipschitzWith.of_dist_le_mul fun s t => by
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
  exact abs_tmax_sub_le s t

/- English proof (translation)
The claim follows from `lipschitz_tmax.continuous`.
-/
lemma continuous_tmax : Continuous (tmax : (ι → ℝ) → ℝ) := lipschitz_tmax.continuous

/- English proof (translation)
The claim follows from `tmax_le fun i => by show a * x i + b * y i ≤ a * tmax x + b * tmax y exact add_le_add (mul_le_mul_of_nonneg_left (le_tmax x i) ha) (mul_le_mul_of_nonneg_left (le_tmax y i) hb)`.
-/
lemma tmax_convex_comb (x y : ι → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    tmax (a • x + b • y) ≤ a * tmax x + b * tmax y := tmax_le fun i => by
  show a * x i + b * y i ≤ a * tmax x + b * tmax y
  exact add_le_add (mul_le_mul_of_nonneg_left (le_tmax x i) ha)
    (mul_le_mul_of_nonneg_left (le_tmax y i) hb)

/- English proof (translation)
Establish `key : ∀ {a b : ι → ℝ}, (∀ i, i ≠ j → a i = b i) → a j ≤ a k → tmax a ≤ tmax b`. Introduce `a b hab ha`. Use `tmax_le fun i => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = j`. Rewrite using `[hi]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hab i hi]`. Conclude with `le_tmax b i`. Conclude with `le_antisymm (key hab ha) (key (fun i hi => (hab i hi).symm) hb)`.
-/
lemma tmax_eq_of_agree {a b : ι → ℝ} {j k : ι} (hkj : k ≠ j) (hab : ∀ i, i ≠ j → a i = b i)
    (ha : a j ≤ a k) (hb : b j ≤ b k) : tmax a = tmax b := by
  have key : ∀ {a b : ι → ℝ}, (∀ i, i ≠ j → a i = b i) → a j ≤ a k → tmax a ≤ tmax b := by
    intro a b hab ha
    refine tmax_le fun i => ?_
    by_cases hi : i = j
    · rw [hi]
      calc a j ≤ a k := ha
        _ = b k := hab k hkj
        _ ≤ tmax b := le_tmax b k
    · rw [hab i hi]
      exact le_tmax b i
  exact le_antisymm (key hab ha) (key (fun i hi => (hab i hi).symm) hb)

end TMax

section Kernel
variable {ι : Type*} [Fintype ι]

def kK (h : ι → ℝ) : ℝ := ∏ j, kθ (h j)

/- English proof (translation)
Unfold `kθ`. Conclude with `ContDiffBump.nonneg_normed _ x`.
-/
lemma kθ_nonneg (x : ℝ) : 0 ≤ kθ x := by
  unfold kθ
  exact ContDiffBump.nonneg_normed _ x
/- English proof (translation)
Unfold `kθ`. Conclude with `ContDiffBump.normed_neg _ x`.
-/
lemma kθ_neg (x : ℝ) : kθ (-x) = kθ x := by
  unfold kθ
  exact ContDiffBump.normed_neg _ x
/- English proof (translation)
Unfold `kθ`. Conclude with `ContDiffBump.contDiff_normed _`.
-/
lemma kθ_contDiff : ContDiff ℝ ∞ kθ := by
  unfold kθ
  exact ContDiffBump.contDiff_normed _
/- English proof (translation)
Unfold `kθ`. Conclude with `ContDiffBump.integral_normed _`.
-/
lemma kθ_integral : ∫ x, kθ x = 1 := by
  unfold kθ
  exact ContDiffBump.integral_normed _
/- English proof (translation)
Establish `hx : x ∈ Function.support kθ` using `h`. Unfold `kθ at hx`. Rewrite `hx` using `[ContDiffBump.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero]`. Conclude with `hx.le`.
-/
lemma abs_le_of_kθ_ne {x : ℝ} (h : kθ x ≠ 0) : |x| ≤ 1 / 2 := by
  have hx : x ∈ Function.support kθ := h
  unfold kθ at hx
  rw [ContDiffBump.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  exact hx.le

/- English proof (translation)
The claim follows from `Finset.prod_nonneg fun j _ => kθ_nonneg _`.
-/
lemma kK_nonneg (h : ι → ℝ) : 0 ≤ kK h := Finset.prod_nonneg fun j _ => kθ_nonneg _
/- English proof (translation)
Simplify using `only [kK, Pi.neg_apply, kθ_neg]`.
-/
lemma kK_neg (h : ι → ℝ) : kK (-h) = kK h := by
  simp only [kK, Pi.neg_apply, kθ_neg]
/- English proof (translation)
Use `show ContDiff ℝ ∞ (fun h : ι → ℝ => ∏ j, kθ (h j))`. Conclude with `contDiff_prod fun j _ => kθ_contDiff.comp (contDiff_apply ℝ ℝ j)`.
-/
lemma kK_contDiff : ContDiff ℝ ∞ (kK : (ι → ℝ) → ℝ) := by
  show ContDiff ℝ ∞ (fun h : ι → ℝ => ∏ j, kθ (h j))
  exact contDiff_prod fun j _ => kθ_contDiff.comp (contDiff_apply ℝ ℝ j)
/- English proof (translation)
Establish `hh' : ∏ j, kθ (h j) ≠ 0` using `hh`. Establish `hj : ∀ j, kθ (h j) ≠ 0` using `fun j => (Finset.prod_ne_zero_iff.1 hh') j (Finset.mem_univ j)`. Use `(pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs]`. Conclude with `abs_le_of_kθ_ne (hj j)`.
-/
lemma norm_le_of_kK_ne {h : ι → ℝ} (hh : kK h ≠ 0) : ‖h‖ ≤ 1 / 2 := by
  have hh' : ∏ j, kθ (h j) ≠ 0 := hh
  have hj : ∀ j, kθ (h j) ≠ 0 := fun j => (Finset.prod_ne_zero_iff.1 hh') j (Finset.mem_univ j)
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  exact abs_le_of_kθ_ne (hj j)
/- English proof (translation)
Use `HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℝ) (1 / 2)) fun h hh => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hh (mem_closedBall_zero_iff.2 (norm_le_of_kK_ne hne))`.
-/
lemma kK_hasCompactSupport : HasCompactSupport (kK : (ι → ℝ) → ℝ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℝ) (1 / 2)) fun h hh => ?_
  by_contra hne
  exact hh (mem_closedBall_zero_iff.2 (norm_le_of_kK_ne hne))
/- English proof (translation)
Use `show ∫ h : ι → ℝ, ∏ j, kθ (h j) = 1`. Use `first`. Consider the case `rw [integral_fintype_prod_eq_pow ι kθ, kθ_integral, one_pow]`. Consider the case `rw [integral_fintype_prod_eq_prod ι (fun _ => kθ)]`. Simplify using `[kθ_integral]`.

Consider the case `(rw [MeasureTheory.integral_fintype_prod_volume_eq_prod (fun _ => kθ)]; simp [kθ_integral])`.
-/
lemma kK_integral : ∫ h : ι → ℝ, kK h = 1 := by
  show ∫ h : ι → ℝ, ∏ j, kθ (h j) = 1
  first
    | rw [integral_fintype_prod_eq_pow ι kθ, kθ_integral, one_pow]
    | rw [integral_fintype_prod_eq_prod ι (fun _ => kθ)]; simp [kθ_integral]
    | (rw [MeasureTheory.integral_fintype_prod_volume_eq_prod (fun _ => kθ)]; simp [kθ_integral])

/- English proof (translation)
Use `first`. Consider the case `exact (hg.mul kK_contDiff.continuous).integrable_of_hasCompactSupport kK_hasCompactSupport.mul_left`. Consider the case `exact (hg.mul kK_contDiff.continuous).integrable_of_hasCompactSupport kK_hasCompactSupport.mul_right`.
-/
lemma integrable_mul_kK {g : (ι → ℝ) → ℝ} (hg : Continuous g) :
    Integrable (fun h => g h * kK h) := by
  first
    | exact (hg.mul kK_contDiff.continuous).integrable_of_hasCompactSupport kK_hasCompactSupport.mul_left
    | exact (hg.mul kK_contDiff.continuous).integrable_of_hasCompactSupport kK_hasCompactSupport.mul_right

/- English proof (translation)
Establish `e` using `integral_neg_eq_self (fun h : ι → ℝ => h i * kK h) volume`. Simplify using `only [Pi.neg_apply, kK_neg, neg_mul, integral_neg] at e`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma integral_coord_kK (i : ι) : ∫ h, h i * kK h = 0 := by
  have e := integral_neg_eq_self (fun h : ι → ℝ => h i * kK h) volume
  simp only [Pi.neg_apply, kK_neg, neg_mul, integral_neg] at e
  linarith

/- English proof (translation)
The claim follows from `kK_contDiff.continuous.integrable_of_hasCompactSupport kK_hasCompactSupport`.
-/
lemma kK_integrable : Integrable (kK : (ι → ℝ) → ℝ) := kK_contDiff.continuous.integrable_of_hasCompactSupport kK_hasCompactSupport

/- English proof (translation)
Establish `e : (fun h : ι → ℝ => (c + a * h i) * kK h) = fun h => c * kK h + a * (h i * kK h)`. Use function extensionality and compare the values at `h`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, integral_add (kK_integrable.const_mul c) ((integrable_mul_kK (continuous_apply i)).const_mul a)]`. Use `first`.

Consider the case `rw [integral_const_mul, integral_const_mul]`. Consider the case `rw [integral_mul_left, integral_mul_left]`. Rewrite using `[kK_integral, integral_coord_kK]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma integral_affine_kK (c a : ℝ) (i : ι) : ∫ h, (c + a * h i) * kK h = c := by
  have e : (fun h : ι → ℝ => (c + a * h i) * kK h) = fun h => c * kK h + a * (h i * kK h) := by
    funext h
    ring
  rw [e, integral_add (kK_integrable.const_mul c) ((integrable_mul_kK (continuous_apply i)).const_mul a)]
  first
    | rw [integral_const_mul, integral_const_mul]
    | rw [integral_mul_left, integral_mul_left]
  rw [kK_integral, integral_coord_kK]
  ring

end Kernel

section RegMaxBasic
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- English proof (translation)
Establish `e` using `norm_le_pi_norm h j`. Rewrite `e` using `[Real.norm_eq_abs]`. Conclude with `e.trans (norm_le_of_kK_ne hh)`.
-/
lemma abs_le_of_kK_ne {h : ι → ℝ} (hh : kK h ≠ 0) (j : ι) : |h j| ≤ 1 / 2 := by
  have e := norm_le_pi_norm h j
  rw [Real.norm_eq_abs] at e
  exact e.trans (norm_le_of_kK_ne hh)

/- English proof (translation)
Take `⟨h1, h2⟩` from `abs_le.1 (abs_le_of_kK_ne hh j)`. Prove the components needed by the constructor for the conclusion. Use polynomial arithmetic with `[mul_nonneg hη (by linarith : (0 : ℝ) ≤ h j + 1 / 2)]`. Use polynomial arithmetic with `[mul_nonneg hη (by linarith : (0 : ℝ) ≤ 1 / 2 - h j)]`.
-/
lemma mul_coord_bounds {η : ℝ} (hη : 0 ≤ η) {h : ι → ℝ} (hh : kK h ≠ 0) (j : ι) :
    -(η / 2) ≤ η * h j ∧ η * h j ≤ η / 2 := by
  obtain ⟨h1, h2⟩ := abs_le.1 (abs_le_of_kK_ne hh j)
  constructor
  · nlinarith [mul_nonneg hη (by linarith : (0 : ℝ) ≤ h j + 1 / 2)]
  · nlinarith [mul_nonneg hη (by linarith : (0 : ℝ) ≤ 1 / 2 - h j)]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma regMax_eq_kK (η : ℝ) (t : ι → ℝ) :
    regMax η t = ∫ h, tmax (fun j => t j + η * h j) * kK h := rfl

/- English proof (translation)
The claim follows from `continuous_tmax.comp (continuous_pi fun j => continuous_const.add (continuous_const.mul (continuous_apply j)))`.
-/
lemma continuous_tmax_shift (η : ℝ) (t : ι → ℝ) :
    Continuous (fun h : ι → ℝ => tmax (fun j => t j + η * h j)) := continuous_tmax.comp
    (continuous_pi fun j => continuous_const.add (continuous_const.mul (continuous_apply j)))

/- English proof (translation)
Use `congr 1`. Use function extensionality and compare the values at `h`. Distinguish the cases in `hh : kK h = 0`. Rewrite using `[hh, mul_zero, mul_zero]`. Rewrite using `[hFG h hh]`.
-/
lemma integral_kK_congr {F G : (ι → ℝ) → ℝ} (hFG : ∀ h, kK h ≠ 0 → F h = G h) :
    ∫ h, F h * kK h = ∫ h, G h * kK h := by
  congr 1
  funext h
  by_cases hh : kK h = 0
  · rw [hh, mul_zero, mul_zero]
  · rw [hFG h hh]

/- English proof (translation)
Use `integral_mono (integrable_mul_kK hF) (integrable_mul_kK hG) fun h => ?_` and prove the remaining obligations. Distinguish the cases in `hh : kK h = 0`. Simplify using `[hh]`. Conclude with `mul_le_mul_of_nonneg_right (hFG h hh) (kK_nonneg h)`.
-/
lemma integral_kK_mono {F G : (ι → ℝ) → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ h, kK h ≠ 0 → F h ≤ G h) : ∫ h, F h * kK h ≤ ∫ h, G h * kK h := by
  refine integral_mono (integrable_mul_kK hF) (integrable_mul_kK hG) fun h => ?_
  by_cases hh : kK h = 0
  · simp [hh]
  · exact mul_le_mul_of_nonneg_right (hFG h hh) (kK_nonneg h)

/- English proof (translation)
Use `first`. Consider the case `rw [integral_const_mul, kK_integral, mul_one]`. Consider the case `rw [integral_mul_left, kK_integral, mul_one]`.
-/
lemma integral_const_kK (c : ℝ) : ∫ h : ι → ℝ, c * kK h = c := by
  first
    | rw [integral_const_mul, kK_integral, mul_one]
    | rw [integral_mul_left, kK_integral, mul_one]

/- English proof (translation)
Establish `e : (fun h => (a * F h + b * G h) * kK h) = fun h => a * (F h * kK h) + b * (G h * kK h)`. Use function extensionality and compare the values at `h`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, integral_add ((integrable_mul_kK hF).const_mul a) ((integrable_mul_kK hG).const_mul b)]`. Use `first`.

Consider the case `rw [integral_const_mul, integral_const_mul]`. Consider the case `rw [integral_mul_left, integral_mul_left]`.
-/
lemma integral_lin_kK {F G : (ι → ℝ) → ℝ} (hF : Continuous F) (hG : Continuous G) (a b : ℝ) :
    ∫ h, (a * F h + b * G h) * kK h = a * (∫ h, F h * kK h) + b * (∫ h, G h * kK h) := by
  have e : (fun h => (a * F h + b * G h) * kK h) = fun h => a * (F h * kK h) + b * (G h * kK h) := by
    funext h
    ring
  rw [e, integral_add ((integrable_mul_kK hF).const_mul a) ((integrable_mul_kK hG).const_mul b)]
  first
    | rw [integral_const_mul, integral_const_mul]
    | rw [integral_mul_left, integral_mul_left]

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_tmax t`. Rewrite using `[regMax_eq_kK]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma regMax_ge (η : ℝ) (t : ι → ℝ) : tmax t ≤ regMax η t := by
  obtain ⟨i, hi⟩ := exists_tmax t
  rw [regMax_eq_kK]
  calc tmax t = t i := hi
    _ = ∫ h, (t i + η * h i) * kK h := (integral_affine_kK (t i) η i).symm
    _ ≤ ∫ h, tmax (fun j => t j + η * h j) * kK h :=
        integral_kK_mono (F := fun h => t i + η * h i) (G := fun h => tmax (fun j => t j + η * h j))
          (continuous_const.add (continuous_const.mul (continuous_apply i)))
          (continuous_tmax_shift η t) fun h _ => le_tmax (fun j => t j + η * h j) i

/- English proof (translation)
Rewrite using `[regMax_eq_kK]`. Combine the equalities or inequalities in the displayed calculation. Combine the linear relations using `[(mul_coord_bounds hη hh j).2, le_tmax t j]`. Use `_ = tmax t + η / 2 := integral_const_kK _`.
-/
lemma regMax_le {η : ℝ} (hη : 0 ≤ η) (t : ι → ℝ) : regMax η t ≤ tmax t + η / 2 := by
  rw [regMax_eq_kK]
  calc ∫ h, tmax (fun j => t j + η * h j) * kK h ≤ ∫ h, (tmax t + η / 2) * kK h :=
        integral_kK_mono (F := fun h => tmax (fun j => t j + η * h j)) (G := fun _ => tmax t + η / 2)
          (continuous_tmax_shift η t) continuous_const fun h hh =>
          tmax_le fun j => by
            show t j + η * h j ≤ tmax t + η / 2
            linarith [(mul_coord_bounds hη hh j).2, le_tmax t j]
    _ = tmax t + η / 2 := integral_const_kK _

/- English proof (translation)
Rewrite using `[regMax_eq_kK]`. Combine the equalities or inequalities in the displayed calculation. Apply `tmax_eq_of_forall_le (i := i)` to reduce the goal to its premises. Introduce `j`. Use `show t j + η * h j ≤ t i + η * h i`.

Distinguish the cases in `hj : j = i`. Rewrite using `[hj]`. Combine the linear relations using `[hi j hj, (mul_coord_bounds hη hh j).2, (mul_coord_bounds hη hh i).1]`. Use `_ = t i := integral_affine_kK _ _ _`.
-/
lemma regMax_eq_of_dom {η : ℝ} (hη : 0 ≤ η) (t : ι → ℝ) (i : ι)
    (hi : ∀ j, j ≠ i → t j + η ≤ t i) : regMax η t = t i := by
  rw [regMax_eq_kK]
  calc ∫ h, tmax (fun j => t j + η * h j) * kK h = ∫ h, (t i + η * h i) * kK h :=
        integral_kK_congr (F := fun h => tmax (fun j => t j + η * h j)) (G := fun h => t i + η * h i)
          fun h hh => by
            show tmax (fun j => t j + η * h j) = t i + η * h i
            apply tmax_eq_of_forall_le (i := i)
            intro j
            show t j + η * h j ≤ t i + η * h i
            by_cases hj : j = i
            · rw [hj]
            · linarith [hi j hj, (mul_coord_bounds hη hh j).2, (mul_coord_bounds hη hh i).1]
    _ = t i := integral_affine_kK _ _ _

/- English proof (translation)
Rewrite using `[regMax_eq_kK, regMax_eq_kK]`. Apply `integral_kK_congr` to reduce the goal to its premises. Introduce `h hh`. Apply `tmax_eq_of_agree hkj` to reduce the goal to its premises. Introduce `i hi show Function.update t j s i + η * h i = t i + η * h i first`.

Consider the case `rw [Function.update_of_ne hi]`. Consider the case `rw [Function.update_noteq hi]`. Use `show Function.update t j s j + η * h j ≤ Function.update t j s k + η * h k first`. Consider the case `rw [Function.update_self, Function.update_of_ne hkj]`. Consider the case `rw [Function.update_same, Function.update_noteq hkj]`.

Combine the linear relations using `[(mul_coord_bounds hη hh j).2, (mul_coord_bounds hη hh k).1]`. Use `show t j + η * h j ≤ t k + η * h k`. Combine the linear relations using `[(mul_coord_bounds hη hh j).2, (mul_coord_bounds hη hh k).1]`.
-/
lemma regMax_update [DecidableEq ι] {η : ℝ} (hη : 0 ≤ η) (t : ι → ℝ) (j k : ι) (s : ℝ)
    (hkj : k ≠ j) (htj : t j + η ≤ t k) (hs : s + η ≤ t k) :
    regMax η (Function.update t j s) = regMax η t := by
  rw [regMax_eq_kK, regMax_eq_kK]
  apply integral_kK_congr
  intro h hh
  apply tmax_eq_of_agree hkj
  · intro i hi
    show Function.update t j s i + η * h i = t i + η * h i
    first
      | rw [Function.update_of_ne hi]
      | rw [Function.update_noteq hi]
  · show Function.update t j s j + η * h j ≤ Function.update t j s k + η * h k
    first
      | rw [Function.update_self, Function.update_of_ne hkj]
      | rw [Function.update_same, Function.update_noteq hkj]
    linarith [(mul_coord_bounds hη hh j).2, (mul_coord_bounds hη hh k).1]
  · show t j + η * h j ≤ t k + η * h k
    linarith [(mul_coord_bounds hη hh j).2, (mul_coord_bounds hη hh k).1]

/- English proof (translation)
Rewrite using `[regMax_eq_kK, regMax_eq_kK]`. Establish `e : ∀ h : ι → ℝ, tmax (fun j => t j + c + η * h j) = tmax (fun j => t j + η * h j) + c` using `fun h => by`. Rewrite using `[← tmax_add_const]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `h`. Rewrite using `[e h]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = 1 * (∫ h, tmax (fun j => t j + η * h j) * kK h) + c * ∫ h, 1 * kK h := integral_lin_kK (F := fun h => tmax (fun j => t j + η * h j)) (G := fun _ => 1) (continuous_tmax_shift η t) continuous_const 1 c`. Use `_ = (∫ h, tmax (fun j => t j + η * h j) * kK h) + c := by`. Rewrite using `[integral_const_kK]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma regMax_add_const (η : ℝ) (t : ι → ℝ) (c : ℝ) :
    regMax η (fun j => t j + c) = regMax η t + c := by
  rw [regMax_eq_kK, regMax_eq_kK]
  have e : ∀ h : ι → ℝ, tmax (fun j => t j + c + η * h j) = tmax (fun j => t j + η * h j) + c :=
    fun h => by
      rw [← tmax_add_const]
      congr 1
      funext j
      ring
  calc ∫ h, tmax (fun j => t j + c + η * h j) * kK h
        = ∫ h, (1 * tmax (fun j => t j + η * h j) + c * 1) * kK h := by
          congr 1
          funext h
          rw [e h]
          ring
    _ = 1 * (∫ h, tmax (fun j => t j + η * h j) * kK h) + c * ∫ h, 1 * kK h :=
          integral_lin_kK (F := fun h => tmax (fun j => t j + η * h j)) (G := fun _ => 1)
            (continuous_tmax_shift η t) continuous_const 1 c
    _ = (∫ h, tmax (fun j => t j + η * h j) * kK h) + c := by
          rw [integral_const_kK]
          ring

/- English proof (translation)
Introduce `s t hst`. Rewrite using `[regMax_eq_kK, regMax_eq_kK]`. Conclude with `integral_kK_mono (continuous_tmax_shift η s) (continuous_tmax_shift η t) fun h _ => tmax_mono fun j => by show s j + η * h j ≤ t j + η * h j`. Combine the linear relations using `[hst j]`.
-/
lemma regMax_mono (η : ℝ) : Monotone (regMax (ι := ι) η) := by
  intro s t hst
  rw [regMax_eq_kK, regMax_eq_kK]
  exact integral_kK_mono (continuous_tmax_shift η s) (continuous_tmax_shift η t) fun h _ =>
    tmax_mono fun j => by
      show s j + η * h j ≤ t j + η * h j
      linarith [hst j]

/- English proof (translation)
Use `⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩` and prove the remaining obligations. Rewrite using `[regMax_eq_kK, regMax_eq_kK, regMax_eq_kK]`. Simplify using `only [smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Apply `integral_kK_mono (continuous_tmax_shift η _) ((continuous_const.mul (continuous_tmax_shift η x)).add (continuous_const.mul (continuous_tmax_shift η y)))` to reduce the goal to its premises.

Introduce `h _`. Establish `e : (fun j => (a • x + b • y) j + η * h j) = a • (fun j => x j + η * h j) + b • (fun j => y j + η * h j)`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Take the linear combination `(-(η * h j)) * hab`.

Rewrite using `[e]`. Conclude with `tmax_convex_comb _ _ ha hb`. Use `_ = a * (∫ h, tmax (fun j => x j + η * h j) * kK h) + b * (∫ h, tmax (fun j => y j + η * h j) * kK h) := integral_lin_kK (continuous_tmax_shift η x) (continuous_tmax_shift η y) a b`.
-/
lemma regMax_convex (η : ℝ) : ConvexOn ℝ Set.univ (regMax (ι := ι) η) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  rw [regMax_eq_kK, regMax_eq_kK, regMax_eq_kK]
  simp only [smul_eq_mul]
  calc ∫ h, tmax (fun j => (a • x + b • y) j + η * h j) * kK h
        ≤ ∫ h, (a * tmax (fun j => x j + η * h j) + b * tmax (fun j => y j + η * h j)) * kK h := by
          apply integral_kK_mono (continuous_tmax_shift η _)
            ((continuous_const.mul (continuous_tmax_shift η x)).add
              (continuous_const.mul (continuous_tmax_shift η y)))
          intro h _
          have e : (fun j => (a • x + b • y) j + η * h j) =
              a • (fun j => x j + η * h j) + b • (fun j => y j + η * h j) := by
            funext j
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            linear_combination (-(η * h j)) * hab
          rw [e]
          exact tmax_convex_comb _ _ ha hb
    _ = a * (∫ h, tmax (fun j => x j + η * h j) * kK h) + b * (∫ h, tmax (fun j => y j + η * h j) * kK h) :=
          integral_lin_kK (continuous_tmax_shift η x) (continuous_tmax_shift η y) a b

/- English proof (translation)
Rewrite using `[← tmax_smul _ hη.le]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[mul_add, ← mul_assoc η η⁻¹, mul_inv_cancel₀ hη.ne']`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma tmax_scale {η : ℝ} (hη : 0 < η) (t h : ι → ℝ) :
    tmax (fun j => t j + η * h j) = η * tmax (fun j => (η⁻¹ • t) j + 1 * h j) := by
  rw [← tmax_smul _ hη.le]
  congr 1
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_add, ← mul_assoc η η⁻¹, mul_inv_cancel₀ hη.ne']
  ring

/- English proof (translation)
Rewrite using `[regMax_eq_kK, regMax_eq_kK]`. Use `first`. Consider the case `rw [← integral_const_mul]`. Consider the case `rw [← integral_mul_left]`. Use `congr 1`.

Use function extensionality and compare the values at `h`. Rewrite using `[tmax_scale hη t h, mul_assoc]`.
-/
lemma regMax_scale {η : ℝ} (hη : 0 < η) (t : ι → ℝ) : regMax η t = η * regMax 1 (η⁻¹ • t) := by
  rw [regMax_eq_kK, regMax_eq_kK]
  first
    | rw [← integral_const_mul]
    | rw [← integral_mul_left]
  congr 1
  funext h
  rw [tmax_scale hη t h, mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[regMax_eq_kK]`. Use `first`. Consider the case `rw [convolution_def]`. Consider the case `unfold convolution`.

Simplify using `only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]`. Establish `e` using `integral_neg_eq_self (fun h : ι → ℝ => tmax (fun j => x j + 1 * h j) * kK h) volume`. Rewrite using `[← e]`. Use `congr 1`. Use function extensionality and compare the values at `h`.

Use `show tmax (fun j => x j + 1 * (-h) j) * kK (-h) = kK h * tmax (x - h)`. Rewrite using `[kK_neg, mul_comm (tmax (fun j => x j + 1 * (-h) j)) (kK h)]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.sub_apply, Pi.neg_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma regMax_one_eq_conv :
    regMax (ι := ι) 1 = convolution kK tmax (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  rw [regMax_eq_kK]
  first
    | rw [convolution_def]
    | unfold convolution
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have e := integral_neg_eq_self (fun h : ι → ℝ => tmax (fun j => x j + 1 * h j) * kK h) volume
  rw [← e]
  congr 1
  funext h
  show tmax (fun j => x j + 1 * (-h) j) * kK (-h) = kK h * tmax (x - h)
  rw [kK_neg, mul_comm (tmax (fun j => x j + 1 * (-h) j)) (kK h)]
  congr 2
  funext j
  simp only [Pi.sub_apply, Pi.neg_apply]
  ring

/- English proof (translation)
Rewrite using `[regMax_one_eq_conv]`. Conclude with `HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) kK_hasCompactSupport kK_contDiff continuous_tmax.locallyIntegrable`.
-/
lemma regMax_one_contDiff : ContDiff ℝ ∞ (regMax (ι := ι) 1) := by
  rw [regMax_one_eq_conv]
  exact HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    kK_hasCompactSupport kK_contDiff continuous_tmax.locallyIntegrable

/- English proof (translation)
The claim follows from `funext fun t => regMax_scale hη t`.
-/
lemma regMax_eq_fun {η : ℝ} (hη : 0 < η) :
    regMax (ι := ι) η = fun t => η * regMax 1 (η⁻¹ • t) := funext fun t => regMax_scale hη t

/- English proof (translation)
Rewrite using `[regMax_eq_fun hη]`. Conclude with `contDiff_const.mul (regMax_one_contDiff.comp (contDiff_id.const_smul η⁻¹))`.
-/
lemma regMax_contDiff {η : ℝ} (hη : 0 < η) : ContDiff ℝ ∞ (regMax (ι := ι) η) := by
  rw [regMax_eq_fun hη]
  exact contDiff_const.mul (regMax_one_contDiff.comp (contDiff_id.const_smul η⁻¹))

end RegMaxBasic

end

end ReciprocityTheory.AnForm.A
