import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Legendre

noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F
namespace AnalyticIdentityTheoremsZetaFacts

/- English proof (translation)
Establish `hl0 : 0 < ‖l‖` using `by linarith`. Establish `hd : ‖l‖ / 2 ≤ ‖s - l‖`. Establish `h1` using `norm_sub_norm_le l s`. Rewrite `h1` using `[norm_sub_rev]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hdpos : 0 < ‖s - l‖` using `by linarith`. Establish `hl : l ≠ 0` using `norm_pos_iff.mp hl0`. Establish `hsl : s - l ≠ 0` using `norm_pos_iff.mp hdpos`. Establish `key : 1 / (s - l) + 1 / l + s / l ^ 2 = s ^ 2 / (l ^ 2 * (s - l))`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, norm_div, norm_mul, norm_pow, norm_pow, show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hl0.le, Real.rpow_natCast]`. Establish `hden : 0 < ‖l‖ ^ 2 * (‖l‖ / 2)` using `mul_pos (pow_pos hl0 2) (half_pos hl0)`. Combine the equalities or inequalities in the displayed calculation. Apply `div_le_div₀ (by positivity) _ hden` to reduce the goal to its premises.

Conclude with `mul_le_mul_of_nonneg_left hd (by positivity)`. Conclude with `pow_le_pow_left₀ (norm_nonneg s) hs.le 2`. Use `_ = 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ := by`. Clear the denominators using the available nonvanishing facts.
-/
lemma term_bound (r : ℝ) (hr : 0 < r) (s : ℂ) (hs : ‖s‖ < r) (l : ℂ) (h : 2 * r ≤ ‖l‖) :
    ‖1 / (s - l) + 1 / l + s / l ^ 2‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hl0 : 0 < ‖l‖ := by linarith
  have hd : ‖l‖ / 2 ≤ ‖s - l‖ := by
    have h1 := norm_sub_norm_le l s
    rw [norm_sub_rev] at h1
    linarith
  have hdpos : 0 < ‖s - l‖ := by linarith
  have hl : l ≠ 0 := norm_pos_iff.mp hl0
  have hsl : s - l ≠ 0 := norm_pos_iff.mp hdpos
  have key : 1 / (s - l) + 1 / l + s / l ^ 2 = s ^ 2 / (l ^ 2 * (s - l)) := by
    field_simp
    ring
  rw [key, norm_div, norm_mul, norm_pow, norm_pow,
    show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hl0.le, Real.rpow_natCast]
  have hden : 0 < ‖l‖ ^ 2 * (‖l‖ / 2) := mul_pos (pow_pos hl0 2) (half_pos hl0)
  calc ‖s‖ ^ 2 / (‖l‖ ^ 2 * ‖s - l‖) ≤ r ^ 2 / (‖l‖ ^ 2 * (‖l‖ / 2)) := by
        apply div_le_div₀ (by positivity) _ hden
        · exact mul_le_mul_of_nonneg_left hd (by positivity)
        · exact pow_le_pow_left₀ (norm_nonneg s) hs.le 2
    _ = 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ := by
        field_simp

def zetaExcept (L : PeriodPair) (l₀ z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l.1 = l₀ then 0 else (1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)

/- English proof (translation)
Establish `hs3 : Summable fun l : L.lattice => ‖(l : ℂ)‖ ^ (-3 : ℝ)` using `ZLattice.summable_norm_rpow L.lattice (-3) (by rw [L.finrank_lattice]; norm_num)`. Use `L.hasSumLocallyUniformly_aux _ (fun r l => 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ)) (fun r _ => hs3.mul_left (2 * r ^ 2)) fun r hr => ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop (2 * r)] with R hR x hx l hl`. Use `split_ifs`. Rewrite using `[norm_zero]`.

Check the signs of the components of the expression. Conclude with `term_bound r hr x hx l (by rw [hl]; exact hR)`.
-/
lemma hasSumLU_zetaExcept (L : PeriodPair) (l₀ : ℂ) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦
        if l.1 = l₀ then 0 else (1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2))
      (zetaExcept L l₀) := by
  have hs3 : Summable fun l : L.lattice => ‖(l : ℂ)‖ ^ (-3 : ℝ) :=
    ZLattice.summable_norm_rpow L.lattice (-3) (by rw [L.finrank_lattice]; norm_num)
  refine L.hasSumLocallyUniformly_aux _ (fun r l => 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ))
    (fun r _ => hs3.mul_left (2 * r ^ 2)) fun r hr => ?_
  filter_upwards [Filter.eventually_ge_atTop (2 * r)] with R hR x hx l hl
  split_ifs
  · rw [norm_zero]
    positivity
  · exact term_bound r hr x hx l (by rw [hl]; exact hR)

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [zetaExcept, wZeta]`. Use `tsum_congr fun l => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce `h`.

Apply `hl` to reduce the goal to its premises. Rewrite using `[← h]`. Conclude with `l.2`.
-/
lemma zetaExcept_of_notMem (L : PeriodPair) (l₀ : ℂ) (hl : l₀ ∉ L.lattice) :
    zetaExcept L l₀ = wZeta L := by
  funext z
  simp only [zetaExcept, wZeta]
  refine tsum_congr fun l => ?_
  rw [if_neg]
  intro h
  apply hl
  rw [← h]
  exact l.2

/- English proof (translation)
Establish `hs3 : Summable fun l : L.lattice => ‖(l : ℂ)‖ ^ (-3 : ℝ)` using `ZLattice.summable_norm_rpow L.lattice (-3) (by rw [L.finrank_lattice]; norm_num)`. Use `L.hasSumLocallyUniformly_aux _ (fun r l => 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ)) (fun r _ => hs3.mul_left (2 * r ^ 2)) fun r hr => ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop (2 * r)] with R hR x hx l hl`. Conclude with `term_bound r hr x hx l (by rw [hl]; exact hR)`.
-/
lemma hasSumLU_wZeta (L : PeriodPair) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦ 1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
      (wZeta L) := by
  have hs3 : Summable fun l : L.lattice => ‖(l : ℂ)‖ ^ (-3 : ℝ) :=
    ZLattice.summable_norm_rpow L.lattice (-3) (by rw [L.finrank_lattice]; norm_num)
  refine L.hasSumLocallyUniformly_aux _ (fun r l => 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ))
    (fun r _ => hs3.mul_left (2 * r ^ 2)) fun r hr => ?_
  filter_upwards [Filter.eventually_ge_atTop (2 * r)] with R hR x hx l hl
  exact term_bound r hr x hx l (by rw [hl]; exact hR)

/- English proof (translation)
Establish `h' : TendstoLocallyUniformlyOn (fun s x => ∑ i ∈ s, F i x) g Filter.atTop U` using `h`. Conclude with `h'.differentiableOn (Filter.Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hF i) hU`.
-/
private lemma differentiableOn_of_hasSumLocallyUniformlyOn' {ι : Type*} {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (h : HasSumLocallyUniformlyOn F g U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U) :
    DifferentiableOn ℂ g U := by
  have h' : TendstoLocallyUniformlyOn (fun s x => ∑ i ∈ s, F i x) g Filter.atTop U := h
  exact h'.differentiableOn
    (Filter.Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hF i) hU

/- English proof (translation)
Establish `h2 : HasDerivAt (fun w : ℂ => (w - l)⁻¹) (-((z - l) ^ 2)⁻¹ * 1) z` using `(hasDerivAt_inv h).comp z ((hasDerivAt_id' z).sub_const l)`. Establish `h4` using `(h2.add_const (1 / l)).add ((hasDerivAt_id' z).div_const (l ^ 2))`. Establish `e : (fun w : ℂ => 1 / (w - l) + 1 / l + w / l ^ 2) = fun w => (w - l)⁻¹ + 1 / l + w / l ^ 2`. Use function extensionality and compare the values at `w`. Rewrite using `[one_div]`.

Rewrite using `[e]`. Conclude with `h4.congr_deriv (by ring)`.
-/
private lemma hasDerivAt_inv_sub_add_inv_add_div_sq (l z : ℂ) (h : z - l ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ 1 / (z - l) + 1 / l + z / l ^ 2)
      (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
  have h2 : HasDerivAt (fun w : ℂ => (w - l)⁻¹) (-((z - l) ^ 2)⁻¹ * 1) z :=
    (hasDerivAt_inv h).comp z ((hasDerivAt_id' z).sub_const l)
  have h4 := (h2.add_const (1 / l)).add ((hasDerivAt_id' z).div_const (l ^ 2))
  have e : (fun w : ℂ => 1 / (w - l) + 1 / l + w / l ^ 2) =
      fun w => (w - l)⁻¹ + 1 / l + w / l ^ 2 := by
    funext w
    rw [one_div]
  rw [e]
  exact h4.congr_deriv (by ring)

/- English proof (translation)
Use `differentiableOn_of_hasSumLocallyUniformlyOn' (hasSumLU_zetaExcept L l₀).hasSumLocallyUniformlyOn (fun l => ?_) L.isOpen_compl_lattice_diff` and prove the remaining obligations. Distinguish the cases in `h : (l : ℂ) = l₀`. Simplify using `only [h, ↓reduceIte]`. Conclude with `differentiableOn_const 0`. Simplify using `only [h, ↓reduceIte]`.

Introduce `z hz`. Establish `hzl : z - l ≠ 0`. Introduce `e`. Apply `hz` to reduce the goal to its premises. Rewrite using `[sub_eq_zero.mp e]`.

Conclude with `⟨l.2, h⟩`. Conclude with `(hasDerivAt_inv_sub_add_inv_add_div_sq l z hzl).differentiableAt.differentiableWithinAt`.
-/
lemma differentiableOn_zetaExcept (L : PeriodPair) (l₀ : ℂ) :
    DifferentiableOn ℂ (zetaExcept L l₀) (L.lattice \ {l₀})ᶜ := by
  refine differentiableOn_of_hasSumLocallyUniformlyOn' (hasSumLU_zetaExcept L l₀).hasSumLocallyUniformlyOn (fun l => ?_)
    L.isOpen_compl_lattice_diff
  by_cases h : (l : ℂ) = l₀
  · simp only [h, ↓reduceIte]
    exact differentiableOn_const 0
  · simp only [h, ↓reduceIte]
    intro z hz
    have hzl : z - l ≠ 0 := by
      intro e
      apply hz
      rw [sub_eq_zero.mp e]
      exact ⟨l.2, h⟩
    exact (hasDerivAt_inv_sub_add_inv_add_div_sq l z hzl).differentiableAt.differentiableWithinAt

/- English proof (translation)
Establish `h1` using `(hasSumLU_zetaExcept L 0).hasSum (x := z)`. Establish `h2` using `hasSum_ite_eq (0 : L.lattice) (1 / z)`. Establish `h3` using `(hasSumLU_wZeta L).hasSum (x := z)`. Use `(h1.add h2).unique ?_` and prove the remaining obligations. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `l`. Distinguish the cases in `hl : l = 0`. Substitute `hl` using the available equality. Simplify using the standard rewrite rules. Establish `hl' : (l : ℂ) ≠ 0`.

Introduce `h`. Apply `hl` to reduce the goal to its premises. Conclude with `Subtype.ext h`. Simplify using `[hl, hl']`.
-/
lemma zetaExcept_zero_add (L : PeriodPair) (z : ℂ) : zetaExcept L 0 z + 1 / z = wZeta L z := by
  have h1 := (hasSumLU_zetaExcept L 0).hasSum (x := z)
  have h2 := hasSum_ite_eq (0 : L.lattice) (1 / z)
  have h3 := (hasSumLU_wZeta L).hasSum (x := z)
  refine (h1.add h2).unique ?_
  convert h3 using 1
  funext l
  by_cases hl : l = 0
  · subst hl
    simp
  · have hl' : (l : ℂ) ≠ 0 := by
      intro h
      apply hl
      exact Subtype.ext h
    simp [hl, hl']

/- English proof (translation)
Establish `h : ∀ l : L.lattice, (if (l : ℂ) = 0 then 0 else (1 / (0 - (l : ℂ)) + 1 / (l : ℂ) + 0 / (l : ℂ) ^ 2)) = 0`. Introduce `l`. Use `split_ifs`. Both sides reduce to the same expression. Rewrite using `[zero_sub, zero_div, add_zero, one_div_neg_eq_neg_one_div, neg_add_cancel]`.

Simplify using `only [zetaExcept, h, tsum_zero]`.
-/
lemma zetaExcept_zero_zero (L : PeriodPair) : zetaExcept L 0 0 = 0 := by
  have h : ∀ l : L.lattice, (if (l : ℂ) = 0 then 0 else
      (1 / (0 - (l : ℂ)) + 1 / (l : ℂ) + 0 / (l : ℂ) ^ 2)) = 0 := by
    intro l
    split_ifs
    · rfl
    · rw [zero_sub, zero_div, add_zero, one_div_neg_eq_neg_one_div, neg_add_cancel]
  simp only [zetaExcept, h, tsum_zero]

/- English proof (translation)
Conclude with `hasDerivAt_inv_sub_add_inv_add_div_sq l z h`.
-/
lemma hasDerivAt_term (l z : ℂ) (h : z - l ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ 1 / (z - l) + 1 / l + z / l ^ 2)
      (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
  exact hasDerivAt_inv_sub_add_inv_add_div_sq l z h

/- English proof (translation)
Establish `h' : TendstoLocallyUniformlyOn (fun s x => ∑ i ∈ s, F i x) g Filter.atTop U` using `h`. Establish `hd` using `h'.deriv (Filter.Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hF i) hU`. Establish `hD : TendstoLocallyUniformlyOn (fun s x => ∑ i ∈ s, deriv (F i) x) (deriv g) Filter.atTop U`. Use `hd.congr fun s x hx => ?_` and prove the remaining obligations. Establish `he : (fun y => ∑ i ∈ s, F i y) = ∑ i ∈ s, F i`.

Use function extensionality and compare the values at `y`. Simplify using `[Finset.sum_apply]`. Simplify using `only [Function.comp_apply]`. Rewrite using `[he, deriv_sum fun i _ => (hF i).differentiableAt (hU.mem_nhds hx)]`. Conclude with `HasSumLocallyUniformlyOn.hasSum hD hz`.
-/
private lemma hasSum_deriv_of_hasSumLocallyUniformlyOn {ι : Type*} {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (h : HasSumLocallyUniformlyOn F g U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    {z : ℂ} (hz : z ∈ U) : HasSum (fun i => deriv (F i) z) (deriv g z) := by
  have h' : TendstoLocallyUniformlyOn (fun s x => ∑ i ∈ s, F i x) g Filter.atTop U := h
  have hd := h'.deriv
    (Filter.Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hF i) hU
  have hD : TendstoLocallyUniformlyOn (fun s x => ∑ i ∈ s, deriv (F i) x) (deriv g)
      Filter.atTop U := by
    refine hd.congr fun s x hx => ?_
    have he : (fun y => ∑ i ∈ s, F i y) = ∑ i ∈ s, F i := by
      funext y
      simp [Finset.sum_apply]
    simp only [Function.comp_apply]
    rw [he, deriv_sum fun i _ => (hF i).differentiableAt (hU.mem_nhds hx)]
  exact HasSumLocallyUniformlyOn.hasSum hD hz

/- English proof (translation)
Introduce `z hz`. Establish `hU : IsOpen ((L.lattice : Set ℂ)ᶜ)` using `L.isClosed_lattice.isOpen_compl`. Establish `hF : ∀ l : L.lattice, DifferentiableOn ℂ (fun w : ℂ => 1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2) (L.lattice : Set ℂ)ᶜ`. Introduce `l w hw`. Establish `hwl : w - l ≠ 0`.

Introduce `e`. Apply `hw` to reduce the goal to its premises. Rewrite using `[sub_eq_zero.mp e]`. Conclude with `l.2`. Conclude with `(hasDerivAt_term l w hwl).differentiableAt.differentiableWithinAt`.

Establish `hs` using `hasSum_deriv_of_hasSumLocallyUniformlyOn (hasSumLU_wZeta L).hasSumLocallyUniformlyOn hF hU hz`. Establish `hder : (fun l : L.lattice => deriv (fun w : ℂ => 1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2) z) = fun l : L.lattice => -(1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)`. Use function extensionality and compare the values at `l`. Establish `hzl : z - l ≠ 0`. Introduce `e`.

Apply `hz` to reduce the goal to its premises. Rewrite using `[sub_eq_zero.mp e]`. Conclude with `l.2`. Conclude with `(hasDerivAt_term l z hzl).deriv`. Rewrite `hs` using `[hder]`.

Conclude with `hs.unique (L.hasSum_weierstrassP z).neg`.
-/
lemma eqOn_deriv_wZeta (L : PeriodPair) :
    Set.EqOn (deriv (wZeta L)) (fun z ↦ -(L.weierstrassP z)) (L.lattice : Set ℂ)ᶜ := by
  intro z hz
  have hU : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hF : ∀ l : L.lattice, DifferentiableOn ℂ
      (fun w : ℂ => 1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2) (L.lattice : Set ℂ)ᶜ := by
    intro l w hw
    have hwl : w - l ≠ 0 := by
      intro e
      apply hw
      rw [sub_eq_zero.mp e]
      exact l.2
    exact (hasDerivAt_term l w hwl).differentiableAt.differentiableWithinAt
  have hs := hasSum_deriv_of_hasSumLocallyUniformlyOn (hasSumLU_wZeta L).hasSumLocallyUniformlyOn hF hU hz
  have hder : (fun l : L.lattice =>
      deriv (fun w : ℂ => 1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2) z) =
      fun l : L.lattice => -(1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2) := by
    funext l
    have hzl : z - l ≠ 0 := by
      intro e
      apply hz
      rw [sub_eq_zero.mp e]
      exact l.2
    exact (hasDerivAt_term l z hzl).deriv
  rw [hder] at hs
  exact hs.unique (L.hasSum_weierstrassP z).neg

/- English proof (translation)
Use `differentiableOn_of_hasSumLocallyUniformlyOn' (hasSumLU_wZeta L).hasSumLocallyUniformlyOn (fun l => ?_) L.isClosed_lattice.isOpen_compl` and prove the remaining obligations. Introduce `w hw`. Establish `hwl : w - l ≠ 0`. Introduce `e`. Apply `hw` to reduce the goal to its premises.

Rewrite using `[sub_eq_zero.mp e]`. Conclude with `l.2`. Conclude with `(hasDerivAt_term l w hwl).differentiableAt.differentiableWithinAt`.
-/
lemma differentiableOn_wZeta (L : PeriodPair) :
    DifferentiableOn ℂ (wZeta L) (L.lattice : Set ℂ)ᶜ := by
  refine differentiableOn_of_hasSumLocallyUniformlyOn' (hasSumLU_wZeta L).hasSumLocallyUniformlyOn (fun l => ?_)
    L.isClosed_lattice.isOpen_compl
  intro w hw
  have hwl : w - l ≠ 0 := by
    intro e
    apply hw
    rw [sub_eq_zero.mp e]
    exact l.2
  exact (hasDerivAt_term l w hwl).differentiableAt.differentiableWithinAt

end AnalyticIdentityTheoremsZetaFacts

open AnalyticIdentityTheoremsZetaFacts

/- English proof (translation)
Introduce `L z`. Conclude with `(hasSumLU_wZeta L).hasSum.summable`.
-/
theorem zeta_summable : ZetaSummable := by
  intro L z
  exact (hasSumLU_wZeta L).hasSum.summable

/- English proof (translation)
Introduce `L z hz`. Establish `hU : IsOpen ((L.lattice : Set ℂ)ᶜ)` using `L.isClosed_lattice.isOpen_compl`. Establish `hd` using `(differentiableOn_wZeta L).differentiableAt (hU.mem_nhds hz)`. Use `hd.hasDerivAt` as an intermediate fact. Rewrite `this` using `[eqOn_deriv_wZeta L hz]`. Then use the resulting hypothesis.
-/
theorem zeta_has_deriv : ZetaHasDeriv := by
  intro L z hz
  have hU : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hd := (differentiableOn_wZeta L).differentiableAt (hU.mem_nhds hz)
  have := hd.hasDerivAt
  rwa [eqOn_deriv_wZeta L hz] at this

/- English proof (translation)
Introduce `L z`. Unfold `wZeta`. Rewrite using `[← (Equiv.neg L.lattice).tsum_eq, ← tsum_neg]`. Use `tsum_congr fun l => ?_` and prove the remaining obligations. Simplify using `only [Equiv.neg_apply, Submodule.coe_neg]`.

Establish `h1 : -z - -(l : ℂ) = -(z - l)` using `by ring`. Rewrite using `[h1, neg_sq, one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div, neg_div]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zeta_odd : ZetaOdd := by
  intro L z
  unfold wZeta
  rw [← (Equiv.neg L.lattice).tsum_eq, ← tsum_neg]
  refine tsum_congr fun l => ?_
  simp only [Equiv.neg_apply, Submodule.coe_neg]
  have h1 : -z - -(l : ℂ) = -(z - l) := by ring
  rw [h1, neg_sq, one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div, neg_div]
  ring

/- English proof (translation)
Introduce `L`. Establish `hU : IsOpen (((L.lattice : Set ℂ) \ {0})ᶜ)` using `L.isOpen_compl_lattice_diff`. Establish `h0 : (0 : ℂ) ∈ ((L.lattice : Set ℂ) \ {0})ᶜ` using `by simp`. Establish `hc : ContinuousAt (zetaExcept L 0) 0` using `((differentiableOn_zetaExcept L 0).differentiableAt (hU.mem_nhds h0)).continuousAt`. Establish `ht` using `hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))`.

Rewrite `ht` using `[zetaExcept_zero_zero]`. Use `ht.congr' (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Use `show zetaExcept L 0 z = wZeta L z - 1 / z`. Rewrite using `[← zetaExcept_zero_add L z]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zeta_pole_holds : ZetaPole := by
  intro L
  have hU : IsOpen (((L.lattice : Set ℂ) \ {0})ᶜ) := L.isOpen_compl_lattice_diff
  have h0 : (0 : ℂ) ∈ ((L.lattice : Set ℂ) \ {0})ᶜ := by simp
  have hc : ContinuousAt (zetaExcept L 0) 0 :=
    ((differentiableOn_zetaExcept L 0).differentiableAt (hU.mem_nhds h0)).continuousAt
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
  rw [zetaExcept_zero_zero] at ht
  refine ht.congr' (Filter.Eventually.of_forall fun z => ?_)
  show zetaExcept L 0 z = wZeta L z - 1 / z
  rw [← zetaExcept_zero_add L z]
  ring

end Formalism.L2.Th1.F
