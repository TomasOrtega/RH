import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.IntegrableUnitIndicator

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Simplify using `only [dotProduct, Pi.star_apply, Complex.ofReal_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Both sides reduce to the same expression.
-/
lemma dot_star_self (y : ι → ℂ) : star y ⬝ᵥ y = ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/- English proof (translation)
Unfold `tW`. Apply the tactic sequence `rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by split_ifs <;> simp [Complex.normSq_nonneg])]`. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_ne', Finset.sum_erase_eq_sub (Finset.mem_univ q)]`.
-/
lemma tW_sq (q : ι) (x : ι → ℂ) :
    tW q x ^ 2 = ∑ i, Complex.normSq (x i) - Complex.normSq (x q) := by
  unfold tW
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by split_ifs <;> simp [Complex.normSq_nonneg])]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_ne',
    Finset.sum_erase_eq_sub (Finset.mem_univ q)]

/- English proof (translation)
Establish `hq : (h *ᵥ x) q = x q`. Simplify using `[mulVec, dotProduct, hrow]`. Use `⟨?_, hq⟩` and prove the remaining obligations. Establish `hn : ∑ i, Complex.normSq ((h *ᵥ x) i) = ∑ i, Complex.normSq (x i)`. Establish `e : star (h *ᵥ x) ⬝ᵥ (h *ᵥ x) = star x ⬝ᵥ x`.

Rewrite using `[star_mulVec, dotProduct_mulVec, vecMul_vecMul, hu, vecMul_one]`. Rewrite `e` using `[dot_star_self, dot_star_self]`. Conclude with `e` after adjusting the coercions. Establish `h1` using `tW_sq q (h *ᵥ x)`. Establish `h2` using `tW_sq q x`.

Rewrite `h1` using `[hn, hq, ← h2]`. Establish `n1 : 0 ≤ tW q (h *ᵥ x)` using `Real.sqrt_nonneg _`. Establish `n2 : 0 ≤ tW q x` using `Real.sqrt_nonneg _`. Conclude with `(pow_left_inj₀ n1 n2 two_ne_zero).mp h1`.
-/
lemma tW_mulVec {h : Matrix ι ι ℂ} (hu : hᴴ * h = 1) {q : ι}
    (hrow : ∀ j, h q j = if j = q then 1 else 0) (x : ι → ℂ) :
    tW q (h *ᵥ x) = tW q x ∧ (h *ᵥ x) q = x q := by
  have hq : (h *ᵥ x) q = x q := by
    simp [mulVec, dotProduct, hrow]
  refine ⟨?_, hq⟩
  have hn : ∑ i, Complex.normSq ((h *ᵥ x) i) = ∑ i, Complex.normSq (x i) := by
    have e : star (h *ᵥ x) ⬝ᵥ (h *ᵥ x) = star x ⬝ᵥ x := by
      rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hu, vecMul_one]
    rw [dot_star_self, dot_star_self] at e
    exact_mod_cast e
  have h1 := tW_sq q (h *ᵥ x)
  have h2 := tW_sq q x
  rw [hn, hq, ← h2] at h1
  have n1 : 0 ≤ tW q (h *ᵥ x) := Real.sqrt_nonneg _
  have n2 : 0 ≤ tW q x := Real.sqrt_nonneg _
  exact (pow_left_inj₀ n1 n2 two_ne_zero).mp h1

/- English proof (translation)
Establish `hc : Continuous (tW q)`. Unfold `tW`. Use `Continuous.sqrt (continuous_finset_sum _ fun i _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hi : i = q`. Simplify using `only [hi, ↓reduceIte]`.

Conclude with `continuous_const`. Simplify using `only [hi, ↓reduceIte]`. Conclude with `Complex.continuous_normSq.comp (continuous_apply i)`. Establish `hU : IsOpen {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1}` using `(isOpen_lt continuous_const hc).inter ((isOpen_lt hc continuous_const).inter (isOpen_lt (continuous_norm.comp (continuous_apply q)) continuous_const))`. Set `x0 : ι → ℂ` to `fun i => if i = p then ((3 / 4 : ℝ) : ℂ) else 0`.

Establish `hs : (∑ i, if i = q then (0 : ℝ) else Complex.normSq (x0 i)) = 9 / 16`. Rewrite using `[Finset.sum_eq_single p]`. Simplify using `only [hpq, ↓reduceIte, x0, Complex.normSq_ofReal]`. Evaluate the numerical expressions. Introduce `b _ hb`.

Simplify using `[x0, hb]`. Introduce `hp`. Conclude with `absurd (Finset.mem_univ p) hp`. Establish `ht : tW q x0 = 3 / 4`. Unfold `tW`.

Rewrite using `[hs, show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]`. Establish `hx0 : x0 ∈ {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1}`. Use `⟨by rw [ht]; norm_num, by rw [ht]; norm_num, ?_⟩` and prove the remaining obligations. Simplify using `[x0, Ne.symm hpq]`. Establish `hsub : {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1} ⊆ Bset q` using `fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩`.

Introduce `h0`. Conclude with `(hU.measure_pos volume ⟨x0, hx0⟩).ne' (measure_mono_null hsub h0)`.
-/
lemma volume_Bset_ne_zero {p q : ι} (hpq : p ≠ q) {k : ℕ} (hk : Fintype.card ι = k + 1) :
    volume (Bset q) ≠ 0 := by
  have hc : Continuous (tW q) := by
    unfold tW
    refine Continuous.sqrt (continuous_finset_sum _ fun i _ => ?_)
    by_cases hi : i = q
    · simp only [hi, ↓reduceIte]; exact continuous_const
    · simp only [hi, ↓reduceIte]; exact Complex.continuous_normSq.comp (continuous_apply i)
  have hU : IsOpen {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1} :=
    (isOpen_lt continuous_const hc).inter
      ((isOpen_lt hc continuous_const).inter
        (isOpen_lt (continuous_norm.comp (continuous_apply q)) continuous_const))
  let x0 : ι → ℂ := fun i => if i = p then ((3 / 4 : ℝ) : ℂ) else 0
  have hs : (∑ i, if i = q then (0 : ℝ) else Complex.normSq (x0 i)) = 9 / 16 := by
    rw [Finset.sum_eq_single p]
    · simp only [hpq, ↓reduceIte, x0, Complex.normSq_ofReal]; norm_num
    · intro b _ hb; simp [x0, hb]
    · intro hp; exact absurd (Finset.mem_univ p) hp
  have ht : tW q x0 = 3 / 4 := by
    unfold tW
    rw [hs, show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hx0 : x0 ∈ {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1} := by
    refine ⟨by rw [ht]; norm_num, by rw [ht]; norm_num, ?_⟩
    simp [x0, Ne.symm hpq]
  have hsub : {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1} ⊆ Bset q :=
    fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩
  intro h0
  exact (hU.measure_pos volume ⟨x0, hx0⟩).ne' (measure_mono_null hsub h0)

end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
