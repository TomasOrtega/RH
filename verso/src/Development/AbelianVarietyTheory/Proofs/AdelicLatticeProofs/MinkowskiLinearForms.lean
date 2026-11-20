import Mathlib

namespace GlobalTheory.MinkowskiLinearForms

open MeasureTheory

/- English proof (translation)
Establish `hli : LinearIndependent ℝ (fun i => A i)` using `Matrix.linearIndependent_rows_of_det_ne_zero hA`. Set `b : Module.Basis ι ℝ (ι → ℝ)` to `basisOfPiSpaceOfLinearIndependent hli`. Establish `hb : (⇑b : ι → ι → ℝ) = fun i => A i` using `coe_basisOfPiSpaceOfLinearIndependent hli`. Set `L : AddSubgroup (ι → ℝ)` to `(Submodule.span ℤ (Set.range b)).toAddSubgroup`. Establish `hF` using `ZSpan.isAddFundamentalDomain' b (volume : Measure (ι → ℝ))`.

Set `s : Set (ι → ℝ)` to `Set.univ.pi fun _ => Set.Ioo (-t) t`. Establish `hsymm : ∀ x ∈ s, -x ∈ s`. Introduce `x hx`. Simplify using `only [s, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Pi.neg_apply] at hx ⊢`. Introduce `i`.

Take `⟨h1, h2⟩` from `hx i`. Conclude with `⟨by linarith, by linarith⟩`. Establish `hconv : Convex ℝ s` using `convex_pi (fun i _ => convex_Ioo (-t) t)`. Establish `hvolF : volume (ZSpan.fundamentalDomain b) = ENNReal.ofReal |Matrix.det A|`. Rewrite using `[ZSpan.volume_fundamentalDomain]`.

Use `congr 3`. Establish `hvols : volume s = ENNReal.ofReal ((2 * t) ^ Fintype.card ι)`. Simplify using `only [s, Real.volume_pi_Ioo]`. Rewrite using `[Finset.prod_const, Finset.card_univ, ← ENNReal.ofReal_pow (by linarith)]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Establish `hlt' : volume (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ (ι → ℝ) < volume s`. Rewrite using `[hvolF, hvols, Module.finrank_fintype_fun_eq_card]`. Rewrite using `[show (2 : ENNReal) ^ Fintype.card ι = ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι) by`. Rewrite using `[ENNReal.ofReal_pow (by norm_num)]; simp]`.

Rewrite using `[← ENNReal.ofReal_mul (abs_nonneg _)]`. Rewrite using `[ENNReal.ofReal_lt_ofReal_iff (by positivity)]`. Rewrite using `[mul_pow, mul_comm ((2:ℝ) ^ _)]`. Conclude with `mul_lt_mul_of_pos_right hlt (by positivity)`. Use `haveI hcount : Countable (Submodule.span ℤ (Set.range b)) := inferInstance`.

Use `haveI : Countable L := hcount`. Take `⟨x, hx0, hxs⟩` from `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF hsymm hconv hlt'`. Establish `hxmem : (x : ι → ℝ) ∈ Submodule.span ℤ (Set.range b)` using `x.2`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hxmem`. Use `⟨c, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hc0`. Apply `hx0` to reduce the goal to its premises. Use `ext1`. Rewrite using `[← hc, hc0]`. Simplify using the standard rewrite rules.

Introduce `j`. Establish `hxj` using `hxs j (Set.mem_univ j)`. Rewrite `hxj` using `[Set.mem_Ioo]`. Establish `: (x : ι → ℝ) j = ∑ i, (c i : ℝ) * A i j`. Rewrite using `[← hc, Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[hb, zsmul_eq_mul]`. Rewrite using `[← this, abs_lt]`. Conclude with `hxj`.
-/
theorem minkowski_linear_forms {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : Matrix.det A ≠ (0 : ℝ)) {t : ℝ} (ht : (0 : ℝ) < t)
    (hlt : |Matrix.det A| < t ^ Fintype.card ι) :
    ∃ (z : ι → ℤ), z ≠ (0 : ι → ℤ) ∧ ∀ (j : ι), |∑ i : ι, (↑(z i) : ℝ) * A i j| < t := by
  classical
  have hli : LinearIndependent ℝ (fun i => A i) := Matrix.linearIndependent_rows_of_det_ne_zero hA
  let b : Module.Basis ι ℝ (ι → ℝ) := basisOfPiSpaceOfLinearIndependent hli
  have hb : (⇑b : ι → ι → ℝ) = fun i => A i := coe_basisOfPiSpaceOfLinearIndependent hli
  let L : AddSubgroup (ι → ℝ) := (Submodule.span ℤ (Set.range b)).toAddSubgroup
  have hF := ZSpan.isAddFundamentalDomain' b (volume : Measure (ι → ℝ))
  let s : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Ioo (-t) t
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simp only [s, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Pi.neg_apply] at hx ⊢
    intro i
    obtain ⟨h1, h2⟩ := hx i
    exact ⟨by linarith, by linarith⟩
  have hconv : Convex ℝ s := convex_pi (fun i _ => convex_Ioo (-t) t)
  have hvolF : volume (ZSpan.fundamentalDomain b) = ENNReal.ofReal |Matrix.det A| := by
    rw [ZSpan.volume_fundamentalDomain]
    congr 3
  have hvols : volume s = ENNReal.ofReal ((2 * t) ^ Fintype.card ι) := by
    simp only [s, Real.volume_pi_Ioo]
    rw [Finset.prod_const, Finset.card_univ, ← ENNReal.ofReal_pow (by linarith)]
    congr 2
    ring
  have hlt' : volume (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ (ι → ℝ) < volume s := by
    rw [hvolF, hvols, Module.finrank_fintype_fun_eq_card]
    rw [show (2 : ENNReal) ^ Fintype.card ι = ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι) by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp]
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    rw [mul_pow, mul_comm ((2:ℝ) ^ _)]
    exact mul_lt_mul_of_pos_right hlt (by positivity)
  haveI hcount : Countable (Submodule.span ℤ (Set.range b)) := inferInstance
  haveI : Countable L := hcount
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF hsymm hconv hlt'
  have hxmem : (x : ι → ℝ) ∈ Submodule.span ℤ (Set.range b) := x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hxmem
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    apply hx0
    ext1
    rw [← hc, hc0]
    simp
  · intro j
    have hxj := hxs j (Set.mem_univ j)
    rw [Set.mem_Ioo] at hxj
    have : (x : ι → ℝ) j = ∑ i, (c i : ℝ) * A i j := by
      rw [← hc, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hb, zsmul_eq_mul]
    rw [← this, abs_lt]
    exact hxj

end GlobalTheory.MinkowskiLinearForms
