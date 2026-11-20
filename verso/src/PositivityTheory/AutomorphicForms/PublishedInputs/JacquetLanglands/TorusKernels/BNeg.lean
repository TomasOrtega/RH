import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.AutomorphyFactorLemmas

open UpperTheory.Esk

/- English proof (translation)
Conclude with `continuous_subtype_val`.
-/
theorem b_cv : Continuous (fun z : P => z.1) := by
  exact continuous_subtype_val

/- English proof (translation)
Introduce `h0`. Establish `h1` using `congrArg Complex.im h0`. Simplify using `only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at h1`. Establish `h2 : w.im = -z.im` using `by linarith`. Rewrite `h` using `[h2]`.

Use polynomial arithmetic with `[mul_self_nonneg z.im]`.
-/
theorem b_ne (z w : ℂ) (h : 0 < z.im * w.im) : z - conj w ≠ 0 := by
  intro h0
  have h1 := congrArg Complex.im h0
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at h1
  have h2 : w.im = -z.im := by linarith
  rw [h2] at h
  nlinarith [mul_self_nonneg z.im]

/- English proof (translation)
Establish `hne : z.1.im * w.1.im ≠ 0` using `mul_ne_zero z.2 w.2`. Conclude with `lt_of_le_of_ne (not_lt.mp h) hne`.
-/
theorem b_neg (z w : P) (h : ¬ 0 < z.1.im * w.1.im) : z.1.im * w.1.im < 0 := by
  have hne : z.1.im * w.1.im ≠ 0 := mul_ne_zero z.2 w.2
  exact lt_of_le_of_ne (not_lt.mp h) hne

/- English proof (translation)
Unfold `j1 den`. Conclude with `(((continuous_const.mul b_cv).add continuous_const).pow k).mul continuous_const`.
-/
theorem p7 (k : ℕ) (g : GL (Fin 2) ℝ) : Continuous (j1 k g) := by
  unfold j1 den
  exact (((continuous_const.mul b_cv).add continuous_const).pow k).mul continuous_const

/- English proof (translation)
Establish `hz : Continuous fun p : P × P => p.1.1` using `b_cv.comp continuous_fst`. Establish `hw : Continuous fun p : P × P => p.2.1` using `b_cv.comp continuous_snd`. Establish `hf : Continuous fun p : P × P => p.1.1.im * p.2.1.im` using `(Complex.continuous_im.comp hz).mul (Complex.continuous_im.comp hw)`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `p`.

Distinguish the cases in `hp : 0 < p.1.1.im * p.2.1.im`. Establish `hU : ∀ᶠ q in nhds p, 0 < q.1.1.im * q.2.1.im` using `(hf.tendsto p).eventually (lt_mem_nhds hp)`. Establish `hg : ContinuousAt (fun q : P × P => ((k : ℂ) - 1) / (4 * Real.pi) * ((q.2.1 - conj q.2.1) / (q.1.1 - conj q.2.1)) ^ k) p`. Apply `ContinuousAt.mul continuousAt_const` to reduce the goal to its premises. Apply `ContinuousAt.pow` to reduce the goal to its premises.

Apply `ContinuousAt.div` to reduce the goal to its premises. Conclude with `(hw.sub (Complex.continuous_conj.comp hw)).continuousAt`. Conclude with `(hz.sub (Complex.continuous_conj.comp hw)).continuousAt`. Conclude with `b_ne _ _ hp`. Apply `hg.congr` to reduce the goal to its premises.

Use `filter_upwards [hU] with q hq`. Simplify using `only [q1, if_pos hq]`. Establish `hV : ∀ᶠ q in nhds p, q.1.1.im * q.2.1.im < 0` using `(hf.tendsto p).eventually (gt_mem_nhds (b_neg p.1 p.2 hp))`. Establish `hg : ContinuousAt (fun _ : P × P => (0 : ℂ)) p` using `continuousAt_const`. Apply `hg.congr` to reduce the goal to its premises.

Use `filter_upwards [hV] with q hq`. Simplify using `only [q1, if_neg (not_lt.mpr hq.le)]`.
-/
theorem p8 (k : ℕ) : Continuous fun p : P × P => q1 k p.1 p.2 := by
  have hz : Continuous fun p : P × P => p.1.1 := b_cv.comp continuous_fst
  have hw : Continuous fun p : P × P => p.2.1 := b_cv.comp continuous_snd
  have hf : Continuous fun p : P × P => p.1.1.im * p.2.1.im :=
    (Complex.continuous_im.comp hz).mul (Complex.continuous_im.comp hw)
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : 0 < p.1.1.im * p.2.1.im
  · have hU : ∀ᶠ q in nhds p, 0 < q.1.1.im * q.2.1.im := (hf.tendsto p).eventually (lt_mem_nhds hp)
    have hg : ContinuousAt (fun q : P × P =>
        ((k : ℂ) - 1) / (4 * Real.pi) * ((q.2.1 - conj q.2.1) / (q.1.1 - conj q.2.1)) ^ k) p := by
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.pow
      apply ContinuousAt.div
      · exact (hw.sub (Complex.continuous_conj.comp hw)).continuousAt
      · exact (hz.sub (Complex.continuous_conj.comp hw)).continuousAt
      · exact b_ne _ _ hp
    apply hg.congr
    filter_upwards [hU] with q hq
    simp only [q1, if_pos hq]
  · have hV : ∀ᶠ q in nhds p, q.1.1.im * q.2.1.im < 0 :=
      (hf.tendsto p).eventually (gt_mem_nhds (b_neg p.1 p.2 hp))
    have hg : ContinuousAt (fun _ : P × P => (0 : ℂ)) p := continuousAt_const
    apply hg.congr
    filter_upwards [hV] with q hq
    simp only [q1, if_neg (not_lt.mpr hq.le)]

/- English proof (translation)
Introduce `t ht`. Establish `ht' : t.im ≠ 0` using `ht`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Establish `hcont : Continuous fun s : ℂ => s.im * w.1.im` using `Complex.continuous_im.mul continuous_const`. Distinguish the cases in `hp : 0 < t.im * w.1.im`.

Establish `hU : ∀ᶠ s in nhds t, 0 < s.im * w.1.im` using `(hcont.tendsto t).eventually (lt_mem_nhds hp)`. Establish `hd : DifferentiableAt ℂ (fun s : ℂ => ((k : ℂ) - 1) / (4 * Real.pi) * ((w.1 - conj w.1) / (s - conj w.1)) ^ k) t`. Apply `DifferentiableAt.mul (differentiableAt_const _)` to reduce the goal to its premises. Apply `DifferentiableAt.pow` to reduce the goal to its premises. Apply `DifferentiableAt.div (differentiableAt_const _) (differentiableAt_id.sub (differentiableAt_const _))` to reduce the goal to its premises.

Conclude with `b_ne _ _ hp`. Apply `hd.congr_of_eventuallyEq` to reduce the goal to its premises. Use `filter_upwards [hU] with s hs`. Establish `hs' : s.im ≠ 0` using `fun h0 => by rw [h0, zero_mul] at hs; exact lt_irrefl _ hs`. Simplify using `only [ext1, dif_pos hs', q1, if_pos hs]`.

Establish `hneg : t.im * w.1.im < 0` using `lt_of_le_of_ne (not_lt.mp hp) (mul_ne_zero ht' w.2)`. Establish `hV : ∀ᶠ s in nhds t, s.im * w.1.im < 0` using `(hcont.tendsto t).eventually (gt_mem_nhds hneg)`. Apply `(differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq` to reduce the goal to its premises. Use `filter_upwards [hV] with s hs`. Distinguish the cases in `hs' : s.im ≠ 0`.

Simplify using `only [ext1, dif_pos hs', q1, if_neg (not_lt.mpr hs.le)]`. Simplify using `only [ext1, dif_neg hs']`.
-/
theorem p9 (k : ℕ) (w : P) : Hol1 fun z => q1 k z w := by
  intro t ht
  have ht' : t.im ≠ 0 := ht
  apply DifferentiableAt.differentiableWithinAt
  have hcont : Continuous fun s : ℂ => s.im * w.1.im := Complex.continuous_im.mul continuous_const
  by_cases hp : 0 < t.im * w.1.im
  · have hU : ∀ᶠ s in nhds t, 0 < s.im * w.1.im := (hcont.tendsto t).eventually (lt_mem_nhds hp)
    have hd : DifferentiableAt ℂ (fun s : ℂ =>
        ((k : ℂ) - 1) / (4 * Real.pi) * ((w.1 - conj w.1) / (s - conj w.1)) ^ k) t := by
      apply DifferentiableAt.mul (differentiableAt_const _)
      apply DifferentiableAt.pow
      apply DifferentiableAt.div (differentiableAt_const _) (differentiableAt_id.sub (differentiableAt_const _))
      exact b_ne _ _ hp
    apply hd.congr_of_eventuallyEq
    filter_upwards [hU] with s hs
    have hs' : s.im ≠ 0 := fun h0 => by rw [h0, zero_mul] at hs; exact lt_irrefl _ hs
    simp only [ext1, dif_pos hs', q1, if_pos hs]
  · have hneg : t.im * w.1.im < 0 := lt_of_le_of_ne (not_lt.mp hp) (mul_ne_zero ht' w.2)
    have hV : ∀ᶠ s in nhds t, s.im * w.1.im < 0 := (hcont.tendsto t).eventually (gt_mem_nhds hneg)
    apply (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [hV] with s hs
    by_cases hs' : s.im ≠ 0
    · simp only [ext1, dif_pos hs', q1, if_neg (not_lt.mpr hs.le)]
    · simp only [ext1, dif_neg hs']

end UpperTheory.Esk.AutomorphyFactorLemmas
