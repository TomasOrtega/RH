import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.ValRing

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
The claim follows from `RingHom.ker_isPrime _`.
-/
theorem isPrime_mCoordIdeal (z : (Σ k, ι k) → ℂ) : (mCoordIdeal z).IsPrime :=
  RingHom.ker_isPrime _

/- English proof (translation)
Introduce `h0`. Use `hn (mem_mCoordIdeal_of_aeval_eq_zero z hh ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]`. Simplify using `using h0`.
-/
theorem eval_ne_zero_of_notMem {z : (Σ k, ι k) → ℂ} {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) (hn : h ∉ mCoordIdeal z) :
    eval z (map (Int.castRingHom ℂ) h) ≠ 0 := by
  intro h0
  refine hn (mem_mCoordIdeal_of_aeval_eq_zero z hh ?_)
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  simpa using h0

/- English proof (translation)
Introduce `h0` and use `eval_ne_zero_of_notMem hh hn (eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero x hh h0))`.
-/
theorem aeval_ne_zero_of_notMem {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal x)) {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) (hn : h ∉ mCoordIdeal z) : aeval x h ≠ 0 := fun h0 =>
  eval_ne_zero_of_notMem hh hn
    (eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero x hh h0))

/- English proof (translation)
Take `⟨d, g, h, hg, hh, hn, heq⟩` from `hs`. Conclude with `⟨_, d, g, h, hg, hh, aeval_ne_zero_of_notMem hz hh hn, heq, eval_ne_zero_of_notMem hh hn, rfl⟩`.
-/
theorem exists_isValueAt {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (hs : RegAt x (mCoordIdeal z) s) :
    ∃ v, IsValueAt x s z v := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  exact ⟨_, d, g, h, hg, hh, aeval_ne_zero_of_notMem hz hh hn, heq,
    eval_ne_zero_of_notMem hh hn, rfl⟩

/- English proof (translation)
Take `⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩` from `hv`. Take `⟨d', g', h', hg', hh', hy', heq', hz0', rfl⟩` from `hw`. Use `⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add (isMultiHomog_mul hg hh') ?_, isMultiHomog_mul hh hh', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_comm d d']`. Conclude with `isMultiHomog_mul hg' hh`.

Rewrite using `[map_mul]`. Conclude with `mul_ne_zero hy hy'`. Simplify using `only [map_add, map_mul, heq, heq']`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_mul]`.

Conclude with `mul_ne_zero hz0 hz0'`. Simplify using `only [map_add, map_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem isValueAt_add {x : (Σ k, ι k) → Ω} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (hv : IsValueAt x s z v) (hw : IsValueAt x t z w) : IsValueAt x (s + t) z (v + w) := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  obtain ⟨d', g', h', hg', hh', hy', heq', hz0', rfl⟩ := hw
  refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add (isMultiHomog_mul hg hh') ?_,
    isMultiHomog_mul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [add_comm d d']
    exact isMultiHomog_mul hg' hh
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · simp only [map_add, map_mul, heq, heq']; ring
  · simp only [map_mul]; exact mul_ne_zero hz0 hz0'
  · simp only [map_add, map_mul]
    field_simp

/- English proof (translation)
Take `⟨d, g, h, hg, hh, hn, heq⟩` from `hs`. Take `⟨d', g', h', hg', hh', hn', heq'⟩` from `ht`. Use `⟨d + d', g * g', h * h', isMultiHomog_mul hg hg', isMultiHomog_mul hh hh', fun hm => ((isPrime_mCoordIdeal z).mem_or_mem hm).elim hn hn', ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, heq, heq']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem regAt_mul {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s t : Ω}
    (hs : RegAt x (mCoordIdeal z) s) (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s * t) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  obtain ⟨d', g', h', hg', hh', hn', heq'⟩ := ht
  refine ⟨d + d', g * g', h * h', isMultiHomog_mul hg hg', isMultiHomog_mul hh hh',
    fun hm => ((isPrime_mCoordIdeal z).mem_or_mem hm).elim hn hn', ?_⟩
  rw [map_mul, map_mul, heq, heq']; ring

/- English proof (translation)
Take `⟨d, g, h, hg, hh, hn, heq⟩` from `hs`. Take `⟨d', g', h', hg', hh', hn', heq'⟩` from `ht`. Use `⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add (isMultiHomog_mul hg hh') ?_, isMultiHomog_mul hh hh', fun hm => ((isPrime_mCoordIdeal z).mem_or_mem hm).elim hn hn', ?_⟩` and prove the remaining obligations. Rewrite using `[add_comm d d']`. Conclude with `isMultiHomog_mul hg' hh`.

Simplify using `only [map_add, map_mul, heq, heq']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem regAt_add {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s t : Ω}
    (hs : RegAt x (mCoordIdeal z) s) (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s + t) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  obtain ⟨d', g', h', hg', hh', hn', heq'⟩ := ht
  refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add (isMultiHomog_mul hg hh') ?_,
    isMultiHomog_mul hh hh',
    fun hm => ((isPrime_mCoordIdeal z).mem_or_mem hm).elim hn hn', ?_⟩
  · rw [add_comm d d']
    exact isMultiHomog_mul hg' hh
  · simp only [map_add, map_mul, heq, heq']; ring

/- English proof (translation)
The claim follows from `(Ideal.ne_top_iff_one _).1 (isPrime_mCoordIdeal z).ne_top`.
-/
theorem one_notMem_mCoordIdeal (z : (Σ k, ι k) → ℂ) : (1 : MRing ι) ∉ mCoordIdeal z :=
  (Ideal.ne_top_iff_one _).1 (isPrime_mCoordIdeal z).ne_top

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, 0, 1, isMultiHomog_zero 0, isMultiHomog_one, one_notMem_mCoordIdeal z, by simp⟩`.
-/
theorem regAt_zero (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : RegAt x (mCoordIdeal z) 0 :=
  ⟨0, 0, 1, isMultiHomog_zero 0, isMultiHomog_one, one_notMem_mCoordIdeal z, by simp⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, 1, 1, isMultiHomog_one, isMultiHomog_one, one_notMem_mCoordIdeal z, by simp⟩`.
-/
theorem regAt_one (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : RegAt x (mCoordIdeal z) 1 :=
  ⟨0, 1, 1, isMultiHomog_one, isMultiHomog_one, one_notMem_mCoordIdeal z, by simp⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, 0, 1, isMultiHomog_zero 0, isMultiHomog_one, by simp, by simp, by simp, by simp⟩`.
-/
theorem isValueAt_zero_self (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : IsValueAt x 0 z 0 :=
  ⟨0, 0, 1, isMultiHomog_zero 0, isMultiHomog_one, by simp, by simp, by simp, by simp⟩

end

/- English proof (translation)
Introduce `K _ ι _ Ω _ x z hz`. Use `⟨regAt_zero x z, regAt_one x z, valAt_eq hz (isValueAt_zero_self x z), valAt_eq hz (isValueAt_one_self x z), fun s t hs ht => ⟨regAt_mul hs ht, regAt_add hs ht, ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `exists_isValueAt hz hs`. Take `⟨w, hw⟩` from `exists_isValueAt hz ht`. Rewrite using `[valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (isValueAt_mul hv hw)]`.

Take `⟨v, hv⟩` from `exists_isValueAt hz hs`. Take `⟨w, hw⟩` from `exists_isValueAt hz ht`. Rewrite using `[valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (isValueAt_add hv hw)]`.
-/
theorem regAt_valAt_ring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal x) → RegAt x (mCoordIdeal z) 0 ∧ RegAt x (mCoordIdeal z) 1 ∧ valAt x 0 z = 0 ∧ valAt x 1 z = 1 ∧ ∀ s t : Ω, RegAt x (mCoordIdeal z) s → RegAt x (mCoordIdeal z) t → RegAt x (mCoordIdeal z) (s * t) ∧ RegAt x (mCoordIdeal z) (s + t) ∧ valAt x (s * t) z = valAt x s z * valAt x t z ∧ valAt x (s + t) z = valAt x s z + valAt x t z := by
  intro K _ ι _ Ω _ x z hz
  refine ⟨regAt_zero x z, regAt_one x z, valAt_eq hz (isValueAt_zero_self x z),
    valAt_eq hz (isValueAt_one_self x z), fun s t hs ht => ⟨regAt_mul hs ht, regAt_add hs ht, ?_, ?_⟩⟩
  · obtain ⟨v, hv⟩ := exists_isValueAt hz hs
    obtain ⟨w, hw⟩ := exists_isValueAt hz ht
    rw [valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (isValueAt_mul hv hw)]
  · obtain ⟨v, hv⟩ := exists_isValueAt hz hs
    obtain ⟨w, hw⟩ := exists_isValueAt hz ht
    rw [valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (isValueAt_add hv hw)]

end GlobalTheory.CompanionTheory.Ar.PB.ValRing
