import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

/- English proof (translation)
Introduce `K _ ι _ A hA`. Establish `hne : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ k, ∃ i, (fun p => starRingEnd ℂ (z p)) ⟨k, i⟩ ≠ 0`. Introduce `z hz k`. Take `⟨i, hi⟩` from `hz k`. Conclude with `⟨i, by simpa using hi⟩`.

Use `⟨⟨A.a, fun z => Real.sqrt (A.h z * A.h fun p => starRingEnd ℂ (z p)), ?_, ?_⟩, rfl, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Conclude with `Real.sqrt_pos.2 (mul_pos (A.pos z hz) (A.pos _ (hne z hz)))`. Introduce `c z hc`. Establish `h1` using `A.smul (fun k => starRingEnd ℂ (c k)) (fun p => starRingEnd ℂ (z p)) (fun k => by simpa using hc k)`.

Simplify using `only [RCLike.norm_conj] at h1`. Simplify using `only [map_mul]`. Rewrite using `[h1, A.smul c z hc]`. Establish `h0 : 0 ≤ ∏ k, ‖c k‖ ^ A.a k` using `Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _`. Rewrite using `[mul_mul_mul_comm, Real.sqrt_mul (mul_nonneg h0 h0), Real.sqrt_mul_self h0]`.

Establish `hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => fun p => starRingEnd ℂ (z p))`. Use `contDiff_pi.2 fun p => ?_` and prove the remaining obligations. Conclude with `Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ p)`. Use `ContDiffOn.sqrt (ContDiffOn.mul hA (hA.comp hc.contDiffOn fun z hz => hne z hz)) ?_` and prove the remaining obligations. Introduce `z hz`.

Conclude with `(mul_pos (A.pos z hz) (A.pos _ (hne z hz))).ne'`. Introduce `z`. Simplify using `only [Complex.conj_conj, mul_comm]`. Introduce `z hz show Real.log (Real.sqrt _) = _`. Rewrite using `[Real.log_sqrt (mul_pos (A.pos z hz) (A.pos _ (hne z hz))).le, Real.log_mul (A.pos z hz).ne' (A.pos _ (hne z hz)).ne']`.
-/
theorem PositivityTheory.Xgp.t_line_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι), IsSmoothHerm A → ∃ B : HermLine ι, B.a = A.a ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → Real.log (B.h z) = (Real.log (A.h z) + Real.log (A.h fun p => starRingEnd ℂ (z p))) / 2 := by
  intro K _ ι _ A hA
  have hne : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ∀ k, ∃ i, (fun p => starRingEnd ℂ (z p)) ⟨k, i⟩ ≠ 0 := by
    intro z hz k
    obtain ⟨i, hi⟩ := hz k
    exact ⟨i, by simpa using hi⟩
  refine ⟨⟨A.a, fun z => Real.sqrt (A.h z * A.h fun p => starRingEnd ℂ (z p)), ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
  · intro z hz
    exact Real.sqrt_pos.2 (mul_pos (A.pos z hz) (A.pos _ (hne z hz)))
  · intro c z hc
    have h1 := A.smul (fun k => starRingEnd ℂ (c k)) (fun p => starRingEnd ℂ (z p)) (fun k => by simpa using hc k)
    simp only [RCLike.norm_conj] at h1
    simp only [map_mul]
    rw [h1, A.smul c z hc]
    have h0 : 0 ≤ ∏ k, ‖c k‖ ^ A.a k := Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
    rw [mul_mul_mul_comm, Real.sqrt_mul (mul_nonneg h0 h0), Real.sqrt_mul_self h0]
  · have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => fun p => starRingEnd ℂ (z p)) := by
      refine contDiff_pi.2 fun p => ?_
      exact Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ p)
    refine ContDiffOn.sqrt (ContDiffOn.mul hA (hA.comp hc.contDiffOn fun z hz => hne z hz)) ?_
    intro z hz
    exact (mul_pos (A.pos z hz) (A.pos _ (hne z hz))).ne'
  · intro z
    simp only [Complex.conj_conj, mul_comm]
  · intro z hz
    show Real.log (Real.sqrt _) = _
    rw [Real.log_sqrt (mul_pos (A.pos z hz) (A.pos _ (hne z hz))).le,
      Real.log_mul (A.pos z hz).ne' (A.pos _ (hne z hz)).ne']
