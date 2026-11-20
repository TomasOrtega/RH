import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps

open MeasureTheory

namespace GlobalTheory.CompanionTheory.GunrVol

/- English proof (translation)
Introduce `V _ _ _ _ _ μ χ hsd L hLo hLc hadd _ hann`. Take `⟨hH, hinv⟩` from `hsd`. Use `haveI := hH`. Establish `hLcl : IsClosed (L : Set V)` using `AddSubgroup.isClosed_of_isOpen L hLo`. Establish `hLm : MeasurableSet (L : Set V)` using `hLo.measurableSet`.

Establish `hfin : μ (L : Set V) ≠ ⊤` using `hLc.measure_lt_top.ne`. Establish `hpos : μ (L : Set V) ≠ 0` using `(hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne'`. Take `⟨Φ, hΦ⟩ : ∃ Φ : V → ℂ, Φ = (L : Set V).indicator 1` from `⟨_, rfl⟩`. Establish `hΦin : ∀ x ∈ L, Φ x = 1` using `fun x hx => by`. Rewrite using `[hΦ]`.

Conclude with `Set.indicator_of_mem (s := (L : Set V)) hx _`. Establish `hΦout : ∀ x, x ∉ L → Φ x = 0` using `fun x hx => by`. Rewrite using `[hΦ]`. Conclude with `Set.indicator_of_notMem (s := (L : Set V)) hx _`. Establish `hΦc : Continuous Φ`.

Rewrite using `[hΦ]`. Conclude with `continuous_one.indicator (by`. Introduce `a ha`. Rewrite `ha` using `[(IsClopen.frontier_eq ⟨hLcl, hLo⟩)]`. Conclude with `absurd ha (Set.notMem_empty a))`.

Establish `hΦs : HasCompactSupport Φ`. Use `HasCompactSupport.intro hLc ?_` and prove the remaining obligations. Introduce `x hx`. Conclude with `hΦout x hx`. Take `⟨m, hm⟩ : ∃ m : ℝ, m = μ.real (L : Set V)` from `⟨_, rfl⟩`.

Establish `hI : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => (m : ℂ)) y`. Introduce `y`. Distinguish the cases in `hy : y ∈ L`. Establish `h1 : (fun x => Φ x * χ x y) = Φ`. Use function extensionality and compare the values at `x`.

Distinguish the cases in `hx : x ∈ L`. Rewrite using `[(hann y).2 hy x hx, mul_one]`. Rewrite using `[hΦout x hx, zero_mul]`. Rewrite using `[h1, Set.indicator_of_mem (s := (L : Set V)) hy, hΦ, integral_indicator hLm]`. Simplify using `[hm]`.

Rewrite using `[Set.indicator_of_notMem (s := (L : Set V)) hy]`. Establish `h2` using `(hann y).not.2 hy`. Use `push_neg at h2`. Take `⟨x0, hx0, hne⟩` from `h2`. Establish `h3 : ∫ x, Φ x * χ x y ∂μ = χ x0 y * ∫ x, Φ x * χ x y ∂μ`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `x`. Establish `: Φ (x0 + x) = Φ x`. Distinguish the cases in `hx : x ∈ L`.

Rewrite using `[hΦin _ (L.add_mem hx0 hx), hΦin _ hx]`. Rewrite using `[hΦout _ (fun h => hx ((L.add_mem_cancel_left hx0).1 h)), hΦout _ hx]`. Simplify using `only [this, hadd]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = χ x0 y * ∫ x, Φ x * χ x y ∂μ := integral_const_mul _ _`.

Establish `h4 : (1 - χ x0 y) * ∫ x, Φ x * χ x y ∂μ = 0`. Rewrite using `[sub_mul, one_mul, ← h3, sub_self]`. Conclude with `(mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (Ne.symm hne))`. Establish `hInt : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ`. Rewrite using `[funext hI]`.

Conclude with `(integrable_indicator_iff hLm).2 (integrableOn_const hfin)`. Establish `h0` using `hinv Φ hΦc hΦs hInt 0`. Establish `hout : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) = (L : Set V).indicator (fun _ => (m : ℂ))`. Use function extensionality and compare the values at `y`. Rewrite using `[hI]`.

Distinguish the cases in `hy : y ∈ L`. Rewrite using `[(hann 0).2 L.zero_mem y hy, mul_one]`. Rewrite using `[Set.indicator_of_notMem (s := (L : Set V)) hy, zero_mul]`. Rewrite `h0` using `[hout, integral_indicator hLm, neg_zero, hΦin 0 L.zero_mem]`. Establish `h5 : (m : ℂ) * m = 1`.

Use `h0` as an intermediate fact. Simplify using `only [setIntegral_const, ← hm, Complex.real_smul] at this`. Conclude with `this`. Establish `h6 : m * m = 1` using `by exact_mod_cast h5`. Establish `hm0 : 0 ≤ m` using `by rw [hm]; exact measureReal_nonneg`.

Establish `h7 : m = 1` using `by nlinarith`. Rewrite `h7` using `[hm, measureReal_def, ENNReal.toReal_eq_one_iff]`. Conclude with `h7`.
-/
theorem selfDualVol : PositivityTheory.SiegelWeilFormula.Gunr.SelfDualVol := by
  intro V _ _ _ _ _ μ χ hsd L hLo hLc hadd _ hann
  obtain ⟨hH, hinv⟩ := hsd
  haveI := hH
  have hLcl : IsClosed (L : Set V) := AddSubgroup.isClosed_of_isOpen L hLo
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet
  have hfin : μ (L : Set V) ≠ ⊤ := hLc.measure_lt_top.ne
  have hpos : μ (L : Set V) ≠ 0 := (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne'
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : V → ℂ, Φ = (L : Set V).indicator 1 := ⟨_, rfl⟩
  have hΦin : ∀ x ∈ L, Φ x = 1 := fun x hx => by
    rw [hΦ]; exact Set.indicator_of_mem (s := (L : Set V)) hx _
  have hΦout : ∀ x, x ∉ L → Φ x = 0 := fun x hx => by
    rw [hΦ]; exact Set.indicator_of_notMem (s := (L : Set V)) hx _
  have hΦc : Continuous Φ := by
    rw [hΦ]
    exact continuous_one.indicator (by
      intro a ha
      rw [(IsClopen.frontier_eq ⟨hLcl, hLo⟩)] at ha
      exact absurd ha (Set.notMem_empty a))
  have hΦs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro hLc ?_
    intro x hx
    exact hΦout x hx
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = μ.real (L : Set V) := ⟨_, rfl⟩
  have hI : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => (m : ℂ)) y := by
    intro y
    by_cases hy : y ∈ L
    · have h1 : (fun x => Φ x * χ x y) = Φ := by
        funext x
        by_cases hx : x ∈ L
        · rw [(hann y).2 hy x hx, mul_one]
        · rw [hΦout x hx, zero_mul]
      rw [h1, Set.indicator_of_mem (s := (L : Set V)) hy, hΦ, integral_indicator hLm]
      simp [hm]
    · rw [Set.indicator_of_notMem (s := (L : Set V)) hy]
      have h2 := (hann y).not.2 hy
      push_neg at h2
      obtain ⟨x0, hx0, hne⟩ := h2
      have h3 : ∫ x, Φ x * χ x y ∂μ = χ x0 y * ∫ x, Φ x * χ x y ∂μ := by
        calc ∫ x, Φ x * χ x y ∂μ = ∫ x, (fun x => Φ x * χ x y) (x0 + x) ∂μ :=
              (integral_add_left_eq_self _ x0).symm
          _ = ∫ x, χ x0 y * (Φ x * χ x y) ∂μ := by
              congr 1
              funext x
              have : Φ (x0 + x) = Φ x := by
                by_cases hx : x ∈ L
                · rw [hΦin _ (L.add_mem hx0 hx), hΦin _ hx]
                · rw [hΦout _ (fun h => hx ((L.add_mem_cancel_left hx0).1 h)), hΦout _ hx]
              simp only [this, hadd]
              ring
          _ = χ x0 y * ∫ x, Φ x * χ x y ∂μ := integral_const_mul _ _
      have h4 : (1 - χ x0 y) * ∫ x, Φ x * χ x y ∂μ = 0 := by
        rw [sub_mul, one_mul, ← h3, sub_self]
      exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  have hInt : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    rw [funext hI]
    exact (integrable_indicator_iff hLm).2 (integrableOn_const hfin)
  have h0 := hinv Φ hΦc hΦs hInt 0
  have hout : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) = (L : Set V).indicator (fun _ => (m : ℂ)) := by
    funext y
    rw [hI]
    by_cases hy : y ∈ L
    · rw [(hann 0).2 L.zero_mem y hy, mul_one]
    · rw [Set.indicator_of_notMem (s := (L : Set V)) hy, zero_mul]
  rw [hout, integral_indicator hLm, neg_zero, hΦin 0 L.zero_mem] at h0
  have h5 : (m : ℂ) * m = 1 := by
    have := h0
    simp only [setIntegral_const, ← hm, Complex.real_smul] at this
    exact this
  have h6 : m * m = 1 := by exact_mod_cast h5
  have hm0 : 0 ≤ m := by rw [hm]; exact measureReal_nonneg
  have h7 : m = 1 := by nlinarith
  rw [hm, measureReal_def, ENNReal.toReal_eq_one_iff] at h7
  exact h7

end GlobalTheory.CompanionTheory.GunrVol
