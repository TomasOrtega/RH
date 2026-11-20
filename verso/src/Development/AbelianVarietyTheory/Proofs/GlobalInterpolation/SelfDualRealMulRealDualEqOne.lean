import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ _ _ _ _ μ χ hsd hadd h0 L L' hLc hLo hL'c hL'o hdual`. Take `⟨hH, hinv⟩` from `hsd`. Use `set Φ : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hΦ`. Establish `hclopen : IsClopen (L : Set V)` using `⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩`. Establish `hcont : Continuous Φ` using `hclopen.continuous_indicator continuous_const`.

Establish `hsupp : HasCompactSupport Φ` using `HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)`. Establish `htr : (fun y => ∫ x, Φ x * χ x y ∂μ) = (L' : Set V).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ))`. Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y ∈ L'`. Rewrite using `[Set.indicator_of_mem (show y ∈ (L' : Set V) from hy)]`.

Establish `: (fun x => Φ x * χ x y) = Φ`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ L`. Rewrite using `[(hdual y).1 hy x hx, mul_one]`. Simplify using `[hΦ, Set.indicator_of_notMem (show x ∉ (L : Set V) from hx)]`.

Rewrite using `[this, hΦ, integral_indicator_const _ hLo.measurableSet]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem (show y ∉ (L' : Set V) from hy)]`. Establish `hy'` using `mt (hdual y).2 hy`. Use `push Not at hy'`.

Take `⟨x0, hx0, hne⟩` from `hy'`. Establish `h1` using `integral_add_left_eq_self (μ := μ) (fun x => Φ x * χ x y) x0`. Establish `h2 : (fun x => Φ (x0 + x) * χ (x0 + x) y) = fun x => χ x0 y * (Φ x * χ x y)`. Use function extensionality and compare the values at `x`. Establish `: Φ (x0 + x) = Φ x`.

Distinguish the cases in `hx : x ∈ L`. Simplify using `[hΦ, Set.indicator_of_mem (show x ∈ (L : Set V) from hx), Set.indicator_of_mem (show x0 + x ∈ (L : Set V) from L.add_mem hx0 hx)]`. Establish `hx' : x0 + x ∉ L` using `fun h => hx ((L.add_mem_cancel_left hx0).1 h)`. Simplify using `[hΦ, Set.indicator_of_notMem (show x ∉ (L : Set V) from hx), Set.indicator_of_notMem (show x0 + x ∉ (L : Set V) from hx')]`. Rewrite using `[this, hadd]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[h2, integral_const_mul]`. Establish `h3 : (χ x0 y - 1) * ∫ x, Φ x * χ x y ∂μ = 0` using `by rw [sub_mul, h1]; ring`. Conclude with `(mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)`. Establish `hint : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ`.

Rewrite using `[htr, integrable_indicator_iff hL'o.measurableSet]`. Conclude with `integrableOn_const hL'c.measure_lt_top.ne`. Establish `key` using `hinv Φ hcont hsupp hint 0`. Simplify using `only [h0, mul_one, neg_zero] at key`. Rewrite `key` using `[htr, integral_indicator_const _ hL'o.measurableSet, hΦ, Set.indicator_of_mem (show (0 : V) ∈ (L : Set V) from L.zero_mem)]`.

Rewrite `key` using `[Complex.real_smul, mul_comm]`. Conclude with `key` after adjusting the coercions.
-/
theorem selfDual_real_mul_real_dual_eq_one :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (χ : V → V → ℂ), SelfDual μ χ → (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → (∀ y, χ y 0 = 1) → ∀ L L' : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → IsCompact (L' : Set V) → IsOpen (L' : Set V) → (∀ y, y ∈ L' ↔ ∀ x ∈ L, χ x y = 1) → μ.real (L : Set V) * μ.real (L' : Set V) = 1 := by
  intro V _ _ _ _ _ μ χ hsd hadd h0 L L' hLc hLo hL'c hL'o hdual
  obtain ⟨hH, hinv⟩ := hsd
  set Φ : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hΦ
  have hclopen : IsClopen (L : Set V) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  have hcont : Continuous Φ := hclopen.continuous_indicator continuous_const
  have hsupp : HasCompactSupport Φ :=
    HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  have htr : (fun y => ∫ x, Φ x * χ x y ∂μ)
      = (L' : Set V).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) := by
    funext y
    by_cases hy : y ∈ L'
    · rw [Set.indicator_of_mem (show y ∈ (L' : Set V) from hy)]
      have : (fun x => Φ x * χ x y) = Φ := by
        funext x
        by_cases hx : x ∈ L
        · rw [(hdual y).1 hy x hx, mul_one]
        · simp [hΦ, Set.indicator_of_notMem (show x ∉ (L : Set V) from hx)]
      rw [this, hΦ, integral_indicator_const _ hLo.measurableSet]
      simp
    · rw [Set.indicator_of_notMem (show y ∉ (L' : Set V) from hy)]
      have hy' := mt (hdual y).2 hy
      push Not at hy'
      obtain ⟨x0, hx0, hne⟩ := hy'
      have h1 := integral_add_left_eq_self (μ := μ) (fun x => Φ x * χ x y) x0
      have h2 : (fun x => Φ (x0 + x) * χ (x0 + x) y) = fun x => χ x0 y * (Φ x * χ x y) := by
        funext x
        have : Φ (x0 + x) = Φ x := by
          by_cases hx : x ∈ L
          · simp [hΦ, Set.indicator_of_mem (show x ∈ (L : Set V) from hx),
              Set.indicator_of_mem (show x0 + x ∈ (L : Set V) from L.add_mem hx0 hx)]
          · have hx' : x0 + x ∉ L := fun h => hx ((L.add_mem_cancel_left hx0).1 h)
            simp [hΦ, Set.indicator_of_notMem (show x ∉ (L : Set V) from hx),
              Set.indicator_of_notMem (show x0 + x ∉ (L : Set V) from hx')]
        rw [this, hadd]; ring
      rw [h2, integral_const_mul] at h1
      have h3 : (χ x0 y - 1) * ∫ x, Φ x * χ x y ∂μ = 0 := by rw [sub_mul, h1]; ring
      exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)
  have hint : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    rw [htr, integrable_indicator_iff hL'o.measurableSet]
    exact integrableOn_const hL'c.measure_lt_top.ne
  have key := hinv Φ hcont hsupp hint 0
  simp only [h0, mul_one, neg_zero] at key
  rw [htr, integral_indicator_const _ hL'o.measurableSet, hΦ,
    Set.indicator_of_mem (show (0 : V) ∈ (L : Set V) from L.zero_mem)] at key
  rw [Complex.real_smul, mul_comm] at key
  exact_mod_cast key

end GlobalTheory
