import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Unfold `d`. Use `split_ifs with h`. Use `set e := Classical.choose h`. Establish `he` using `Classical.choose_spec h`. Establish `hzx : z x = e x` using `he.1 he.2`.

Establish `ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x)`. Establish `hc` using `e.continuousAt_symm (e.map_source he.2)`. Rewrite `hc` using `[ContinuousAt, e.left_inv he.2]`. Conclude with `hc`. Establish `hg : (f ∘ e.symm) =ᶠ[𝓝 (e x)] fun _ => (0 : ℂ)` using `(ht.eventually hf).mono fun y hy => by simpa using hy`.

Rewrite using `[hzx]`. Unfold `wd`. Rewrite using `[hg.fderiv_eq]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
private lemma d_apply_eq_zero_of_eventuallyEq_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M) (hf : f =ᶠ[𝓝 x] 0) : d n z j f x = 0 := by
  unfold d
  split_ifs with h
  · set e := Classical.choose h
    have he := Classical.choose_spec h
    have hzx : z x = e x := he.1 he.2
    have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      have hc := e.continuousAt_symm (e.map_source he.2)
      rw [ContinuousAt, e.left_inv he.2] at hc
      exact hc
    have hg : (f ∘ e.symm) =ᶠ[𝓝 (e x)] fun _ => (0 : ℂ) :=
      (ht.eventually hf).mono fun y hy => by simpa using hy
    rw [hzx]
    unfold wd
    rw [hg.fderiv_eq]
    simp
  · rfl

/- English proof (translation)
Introduce `z _ ph ph' ψ U f _ _ hsupp hph`. Establish `hfz : ∀ x, x ∉ U → f x = 0`. Introduce `x hx`. Assume the negation of the conclusion as `h`. Conclude with `hx (hsupp (subset_tsupport _ h))`.

Establish `hfun : ∀ j, (fun y => (Real.exp (-(w2 ph' ψ y)) : ℂ) * f y j) = fun y => (Real.exp (-ph y) : ℂ) * f y j`. Introduce `j`. Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y ∈ U`. Simplify using `[w2, (hph y hy).1, (hph y hy).2]`.

Simplify using `[hfz y hy]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `v`. Unfold `ipV`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ U`. Simplify using `[w2, (hph x hx).1, (hph x hx).2]`. Simplify using `[hfz x hx]`. Unfold `wint`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [tstar]`. Repeatedly rewrite using `[hfun]`. Distinguish the cases in `hx : x ∈ U`.

Establish `h1 : w1 ph' ψ x = ph x` using `by simp [w1, (hph x hx).1, (hph x hx).2]`. Rewrite using `[h1]`. Establish `hx' : x ∉ tsupport f` using `fun h => hx (hsupp h)`. Establish `hev : f =ᶠ[𝓝 x] 0` using `notMem_tsupport_iff_eventuallyEq.1 hx'`. Establish `hS : ∀ j, d n z j (fun y => (Real.exp (-ph y) : ℂ) * f y j) x = 0` using `fun j => d_apply_eq_zero_of_eventuallyEq_zero n z j _ x (hev.mono fun y hy => by simp [hy])`.

Rewrite using `[Finset.sum_eq_zero (fun j _ => hS j)]`. Simplify using the standard rewrite rules.
-/
theorem locality (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : LocalityStatement n M := by
  intro z _ ph ph' ψ U f _ _ hsupp hph
  have hfz : ∀ x, x ∉ U → f x = 0 := by
    intro x hx
    by_contra h
    exact hx (hsupp (subset_tsupport _ h))
  have hfun : ∀ j, (fun y => (Real.exp (-(w2 ph' ψ y)) : ℂ) * f y j) =
      fun y => (Real.exp (-ph y) : ℂ) * f y j := by
    intro j
    funext y
    by_cases hy : y ∈ U
    · simp [w2, (hph y hy).1, (hph y hy).2]
    · simp [hfz y hy]
  refine ⟨?_, ?_⟩
  · intro v
    unfold ipV
    congr 1
    funext x
    by_cases hx : x ∈ U
    · simp [w2, (hph x hx).1, (hph x hx).2]
    · simp [hfz x hx]
  · unfold wint
    congr 1
    funext x
    simp only [tstar]
    simp_rw [hfun]
    by_cases hx : x ∈ U
    · have h1 : w1 ph' ψ x = ph x := by simp [w1, (hph x hx).1, (hph x hx).2]
      rw [h1]
    · have hx' : x ∉ tsupport f := fun h => hx (hsupp h)
      have hev : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx'
      have hS : ∀ j, d n z j (fun y => (Real.exp (-ph y) : ℂ) * f y j) x = 0 := fun j =>
        d_apply_eq_zero_of_eventuallyEq_zero n z j _ x (hev.mono fun y hy => by simp [hy])
      rw [Finset.sum_eq_zero (fun j _ => hS j)]
      simp

end

end ReciprocityTheory.L2DbarEstimates.F
