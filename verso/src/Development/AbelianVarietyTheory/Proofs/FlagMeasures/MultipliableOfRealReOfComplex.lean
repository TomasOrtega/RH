import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory

/- English proof (translation)
Take `⟨a, ha⟩` from `hc`. Establish `hc' : ∀ i, c i = ((c i).re : ℂ)` using `fun i => Complex.ext (by simp) (by simp [(hcr i).1])`. Establish `hre : HasProd (fun i => (c i).re) a.re`. Establish `h` using `(Complex.continuous_re.tendsto a).comp ha`. Use `h.congr ?_` and prove the remaining obligations.

Introduce `s`. Simplify using `only [Function.comp]`. Rewrite using `[Finset.prod_congr rfl (fun i _ => hc' i), ← Complex.ofReal_prod, Complex.ofReal_re]`. Establish `h2 : HasProd (fun i => ENNReal.ofReal (c i).re) (ENNReal.ofReal a.re)`. Establish `h` using `(ENNReal.continuous_ofReal.tendsto a.re).comp hre`.

Use `h.congr ?_` and prove the remaining obligations. Introduce `s`. Simplify using `only [Function.comp]`. Rewrite using `[ENNReal.ofReal_prod_of_nonneg (fun i _ => (hcr i).2)]`. Conclude with `⟨h2.multipliable, by rw [h2.tprod_eq, ha.tprod_eq]⟩`.
-/
theorem multipliable_ofReal_re_of_complex (ι : Type) (c : ι → ℂ) (hc : Multipliable c)
    (hcr : ∀ i, (c i).im = 0 ∧ 0 ≤ (c i).re) :
    Multipliable (fun i => ENNReal.ofReal (c i).re) ∧
      ∏' i, ENNReal.ofReal (c i).re = ENNReal.ofReal (∏' i, c i).re := by
  obtain ⟨a, ha⟩ := hc
  have hc' : ∀ i, c i = ((c i).re : ℂ) := fun i => Complex.ext (by simp) (by simp [(hcr i).1])
  have hre : HasProd (fun i => (c i).re) a.re := by
    have h := (Complex.continuous_re.tendsto a).comp ha
    refine h.congr ?_
    intro s
    simp only [Function.comp]
    rw [Finset.prod_congr rfl (fun i _ => hc' i), ← Complex.ofReal_prod, Complex.ofReal_re]
  have h2 : HasProd (fun i => ENNReal.ofReal (c i).re) (ENNReal.ofReal a.re) := by
    have h := (ENNReal.continuous_ofReal.tendsto a.re).comp hre
    refine h.congr ?_
    intro s
    simp only [Function.comp]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (hcr i).2)]
  exact ⟨h2.multipliable, by rw [h2.tprod_eq, ha.tprod_eq]⟩

/- English proof (translation)
The claim follows from `multipliable_ofReal_re_of_complex`.
-/
theorem multipliable_ofReal_re_of_complex' : ∀ (ι : Type) (c : ι → ℂ), Multipliable c → (∀ i, (c i).im = 0 ∧ 0 ≤ (c i).re) → Multipliable (fun i => ENNReal.ofReal (c i).re) ∧ ∏' i, ENNReal.ofReal (c i).re = ENNReal.ofReal (∏' i, c i).re :=
  multipliable_ofReal_re_of_complex

end GlobalTheory
