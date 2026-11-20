import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric

/- English proof (translation)
Introduce `ι _ m`. Unfold `rootDiscr`. Use `Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun j _ => Finset.prod_ne_zero_iff.mpr fun i hi => ?_` and prove the remaining obligations. Rewrite using `[sub_ne_zero]`. Introduce `h`.

Establish `h2` using `X_injective (σ := Root m) (R := ℝ) h`. Simplify using `only [Sigma.mk.injEq, heq_eq_eq, true_and] at h2`. Conclude with `(Finset.mem_Iio.mp hi).ne h2.symm`.
-/
theorem rootDiscr_ne_zero : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ), rootDiscr m ≠ 0 := by
  intro ι _ m
  unfold rootDiscr
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun j _ =>
    Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  rw [sub_ne_zero]
  intro h
  have h2 := X_injective (σ := Root m) (R := ℝ) h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h2
  exact (Finset.mem_Iio.mp hi).ne h2.symm

end GlobalTheory.GoodMetric
