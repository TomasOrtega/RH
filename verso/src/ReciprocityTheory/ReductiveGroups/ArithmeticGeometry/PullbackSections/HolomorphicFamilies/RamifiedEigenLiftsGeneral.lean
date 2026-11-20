import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamHelp

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB Pf.ERam

/- English proof (translation)
Use `set ω := RingOfIntegers.basis E`. Use `set bq := integralBasis E`. Establish `hbqω : ∀ i, bq i = algebraMap (𝓞 E) E (ω i)` using `fun i => integralBasis_apply E i`. Establish `h` using `_root_.dual_difference E _ bq (fun i => by rw [hbqω]; exact RingOfIntegers.isIntegral_coe _) (fun x => by`. Use `⟨fun i => ω.repr x i, ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrArg (algebraMap (𝓞 E) E) (ω.sum_repr x)`. Rewrite `h1` using `[map_sum]`. Use `show algebraMap (𝓞 E) E x = _`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hbqω, map_zsmul, Int.cast_smul_eq_zsmul]) _ hδ`. Introduce `i`. Conclude with `h _`.
-/
theorem dual_int {E : Type} [Field E] [NumberField E] (δ : 𝓞 E) (hδ : δ ∈ differentIdeal ℤ (𝓞 E)) :
    ∀ i : Fin (nI E), IsIntegral ℤ ((δ : E) * omDF (E := E) i) := by
  set ω := RingOfIntegers.basis E
  set bq := integralBasis E
  have hbqω : ∀ i, bq i = algebraMap (𝓞 E) E (ω i) := fun i => integralBasis_apply E i
  have h := _root_.dual_difference E _ bq (fun i => by rw [hbqω]; exact RingOfIntegers.isIntegral_coe _) (fun x => by
      refine ⟨fun i => ω.repr x i, ?_⟩
      have h1 := congrArg (algebraMap (𝓞 E) E) (ω.sum_repr x)
      rw [map_sum] at h1
      show algebraMap (𝓞 E) E x = _
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbqω, map_zsmul, Int.cast_smul_eq_zsmul]) _ hδ
  intro i
  exact h _

end ReciprocityTheory.ChartRestriction.G.PullbackSections
