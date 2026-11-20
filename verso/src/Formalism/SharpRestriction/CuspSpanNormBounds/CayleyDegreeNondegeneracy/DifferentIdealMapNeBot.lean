import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericDetOfFlagProductBound

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
open scoped nonZeroDivisors

/- English proof (translation)
Establish `hI0 : (I : FractionalIdeal R⁰ K) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr hI`. Establish `h1 : ((I : FractionalIdeal R⁰ K) ^ n) ≤ 1` using `pow_le_one' FractionalIdeal.coeIdeal_le_one n`. Establish `h2 : (1 : FractionalIdeal R⁰ K) ≤ ((I : FractionalIdeal R⁰ K) ^ n)⁻¹`. Establish `h3` using `FractionalIdeal.inv_anti_mono (pow_ne_zero n hI0) one_ne_zero h1`. Rewrite `h3` using `[inv_one]`. Then use the resulting hypothesis.

Rewrite using `[zpow_neg, zpow_natCast]`. Conclude with `h2 (FractionalIdeal.one_mem_one _)`.
-/
theorem one_mem_ideal_zpow_neg {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) (hI : I ≠ ⊥) (n : ℕ) : (1 : K) ∈ ((I : FractionalIdeal R⁰ K) ^ (-(n : ℤ))) := by
  have hI0 : (I : FractionalIdeal R⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hI
  have h1 : ((I : FractionalIdeal R⁰ K) ^ n) ≤ 1 := pow_le_one' FractionalIdeal.coeIdeal_le_one n
  have h2 : (1 : FractionalIdeal R⁰ K) ≤ ((I : FractionalIdeal R⁰ K) ^ n)⁻¹ := by
    have h3 := FractionalIdeal.inv_anti_mono (pow_ne_zero n hI0) one_ne_zero h1
    rwa [inv_one] at h3
  rw [zpow_neg, zpow_natCast]
  exact h2 (FractionalIdeal.one_mem_one _)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fr

variable (D : D7)

/- English proof (translation)
Rewrite using `[Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))]`. Conclude with `differentIdeal_ne_bot`.
-/
theorem different_ideal_map_ne_bot : (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :
    Ideal (𝓞 D.host.E)) ≠ ⊥ := by
  rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))]
  exact differentIdeal_ne_bot

/- English proof (translation)
Use `Submodule.subset_span ⟨a, 1, ?_, by simp⟩` and prove the remaining obligations. Establish `h : -((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = -(((D.R.rS - (a : ℕ) : ℕ)) : ℤ)`. Use `a.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[h]`.

Conclude with `one_mem_ideal_zpow_neg _ (different_ideal_map_ne_bot D) _`.
-/
theorem basis_vector_mem_span {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) : F0.e a ∈ XS D F0 := by
  refine Submodule.subset_span ⟨a, 1, ?_, by simp⟩
  have h : -((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = -(((D.R.rS - (a : ℕ) : ℕ)) : ℤ) := by
    have := a.2
    omega
  rw [h]
  exact one_mem_ideal_zpow_neg _ (different_ideal_map_ne_bot D) _

end Fr

end Formalism.MainNotions.BridgeLemma₂

end
