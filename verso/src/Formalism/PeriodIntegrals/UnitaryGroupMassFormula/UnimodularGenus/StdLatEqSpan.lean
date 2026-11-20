import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.Development

open NumberField

noncomputable section

namespace PI.UG.W

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hStd_apply (E : Type) [Field E] [StarRing E] (n : ℕ) (x y : Sp E n) :
    hStd E n x y = ∑ i, star (x i) * y i := rfl

/- English proof (translation)
Use `LinearMap.isSymm_def.mpr fun x y => ?_` and prove the remaining obligations. Rewrite using `[hStd_apply, hStd_apply, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[starRingEnd_apply, star_mul, star_star, mul_comm]`.
-/
theorem hStd_isSymm (E : Type) [Field E] [StarRing E] (n : ℕ) : (hStd E n).IsSymm := by
  refine LinearMap.isSymm_def.mpr fun x y => ?_
  rw [hStd_apply, hStd_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starRingEnd_apply, star_mul, star_star, mul_comm]

/- English proof (translation)
Conclude with `⟨⟨star (algebraMap (𝓞 E) E r), (RingOfIntegers.isIntegral_coe r).map (starRingEnd E).toIntAlgHom⟩, rfl⟩`.
-/
theorem star_mem_range (E : Type) [Field E] [NumberField E] [StarRing E] (r : 𝓞 E) :
    star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := by
  exact ⟨⟨star (algebraMap (𝓞 E) E r), (RingOfIntegers.isIntegral_coe r).map (starRingEnd E).toIntAlgHom⟩, rfl⟩

def eStd (E : Type) [Field E] (n : ℕ) (i : Fin n) : Sp E n := Pi.single i 1

/- English proof (translation)
Rewrite using `[hStd_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Finset.sum_eq_single i (fun k _ hk => by simp [eStd, hk]) (by simp)]`. Simplify using `[eStd]`.

Rewrite using `[if_neg h]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[eStd, Ne.symm h]`.

Simplify using `[eStd, Pi.single_apply, hk]`.
-/
theorem hStd_eStd (E : Type) [Field E] [StarRing E] (n : ℕ) (i j : Fin n) :
    hStd E n (eStd E n i) (eStd E n j) = if i = j then 1 else 0 := by
  rw [hStd_apply]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [eStd, hk]) (by simp)]
    simp [eStd]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · subst hk
      simp [eStd, Ne.symm h]
    · simp [eStd, Pi.single_apply, hk]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `h' : ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = x i` using `fun i => Submodule.mem_one.mp ((Submodule.mem_pi.mp hx) i (Set.mem_univ i))`. Use `choose a ha using h'`. Establish `hx' : x = ∑ i, a i • eStd E n i`.

Use extensionality with `k`. Simplify using `[eStd, Pi.single_apply, Finset.sum_apply, ← ha, Algebra.smul_def]`. Rewrite using `[hx']`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Use `Submodule.mem_pi.mpr fun k _ => Submodule.mem_one.mpr ?_` and prove the remaining obligations. Distinguish the cases in `h : k = i`. Substitute `h` using the available equality. Conclude with `⟨1, by simp [eStd]⟩`.

Conclude with `⟨0, by simp [eStd, h]⟩`.
-/
theorem stdLat_eq_span (E : Type) [Field E] [NumberField E] (n : ℕ) :
    stdLat E n = Submodule.span (𝓞 E) (Set.range (eStd E n)) := by
  apply le_antisymm
  · intro x hx
    have h' : ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = x i := fun i =>
      Submodule.mem_one.mp ((Submodule.mem_pi.mp hx) i (Set.mem_univ i))
    choose a ha using h'
    have hx' : x = ∑ i, a i • eStd E n i := by
      ext k
      simp [eStd, Pi.single_apply, Finset.sum_apply, ← ha, Algebra.smul_def]
    rw [hx']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.mem_pi.mpr fun k _ => Submodule.mem_one.mpr ?_
    by_cases h : k = i
    · subst h
      exact ⟨1, by simp [eStd]⟩
    · exact ⟨0, by simp [eStd, h]⟩

end PI.UG.W
