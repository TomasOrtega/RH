import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ _ z hz hroot J J' hsum`. Establish `hlt : ∀ a b : ℤ, a < b → z ^ a ≠ z ^ b`. Introduce `a b hab heq`. Establish `h1 : z ^ (b - a) = 1`. Rewrite using `[zpow_sub₀ hz, heq, div_self (zpow_ne_zero _ hz)]`.

Establish `h2 : ((b - a).toNat : ℤ) = b - a` using `Int.toNat_of_nonneg (by omega)`. Rewrite `h1` using `[← h2, zpow_natCast]`. Conclude with `hroot _ (by omega) h1`. Establish `hinj : Function.Injective (fun h : ℤ => z ^ h)`. Introduce `a b hab`.

Simplify using `only at hab`. Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Conclude with `hlt a b h hab`. Conclude with `hlt b a h hab.symm`.

Set `χ : ℤ → (Multiplicative ℕ →* k)` to `fun h => powersHom k (z ^ h)`. Establish `hχ : Function.Injective χ` using `(powersHom k).injective.comp hinj`. Establish `hli` using `(linearIndependent_monoidHom (Multiplicative ℕ) k).comp χ hχ`. Rewrite `hli` using `[linearIndependent_iff']`. Establish `key : ∀ (M : Multiset ℤ) (s : Finset ℤ), M.toFinset ⊆ s → ∀ f : ℤ → k, (M.map f).sum = ∑ h ∈ s, (M.count h : k) * f h`.

Introduce `M s hs f`. Rewrite using `[Finset.sum_multiset_map_count]`. Repeatedly rewrite using `[nsmul_eq_mul]`. Apply `Finset.sum_subset hs` to reduce the goal to its premises. Introduce `x _ hx`.

Rewrite `hx` using `[Multiset.mem_toFinset]`. Simplify using `[Multiset.count_eq_zero.mpr hx]`. Use `set s : Finset ℤ := (J + J').toFinset with hs`. Establish `hJ : J.toFinset ⊆ s`. Introduce `x hx`.

Rewrite `hx` using `[Multiset.mem_toFinset]`. Rewrite using `[hs, Multiset.mem_toFinset]`. Conclude with `Multiset.mem_add.mpr (Or.inl hx)`. Establish `hJ' : J'.toFinset ⊆ s`. Introduce `x hx`.

Rewrite `hx` using `[Multiset.mem_toFinset]`. Rewrite using `[hs, Multiset.mem_toFinset]`. Conclude with `Multiset.mem_add.mpr (Or.inr hx)`. Establish `hzero` using `hli s (fun h => (J.count h : k) - (J'.count h : k)) (by`. Use function extensionality and compare the values at `m`.

Establish `e` using `hsum (Multiplicative.toAdd m)`. Rewrite `e` using `[key J s hJ, key J' s hJ']`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]`. Simplify using `only [χ, powersHom_apply, sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[sub_eq_zero]`.

Conclude with `e)`. Use `Multiset.ext.mpr (fun a => ?_)` and prove the remaining obligations. Distinguish the cases in `ha : a ∈ s`. Use `hzero a ha` as an intermediate fact. Rewrite `this` using `[sub_eq_zero]`.

Conclude with `this` after adjusting the coercions. Rewrite `ha` using `[hs, Multiset.mem_toFinset, Multiset.mem_add, not_or]`. Rewrite using `[Multiset.count_eq_zero.mpr ha.1, Multiset.count_eq_zero.mpr ha.2]`.
-/
theorem multiset_eq_of_powerSums_zpow_eq : ∀ (k : Type) [Field k] [CharZero k] (z : k), z ≠ 0 →
    (∀ i : ℕ, 1 ≤ i → z ^ i ≠ 1) → ∀ J J' : Multiset ℤ,
    (∀ n : ℕ, (J.map fun h => (z ^ h) ^ n).sum = (J'.map fun h => (z ^ h) ^ n).sum) → J = J' := by
  intro k _ _ z hz hroot J J' hsum

  have hlt : ∀ a b : ℤ, a < b → z ^ a ≠ z ^ b := by
    intro a b hab heq
    have h1 : z ^ (b - a) = 1 := by
      rw [zpow_sub₀ hz, heq, div_self (zpow_ne_zero _ hz)]
    have h2 : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
    rw [← h2, zpow_natCast] at h1
    exact hroot _ (by omega) h1
  have hinj : Function.Injective (fun h : ℤ => z ^ h) := by
    intro a b hab
    simp only at hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt a b h hab
    · exact hlt b a h hab.symm

  let χ : ℤ → (Multiplicative ℕ →* k) := fun h => powersHom k (z ^ h)
  have hχ : Function.Injective χ := (powersHom k).injective.comp hinj
  have hli := (linearIndependent_monoidHom (Multiplicative ℕ) k).comp χ hχ
  rw [linearIndependent_iff'] at hli

  have key : ∀ (M : Multiset ℤ) (s : Finset ℤ), M.toFinset ⊆ s → ∀ f : ℤ → k,
      (M.map f).sum = ∑ h ∈ s, (M.count h : k) * f h := by
    intro M s hs f
    rw [Finset.sum_multiset_map_count]
    simp_rw [nsmul_eq_mul]
    apply Finset.sum_subset hs
    intro x _ hx
    rw [Multiset.mem_toFinset] at hx
    simp [Multiset.count_eq_zero.mpr hx]
  set s : Finset ℤ := (J + J').toFinset with hs
  have hJ : J.toFinset ⊆ s := by
    intro x hx; rw [Multiset.mem_toFinset] at hx; rw [hs, Multiset.mem_toFinset]
    exact Multiset.mem_add.mpr (Or.inl hx)
  have hJ' : J'.toFinset ⊆ s := by
    intro x hx; rw [Multiset.mem_toFinset] at hx; rw [hs, Multiset.mem_toFinset]
    exact Multiset.mem_add.mpr (Or.inr hx)
  have hzero := hli s (fun h => (J.count h : k) - (J'.count h : k)) (by
    funext m
    have e := hsum (Multiplicative.toAdd m)
    rw [key J s hJ, key J' s hJ'] at e
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    simp only [χ, powersHom_apply, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact e)
  refine Multiset.ext.mpr (fun a => ?_)
  by_cases ha : a ∈ s
  · have := hzero a ha
    rw [sub_eq_zero] at this
    exact_mod_cast this
  · rw [hs, Multiset.mem_toFinset, Multiset.mem_add, not_or] at ha
    rw [Multiset.count_eq_zero.mpr ha.1, Multiset.count_eq_zero.mpr ha.2]

end GlobalTheory
