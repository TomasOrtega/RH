import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsProdXSubCOfMonic

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on generalizing n with`. Consider the case `empty => simpa using continuous_const`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.prod_insert ha, coeff_mul]`. Use `continuous_finset_sum _ fun p _ => Continuous.mul ?_ (ih _)` and prove the remaining obligations.

Simplify using `only [coeff_sub, coeff_C]`. Use `continuous_const.sub ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `continuous_apply a`. Conclude with `continuous_const`.
-/
theorem continuous_coeff_prod_X_sub_C {ι : Type} (s : Finset ι) (n : ℕ) :
    Continuous fun r : ι → ℂ => (∏ j ∈ s, (X - C (r j))).coeff n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, coeff_mul]
    refine continuous_finset_sum _ fun p _ => Continuous.mul ?_ (ih _)
    simp only [coeff_sub, coeff_C]
    refine continuous_const.sub ?_
    split_ifs
    · exact continuous_apply a
    · exact continuous_const

/- English proof (translation)
Establish `hm : (∏ j, (X - C (r j)) : ℂ[X]).Monic` using `monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _`. Establish `hd : (∏ j, (X - C (r j)) : ℂ[X]).natDegree = δ`. Rewrite using `[natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]`. Simplify using the standard rewrite rules. Use `hm.as_sum` as an intermediate fact.

Rewrite `this` using `[hd, Finset.sum_range]`. Conclude with `this`.
-/
theorem prod_X_sub_C_eq_X_pow_add_sum {δ : ℕ} (r : Fin δ → ℂ) :
    ∏ j, (X - C (r j)) =
      X ^ δ + ∑ i : Fin δ, C ((∏ j, (X - C (r j))).coeff i) * X ^ (i : ℕ) := by
  have hm : (∏ j, (X - C (r j)) : ℂ[X]).Monic :=
    monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
  have hd : (∏ j, (X - C (r j)) : ℂ[X]).natDegree = δ := by
    rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    simp
  have := hm.as_sum
  rw [hd, Finset.sum_range] at this
  exact this

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.MonicRootsProduct.exists_roots`. Consider the case `exact _root_.GlobalTheory.MonicRootsProduct.exists_roots`. Consider the case `(apply _root_.GlobalTheory.MonicRootsProduct.exists_roots <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.MonicRootsProduct.exists_roots <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.MonicRootsProduct.exists_roots <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.MonicRootsProduct.exists_roots ..)`.
-/
theorem exists_prod_X_sub_C_eq {δ : ℕ} (c : Fin δ → ℂ) :
    ∃ r : Fin δ → ℂ,
      ∏ j, (X - C (r j)) = X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
  first
  | exact @_root_.GlobalTheory.MonicRootsProduct.exists_roots
  | exact _root_.GlobalTheory.MonicRootsProduct.exists_roots
  | (apply _root_.GlobalTheory.MonicRootsProduct.exists_roots <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonicRootsProduct.exists_roots <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonicRootsProduct.exists_roots <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonicRootsProduct.exists_roots ..)

/- English proof (translation)
Introduce `δ`. Set `e : ℂ ≃ᵐ ℝ` to `PolishSpace.measurableEquivOfNotCountable (fun _ => not_countable_iff.mpr (inferInstance : Uncountable ℝ) Complex.ofReal_injective.countable) (not_countable_iff.mpr inferInstance)`. Set `S : Set (Fin δ → ℂ)` to `{r | Monotone (e ∘ r)}`. Establish `hS : MeasurableSet S`. Establish `: S = ⋂ i, ⋂ j, ⋂ _ : i ≤ j, {r : Fin δ → ℂ | e (r i) ≤ e (r j)}`.

Use extensionality with `r`. Simplify using `only [S, Set.mem_setOf_eq, Set.mem_iInter, Monotone, Function.comp]`. Rewrite using `[this]`. Use `MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => measurableSet_le ?_ ?_` and prove the remaining obligations. Conclude with `e.measurable.comp (measurable_pi_apply i)`.

Conclude with `e.measurable.comp (measurable_pi_apply j)`. Set `V : (Fin δ → ℂ) → (Fin δ → ℂ)` to `fun r i => (∏ j, (X - C (r j))).coeff i`. Establish `hV : Measurable V` using `(continuous_pi fun i => continuous_coeff_prod_X_sub_C _ _).measurable`. Use `haveI : StandardBorelSpace S := hS.standardBorel`. Establish `hinj : Function.Injective fun x : S => V x`.

Introduce and unpack `⟨r, hr⟩ ⟨s, hs⟩ h`. Establish `h1 : (∏ j, (X - C (r j)) : ℂ[X]) = ∏ j, (X - C (s j))`. Use `(prod_X_sub_C_eq_X_pow_add_sum r).trans (Eq.trans ?_ (prod_X_sub_C_eq_X_pow_add_sum s).symm)` and prove the remaining obligations. Use `congrArg (X ^ δ + ·) (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun a => C a * X ^ (i : ℕ)) (congrFun h i)`.

Establish `h2 : Finset.univ.val.map r = Finset.univ.val.map s`. Rewrite using `[← roots_multiset_prod_X_sub_C (Finset.univ.val.map r), ← roots_multiset_prod_X_sub_C (Finset.univ.val.map s), Multiset.map_map, Multiset.map_map]`. Conclude with `congrArg roots h1`. Establish `h3 : Finset.univ.val.map (e ∘ r) = Finset.univ.val.map (e ∘ s)`. Rewrite using `[← Multiset.map_map, ← Multiset.map_map, h2]`.

Rewrite `h3` using `[Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe]`. Establish `h4` using `List.ofFn_injective (h3.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr hr) (List.sortedLE_ofFn_iff.mpr hs))`. Use extensionality with `i`. Conclude with `e.injective (congrFun h4 i)`. Establish `hemb : MeasurableEmbedding fun x : S => V x` using `(hV.comp measurable_subtype_coe).measurableEmbedding hinj`.

Take `⟨ρ, hρ, hρV⟩` from `hemb.exists_measurable_extend (g := fun x : S => (x : Fin δ → ℂ)) measurable_subtype_coe fun _ => inferInstance`. Use `⟨ρ, hρ, fun c => ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `exists_prod_X_sub_C_eq c`. Establish `hrS : r ∘ Tuple.sort (e ∘ r) ∈ S` using `Tuple.monotone_sort (e ∘ r)`. Establish `hp : (∏ j, (X - C ((r ∘ Tuple.sort (e ∘ r)) j)) : ℂ[X]) = X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ)`.

Rewrite using `[← hr]`. Conclude with `Equiv.prod_comp (Tuple.sort (e ∘ r)) fun j => X - C (r j)`. Establish `hc : V (r ∘ Tuple.sort (e ∘ r)) = c`. Use function extensionality and compare the values at `i`. Simplify using `only [V]`.

Rewrite using `[hp, coeff_add, coeff_X_pow, if_neg i.2.ne, zero_add, finset_sum_coeff]`. Simplify using `only [coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Conclude with `if_neg fun h => hj (Fin.ext h.symm)`. Simplify using the standard rewrite rules. Establish `: ρ c = r ∘ Tuple.sort (e ∘ r)`. Rewrite using `[← hc]`. Conclude with `congrFun hρV ⟨_, hrS⟩`.

Rewrite using `[this, hp]`.
-/
theorem exists_measurable_roots_enumeration :
    ∀ δ : ℕ, ∃ ρ : (Fin δ → ℂ) → (Fin δ → ℂ), Measurable ρ ∧ ∀ c : Fin δ → ℂ,
      ∏ i, (Polynomial.X - Polynomial.C (ρ c i)) =
        Polynomial.X ^ δ + ∑ i : Fin δ, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) := by
  intro δ
  let e : ℂ ≃ᵐ ℝ := PolishSpace.measurableEquivOfNotCountable
    (fun _ => not_countable_iff.mpr (inferInstance : Uncountable ℝ)
      Complex.ofReal_injective.countable) (not_countable_iff.mpr inferInstance)
  let S : Set (Fin δ → ℂ) := {r | Monotone (e ∘ r)}
  have hS : MeasurableSet S := by
    have : S = ⋂ i, ⋂ j, ⋂ _ : i ≤ j, {r : Fin δ → ℂ | e (r i) ≤ e (r j)} := by
      ext r
      simp only [S, Set.mem_setOf_eq, Set.mem_iInter, Monotone, Function.comp]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_le ?_ ?_
    · exact e.measurable.comp (measurable_pi_apply i)
    · exact e.measurable.comp (measurable_pi_apply j)
  let V : (Fin δ → ℂ) → (Fin δ → ℂ) := fun r i => (∏ j, (X - C (r j))).coeff i
  have hV : Measurable V :=
    (continuous_pi fun i => continuous_coeff_prod_X_sub_C _ _).measurable
  haveI : StandardBorelSpace S := hS.standardBorel
  have hinj : Function.Injective fun x : S => V x := by
    rintro ⟨r, hr⟩ ⟨s, hs⟩ h
    have h1 : (∏ j, (X - C (r j)) : ℂ[X]) = ∏ j, (X - C (s j)) := by
      refine (prod_X_sub_C_eq_X_pow_add_sum r).trans
        (Eq.trans ?_ (prod_X_sub_C_eq_X_pow_add_sum s).symm)
      refine congrArg (X ^ δ + ·) (Finset.sum_congr rfl fun i _ => ?_)
      exact congrArg (fun a => C a * X ^ (i : ℕ)) (congrFun h i)
    have h2 : Finset.univ.val.map r = Finset.univ.val.map s := by
      rw [← roots_multiset_prod_X_sub_C (Finset.univ.val.map r),
        ← roots_multiset_prod_X_sub_C (Finset.univ.val.map s), Multiset.map_map,
        Multiset.map_map]
      exact congrArg roots h1
    have h3 : Finset.univ.val.map (e ∘ r) = Finset.univ.val.map (e ∘ s) := by
      rw [← Multiset.map_map, ← Multiset.map_map, h2]
    rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at h3
    have h4 := List.ofFn_injective
      (h3.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr hr) (List.sortedLE_ofFn_iff.mpr hs))
    ext i
    exact e.injective (congrFun h4 i)
  have hemb : MeasurableEmbedding fun x : S => V x :=
    (hV.comp measurable_subtype_coe).measurableEmbedding hinj
  obtain ⟨ρ, hρ, hρV⟩ := hemb.exists_measurable_extend (g := fun x : S => (x : Fin δ → ℂ))
    measurable_subtype_coe fun _ => inferInstance
  refine ⟨ρ, hρ, fun c => ?_⟩
  obtain ⟨r, hr⟩ := exists_prod_X_sub_C_eq c
  have hrS : r ∘ Tuple.sort (e ∘ r) ∈ S := Tuple.monotone_sort (e ∘ r)
  have hp : (∏ j, (X - C ((r ∘ Tuple.sort (e ∘ r)) j)) : ℂ[X])
      = X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
    rw [← hr]
    exact Equiv.prod_comp (Tuple.sort (e ∘ r)) fun j => X - C (r j)
  have hc : V (r ∘ Tuple.sort (e ∘ r)) = c := by
    funext i
    simp only [V]
    rw [hp, coeff_add, coeff_X_pow, if_neg i.2.ne, zero_add, finset_sum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      exact if_neg fun h => hj (Fin.ext h.symm)
    · simp
  have : ρ c = r ∘ Tuple.sort (e ∘ r) := by
    rw [← hc]
    exact congrFun hρV ⟨_, hrS⟩
  rw [this, hp]

end GlobalTheory
