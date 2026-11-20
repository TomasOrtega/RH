import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h k`. Take `⟨i, hi⟩` from `h k`. Conclude with `⟨⟨k, i⟩, rfl, hi⟩`. Introduce `h k`.

Take `⟨⟨k', i⟩, hk, hi⟩` from `h k`. Substitute `hk` using the available equality. Conclude with `⟨i, hi⟩`.
-/
theorem isRelevant_iff {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    (I : Ideal (MRing ι R)) :
    IsRelevant I ↔ ∀ k, ∃ v : Σ k, ι k, v.1 = k ∧ (X v : MRing ι R) ∉ I := by
  constructor
  · intro h k
    obtain ⟨i, hi⟩ := h k
    exact ⟨⟨k, i⟩, rfl, hi⟩
  · intro h k
    obtain ⟨⟨k', i⟩, hk, hi⟩ := h k
    subst hk
    exact ⟨i, hi⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => funext fun k => by simpa [hj.extend_apply] using congrFun h (j k), fun h => h ▸ rfl⟩`.
-/
theorem extend_zero_inj {K K' : Type*} {j : K → K'} (hj : Function.Injective j)
    {x y : K → ℕ} : Function.extend j x 0 = Function.extend j y 0 ↔ x = y :=
  ⟨fun h => funext fun k => by simpa [hj.extend_apply] using congrFun h (j k), fun h => h ▸ rfl⟩

variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {ι : K → Type*} {ι' : K' → Type*}
  {j : K → K'} {g : (Σ k, ι k) → (Σ k, ι' k)} (hgj : ∀ v, (g v).1 = j v.1)

include hgj in

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) => c • blockWeight ι' i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]`. Use function extensionality and compare the values at `k'`. Distinguish the cases in `hk : ∃ k, j k = k'`. Take `⟨k, rfl⟩` from `hk`. Rewrite using `[hj.extend_apply]`.

Simplify using `only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight, hgj, Pi.single_apply, hj.eq_iff]`. Rewrite using `[Function.extend_apply' _ _ _ hk]`. Simplify using `only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight, hgj, Pi.single_apply, Pi.zero_apply]`. Use `Finset.sum_eq_zero fun v _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg fun h => hk ⟨v.1, h.symm⟩, smul_zero]`.
-/
theorem weight_mapDomain (hj : Function.Injective j) (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain g d) =
      Function.extend j (Finsupp.weight (blockWeight ι) d) 0 := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) => c • blockWeight ι' i)
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  funext k'
  by_cases hk : ∃ k, j k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hj.extend_apply]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight, hgj, Pi.single_apply,
      hj.eq_iff]
  · rw [Function.extend_apply' _ _ _ hk]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight, hgj, Pi.single_apply,
      Pi.zero_apply]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [if_neg fun h => hk ⟨v.1, h.symm⟩, smul_zero]

include hgj in

/- English proof (translation)
Use extensionality with `d'`. Rewrite using `[coeff_weightedHomogeneousComponent]`. Distinguish the cases in `hd : ∃ d, Finsupp.mapDomain g d = d'`. Take `⟨d, rfl⟩` from `hd`. Rewrite using `[coeff_rename_mapDomain g hg, coeff_rename_mapDomain g hg, coeff_weightedHomogeneousComponent, weight_mapDomain hgj hj, extend_zero_inj hj]`.

Use `push Not at hd`. Rewrite using `[coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (hd u)]`. Use `split_ifs`. Rewrite using `[coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (hd u)]`. Both sides reduce to the same expression.
-/
theorem rename_weightedHomogeneousComponent (hj : Function.Injective j)
    (hg : Function.Injective g) {R : Type*} [CommSemiring R] (b : K → ℕ)
    (f : MvPolynomial (Σ k, ι k) R) :
    rename g (weightedHomogeneousComponent (blockWeight ι) b f) =
      weightedHomogeneousComponent (blockWeight ι') (Function.extend j b 0) (rename g f) := by
  classical
  ext d'
  rw [coeff_weightedHomogeneousComponent]
  by_cases hd : ∃ d, Finsupp.mapDomain g d = d'
  · obtain ⟨d, rfl⟩ := hd
    rw [coeff_rename_mapDomain g hg, coeff_rename_mapDomain g hg,
      coeff_weightedHomogeneousComponent, weight_mapDomain hgj hj, extend_zero_inj hj]
  · push Not at hd
    rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (hd u)]
    split_ifs
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (hd u)]
    · rfl

include hgj in

/- English proof (translation)
The claim follows from `haveI := hP.isPrime; Ideal.comap_isPrime _ _ multiHomog f hf b := by rw [Ideal.mem_comap] at hf ⊢ rw [rename_weightedHomogeneousComponent hgj hj hg] exact hP.multiHomog _ hf _ relevant := by rw [isRelevant_iff] intro k obtain ⟨w, hw, hwP⟩ := (isRelevant_iff P).1 hP.relevant (j k) …`.
-/
theorem isMultiProjPrime_comap_rename (hj : Function.Injective j) (hg : Function.Injective g)
    (hsurj : ∀ w : Σ k, ι' k, w.1 ∈ Set.range j → ∃ v, g v = w) {R : Type*} [CommRing R]
    {P : Ideal (MRing ι' R)} (hP : IsMultiProjPrime P) :
    IsMultiProjPrime (P.comap (rename (R := R) g)) where
  isPrime := haveI := hP.isPrime; Ideal.comap_isPrime _ _
  multiHomog f hf b := by
    rw [Ideal.mem_comap] at hf ⊢
    rw [rename_weightedHomogeneousComponent hgj hj hg]
    exact hP.multiHomog _ hf _
  relevant := by
    rw [isRelevant_iff]
    intro k
    obtain ⟨w, hw, hwP⟩ := (isRelevant_iff P).1 hP.relevant (j k)
    obtain ⟨v, rfl⟩ := hsurj w ⟨k, hw.symm⟩
    refine ⟨v, hj (by rw [← hgj, hw]), ?_⟩
    rw [Ideal.mem_comap, rename_X]
    exact hwP

end

end GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
