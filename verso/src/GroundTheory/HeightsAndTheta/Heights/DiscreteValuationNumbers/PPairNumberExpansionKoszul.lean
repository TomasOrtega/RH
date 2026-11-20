import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMixedDiffLinear
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section Koszul

variable {n : ℕ}

def pairDiff (i : Fin n) : MvPolynomial (Fin n ⊕ Fin n) ℤ := X (Sum.inl i) - X (Sum.inr i)

def pairCollapse (p : Fin n) : Fin n ⊕ Fin n → Fin n ⊕ Fin n :=
  fun s => if s = Sum.inl p then Sum.inr p else s

/- English proof (translation)
Use function extensionality and compare the values at `s`. Simplify using `only [Function.comp, pairCollapse]`. Apply the tactic sequence `split_ifs with h1 h2 <;> simp_all`.
-/
theorem pairCollapse_comp (p : Fin n) : pairCollapse p ∘ pairCollapse p = pairCollapse p := by
  funext s
  simp only [Function.comp, pairCollapse]
  split_ifs with h1 h2 <;> simp_all

/- English proof (translation)
Rewrite using `[rename_rename, pairCollapse_comp]`.
-/
theorem rename_pairCollapse_idem (p : Fin n) (G : MvPolynomial (Fin n ⊕ Fin n) ℤ) :
    rename (pairCollapse p) (rename (pairCollapse p) G) = rename (pairCollapse p) G := by
  rw [rename_rename, pairCollapse_comp]

/- English proof (translation)
Unfold `pairDiff`. Distinguish the cases in `h : i = p`. Substitute `h` using the available equality. Simplify using `[pairCollapse]`. Simplify using `[pairCollapse, h]`.
-/
theorem rename_pairCollapse_pairDiff (p i : Fin n) :
    rename (pairCollapse p) (pairDiff i) = if i = p then 0 else pairDiff i := by
  unfold pairDiff
  by_cases h : i = p
  · subst h
    simp [pairCollapse]
  · simp [pairCollapse, h]

/- English proof (translation)
Unfold `pairDiff`. Rewrite using `[sub_ne_zero]`. Introduce `h`. Conclude with `Sum.inl_ne_inr (X_injective h)`.
-/
theorem pairDiff_ne_zero (i : Fin n) : pairDiff i ≠ 0 := by
  unfold pairDiff
  rw [sub_ne_zero]
  intro h
  exact Sum.inl_ne_inr (X_injective h)

/- English proof (translation)
The claim follows from `(isHomogeneous_X _ _).sub (isHomogeneous_X _ _)`.
-/
theorem isHomogeneous_pairDiff (i : Fin n) : (pairDiff i).IsHomogeneous 1 :=
  (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)

/- English proof (translation)
Proceed by induction on `G using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨0, by simp⟩`. Consider the case `add G H hG hH`. Take `⟨Q₁, h₁⟩` from `hG`. Take `⟨Q₂, h₂⟩` from `hH`.

Use `⟨Q₁ + Q₂, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, mul_add, ← h₁, ← h₂]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X G s hG`. Take `⟨Q, hQ⟩` from `hG`.

Use `⟨Q * X s + if s = Sum.inl p then rename (pairCollapse p) G else 0, ?_⟩` and prove the remaining obligations. Establish `hs : X s - rename (pairCollapse p) (X s) = pairDiff p * (if s = Sum.inl p then 1 else 0)`. Rewrite using `[rename_X]`. Unfold `pairCollapse pairDiff`. Use `split_ifs with h`.

Substitute `h` using the available equality. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`. Rewrite using `[hQ, hs]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem exists_sub_rename_pairCollapse (p : Fin n) (G : MvPolynomial (Fin n ⊕ Fin n) ℤ) :
    ∃ Q, G - rename (pairCollapse p) G = pairDiff p * Q := by
  induction G using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp⟩
  | add G H hG hH =>
    obtain ⟨Q₁, h₁⟩ := hG
    obtain ⟨Q₂, h₂⟩ := hH
    refine ⟨Q₁ + Q₂, ?_⟩
    rw [map_add, mul_add, ← h₁, ← h₂]
    ring
  | mul_X G s hG =>
    obtain ⟨Q, hQ⟩ := hG
    refine ⟨Q * X s + if s = Sum.inl p then rename (pairCollapse p) G else 0, ?_⟩
    have hs : X s - rename (pairCollapse p) (X s) =
        pairDiff p * (if s = Sum.inl p then 1 else 0) := by
      rw [rename_X]
      unfold pairCollapse pairDiff
      split_ifs with h
      · subst h
        ring
      · simp
    calc G * X s - rename (pairCollapse p) (G * X s)
        = (G - rename (pairCollapse p) G) * X s +
            rename (pairCollapse p) G * (X s - rename (pairCollapse p) (X s)) := by
          rw [map_mul]
          ring
      _ = _ := by
          rw [hQ, hs]
          split_ifs <;> ring

/- English proof (translation)
Establish `h : ∑ i, pairDiff i * ∑ j, pairDiff j * M i j = -∑ i, pairDiff i * ∑ j, pairDiff j * M i j` using `by conv_lhs => simp only [Finset.mul_sum]; rw [Finset.sum_comm]`. Simplify using `only [Finset.mul_sum, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hM j i]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : (2 : MvPolynomial (Fin n ⊕ Fin n) ℤ) * ∑ i, pairDiff i * ∑ j, pairDiff j * M i j = 0`. Take the linear combination `h`. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases. Conclude with `absurd h3 two_ne_zero`. Conclude with `h3`.
-/
theorem sum_pairDiff_koszul (M : Fin n → Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ)
    (hM : ∀ i j, M i j = -M j i) :
    ∑ i, pairDiff i * ∑ j, pairDiff j * M i j = 0 := by
  have h : ∑ i, pairDiff i * ∑ j, pairDiff j * M i j =
      -∑ i, pairDiff i * ∑ j, pairDiff j * M i j := by
    conv_lhs => simp only [Finset.mul_sum]; rw [Finset.sum_comm]
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hM j i]
    ring
  have h2 : (2 : MvPolynomial (Fin n ⊕ Fin n) ℤ) * ∑ i, pairDiff i * ∑ j, pairDiff j * M i j = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact h3

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `G hG _`. Conclude with `⟨0, fun _ _ => by simp, fun i => by simp [hG i (Finset.notMem_empty i)]⟩`. Consider the case `insert p s hp ih`.

Introduce `G hG hrel`. Use `choose Q hQ using fun i => exists_sub_rename_pairCollapse p (G i)`. Set `M : Fin n → Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ` to `fun i j => if i ∈ s ∧ j = p then Q i else if i = p ∧ j ∈ s then -Q j else 0`. Establish `hM : ∀ i j, M i j = -M j i`. Introduce `i j`.

Simplify using `only [M]`. Apply the tactic sequence `by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> by_cases hip : i = p <;>`. Apply the tactic sequence `by_cases hjp : j = p <;> simp_all`. Set `G' : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ` to `fun i => G i - ∑ j, pairDiff j * M i j`. Establish `hrel' : ∑ i, pairDiff i * G' i = 0`.

Simplify using `only [G', mul_sub, Finset.sum_sub_distrib, hrel, sum_pairDiff_koszul M hM, sub_self]`. Establish `hs : ∀ i ∈ s, G' i = rename (pairCollapse p) (G i)`. Introduce `i hi`. Establish `hip : i ≠ p` using `fun h => hp (h ▸ hi)`. Establish `hsum : ∑ j, pairDiff j * M i j = pairDiff p * Q i`.

Simplify using `[M, hi, hip]`. Simplify using `only [G', hsum]`. Take the linear combination `hQ i`. Establish `hout : ∀ i, i ∉ insert p s → G' i = 0`. Introduce `i hi`.

Rewrite `hi` using `[Finset.mem_insert, not_or]`. Establish `hsum : ∑ j, pairDiff j * M i j = 0`. Simplify using `[M, hi.1, hi.2]`. Simplify using `only [G', hsum, hG i (by rw [Finset.mem_insert, not_or]; exact hi), sub_zero]`. Establish `hcol : ∑ i, (if i = p then 0 else pairDiff i * G' i) = 0`.

Establish `h` using `congrArg (rename (pairCollapse p)) hrel'`. Rewrite `h` using `[map_sum, map_zero]`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h` and prove the remaining obligations. Rewrite using `[map_mul, rename_pairCollapse_pairDiff]`. Distinguish the cases in `hip : i = p`.

Simplify using `[hip]`. Rewrite using `[if_neg hip, if_neg hip]`. Distinguish the cases in `hi : i ∈ s`. Rewrite using `[hs i hi, rename_pairCollapse_idem]`. Rewrite using `[hout i (by rw [Finset.mem_insert, not_or]; exact ⟨hip, hi⟩), map_zero]`.

Establish `hp0 : G' p = 0`. Establish `hsplit : ∑ i, pairDiff i * G' i = ∑ i, (if i = p then 0 else pairDiff i * G' i) + ∑ i, (if i = p then pairDiff p * G' p else 0)`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hip : i = p`.

Substitute `hip` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hip]`. Rewrite `hsplit` using `[hrel', hcol, zero_add, Finset.sum_ite_eq', if_pos (Finset.mem_univ p)]`. Break down `mul_eq_zero.mp hsplit.symm with h | h` into its components or cases.

Conclude with `absurd h (pairDiff_ne_zero p)`. Conclude with `h`. Take `⟨K', hK'a, hK'⟩` from `ih G' (fun i hi => by`. Distinguish the cases in `hip : i = p`. Rewrite using `[hip, hp0]`.

Conclude with `hout i (by rw [Finset.mem_insert, not_or]; exact ⟨hip, hi⟩)) hrel'`. Use `⟨K' + M, fun i j => ?_, fun i => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`. Rewrite using `[hK'a i j, hM i j, neg_add]`. Establish `h` using `hK' i`.

Simplify using `only [G'] at h`. Simplify using `only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ← h, sub_add_cancel]`.
-/
theorem koszul_finset (s : Finset (Fin n)) :
    ∀ G : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ, (∀ i, i ∉ s → G i = 0) →
      ∑ i, pairDiff i * G i = 0 →
      ∃ K : Fin n → Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ,
        (∀ i j, K i j = -K j i) ∧ ∀ i, G i = ∑ j, pairDiff j * K i j := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro G hG _
    exact ⟨0, fun _ _ => by simp, fun i => by simp [hG i (Finset.notMem_empty i)]⟩
  | insert p s hp ih =>
    intro G hG hrel
    choose Q hQ using fun i => exists_sub_rename_pairCollapse p (G i)
    let M : Fin n → Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ := fun i j =>
      if i ∈ s ∧ j = p then Q i else if i = p ∧ j ∈ s then -Q j else 0
    have hM : ∀ i j, M i j = -M j i := by
      intro i j
      simp only [M]
      by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> by_cases hip : i = p <;>
        by_cases hjp : j = p <;> simp_all
    let G' : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ := fun i => G i - ∑ j, pairDiff j * M i j
    have hrel' : ∑ i, pairDiff i * G' i = 0 := by
      simp only [G', mul_sub, Finset.sum_sub_distrib, hrel, sum_pairDiff_koszul M hM, sub_self]

    have hs : ∀ i ∈ s, G' i = rename (pairCollapse p) (G i) := by
      intro i hi
      have hip : i ≠ p := fun h => hp (h ▸ hi)
      have hsum : ∑ j, pairDiff j * M i j = pairDiff p * Q i := by
        simp [M, hi, hip]
      simp only [G', hsum]
      linear_combination hQ i
    have hout : ∀ i, i ∉ insert p s → G' i = 0 := by
      intro i hi
      rw [Finset.mem_insert, not_or] at hi
      have hsum : ∑ j, pairDiff j * M i j = 0 := by
        simp [M, hi.1, hi.2]
      simp only [G', hsum, hG i (by rw [Finset.mem_insert, not_or]; exact hi), sub_zero]

    have hcol : ∑ i, (if i = p then 0 else pairDiff i * G' i) = 0 := by
      have h := congrArg (rename (pairCollapse p)) hrel'
      rw [map_sum, map_zero] at h
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
      rw [map_mul, rename_pairCollapse_pairDiff]
      by_cases hip : i = p
      · simp [hip]
      · rw [if_neg hip, if_neg hip]
        by_cases hi : i ∈ s
        · rw [hs i hi, rename_pairCollapse_idem]
        · rw [hout i (by rw [Finset.mem_insert, not_or]; exact ⟨hip, hi⟩), map_zero]
    have hp0 : G' p = 0 := by
      have hsplit : ∑ i, pairDiff i * G' i =
          ∑ i, (if i = p then 0 else pairDiff i * G' i) +
            ∑ i, (if i = p then pairDiff p * G' p else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hip : i = p
        · subst hip
          simp
        · simp [hip]
      rw [hrel', hcol, zero_add, Finset.sum_ite_eq', if_pos (Finset.mem_univ p)] at hsplit
      rcases mul_eq_zero.mp hsplit.symm with h | h
      · exact absurd h (pairDiff_ne_zero p)
      · exact h
    obtain ⟨K', hK'a, hK'⟩ := ih G' (fun i hi => by
      by_cases hip : i = p
      · rw [hip, hp0]
      · exact hout i (by rw [Finset.mem_insert, not_or]; exact ⟨hip, hi⟩)) hrel'
    refine ⟨K' + M, fun i j => ?_, fun i => ?_⟩
    · simp only [Pi.add_apply]
      rw [hK'a i j, hM i j, neg_add]
    · have h := hK' i
      simp only [G'] at h
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ← h, sub_add_cancel]

/- English proof (translation)
Take `⟨K, hK, hGK⟩` from `koszul_finset Finset.univ G (fun i h => absurd (Finset.mem_univ i) h) hrel`. Use `⟨fun i j => if m - 1 = 0 then 0 else homogeneousComponent (m - 2) (K i j), fun i j => ?_, fun i j => ?_, fun hm i j => if_pos hm, fun i => ?_⟩` and prove the remaining obligations. Use `split_ifs`. Simplify using the standard rewrite rules. Use `show homogeneousComponent (m - 2) (K i j) = -homogeneousComponent (m - 2) (K j i)`.

Rewrite using `[hK i j, map_neg]`. Use `split_ifs`. Conclude with `isHomogeneous_zero _ _ _`. Conclude with `homogeneousComponent_isHomogeneous _ _`. Establish `h` using `congrArg (homogeneousComponent (m - 1)) (hGK i)`.

Rewrite `h` using `[homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr (hG i)), if_pos rfl, map_sum]`. Simplify using `only [homogeneousComponent_linear_mul (isHomogeneous_pairDiff _)] at h`. Rewrite using `[h]`. Distinguish the cases in `hm : m - 1 = 0`. Simplify using `[hm]`.

Simplify using `only [hm, if_false]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[show m - 1 - 1 = m - 2 by omega]`.
-/
theorem koszul_homogeneous {m : ℕ} (G : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ)
    (hG : ∀ i, (G i).IsHomogeneous (m - 1)) (hrel : ∑ i, pairDiff i * G i = 0) :
    ∃ K : Fin n → Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ,
      (∀ i j, K i j = -K j i) ∧ (∀ i j, (K i j).IsHomogeneous (m - 2)) ∧
      (m - 1 = 0 → ∀ i j, K i j = 0) ∧ ∀ i, G i = ∑ j, pairDiff j * K i j := by
  obtain ⟨K, hK, hGK⟩ := koszul_finset Finset.univ G
    (fun i h => absurd (Finset.mem_univ i) h) hrel
  refine ⟨fun i j => if m - 1 = 0 then 0 else homogeneousComponent (m - 2) (K i j),
    fun i j => ?_, fun i j => ?_, fun hm i j => if_pos hm, fun i => ?_⟩
  · split_ifs
    · simp
    · show homogeneousComponent (m - 2) (K i j) = -homogeneousComponent (m - 2) (K j i)
      rw [hK i j, map_neg]
  · split_ifs
    · exact isHomogeneous_zero _ _ _
    · exact homogeneousComponent_isHomogeneous _ _
  · have h := congrArg (homogeneousComponent (m - 1)) (hGK i)
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr (hG i)), if_pos rfl,
      map_sum] at h
    simp only [homogeneousComponent_linear_mul (isHomogeneous_pairDiff _)] at h
    rw [h]
    by_cases hm : m - 1 = 0
    · simp [hm]
    · simp only [hm, if_false]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show m - 1 - 1 = m - 2 by omega]

end Koszul

section Numbers

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Unfold `vNumL vNum intNum mixedDiff`. Rewrite using `[List.ofFn_get]`.
-/
theorem vNumL_eq_foldr (W : Ideal (MRing ι O)) (l : List (K → ℤ)) :
    vNumL W l = eventualValue (l.foldr diffStep (hilbFn (specialIdeal W))) := by
  unfold vNumL vNum intNum mixedDiff
  rw [List.ofFn_get]

/- English proof (translation)
Rewrite using `[vNumL_eq_foldr]`. Unfold `vNum intNum mixedDiff`. Rewrite using `[List.ofFn_succ]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_succ]`.
-/
theorem vNum_vecCons_eq (W : Ideal (MRing ι O)) {k : ℕ} (b : K → ℤ) (L : Fin k → K → ℤ) :
    vNum W (Matrix.vecCons b L) = vNumL W (b :: List.ofFn L) := by
  rw [vNumL_eq_foldr]
  unfold vNum intNum mixedDiff
  rw [List.ofFn_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]

omit [DecidableEq K] in

/- English proof (translation)
Proceed by induction on `hl with`. Consider the case `nil => rfl`. Consider the case `cons x _ ih => simp only [List.foldr_cons, ih]`. Consider the case `swap x y l`. Simplify using `only [List.foldr_cons]`.

Conclude with `diffStep_comm' _ _ _`. Consider the case `trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂`.
-/
theorem foldr_diffStep_perm {l₁ l₂ : List (K → ℤ)} (hl : l₁.Perm l₂) (h : (K → ℤ) → ℤ) :
    l₁.foldr diffStep h = l₂.foldr diffStep h := by
  induction hl with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x y l =>
    simp only [List.foldr_cons]
    exact diffStep_comm' _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/- English proof (translation)
Rewrite using `[vNumL_eq_foldr, vNumL_eq_foldr, foldr_diffStep_perm hl]`.
-/
theorem vNumL_perm (W : Ideal (MRing ι O)) {l₁ l₂ : List (K → ℤ)} (hl : l₁.Perm l₂) :
    vNumL W l₁ = vNumL W l₂ := by
  rw [vNumL_eq_foldr, vNumL_eq_foldr, foldr_diffStep_perm hl]

omit [DecidableEq K] in

/- English proof (translation)
Rewrite using `[← Multiset.coe_eq_coe]`. Unfold `classList`. Rewrite using `[Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList]`. Simplify using `[Finsupp.toMultiset_single]`.
-/
theorem classList_single_add_perm {σ : Type*} (cls : σ → K → ℤ) (s : σ) (μ : σ →₀ ℕ) :
    (classList cls (Finsupp.single s 1 + μ)).Perm (cls s :: classList cls μ) := by
  rw [← Multiset.coe_eq_coe]
  unfold classList
  rw [Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList]
  simp [Finsupp.toMultiset_single]

omit [DecidableEq K] in

/- English proof (translation)
Unfold `classList`. Rewrite using `[Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]`. Establish `h` using `hH (mem_support_iff.mp hμ)`. Rewrite `h` using `[Finsupp.weight_apply]`. Simplify using `only [Pi.one_apply, smul_eq_mul, mul_one] at h`.

Conclude with `h`.
-/
theorem classList_length_of_mem_support {σ : Type*} (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ}
    {t : ℕ} (hH : H.IsHomogeneous t) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) :
    (classList cls μ).length = t := by
  unfold classList
  rw [Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
  have h := hH (mem_support_iff.mp hμ)
  rw [Finsupp.weight_apply] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  exact h

/- English proof (translation)
Use `conv_lhs => rw [H.as_sum, Finset.mul_sum]`. Establish `h` using `map_sum (classNumAddHom cls Q W) (fun μ => X s * monomial μ (H.coeff μ)) H.support`. Simplify using `only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h`. Rewrite using `[h]`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations.

Rewrite using `[show (X s : MvPolynomial σ ℤ) = monomial (Finsupp.single s 1) 1 from rfl, monomial_mul, one_mul, classNum_monomial_eq]`. Use `congr 1`. Conclude with `vNumL_perm W ((classList_single_add_perm cls s μ).append_right Q)`.
-/
theorem classNum_X_mul {σ : Type*} [DecidableEq σ] (cls : σ → K → ℤ) (s : σ) (H : MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (X s * H) Q W =
      ∑ μ ∈ H.support, H.coeff μ * vNumL W (cls s :: (classList cls μ ++ Q)) := by
  conv_lhs => rw [H.as_sum, Finset.mul_sum]
  have h := map_sum (classNumAddHom cls Q W) (fun μ => X s * monomial μ (H.coeff μ)) H.support
  simp only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  rw [h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [show (X s : MvPolynomial σ ℤ) = monomial (Finsupp.single s 1) 1 from rfl, monomial_mul,
    one_mul, classNum_monomial_eq]
  congr 1
  exact vNumL_perm W ((classList_single_add_perm cls s μ).append_right Q)

end Numbers

section Additivity

/- English proof (translation)
Take `⟨bf, bg, hbf, hbg, -⟩` from `hD.degrees`. Establish `hPmh : IsMultiHomogIdeal P` using `hP.multiProj.multiHomog`. Establish `: P.IsPrime` using `hP.multiProj.isPrime`. Establish `hmh : ∀ (h : MRing ι O) (c : K → ℕ), IsMultiHomog h c → divCycle P h W ≠ 0 → IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W`. Introduce `h c hc hW'`.

Unfold `divCycle at hW'`. Use `split_ifs at hW' with hW''`. Conclude with `⟨MinimalPrimeMultiHomog.full O K ι _ W (SupSpanMultiHomog.full O K ι P h c hPmh hc) hW''.1, hW''.1.1.1, le_sup_left.trans hW''.1.1.2⟩`. Conclude with `absurd rfl hW'`. Establish `hϖP : (C ϖ : MRing ι O) ∉ P`.

Introduce `h`. Establish `h' : ϖ ∈ P.comap (C : O →+* MRing ι O)` using `h`. Rewrite `h'` using `[hP.noTorsion, Ideal.mem_bot]`. Conclude with `hϖ.ne_zero h'`. Establish `hϖW : (C ϖ : MRing ι O) ∈ W` using `hD.vertical W hW`.

Choose the witnesses or unpack the hypotheses as in `⟨hWm, hWp, hPW⟩ : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by`. Distinguish the cases in `hWf : divCycle P f W = 0`. Conclude with `hmh g bg hbg (fun hWg => hW (by simp [ratDiv, hWf, hWg]))`. Conclude with `hmh f bf hbf hWf`. Use `hWp` as an intermediate fact.

Establish `hlt : P < W` using `lt_of_le_of_ne hPW (fun h => hϖP (h ▸ hϖW))`. Establish `hdrop` using `DimStrictDrop.full (MRing ι O) P W hlt`. Rewrite `hdrop` using `[hP.dim]`. Establish `hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) < ((l.length + 2 + Fintype.card K : ℕ) : WithBot ℕ∞)`. Rewrite using `[SpecialQuotDim.full O ϖ hϖ K ι W hϖW]`.

Use `lt_of_lt_of_le (lt_natCast_of_add_one_le hdrop) ?_` and prove the remaining obligations. Conclude with `(by omega : e + 1 + 1 + Fintype.card K ≤ l.length + 2 + Fintype.card K)` after adjusting the coercions. Establish `key` using `IntNumAddFirst.full (IsLocalRing.ResidueField O) K ι l.length (specialIdeal W) (SpecialIdealCorresp.full O ϖ hϖ K ι P W hWp hϖW).1 (SpecialIdealMultiHomog.full O K ι W hWm) hdim a₁ a₂ l.get`. Establish `e' : ∀ c, vNumL W (c :: l) = intNum (IsLocalRing.ResidueField O) (specialIdeal W) (Matrix.vecCons c l.get)`. Introduce `c`.

Express the relevant statement in the definitionally equal form `_ = vNum W (Matrix.vecCons c l.get)`. Rewrite using `[vNum_vecCons_eq, List.ofFn_get]`. Rewrite using `[e', e', e', key]`.
-/
theorem vNumL_add_of_ratDiv_ne_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} {e : ℕ} (hP : IsModelOver P (e + 1))
    {b : K → ℤ} {f g : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g) {W : Ideal (MRing ι O)}
    (hW : ratDiv P f g W ≠ 0) (a₁ a₂ : K → ℤ) (l : List (K → ℤ)) (hl : e ≤ l.length) :
    vNumL W ((a₁ + a₂) :: l) = vNumL W (a₁ :: l) + vNumL W (a₂ :: l) := by
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime
  have hmh : ∀ (h : MRing ι O) (c : K → ℕ), IsMultiHomog h c → divCycle P h W ≠ 0 →
      IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
    intro h c hc hW'
    unfold divCycle at hW'
    split_ifs at hW' with hW''
    · exact ⟨MinimalPrimeMultiHomog.full O K ι _ W (SupSpanMultiHomog.full O K ι P h c hPmh hc)
        hW''.1, hW''.1.1.1, le_sup_left.trans hW''.1.1.2⟩
    · exact absurd rfl hW'
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
  obtain ⟨hWm, hWp, hPW⟩ : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
    by_cases hWf : divCycle P f W = 0
    · exact hmh g bg hbg (fun hWg => hW (by simp [ratDiv, hWf, hWg]))
    · exact hmh f bf hbf hWf
  have := hWp
  have hlt : P < W := lt_of_le_of_ne hPW (fun h => hϖP (h ▸ hϖW))
  have hdrop := DimStrictDrop.full (MRing ι O) P W hlt
  rw [hP.dim] at hdrop
  have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
      ((l.length + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [SpecialQuotDim.full O ϖ hϖ K ι W hϖW]
    refine lt_of_lt_of_le (lt_natCast_of_add_one_le hdrop) ?_
    exact_mod_cast (by omega : e + 1 + 1 + Fintype.card K ≤ l.length + 2 + Fintype.card K)
  have key := IntNumAddFirst.full (IsLocalRing.ResidueField O) K ι l.length (specialIdeal W)
    (SpecialIdealCorresp.full O ϖ hϖ K ι P W hWp hϖW).1 (SpecialIdealMultiHomog.full O K ι W hWm)
    hdim a₁ a₂ l.get
  have e' : ∀ c, vNumL W (c :: l) =
      intNum (IsLocalRing.ResidueField O) (specialIdeal W) (Matrix.vecCons c l.get) := by
    intro c
    change _ = vNum W (Matrix.vecCons c l.get)
    rw [vNum_vecCons_eq, List.ofFn_get]
  rw [e', e', e', key]

end Additivity

end

end GroundTheory.Heights₂.Heights.NumbersDVR
