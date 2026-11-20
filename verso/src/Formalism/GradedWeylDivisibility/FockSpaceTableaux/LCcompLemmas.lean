import Formalism.GradedWeylDivisibility.StatementC

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def lccompW {r n : ℕ} (l j : Fin n) : Option (Fin r × Fin n) → (Fin r × Fin n →₀ ℕ) :=
  fun o => match o with
    | none => 0
    | some v => pairW l j v

/- English proof (translation)
Unfold `pairW`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem lccomp_pairW_col {r n : ℕ} (l j : Fin n) (b : Fin r) :
    pairW (r := r) l j (b, l) = Finsupp.single (b, l) 1 := by
  unfold pairW
  split_ifs <;> rfl

/- English proof (translation)
Use `split_ifs with h`. Use `IsWeightedHomogeneous.add (isWeightedHomogeneous_X B (lccompW l j) (some v)) ?_` and prove the remaining obligations. Establish `hm` using `(isWeightedHomogeneous_X B (lccompW l j) none).mul (isWeightedHomogeneous_X B (lccompW l j) (some (v.1, l)))`. Use `hm using 1` and compare the differences between its conclusion and the goal. Use `show pairW l j v = 0 + pairW l j (v.1, l)`.

Rewrite using `[lccomp_pairW_col, zero_add]`. Simplify using `only [pairW, if_pos h]`. Conclude with `isWeightedHomogeneous_X B (lccompW l j) (some v)`.
-/
theorem lccomp_image_var_homog {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) :
    IsWeightedHomogeneous (lccompW l j)
      ((if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) :
        MvPolynomial (Option (Fin r × Fin n)) B)) (pairW l j v) := by
  split_ifs with h
  · refine IsWeightedHomogeneous.add (isWeightedHomogeneous_X B (lccompW l j) (some v)) ?_
    have hm := (isWeightedHomogeneous_X B (lccompW l j) none).mul
      (isWeightedHomogeneous_X B (lccompW l j) (some (v.1, l)))
    convert hm using 1
    show pairW l j v = 0 + pairW l j (v.1, l)
    rw [lccomp_pairW_col, zero_add]
    simp only [pairW, if_pos h]
  · exact isWeightedHomogeneous_X B (lccompW l j) (some v)

/- English proof (translation)
Establish `hp : IsWeightedHomogeneous (lccompW l j) (∏ v ∈ d.support, ((if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) : MvPolynomial (Option (Fin r × Fin n)) B)) ^ d v) (∑ v ∈ d.support, d v • pairW l j v)` using `IsWeightedHomogeneous.prod _ _ _ fun v _ => (lccomp_image_var_homog l j v).pow _`. Establish `hc : IsWeightedHomogeneous (lccompW l j) (C a : MvPolynomial (Option (Fin r × Fin n)) B) 0` using `isWeightedHomogeneous_C _ a`. Establish `h` using `hc.mul hp`. Rewrite `h` using `[zero_add]`. Rewrite using `[colAddGen, aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.weight_apply]`.

Conclude with `h`.
-/
theorem lccomp_colAddGen_monomial_homog {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (d : Fin r × Fin n →₀ ℕ) (a : B) :
    IsWeightedHomogeneous (lccompW l j) (colAddGen B l j (monomial d a))
      (Finsupp.weight (pairW l j) d) := by
  classical
  have hp : IsWeightedHomogeneous (lccompW l j)
      (∏ v ∈ d.support, ((if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) :
        MvPolynomial (Option (Fin r × Fin n)) B)) ^ d v)
      (∑ v ∈ d.support, d v • pairW l j v) :=
    IsWeightedHomogeneous.prod _ _ _ fun v _ => (lccomp_image_var_homog l j v).pow _
  have hc : IsWeightedHomogeneous (lccompW l j) (C a : MvPolynomial (Option (Fin r × Fin n)) B) 0 :=
    isWeightedHomogeneous_C _ a
  have h := hc.mul hp
  rw [zero_add] at h
  rw [colAddGen, aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.weight_apply]
  exact h

/- English proof (translation)
Rewrite using `[f.as_sum, map_sum]`. Use `IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_` and prove the remaining obligations. Establish `h` using `lccomp_colAddGen_monomial_homog (B := B) l j d (coeff d f)`. Rewrite `h` using `[hf (mem_support_iff.mp hd)]`. Then use the resulting hypothesis.
-/
theorem lccomp_colAddGen_homog {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (ω : Fin r × Fin n →₀ ℕ) (f : MvPolynomial (Fin r × Fin n) B)
    (hf : IsWeightedHomogeneous (pairW l j) f ω) :
    IsWeightedHomogeneous (lccompW l j) (colAddGen B l j f) ω := by
  classical
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have h := lccomp_colAddGen_monomial_homog (B := B) l j d (coeff d f)
  rwa [hf (mem_support_iff.mp hd)] at h

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_sum]`. Simplify using `only [coeff_weightedHomogeneousComponent]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`. Conclude with `h (hT d (mem_support_iff.mpr hne))`.
-/
theorem lccomp_sum_components {R : Type*} [CommRing R] {σ M : Type*} [AddCommMonoid M] [DecidableEq M]
    (w : σ → M) (f : MvPolynomial σ R) (T : Finset M)
    (hT : ∀ d ∈ f.support, Finsupp.weight w d ∈ T) :
    f = ∑ ω' ∈ T, weightedHomogeneousComponent w ω' f := by
  classical
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hT d (mem_support_iff.mpr hne))

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_weightedHomogeneousComponent]`. Use `split_ifs with hd`. Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`.

Conclude with `hd (h (Ne.symm hne))`.
-/
private lemma weightedHomogeneousComponent_self_of_isWH_ring {σ M R : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M} {m : M}
    {p : MvPolynomial σ R} (h : IsWeightedHomogeneous w p m) :
    weightedHomogeneousComponent w m p = p := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rfl
  · by_contra hne
    exact hd (h (Ne.symm hne))

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_zero]`. Use `split_ifs with hd`. Assume the negation of the conclusion as `hne`. Conclude with `hn (hd.symm.trans (h hne))`.

Both sides reduce to the same expression.
-/
private lemma weightedHomogeneousComponent_eq_zero_of_ne_isWH {σ M R : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M} {m n : M}
    {p : MvPolynomial σ R} (h : IsWeightedHomogeneous w p m) (hn : n ≠ m) :
    weightedHomogeneousComponent w n p = 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with hd
  · by_contra hne
    exact hn (hd.symm.trans (h hne))
  · rfl

/- English proof (translation)
Establish `hf` using `lccomp_sum_components (pairW l j) f (f.support.image (Finsupp.weight (pairW l j))) (fun d hd => Finset.mem_image_of_mem _ hd)`. Use `conv_lhs => rw [hf]`. Rewrite using `[map_sum, map_sum]`. Distinguish the cases in `hω : ω ∈ f.support.image (Finsupp.weight (pairW l j))`. Rewrite using `[Finset.sum_eq_single ω]`.

Conclude with `weightedHomogeneousComponent_self_of_isWH_ring (lccomp_colAddGen_homog l j ω _ (weightedHomogeneousComponent_isWeightedHomogeneous ω f))`. Introduce `b _ hb`. Conclude with `weightedHomogeneousComponent_eq_zero_of_ne_isWH (lccomp_colAddGen_homog l j b _ (weightedHomogeneousComponent_isWeightedHomogeneous b f)) (Ne.symm hb)`. Introduce `h`. Conclude with `absurd hω h`.

Rewrite using `[Finset.sum_eq_zero]`. Establish `h0 : weightedHomogeneousComponent (pairW l j) ω f = 0`. Use extensionality with `d`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_zero]`. Use `split_ifs with h`.

Assume the negation of the conclusion as `hne`. Conclude with `hω (h ▸ Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))`. Both sides reduce to the same expression. Rewrite using `[h0, map_zero]`. Introduce `b hb`.

Use `weightedHomogeneousComponent_eq_zero_of_ne_isWH (lccomp_colAddGen_homog l j b _ (weightedHomogeneousComponent_isWeightedHomogeneous b f)) ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hω hb`.
-/
theorem lccomp_component_colAddGen {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (ω : Fin r × Fin n →₀ ℕ) (f : MvPolynomial (Fin r × Fin n) B) :
    weightedHomogeneousComponent (lccompW l j) ω (colAddGen B l j f) =
      colAddGen B l j (weightedHomogeneousComponent (pairW l j) ω f) := by
  classical
  have hf := lccomp_sum_components (pairW l j) f (f.support.image (Finsupp.weight (pairW l j)))
    (fun d hd => Finset.mem_image_of_mem _ hd)
  conv_lhs => rw [hf]
  rw [map_sum, map_sum]
  by_cases hω : ω ∈ f.support.image (Finsupp.weight (pairW l j))
  · rw [Finset.sum_eq_single ω]
    · exact weightedHomogeneousComponent_self_of_isWH_ring
        (lccomp_colAddGen_homog l j ω _ (weightedHomogeneousComponent_isWeightedHomogeneous ω f))
    · intro b _ hb
      exact weightedHomogeneousComponent_eq_zero_of_ne_isWH
        (lccomp_colAddGen_homog l j b _ (weightedHomogeneousComponent_isWeightedHomogeneous b f))
        (Ne.symm hb)
    · intro h
      exact absurd hω h
  · rw [Finset.sum_eq_zero]
    · have h0 : weightedHomogeneousComponent (pairW l j) ω f = 0 := by
        ext d
        rw [coeff_weightedHomogeneousComponent, coeff_zero]
        split_ifs with h
        · by_contra hne
          exact hω (h ▸ Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))
        · rfl
      rw [h0, map_zero]
    · intro b hb
      refine weightedHomogeneousComponent_eq_zero_of_ne_isWH
        (lccomp_colAddGen_homog l j b _ (weightedHomogeneousComponent_isWeightedHomogeneous b f)) ?_
      rintro rfl
      exact hω hb

/- English proof (translation)
Rewrite using `[degreeOf_le_iff]`. Introduce `m hm`. Apply `monomial_le_degreeOf i` to reduce the goal to its premises. Rewrite `hm` using `[mem_support_iff, coeff_weightedHomogeneousComponent]`. Use `split_ifs at hm`.

Conclude with `mem_support_iff.mpr hm`. Conclude with `absurd rfl hm`.
-/
theorem lccomp_degreeOf_component_le {R : Type*} [CommRing R] {σ M : Type*} [AddCommMonoid M]
    (w : σ → M) (ω : M) (p : MvPolynomial σ R) (i : σ) :
    degreeOf i (weightedHomogeneousComponent w ω p) ≤ degreeOf i p := by
  classical
  rw [degreeOf_le_iff]
  intro m hm
  apply monomial_le_degreeOf i
  rw [mem_support_iff, coeff_weightedHomogeneousComponent] at hm
  split_ifs at hm
  · exact mem_support_iff.mpr hm
  · exact absurd rfl hm

end Formalism.GradedWeylDivisibility
