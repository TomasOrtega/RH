import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

/- English proof (translation)
Simplify using `[midI]`.
-/
theorem midI_val (r : ℕ) (j : Fin r) : (midI r j).val = j.val + 1 := by
  simp [midI]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[midI_val, midI_val]`. Conclude with `Fin.ext (by omega)`.

Introduce and unpack `rfl`. Both sides reduce to the same expression.
-/
theorem midI_inj (r : ℕ) (i j : Fin r) : midI r i = midI r j ↔ i = j := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rw [midI_val, midI_val] at this
    exact Fin.ext (by omega)
  · rintro rfl; rfl

/- English proof (translation)
Rewrite using `[Fin.lt_iff_val_lt_val, midI_val, midI_val]`. Use `Fin.lt_iff_val_lt_val.mp h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem midI_lt (r : ℕ) {i j : Fin r} (h : i < j) : midI r i < midI r j := by
  rw [Fin.lt_iff_val_lt_val, midI_val, midI_val]
  have := Fin.lt_iff_val_lt_val.mp h
  omega

/- English proof (translation)
Rewrite using `[Fin.lt_def, midI_val]`. Simplify using the standard rewrite rules.
-/
theorem midI_pos (r : ℕ) (j : Fin r) : (0 : Fin (r + 1 + 1)) < midI r j := by
  rw [Fin.lt_def, midI_val]
  simp

/- English proof (translation)
Establish `hv` using `midI_val r j`. Establish `hj` using `j.isLt`. Unfold `midOf`. Rewrite using `[dif_pos (by rw [hv]; exact ⟨Nat.succ_pos _, by omega⟩)]`. Use `congr 1`.
-/
theorem midOf_midI (r : ℕ) (j : Fin r) : midOf (midI r j) = some j := by
  have hv := midI_val r j
  have hj := j.isLt
  unfold midOf
  rw [dif_pos (by rw [hv]; exact ⟨Nat.succ_pos _, by omega⟩)]
  congr 1

/- English proof (translation)
Establish `ht` using `t.isLt`. Distinguish the cases in `h : 0 < t.val ∧ t.val < r + 1`. Use `left`. Use `⟨⟨t.val - 1, by omega⟩, ?_⟩` and prove the remaining obligations. Use `ext`.

Rewrite using `[midI_val]`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Use `right`. Use `⟨by unfold midOf; rw [dif_neg h], ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h0 : t.val = 0`. Use `left`. Conclude with `Fin.ext (by simp [h0])`. Use `right`. Conclude with `Fin.ext (by simp; omega)`.
-/
theorem midOf_cases {r : ℕ} (t : Fin (r + 1 + 1)) :
    (∃ j, t = midI r j) ∨ (midOf t = none ∧ (t = 0 ∨ t = Fin.last (r + 1))) := by
  have ht := t.isLt
  by_cases h : 0 < t.val ∧ t.val < r + 1
  · left
    refine ⟨⟨t.val - 1, by omega⟩, ?_⟩
    ext
    rw [midI_val]
    dsimp only
    omega
  · right
    refine ⟨by unfold midOf; rw [dif_neg h], ?_⟩
    by_cases h0 : t.val = 0
    · left
      exact Fin.ext (by simp [h0])
    · right
      exact Fin.ext (by simp; omega)

/- English proof (translation)
Introduce and unpack `rfl`. Rewrite `h` using `[midOf_midI]`. Conclude with `Option.some_ne_none _ h`.
-/
theorem midOf_none_ne {r : ℕ} {t : Fin (r + 1 + 1)} (h : midOf t = none) (j : Fin r) : midI r j ≠ t := by
  rintro rfl
  rw [midOf_midI] at h
  exact Option.some_ne_none _ h

/- English proof (translation)
Simplify using `only [subY, aeval_X, midOf_midI]`.
-/
theorem subY_X_mid (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (j : Fin r) :
    subY A r (X (a, midI r j)) = ∑ i : Fin r, C (X (i, j)) * X (a, midI r i) := by
  simp only [subY, aeval_X, midOf_midI]

/- English proof (translation)
Simplify using `only [subY, aeval_X, h]`.
-/
theorem subY_X_none (A : Type) [CommRing A] (r : ℕ) (a t : Fin (r + 1 + 1)) (h : midOf t = none) :
    subY A r (X (a, t)) = X (a, t) := by
  simp only [subY, aeval_X, h]

/- English proof (translation)
Simplify using `[subY]`.
-/
theorem subY_C (A : Type) [CommRing A] (r : ℕ) (a : A) : subY A r (C a) = C (C a) := by
  simp [subY]

section MAH

variable {R S1 S2 σ : Type} [CommRing R] [CommRing S1] [CommRing S2] [Algebra R S1] [Algebra R S2]

/- English proof (translation)
Use `show coeff u (map (f : S1 →+* S2) p) = _`. Rewrite using `[coeff_map]`. Both sides reduce to the same expression.
-/
theorem mAH_coeff (f : S1 →ₐ[R] S2) (p : MvPolynomial σ S1) (u : σ →₀ ℕ) : coeff u (mapAlgHom f p) = f (coeff u p) := by
  show coeff u (map (f : S1 →+* S2) p) = _
  rw [coeff_map]
  rfl

/- English proof (translation)
Use `show map (f : S1 →+* S2) (C b) = _`. Rewrite using `[map_C]`. Both sides reduce to the same expression.
-/
theorem mAH_C (f : S1 →ₐ[R] S2) (b : S1) : mapAlgHom f (C b : MvPolynomial σ S1) = C (f b) := by
  show map (f : S1 →+* S2) (C b) = _
  rw [map_C]
  rfl

/- English proof (translation)
Use `show map (f : S1 →+* S2) (X w) = _`. Rewrite using `[map_X]`.
-/
theorem mAH_X (f : S1 →ₐ[R] S2) (w : σ) : mapAlgHom f (X w : MvPolynomial σ S1) = X w := by
  show map (f : S1 →+* S2) (X w) = _
  rw [map_X]

end MAH

/- English proof (translation)
Rewrite using `[subY_X_mid]`. Simplify using `only [map_sum, map_mul, mAH_C, mAH_X]`.
-/
theorem mAH_subY_mid {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (r : ℕ)
    (f : MvPolynomial (Fin r × Fin r) A →ₐ[A] S) (a : Fin (r + 1 + 1)) (j : Fin r) :
    mapAlgHom f (subY A r (X (a, midI r j))) = ∑ i : Fin r, C (f (X (i, j))) * X (a, midI r i) := by
  rw [subY_X_mid]
  simp only [map_sum, map_mul, mAH_C, mAH_X]

/- English proof (translation)
Rewrite using `[subY_X_none A r a t h, mAH_X]`.
-/
theorem mAH_subY_none {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (r : ℕ)
    (f : MvPolynomial (Fin r × Fin r) A →ₐ[A] S) (a t : Fin (r + 1 + 1)) (h : midOf t = none) :
    mapAlgHom f (subY A r (X (a, t))) = X (a, t) := by
  rw [subY_X_none A r a t h, mAH_X]

section Coef

variable {A : Type} [CommRing A] {r : ℕ} {σ : Type}

def CoefHom (μ : Fin r → ℕ) (h : MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)) : Prop :=
  ∀ u, IsWeightedHomogeneous (colW r r) (coeff u h) μ

/- English proof (translation)
Introduce `u`. Rewrite using `[coeff_sum]`. Conclude with `IsWeightedHomogeneous.sum _ _ _ (fun i hi => h i hi u)`.
-/
theorem CoefHom.sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)) (μ : Fin r → ℕ)
    (h : ∀ i ∈ s, CoefHom μ (f i)) : CoefHom μ (∑ i ∈ s, f i) := by
  intro u
  rw [coeff_sum]
  exact IsWeightedHomogeneous.sum _ _ _ (fun i hi => h i hi u)

/- English proof (translation)
Introduce `u`. Rewrite using `[coeff_mul]`. Conclude with `IsWeightedHomogeneous.sum _ _ _ (fun x _ => (a x.1).mul (b x.2))`.
-/
theorem CoefHom.mul {μ μ' : Fin r → ℕ} {h1 h2 : MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)}
    (a : CoefHom μ h1) (b : CoefHom μ' h2) : CoefHom (μ + μ') (h1 * h2) := by
  classical
  intro u
  rw [coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ (fun x _ => (a x.1).mul (b x.2))

/- English proof (translation)
Introduce `u`. Rewrite using `[coeff_C]`. Use `split_ifs`. Conclude with `hb`. Conclude with `isWeightedHomogeneous_zero _ _ _`.
-/
theorem CoefHom.ofC {μ : Fin r → ℕ} {b : MvPolynomial (Fin r × Fin r) A} (hb : IsWeightedHomogeneous (colW r r) b μ) :
    CoefHom (σ := σ) μ (C b) := by
  classical
  intro u
  rw [coeff_C]
  split_ifs
  · exact hb
  · exact isWeightedHomogeneous_zero _ _ _

/- English proof (translation)
Introduce `u`. Rewrite using `[coeff_X']`. Use `split_ifs`. Conclude with `isWeightedHomogeneous_one _ _`. Conclude with `isWeightedHomogeneous_zero _ _ _`.
-/
theorem CoefHom.ofX (w : σ) : CoefHom (A := A) (r := r) 0 (X w) := by
  classical
  intro u
  rw [coeff_X']
  split_ifs
  · exact isWeightedHomogeneous_one _ _
  · exact isWeightedHomogeneous_zero _ _ _

/- English proof (translation)
Introduce `u`. Rewrite using `[coeff_one]`. Use `split_ifs`. Conclude with `isWeightedHomogeneous_one _ _`. Introduce `d hd`.

Simplify using `at hd`.
-/
theorem CoefHom.one : CoefHom (A := A) (r := r) (σ := σ) 0 1 := by
  classical
  intro u
  rw [coeff_one]
  split_ifs
  · exact isWeightedHomogeneous_one _ _
  · intro d hd
    simp at hd

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero, zero_smul]`. Conclude with `CoefHom.one`. Consider the case `succ n ih`.

Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `ih.mul a`.
-/
theorem CoefHom.pow {μ : Fin r → ℕ} {h : MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)} (a : CoefHom μ h) (n : ℕ) :
    CoefHom (n • μ) (h ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    exact CoefHom.one
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul a

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.prod_empty, Finset.sum_empty]`. Conclude with `CoefHom.one`. Consider the case `insert i s hi ih`.

Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi]`. Conclude with `(h i (Finset.mem_insert_self i s)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem CoefHom.prod {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial (Fin r × Fin r) A))
    (μ : ι → Fin r → ℕ) (h : ∀ i ∈ s, CoefHom (μ i) (f i)) : CoefHom (∑ i ∈ s, μ i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact CoefHom.one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

end Coef

/- English proof (translation)
Take `⟨a, t⟩` from `w`. Break down `midOf_cases t with ⟨j, rfl⟩ | ⟨hn, -⟩` into its components or cases. Rewrite using `[subY_X_mid]`. Establish `hf : (fun j' : Fin r => colW (r + 1 + 1) (r + 1 + 1) (a, midI r j) (midI r j')) = colW r r (j, j)`. Use function extensionality and compare the values at `j'`.

Simplify using `only [colW, Pi.single_apply, midI_inj]`. Rewrite using `[hf]`. Apply `CoefHom.sum` to reduce the goal to its premises. Introduce `i _`. Establish `h` using `(CoefHom.ofC (σ := Fin (r + 1 + 1) × Fin (r + 1 + 1)) (isWeightedHomogeneous_X A (colW r r) (i, j))).mul (CoefHom.ofX (A := A) (r := r) (a, midI r i))`.

Rewrite `h` using `[add_zero]`. Conclude with `h`. Rewrite using `[subY_X_none _ _ _ _ hn]`. Establish `hf : (fun j' : Fin r => colW (r + 1 + 1) (r + 1 + 1) (a, t) (midI r j')) = 0`. Use function extensionality and compare the values at `j'`.

Simplify using `[colW, Pi.single_apply, midOf_none_ne hn j']`. Rewrite using `[hf]`. Conclude with `CoefHom.ofX _`.
-/
theorem subY_gen_coefHom (A : Type) [CommRing A] (r : ℕ) (w : Fin (r + 1 + 1) × Fin (r + 1 + 1)) :
    CoefHom (fun j => colW (r + 1 + 1) (r + 1 + 1) w (midI r j)) (subY A r (X w)) := by
  obtain ⟨a, t⟩ := w
  rcases midOf_cases t with ⟨j, rfl⟩ | ⟨hn, -⟩
  · rw [subY_X_mid]
    have hf : (fun j' : Fin r => colW (r + 1 + 1) (r + 1 + 1) (a, midI r j) (midI r j')) = colW r r (j, j) := by
      funext j'
      simp only [colW, Pi.single_apply, midI_inj]
    rw [hf]
    apply CoefHom.sum
    intro i _
    have h := (CoefHom.ofC (σ := Fin (r + 1 + 1) × Fin (r + 1 + 1))
      (isWeightedHomogeneous_X A (colW r r) (i, j))).mul (CoefHom.ofX (A := A) (r := r) (a, midI r i))
    rw [add_zero] at h
    exact h
  · rw [subY_X_none _ _ _ _ hn]
    have hf : (fun j' : Fin r => colW (r + 1 + 1) (r + 1 + 1) (a, t) (midI r j')) = 0 := by
      funext j'
      simp [colW, Pi.single_apply, midOf_none_ne hn j']
    rw [hf]
    exact CoefHom.ofX _

/- English proof (translation)
Rewrite using `[v.as_sum, map_sum]`. Apply `CoefHom.sum` to reduce the goal to its premises. Introduce `m hm`. Establish `hw : Finsupp.weight (colW (r + 1 + 1) (r + 1 + 1)) m = ν` using `hv (mem_support_iff.mp hm)`. Rewrite using `[monomial_eq, map_mul, subY_C, Finsupp.prod, map_prod]`.

Establish `hP : CoefHom (∑ w ∈ m.support, m w • fun j => colW (r + 1 + 1) (r + 1 + 1) w (midI r j)) (∏ w ∈ m.support, subY A r (X w ^ m w))`. Apply `CoefHom.prod` to reduce the goal to its premises. Introduce `w _`. Rewrite using `[map_pow]`. Conclude with `(subY_gen_coefHom A r w).pow _`.

Establish `hC : CoefHom (σ` using `Fin (r + 1 + 1) × Fin (r + 1 + 1)) (0 : Fin r → ℕ) (C (C (coeff m v))) := by`. Apply `CoefHom.ofC` to reduce the goal to its premises. Introduce `d hd`. Rewrite `hd` using `[coeff_C]`. Use `split_ifs at hd with h0`.

Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Conclude with `absurd rfl hd`. Establish `h` using `hC.mul hP`. Rewrite `h` using `[zero_add]`.

Establish `hsum : (∑ w ∈ m.support, m w • fun j => colW (r + 1 + 1) (r + 1 + 1) w (midI r j)) = fun j => ν (midI r j)`. Use function extensionality and compare the values at `j`. Rewrite using `[← hw]`. Simplify using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Rewrite `h` using `[hsum]`.

Conclude with `h`.
-/
theorem subY_coefHom (A : Type) [CommRing A] (r : ℕ) (ν : Fin (r + 1 + 1) → ℕ)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A)
    (hv : IsWeightedHomogeneous (colW (r + 1 + 1) (r + 1 + 1)) v ν) :
    CoefHom (fun j => ν (midI r j)) (subY A r v) := by
  classical
  rw [v.as_sum, map_sum]
  apply CoefHom.sum
  intro m hm
  have hw : Finsupp.weight (colW (r + 1 + 1) (r + 1 + 1)) m = ν := hv (mem_support_iff.mp hm)
  rw [monomial_eq, map_mul, subY_C, Finsupp.prod, map_prod]
  have hP : CoefHom (∑ w ∈ m.support, m w • fun j => colW (r + 1 + 1) (r + 1 + 1) w (midI r j))
      (∏ w ∈ m.support, subY A r (X w ^ m w)) := by
    apply CoefHom.prod
    intro w _
    rw [map_pow]
    exact (subY_gen_coefHom A r w).pow _
  have hC : CoefHom (σ := Fin (r + 1 + 1) × Fin (r + 1 + 1)) (0 : Fin r → ℕ) (C (C (coeff m v))) := by
    apply CoefHom.ofC
    intro d hd
    rw [coeff_C] at hd
    split_ifs at hd with h0
    · subst h0
      simp
    · exact absurd rfl hd
  have h := hC.mul hP
  rw [zero_add] at h
  have hsum : (∑ w ∈ m.support, m w • fun j => colW (r + 1 + 1) (r + 1 + 1) w (midI r j)) =
      fun j => ν (midI r j) := by
    funext j
    rw [← hw]
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  rw [hsum] at h
  exact h

/- English proof (translation)
Set `Φ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A) →ₐ[A] MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A)` to `mapAlgHom (colAddGen A l j)`. Set `Ψ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A) →ₐ[A] MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A)` to `mapAlgHom (rename some)`. Set `θ : MvPolynomial (Option (Fin (r + 1 + 1) × Fin (r + 1 + 1))) A →ₐ[A] MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A)` to `aeval fun o => Option.elim o (C (X none)) fun w => Ψ (subY A r (X w))`. Establish `hθn : θ (X none) = C (X none)`. Simplify using `[θ]`.

Establish `hθs : ∀ w, θ (X (some w)) = Ψ (subY A r (X w))` using `fun w => by`. Simplify using `[θ]`. Establish `h1 : Φ.comp (subY A r) = θ.comp (colAddGen A (midI r l) (midI r j))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, t⟩`.

Simplify using `only [AlgHom.comp_apply, colAddGen_X]`. Break down `midOf_cases t with ⟨j', rfl⟩ | ⟨hn, -⟩` into its components or cases. Rewrite using `[mAH_subY_mid]`. Distinguish the cases in `hj : j' = j`. Substitute `hj` using the available equality.

Rewrite using `[if_pos rfl, map_add, map_mul, hθn, hθs, hθs, mAH_subY_mid, mAH_subY_mid, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [colAddGen_X, if_true, rename_X, map_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (fun h => hj ((midI_inj r j' j).mp h)), hθs, mAH_subY_mid]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [colAddGen_X, if_neg hj, rename_X]`. Rewrite using `[if_neg (midOf_none_ne hn j).symm, hθs, mAH_subY_none _ _ _ _ hn, mAH_subY_none _ _ _ _ hn]`. Establish `h2 : Ψ.comp (subY A r) = θ.comp (rename some)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises.

Introduce `w`. Simplify using `only [AlgHom.comp_apply, rename_X, hθs]`. Establish `h3 : Φ (subY A r v) = Ψ (subY A r v)`. Establish `e1` using `congrArg (fun F => F v) h1`. Establish `e2` using `congrArg (fun F => F v) h2`.

Simplify using `only [AlgHom.comp_apply] at e1 e2`. Rewrite using `[e1, e2, hv _ _ (midI_lt r hlj)]`. Establish `h4` using `congrArg (coeff u) h3`. Simplify using `only [Φ, Ψ, mAH_coeff] at h4`. Conclude with `h4`.
-/
theorem subY_inv (A : Type) [CommRing A] (r : ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A)
    (hv : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen A l j v = rename some v) (l j : Fin r) (hlj : l < j)
    (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ) :
    colAddGen A l j (coeff u (subY A r v)) = rename some (coeff u (subY A r v)) := by
  classical
  let Φ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A) →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A) :=
    mapAlgHom (colAddGen A l j)
  let Ψ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A) →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A) :=
    mapAlgHom (rename some)
  let θ : MvPolynomial (Option (Fin (r + 1 + 1) × Fin (r + 1 + 1))) A →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A) :=
    aeval fun o => Option.elim o (C (X none)) fun w => Ψ (subY A r (X w))
  have hθn : θ (X none) = C (X none) := by
    simp [θ]
  have hθs : ∀ w, θ (X (some w)) = Ψ (subY A r (X w)) := fun w => by
    simp [θ]
  have h1 : Φ.comp (subY A r) = θ.comp (colAddGen A (midI r l) (midI r j)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, t⟩
    simp only [AlgHom.comp_apply, colAddGen_X]
    rcases midOf_cases t with ⟨j', rfl⟩ | ⟨hn, -⟩
    · rw [mAH_subY_mid]
      by_cases hj : j' = j
      · subst hj
        rw [if_pos rfl, map_add, map_mul, hθn, hθs, hθs, mAH_subY_mid, mAH_subY_mid, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [colAddGen_X, if_true, rename_X, map_add, map_mul]
        ring
      · rw [if_neg (fun h => hj ((midI_inj r j' j).mp h)), hθs, mAH_subY_mid]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [colAddGen_X, if_neg hj, rename_X]
    · rw [if_neg (midOf_none_ne hn j).symm, hθs, mAH_subY_none _ _ _ _ hn, mAH_subY_none _ _ _ _ hn]
  have h2 : Ψ.comp (subY A r) = θ.comp (rename some) := by
    apply MvPolynomial.algHom_ext
    intro w
    simp only [AlgHom.comp_apply, rename_X, hθs]
  have h3 : Φ (subY A r v) = Ψ (subY A r v) := by
    have e1 := congrArg (fun F => F v) h1
    have e2 := congrArg (fun F => F v) h2
    simp only [AlgHom.comp_apply] at e1 e2
    rw [e1, e2, hv _ _ (midI_lt r hlj)]
  have h4 := congrArg (coeff u) h3
  simp only [Φ, Ψ, mAH_coeff] at h4
  exact h4

/- English proof (translation)
Introduce `A _ r ν v hv u`. Rewrite `hv`, the goal using `[lsat_mem_dualWeyl]`. Conclude with `⟨subY_coefHom A r ν v hv.1 u, fun l j hlj => subY_inv A r v hv.2 l j hlj u⟩`.
-/
theorem subCoeffP : SubCoeffP := by
  intro A _ r ν v hv u
  rw [lsat_mem_dualWeyl] at hv ⊢
  exact ⟨subY_coefHom A r ν v hv.1 u, fun l j hlj => subY_inv A r v hv.2 l j hlj u⟩

end Formalism.MainNotions.flipOneThree.Pf.QB

end
