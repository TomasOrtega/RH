import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ColumnWordReductionOfFour

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Kit

/- English proof (translation)
Take `⟨t, F', G', rfl, rfl⟩` from `exists_finset_letters F G`. Establish `hf : Function.Injective (fun i : {x // x ∈ t} => (i : ι))` using `Subtype.val_injective`. Establish `T` using `fun A => Formalism.MainNotions.SelectionLemmas.valuation_lowest_degree_rename R {x // x ∈ t} ι (fun i : {x // x ∈ t} => (i : ι)) n LL S A hf`. Take `⟨v1, v2, v3, v4, -, -⟩` from `h R {x // x ∈ t} (⟨fun i : {x // x ∈ t} => LL.vec i⟩ : Letters {x // x ∈ t}) n ((fun i : {x // x ∈ t} => (i : ι)) ⁻¹' S)`. Rewrite using `[← map_mul, ← map_add, (T _).1, (T _).1, (T _).1, (T _).1, (T _).2, (T _).2, (T _).2, (T _).2]`.

Conclude with `⟨v1 _ _, v2 _ _, v3 _ _, v4 _ _⟩`.
-/
theorem valuation_lambda_field_properties (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) (R : Type) [Field R] (ι : Type) (n : ℕ) [NeZero n]
    (LL : Letters ι) (S : Set ι) (F G : MvPolynomial (ι × Fin n) R) :
    valS LL S (F * G) = valS LL S F + valS LL S G ∧ min (valS LL S F) (valS LL S G) ≤ valS LL S (F + G) ∧
      lam1S LL S (F * G) = lam1S LL S F + lam1S LL S G ∧
      lam1S LL S (F + G) ≤ max (lam1S LL S F) (lam1S LL S G) := by
  obtain ⟨t, F', G', rfl, rfl⟩ := exists_finset_letters F G
  have hf : Function.Injective (fun i : {x // x ∈ t} => (i : ι)) := Subtype.val_injective
  have T := fun A => Formalism.MainNotions.SelectionLemmas.valuation_lowest_degree_rename R {x // x ∈ t} ι (fun i : {x // x ∈ t} => (i : ι)) n LL S A hf
  obtain ⟨v1, v2, v3, v4, -, -⟩ := h R {x // x ∈ t} (⟨fun i : {x // x ∈ t} => LL.vec i⟩ : Letters {x // x ∈ t}) n
    ((fun i : {x // x ∈ t} => (i : ι)) ⁻¹' S)
  rw [← map_mul, ← map_add, (T _).1, (T _).1, (T _).1, (T _).1, (T _).2, (T _).2, (T _).2, (T _).2]
  exact ⟨v1 _ _, v2 _ _, v3 _ _, v4 _ _⟩

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ}

/- English proof (translation)
Establish `: LaurentPolynomial.C a = LaurentPolynomial.C a * LaurentPolynomial.T 0` using `by simp`. Rewrite using `[this]`. Conclude with `SuppIn.C_mul_T _ _ h0`.
-/
theorem suppIn_one (s : Set ℤ) (h0 : (0 : ℤ) ∈ s) (a : GLCoord R n) : SuppIn s (LaurentPolynomial.C a) := by
  have : LaurentPolynomial.C a = LaurentPolynomial.C a * LaurentPolynomial.T 0 := by simp
  rw [this]; exact SuppIn.C_mul_T _ _ h0

/- English proof (translation)
Use `sDegs_subset LL S j _ _ fun m => ?_` and prove the remaining obligations. Establish `: twistSub LL S j (C c : MvPolynomial (ι × Fin n) R) = C (coefL R n c)` using `by simp [twistSub]`. Rewrite using `[this, coeff_C]`. Use `split_ifs`. Establish `h2 : coefL R n c = LaurentPolynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (C c))` using `rfl`.

Rewrite using `[h2]`. Conclude with `suppIn_one (R := R) (n := n) ({0} : Set ℤ) (Set.mem_singleton 0) _`. Conclude with `SuppIn.zero _`.
-/
theorem sDegs_C (LL : Letters ι) (S : Set ι) (j : Fin n) (c : R) :
    ∀ k ∈ sDegs LL S j (C c : MvPolynomial (ι × Fin n) R), k ∈ ({0} : Set ℤ) := by
  classical
  refine sDegs_subset LL S j _ _ fun m => ?_
  have : twistSub LL S j (C c : MvPolynomial (ι × Fin n) R) = C (coefL R n c) := by simp [twistSub]
  rw [this, coeff_C]
  split_ifs
  · have h2 : coefL R n c =
        LaurentPolynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (C c)) := rfl
    rw [h2]; exact suppIn_one (R := R) (n := n) ({0} : Set ℤ) (Set.mem_singleton 0) _
  · exact SuppIn.zero _

/- English proof (translation)
Use `sDegs_subset LL S j _ _ fun m => ?_` and prove the remaining obligations. Establish `: twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) = X v` using `by simp [twistSub, hv]`. Rewrite using `[this, coeff_X]`. Use `split_ifs`. Establish `h1 : (1 : GLLaurent R n) = LaurentPolynomial.C 1` using `by simp`.

Rewrite using `[h1]`. Conclude with `suppIn_one (R := R) (n := n) ({0} : Set ℤ) (Set.mem_singleton 0) _`. Conclude with `SuppIn.zero _`.
-/
theorem sDegs_X_out (LL : Letters ι) (S : Set ι) (j : Fin n) (v : ι × Fin n) (hv : v.1 ∉ S) :
    ∀ k ∈ sDegs LL S j (X v : MvPolynomial (ι × Fin n) R), k ∈ ({0} : Set ℤ) := by
  classical
  refine sDegs_subset LL S j _ _ fun m => ?_
  have : twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) = X v := by simp [twistSub, hv]
  rw [this, coeff_X]
  split_ifs
  · have h1 : (1 : GLLaurent R n) = LaurentPolynomial.C 1 := by simp
    rw [h1]; exact suppIn_one (R := R) (n := n) ({0} : Set ℤ) (Set.mem_singleton 0) _
  · exact SuppIn.zero _

end Kit

section Kit2

variable (D : Formalism.BasicNotions.D7) (hV : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) {R : Type} [Field R] {n : ℕ} [NeZero n] (S : Set ℤ)

include hV

/- English proof (translation)
Rewrite using `[(valuation_lambda_field_properties D hV R ℤ n LZ S P Q).1, WithTop.coe_add]`. Conclude with `add_le_add hP hQ`.
-/
theorem vg_mul {a b : ℤ} {P Q : MvPolynomial (ℤ × Fin n) R} (hP : (a : WithTop ℤ) ≤ valS LZ S P)
    (hQ : (b : WithTop ℤ) ≤ valS LZ S Q) : ((a + b : ℤ) : WithTop ℤ) ≤ valS LZ S (P * Q) := by
  rw [(valuation_lambda_field_properties D hV R ℤ n LZ S P Q).1, WithTop.coe_add]; exact add_le_add hP hQ

/- English proof (translation)
Rewrite using `[(valuation_lambda_field_properties D hV R ℤ n LZ S P Q).2.2.1, WithBot.coe_add]`. Conclude with `add_le_add hP hQ`.
-/
theorem lg_mul {a b : ℤ} {P Q : MvPolynomial (ℤ × Fin n) R} (hP : lam1S LZ S P ≤ (a : WithBot ℤ))
    (hQ : lam1S LZ S Q ≤ (b : WithBot ℤ)) : lam1S LZ S (P * Q) ≤ ((a + b : ℤ) : WithBot ℤ) := by
  rw [(valuation_lambda_field_properties D hV R ℤ n LZ S P Q).2.2.1, WithBot.coe_add]; exact add_le_add hP hQ

omit hV in
/- English proof (translation)
The claim follows from `(le_valS_iff LZ S _ 0).mpr fun k hk => by have := sDegs_C LZ S _ c k hk simp at this; omega`.
-/
theorem vg_C (c : R) : ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (C c : MvPolynomial (ℤ × Fin n) R) :=
  (le_valS_iff LZ S _ 0).mpr fun k hk => by
    have := sDegs_C LZ S _ c k hk
    simp at this; omega

omit hV in
/- English proof (translation)
The claim follows from `(lowest_degree_le_iff LZ S _ 0).mpr fun k hk => by have := sDegs_C LZ S _ c k hk simp at this; omega`.
-/
theorem lg_C (c : R) : lam1S LZ S (C c : MvPolynomial (ℤ × Fin n) R) ≤ ((0 : ℤ) : WithBot ℤ) :=
  (lowest_degree_le_iff LZ S _ 0).mpr fun k hk => by
    have := sDegs_C LZ S _ c k hk
    simp at this; omega

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using vg_C (n := n) S (1 : R)`. Consider the case `succ m ih`. Rewrite using `[pow_succ]`. Use `vg_mul D hV S ih hP` as an intermediate fact.

Establish `e : (m : ℤ) * a + a = ((m + 1 : ℕ) : ℤ) * a` using `by push_cast; ring`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem vg_pow {a : ℤ} {P : MvPolynomial (ℤ × Fin n) R} (hP : (a : WithTop ℤ) ≤ valS LZ S P) (m : ℕ) :
    (((m : ℤ) * a : ℤ) : WithTop ℤ) ≤ valS LZ S (P ^ m) := by
  induction m with
  | zero => simpa using vg_C (n := n) S (1 : R)
  | succ m ih =>
    rw [pow_succ]
    have := vg_mul D hV S ih hP
    have e : (m : ℤ) * a + a = ((m + 1 : ℕ) : ℤ) * a := by push_cast; ring
    rwa [e] at this

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using lg_C (n := n) S (1 : R)`. Consider the case `succ m ih`. Rewrite using `[pow_succ]`. Use `lg_mul D hV S ih hP` as an intermediate fact.

Establish `e : (m : ℤ) * a + a = ((m + 1 : ℕ) : ℤ) * a` using `by push_cast; ring`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem lg_pow {a : ℤ} {P : MvPolynomial (ℤ × Fin n) R} (hP : lam1S LZ S P ≤ (a : WithBot ℤ)) (m : ℕ) :
    lam1S LZ S (P ^ m) ≤ (((m : ℤ) * a : ℤ) : WithBot ℤ) := by
  induction m with
  | zero => simpa using lg_C (n := n) S (1 : R)
  | succ m ih =>
    rw [pow_succ]
    have := lg_mul D hV S ih hP
    have e : (m : ℤ) * a + a = ((m + 1 : ℕ) : ℤ) * a := by push_cast; ring
    rwa [e] at this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using vg_C (n := n) S (1 : R)`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.prod_insert hi]`. Conclude with `vg_mul D hV S (h i (Finset.mem_insert_self i s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem vg_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ℤ × Fin n) R) (a : κ → ℤ)
    (h : ∀ i ∈ s, (a i : WithTop ℤ) ≤ valS LZ S (f i)) :
    ((∑ i ∈ s, a i : ℤ) : WithTop ℤ) ≤ valS LZ S (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vg_C (n := n) S (1 : R)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact vg_mul D hV S (h i (Finset.mem_insert_self i s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using lg_C (n := n) S (1 : R)`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.prod_insert hi]`. Conclude with `lg_mul D hV S (h i (Finset.mem_insert_self i s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem lg_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ℤ × Fin n) R) (a : κ → ℤ)
    (h : ∀ i ∈ s, lam1S LZ S (f i) ≤ (a i : WithBot ℤ)) :
    lam1S LZ S (∏ i ∈ s, f i) ≤ ((∑ i ∈ s, a i : ℤ) : WithBot ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lg_C (n := n) S (1 : R)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact lg_mul D hV S (h i (Finset.mem_insert_self i s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [valS, sDegs]`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi]`. Conclude with `le_trans (le_min (h i (Finset.mem_insert_self i s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))) (valuation_lambda_field_properties D hV R ℤ n LZ S _ _).2.1`.
-/
theorem vg_sum {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ℤ × Fin n) R) (a : ℤ)
    (h : ∀ i ∈ s, (a : WithTop ℤ) ≤ valS LZ S (f i)) : (a : WithTop ℤ) ≤ valS LZ S (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [valS, sDegs]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact le_trans (le_min (h i (Finset.mem_insert_self i s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk)))
      (valuation_lambda_field_properties D hV R ℤ n LZ S _ _).2.1

omit hV in
/- English proof (translation)
Distinguish the cases in `hv : v.1 ∈ S`. Establish `hc` using `coord_clauses (R := R) LZ S v.1 hv v.2`. Distinguish the cases in `he : Even v.1`. Rewrite using `[if_pos he]; exact (hc.1 (by simp [LZ, he])).1`. Rewrite using `[if_neg he]; exact (hc.2 (by simp [LZ, he])).1`.

Use `(le_valS_iff LZ S _ _).mpr fun k hk => ?_` and prove the remaining obligations. Use `sDegs_X_out (R := R) LZ S _ v hv k hk` as an intermediate fact. Simplify using `at this`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem vg_X (v : ℤ × Fin n) :
    (((if Even v.1 then 0 else -1 : ℤ)) : WithTop ℤ) ≤ valS LZ S (X v : MvPolynomial (ℤ × Fin n) R) := by
  by_cases hv : v.1 ∈ S
  · have hc := coord_clauses (R := R) LZ S v.1 hv v.2
    by_cases he : Even v.1
    · rw [if_pos he]; exact (hc.1 (by simp [LZ, he])).1
    · rw [if_neg he]; exact (hc.2 (by simp [LZ, he])).1
  · refine (le_valS_iff LZ S _ _).mpr fun k hk => ?_
    have := sDegs_X_out (R := R) LZ S _ v hv k hk
    simp at this
    split_ifs <;> omega

omit hV in
/- English proof (translation)
Distinguish the cases in `hv : v.1 ∈ S`. Establish `hc` using `coord_clauses (R := R) LZ S v.1 hv v.2`. Distinguish the cases in `he : Even v.1`. Rewrite using `[if_pos he]; exact (hc.1 (by simp [LZ, he])).2`. Rewrite using `[if_neg he]; exact (hc.2 (by simp [LZ, he])).2`.

Use `(lowest_degree_le_iff LZ S _ _).mpr fun k hk => ?_` and prove the remaining obligations. Use `sDegs_X_out (R := R) LZ S _ v hv k hk` as an intermediate fact. Simplify using `at this`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem lg_X (v : ℤ × Fin n) :
    lam1S LZ S (X v : MvPolynomial (ℤ × Fin n) R) ≤ (((if Even v.1 then 1 else 0 : ℤ)) : WithBot ℤ) := by
  by_cases hv : v.1 ∈ S
  · have hc := coord_clauses (R := R) LZ S v.1 hv v.2
    by_cases he : Even v.1
    · rw [if_pos he]; exact (hc.1 (by simp [LZ, he])).2
    · rw [if_neg he]; exact (hc.2 (by simp [LZ, he])).2
  · refine (lowest_degree_le_iff LZ S _ _).mpr fun k hk => ?_
    have := sDegs_X_out (R := R) LZ S _ v hv k hk
    simp at this
    split_ifs <;> omega

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `vg_sum D hV S _ _ 0 fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def, zsmul_eq_mul]`. Establish `h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (ℤ × Fin n) R) = C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R)`. Simplify using the standard rewrite rules.

Rewrite using `[h1]`. Establish `h2` using `vg_prod D hV S Finset.univ (fun i : Fin n => (Matrix.of fun a b : Fin n => (X (y a, b) : MvPolynomial (ℤ × Fin n) R)) (σ i) i) (fun _ => 0) (fun i _ => by`. Use `vg_X (R := R) S (y (σ i), i)` as an intermediate fact. Simplify `this)` using `[hy (σ i)]`. Use `vg_mul D hV S (vg_C (n := n) S (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R)) h2` as an intermediate fact.

Simplify using `using this`.
-/
theorem vg_det (y : Fin n → ℤ) (hy : ∀ i, Even (y i)) :
    ((0 : ℤ) : WithTop ℤ) ≤
      valS LZ S (Matrix.det (Matrix.of fun a b : Fin n => (X (y a, b) : MvPolynomial (ℤ × Fin n) R))) := by
  rw [Matrix.det_apply]
  refine vg_sum D hV S _ _ 0 fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  have h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (ℤ × Fin n) R) = C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) := by
    simp
  rw [h1]
  have h2 := vg_prod D hV S Finset.univ
    (fun i : Fin n => (Matrix.of fun a b : Fin n => (X (y a, b) : MvPolynomial (ℤ × Fin n) R)) (σ i) i) (fun _ => 0)
    (fun i _ => by
      have := vg_X (R := R) S (y (σ i), i)
      simpa [hy (σ i)] using this)
  have := vg_mul D hV S (vg_C (n := n) S (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R)) h2
  simpa using this

end Kit2

end Formalism.MainNotions.SelectionLemmas.Pf
