import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SegreChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def segForm {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) (Gz : MvPolynomial (Fin (N + 1)) ℤ) : MRing ι :=
  aeval (fun j => ∏ k, (X ⟨k, E j k⟩ : MRing ι)) Gz

omit [∀ k, Fintype (ι k)] in
/- English proof (translation)
Rewrite using `[segForm, comp_aeval_apply]`. Simplify using `only [map_prod, aeval_X]`.
-/
theorem aeval_segForm {R : Type} [CommRing R] (v : (Σ k, ι k) → R) {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k))
    (Gz : MvPolynomial (Fin (N + 1)) ℤ) :
    aeval v (segForm E Gz) = aeval (fun j => ∏ k, v ⟨k, E j k⟩) Gz := by
  rw [segForm, comp_aeval_apply]
  simp only [map_prod, aeval_X]

/- English proof (translation)
Introduce `m hm k`. Establish `h1` using `h k (mem_support_iff.1 hm)`. Rewrite using `[← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[hb]`. Simplify using the standard rewrite rules.
-/
theorem isMultiHomog_of_weighted [DecidableEq K] {s : MRing ι} {n : ℕ}
    (h : ∀ k, IsWeightedHomogeneous (fun p : Σ k, ι k => if p.1 = k then 1 else 0) s n) :
    IsMultiHomog s fun _ => n := by
  intro m hm k
  have h1 := h k (mem_support_iff.1 hm)
  rw [← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

omit [∀ k, Fintype (ι k)] in
/- English proof (translation)
Establish `hseg : ∀ j, IsWeightedHomogeneous w (∏ k, (X ⟨k, E j k⟩ : MRing ι)) 1` using `fun j => by`. Establish `h` using `IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, E j k⟩ : MRing ι)) (fun k => w ⟨k, E j k⟩) fun k _ => isWeightedHomogeneous_X _ w _`. Rewrite `h` using `[hw j]`. Then use the resulting hypothesis. Rewrite using `[segForm, aeval_def, eval₂_eq']`. Use `IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_` and prove the remaining obligations.

Establish `hdeg : ∑ j, m j = n`. Rewrite using `[← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]`. Conclude with `hG (mem_support_iff.1 hm)`. Establish `h1 : IsWeightedHomogeneous w (∏ j, (∏ k, (X ⟨k, E j k⟩ : MRing ι)) ^ m j) (∑ j, m j • 1)` using `IsWeightedHomogeneous.prod _ _ _ fun j _ => (hseg j).pow _`. Establish `h2 : (∑ j, m j • 1) = n` using `by simpa using hdeg`.

Rewrite `h1` using `[h2]`. Establish `h3` using `(isWeightedHomogeneous_C w (coeff m Gz)).mul h1`. Rewrite `h3` using `[zero_add]`. Use `h3 using 2` and compare the differences between its conclusion and the goal. Conclude with `RingHom.congr_fun (RingHom.ext_int _ _) _`.
-/
theorem segForm_weighted {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) {Gz : MvPolynomial (Fin (N + 1)) ℤ} {n : ℕ}
    (hG : Gz.IsHomogeneous n) (w : (Σ k, ι k) → ℕ) (hw : ∀ j, ∑ k, w ⟨k, E j k⟩ = 1) :
    IsWeightedHomogeneous w (segForm E Gz) n := by
  have hseg : ∀ j, IsWeightedHomogeneous w (∏ k, (X ⟨k, E j k⟩ : MRing ι)) 1 := fun j => by
    have h := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, E j k⟩ : MRing ι))
      (fun k => w ⟨k, E j k⟩) fun k _ => isWeightedHomogeneous_X _ w _
    rwa [hw j] at h
  rw [segForm, aeval_def, eval₂_eq']
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  have hdeg : ∑ j, m j = n := by
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    exact hG (mem_support_iff.1 hm)
  have h1 : IsWeightedHomogeneous w (∏ j, (∏ k, (X ⟨k, E j k⟩ : MRing ι)) ^ m j) (∑ j, m j • 1) :=
    IsWeightedHomogeneous.prod _ _ _ fun j _ => (hseg j).pow _
  have h2 : (∑ j, m j • 1) = n := by simpa using hdeg
  rw [h2] at h1
  have h3 := (isWeightedHomogeneous_C w (coeff m Gz)).mul h1
  rw [zero_add] at h3
  convert h3 using 2
  exact RingHom.congr_fun (RingHom.ext_int _ _) _

/- English proof (translation)
Conclude with `isMultiHomog_of_weighted fun k => segForm_weighted E hG _ fun j => by simp`.
-/
theorem segForm_multiHomog {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) {Gz : MvPolynomial (Fin (N + 1)) ℤ} {n : ℕ}
    (hG : Gz.IsHomogeneous n) : IsMultiHomog (segForm E Gz) fun _ => n := by
  classical
  exact isMultiHomog_of_weighted fun k => segForm_weighted E hG _ fun j => by simp

/- English proof (translation)
Rewrite using `[aeval_def, eval₂_eq_eval_map]`. Use `congr 2`.
-/
theorem eval_map_int {σ : Type} (v : σ → ℂ) (f : MvPolynomial σ ℤ) :
    eval v (map (Int.castRingHom ℂ) f) = aeval v f := by
  rw [aeval_def, eval₂_eq_eval_map]
  congr 2

omit [Fintype K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Establish `h : mConeMap v f = 0` using `hf`. Establish `h2` using `congrArg ((aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars ℤ) h`. Rewrite `h2` using `[mConeMap, comp_aeval_apply, map_zero]`. Simplify using `using h2`.
-/
theorem aeval_eq_zero_of_mem {Ω : Type} [Field Ω] (v : (Σ k, ι k) → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal v) :
    aeval v f = 0 := by
  have h : mConeMap v f = 0 := hf
  have h2 := congrArg ((aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars ℤ) h
  rw [mConeMap, comp_aeval_apply, map_zero] at h2
  simpa using h2

section Join

variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K₂] [∀ k, Fintype (ι₂ k)] in
/- English proof (translation)
Use function extensionality and compare the values at `⟨k, i⟩`. Both sides reduce to the same expression.
-/
theorem joinVec_comp_inl {Ω : Type} (y₁ : (Σ k, ι k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) :
    joinVec y₁ y₂ ∘ joinInl ι ι₂ = y₁ := by
  funext ⟨k, i⟩
  rfl

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K₂] [∀ k, Fintype (ι₂ k)] in
/- English proof (translation)
Introduce and unpack `⟨k, i⟩ ⟨k', i'⟩ h`. Take `rfl : k = k'` from `Sum.inl.inj (congrArg Sigma.fst h)`. Establish `h2 : i = i'` using `eq_of_heq (Sigma.mk.inj h).2`. Rewrite using `[h2]`.
-/
theorem joinInl_inj : Function.Injective (joinInl ι ι₂) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ h
  obtain rfl : k = k' := Sum.inl.inj (congrArg Sigma.fst h)
  have h2 : i = i' := eq_of_heq (Sigma.mk.inj h).2
  rw [h2]

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[support_rename_of_injective joinInl_inj, Finset.mem_image]`. Take `⟨m', hm', rfl⟩` from `hm`. Consider the cases of `k with`. Consider the case `inl k`.

Rewrite using `[Sum.elim_inl, ← hg m' hm' k]`. Conclude with `Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply joinInl_inj m' ⟨k, i⟩`. Consider the case `inr k`. Use `Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_notin_range _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨q, hq⟩`.

Conclude with `Sum.inl_ne_inr (congrArg Sigma.fst hq)`.
-/
theorem multiHomog_rename_inl {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    IsMultiHomog (rename (joinInl ι ι₂) g : MRing (joinIdx ι ι₂)) (Sum.elim d 0) := by
  classical
  intro m hm k
  rw [support_rename_of_injective joinInl_inj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  cases k with
  | inl k =>
    rw [Sum.elim_inl, ← hg m' hm' k]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply joinInl_inj m' ⟨k, i⟩
  | inr k =>
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨q, hq⟩
    exact Sum.inl_ne_inr (congrArg Sigma.fst hq)

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K₂] [∀ k, Fintype (ι₂ k)] in

/- English proof (translation)
Establish `key : ∀ g : MRing ι, mConeMap (joinVec y₁ y₂) (rename (joinInl ι ι₂) g) = rename (Sum.inl : K → K ⊕ K₂) (mConeMap y₁ g)`. Introduce `g`. Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.

Consider the case `mul_X p n hp`. Simplify using `only [map_mul, hp, rename_X]`. Use `congr 1`. Simplify using `only [mConeMap, aeval_X, map_mul, rename_C, rename_X]`. Both sides reduce to the same expression.

Establish `hf' : mConeMap y₁ f = 0` using `hf`. Express the relevant statement in the definitionally equal form `mConeMap (joinVec y₁ y₂) (rename (joinInl ι ι₂) f) = 0`. Rewrite using `[key, hf', map_zero]`.
-/
theorem rename_inl_mem {Ω : Type} [Field Ω] (y₁ : (Σ k, ι k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {f : MRing ι}
    (hf : f ∈ mCoordIdeal y₁) : rename (joinInl ι ι₂) f ∈ mCoordIdeal (joinVec y₁ y₂) := by
  have key : ∀ g : MRing ι, mConeMap (joinVec y₁ y₂) (rename (joinInl ι ι₂) g) =
      rename (Sum.inl : K → K ⊕ K₂) (mConeMap y₁ g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp only [mConeMap, aeval_X, map_mul, rename_C, rename_X]
      rfl
  have hf' : mConeMap y₁ f = 0 := hf
  change mConeMap (joinVec y₁ y₂) (rename (joinInl ι ι₂) f) = 0
  rw [key, hf', map_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K₂] [∀ k, Fintype (ι₂ k)] in
/- English proof (translation)
Rewrite using `[evC, evC, eval_map_int, eval_map_int, aeval_rename]`. Both sides reduce to the same expression.
-/
theorem evC_rename_inl (z : (Σ k, joinIdx ι ι₂ k) → ℂ) (g : MRing ι) :
    evC z (rename (joinInl ι ι₂) g) = evC (fun p => z (joinInl ι ι₂ p)) g := by
  rw [evC, evC, eval_map_int, eval_map_int, aeval_rename]
  rfl

end Join

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C n => simpa using intCast_mem A n`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `add_mem hp hq`. Consider the case `mul_X p i hp => rw [map_mul, aeval_X]`.

Conclude with `mul_mem hp (hv i)`.
-/
theorem aeval_mem_int {Ω : Type} [Field Ω] [Algebra ℚ Ω] {σ : Type} (A : Subalgebra ℚ Ω) (v : σ → Ω)
    (hv : ∀ p, v p ∈ A) (g : MvPolynomial σ ℤ) : aeval v g ∈ A := by
  induction g using MvPolynomial.induction_on with
  | C n => simpa using intCast_mem A n
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact mul_mem hp (hv i)

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[← Finset.prod_div_distrib, Finset.prod_eq_single k]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[Function.update_of_ne hb]`. Conclude with `div_self (hc b)`.

Simplify using the standard rewrite rules.
-/
theorem seg_ratio_update [DecidableEq K] {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c₀ : (k : K) → ι k)
    (hc : ∀ k, y ⟨k, c₀ k⟩ ≠ 0) (k : K) (i : ι k) :
    (∏ k', y ⟨k', Function.update c₀ k i k'⟩) / ∏ k', y ⟨k', c₀ k'⟩ = y ⟨k, i⟩ / y ⟨k, c₀ k⟩ := by
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
  · simp
  · intro b _ hb
    rw [Function.update_of_ne hb]
    exact div_self (hc b)
  · simp

section Chart

variable {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ}

abbrev joinPt (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω) :
    (Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k) → Ω :=
  joinVec y fun p : (Σ _ : Unit, Fin (r + 1)) => x' p.2

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[blockFnField, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨⟨k | u, i⟩, ⟨k' | u', i'⟩, hpq, rfl⟩`. Take `rfl : k = k'` from `Sum.inl.inj hpq`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨⟨k, i⟩, ⟨k, i'⟩, rfl, rfl⟩`.

Conclude with `absurd hpq (by simp)`. Conclude with `absurd hpq (by simp)`. Distinguish the cases in `hl : x' i' = 0`. Express the relevant statement in the definitionally equal form `x' i / x' i' ∈ blockFnField y`. Rewrite using `[hl, div_zero]`.

Conclude with `zero_mem _`. Conclude with `hF i i' hl`. Rewrite using `[blockFnField, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨p, q, hpq, rfl⟩`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨joinInl _ _ p, joinInl _ _ q, by simp [joinInl, hpq], rfl⟩`.
-/
theorem blockFnField_joinPt (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω)
    (hF : ∀ i l, x' l ≠ 0 → x' i / x' l ∈ blockFnField y) :
    blockFnField (joinPt y x') = blockFnField y := by
  apply le_antisymm
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k | u, i⟩, ⟨k' | u', i'⟩, hpq, rfl⟩
    · obtain rfl : k = k' := Sum.inl.inj hpq
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, i⟩, ⟨k, i'⟩, rfl, rfl⟩
    · exact absurd hpq (by simp)
    · exact absurd hpq (by simp)
    · by_cases hl : x' i' = 0
      · change x' i / x' i' ∈ blockFnField y
        rw [hl, div_zero]
        exact zero_mem _
      · exact hF i i' hl
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin _ _
      ⟨joinInl _ _ p, joinInl _ _ q, by simp [joinInl, hpq], rfl⟩

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨⟨k | u, i⟩, rfl⟩`. Establish `h1` using `seg_ratio_update y (fun k => c (Sum.inl k)) hc k i`. Use `Algebra.subset_adjoin (Or.inl ⟨E.symm (Function.update (fun k => c (Sum.inl k)) k i), ?_⟩)` and prove the remaining obligations.

Simplify using `only [Equiv.apply_symm_apply, hEa]`. Conclude with `h1`. Consider the cases of `u`. Conclude with `Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)`. Rewrite using `[Algebra.adjoin_le_iff]`.

Introduce and unpack `_ (⟨j, rfl⟩ | ⟨i, rfl⟩)`. Rewrite using `[SetLike.mem_coe]`. Simplify using `only [← Finset.prod_div_distrib]`. Use `prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨Sum.inl k, E j k⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [hEa]`.

Both sides reduce to the same expression. Conclude with `Algebra.subset_adjoin ⟨⟨Sum.inr (), i⟩, rfl⟩`.
-/
theorem adjoin_ratios_eq (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω) {N : ℕ}
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c : (k : K ⊕ Unit) → joinIdx ι (fun _ : Unit => Fin (r + 1)) k)
    (a : Fin (N + 1)) (hEa : ∀ k, E a k = c (Sum.inl k)) (hc : ∀ k, y ⟨k, c (Sum.inl k)⟩ ≠ 0) :
    Algebra.adjoin ℚ (Set.range fun p : Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k =>
        joinPt y x' p / joinPt y x' ⟨p.1, c p.1⟩) =
      Algebra.adjoin ℚ (Set.range (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) ∪
        Set.range (fun k => x' k / x' (c (Sum.inr ())))) := by
  classical
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨⟨k | u, i⟩, rfl⟩
    · have h1 := seg_ratio_update y (fun k => c (Sum.inl k)) hc k i
      refine Algebra.subset_adjoin (Or.inl ⟨E.symm (Function.update (fun k => c (Sum.inl k)) k i), ?_⟩)
      simp only [Equiv.apply_symm_apply, hEa]
      exact h1
    · cases u
      exact Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)
  · rw [Algebra.adjoin_le_iff]
    rintro _ (⟨j, rfl⟩ | ⟨i, rfl⟩)
    · rw [SetLike.mem_coe]
      simp only [← Finset.prod_div_distrib]
      refine prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨Sum.inl k, E j k⟩, ?_⟩
      simp only [hEa]
      rfl
    · exact Algebra.subset_adjoin ⟨⟨Sum.inr (), i⟩, rfl⟩

omit [∀ k, Fintype (ι k)] in
/- English proof (translation)
Rewrite using `[aeval_rename, aeval_segForm, aeval_map_algebraMap]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Simplify using `only [← Finset.prod_div_distrib, hEa]`. Both sides reduce to the same expression.
-/
theorem aeval_ratios_segForm (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω) {N : ℕ}
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (Gz : MvPolynomial (Fin (N + 1)) ℤ)
    (c : (k : K ⊕ Unit) → joinIdx ι (fun _ : Unit => Fin (r + 1)) k)
    (a : Fin (N + 1)) (hEa : ∀ k, E a k = c (Sum.inl k)) :
    aeval (fun p : Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k => joinPt y x' p / joinPt y x' ⟨p.1, c p.1⟩)
        (rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)) =
      aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) (map (algebraMap ℤ ℚ) Gz) := by
  rw [aeval_rename, aeval_segForm, aeval_map_algebraMap]
  congr 2
  funext j
  simp only [← Finset.prod_div_distrib, hEa]
  rfl

/- English proof (translation)
Introduce `c hc`. Establish `hcl : ∀ k, y ⟨k, c (Sum.inl k)⟩ ≠ 0` using `fun k => hc (Sum.inl k)`. Establish `hl : x' (c (Sum.inr ())) ≠ 0` using `hc (Sum.inr ())`. Take `⟨a, hEa⟩ : ∃ a, ∀ k, E a k = c (Sum.inl k)` from `⟨E.symm (fun k => (c (Sum.inl k) : ι k)), fun k => congrFun (E.apply_symm_apply _) k⟩`. Establish `hprod : (∏ k, y ⟨k, E a k⟩) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => by rw [hEa]; exact hcl k`.

Establish `hA` using `adjoin_ratios_eq y x' E c a hEa hcl`. Establish `hval` using `aeval_ratios_segForm y x' E Gz c a hEa`. Take `⟨m, f, b, hf, hb, hsum, hS⟩` from `hch a (c (Sum.inr ())) hprod hl`. Rewrite `hS` using `[← hA, ← hval]`. Use `⟨m, f, b, ?_, ?_, hsum, fun i hfi S hSeq => ?_⟩` and prove the remaining obligations.

Introduce `i`. Rewrite using `[hA]`. Conclude with `hf i`. Introduce `i`. Rewrite using `[hA]`.

Conclude with `hb i`. Establish `hS' : S = Algebra.adjoin ℚ (insert (f i)⁻¹ ((Algebra.adjoin ℚ (Set.range fun p : Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k => joinPt y x' p / joinPt y x' ⟨p.1, c p.1⟩) : Subalgebra ℚ Ω) : Set Ω))`. Rewrite using `[hSeq, Algebra.adjoin_insert_adjoin]`. Take `⟨hsm, z, n, hn, hli, hspan, hq⟩` from `hS i hfi S hS'`. Use `⟨hsm, z, n, hn, hli, hspan, fun q hqp => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hq q hqp]`. Establish `hmemS : ∀ g : MRing (joinIdx ι fun _ : Unit => Fin (r + 1)), aeval (fun p : Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k => joinPt y x' p / joinPt y x' ⟨p.1, c p.1⟩) g ∈ S` using `fun g => by`. Use `aeval_mem_int S _ (fun p => ?_) g` and prove the remaining obligations. Rewrite using `[hSeq]`. Conclude with `Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)`.

Prove the components needed by the constructor for the conclusion. Introduce `h s hs`. Conclude with `h _ (Ideal.subset_span rfl) s hs`. Introduce `h g hg s hs`. Take `⟨g', rfl⟩` from `Ideal.mem_span_singleton'.1 hg`.

Establish `h1` using `h ⟨_, hmemS _⟩ rfl`. Establish `hmul : s = (⟨_, hmemS g'⟩ : S) * ⟨_, hmemS (rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz))⟩` using `Subtype.ext (by rw [hs, map_mul]; rfl)`. Rewrite using `[hmul]`. Conclude with `q.mul_mem_left _ h1`.
-/
theorem isSncModel_joinPt (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω) (e : ℕ) {N : ℕ}
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (Gz : MvPolynomial (Fin (N + 1)) ℤ)
    (hch : ∀ a l, (∏ k, y ⟨k, E a k⟩) ≠ 0 → x' l ≠ 0 →
      SncChart (Algebra.adjoin ℚ (Set.range (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) ∪
        Set.range (fun k => x' k / x' l))) e
        (aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) (map (algebraMap ℤ ℚ) Gz))) :
    IsSncModel (joinPt y x') e
      (Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}) := by
  intro c hc
  have hcl : ∀ k, y ⟨k, c (Sum.inl k)⟩ ≠ 0 := fun k => hc (Sum.inl k)
  have hl : x' (c (Sum.inr ())) ≠ 0 := hc (Sum.inr ())
  obtain ⟨a, hEa⟩ : ∃ a, ∀ k, E a k = c (Sum.inl k) :=
    ⟨E.symm (fun k => (c (Sum.inl k) : ι k)), fun k => congrFun (E.apply_symm_apply _) k⟩
  have hprod : (∏ k, y ⟨k, E a k⟩) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => by rw [hEa]; exact hcl k
  have hA := adjoin_ratios_eq y x' E c a hEa hcl
  have hval := aeval_ratios_segForm y x' E Gz c a hEa
  obtain ⟨m, f, b, hf, hb, hsum, hS⟩ := hch a (c (Sum.inr ())) hprod hl
  rw [← hA, ← hval] at hS
  refine ⟨m, f, b, ?_, ?_, hsum, fun i hfi S hSeq => ?_⟩
  · intro i
    rw [hA]
    exact hf i
  · intro i
    rw [hA]
    exact hb i
  have hS' : S = Algebra.adjoin ℚ (insert (f i)⁻¹
      ((Algebra.adjoin ℚ (Set.range fun p : Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k =>
        joinPt y x' p / joinPt y x' ⟨p.1, c p.1⟩) : Subalgebra ℚ Ω) : Set Ω)) := by
    rw [hSeq, Algebra.adjoin_insert_adjoin]
  obtain ⟨hsm, z, n, hn, hli, hspan, hq⟩ := hS i hfi S hS'
  refine ⟨hsm, z, n, hn, hli, hspan, fun q hqp => ?_⟩
  rw [← hq q hqp]
  have hmemS : ∀ g : MRing (joinIdx ι fun _ : Unit => Fin (r + 1)),
      aeval (fun p : Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k =>
        joinPt y x' p / joinPt y x' ⟨p.1, c p.1⟩) g ∈ S := fun g => by
    refine aeval_mem_int S _ (fun p => ?_) g
    rw [hSeq]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  constructor
  · intro h s hs
    exact h _ (Ideal.subset_span rfl) s hs
  · intro h g hg s hs
    obtain ⟨g', rfl⟩ := Ideal.mem_span_singleton'.1 hg
    have h1 := h ⟨_, hmemS _⟩ rfl
    have hmul : s = (⟨_, hmemS g'⟩ : S) *
        ⟨_, hmemS (rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz))⟩ :=
      Subtype.ext (by rw [hs, map_mul]; rfl)
    rw [hmul]
    exact q.mul_mem_left _ h1

/- English proof (translation)
Establish `hw : (fun p => z (joinInl ι (fun _ : Unit => Fin (r + 1)) p)) ∈ mcPts (mCoordIdeal y)`. Use `⟨fun k => hz.1 (Sum.inl k), fun f hf => ?_⟩` and prove the remaining obligations. Establish `h1` using `hz.2 _ (rename_inl_mem y (fun p : (Σ _ : Unit, Fin (r + 1)) => x' p.2) hf)`. Express the relevant statement in the definitionally equal form `evC _ _ = 0 at h1`. Rewrite `h1` using `[evC_rename_inl]`.

Conclude with `h1`. Rewrite `hb` using `[evC_rename_inl]`. Establish `h2` using `hβ _ hw hb`. Rewrite `h2` using `[eval_map_int]`. Use `⟨hz.1, fun f hf => ?_⟩` and prove the remaining obligations.

Take `⟨g, rfl⟩` from `Ideal.mem_span_singleton'.1 hf`. Establish `h3 : evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)) = 0`. Rewrite using `[evC_rename_inl, evC, eval_map_int, aeval_segForm]`. Conclude with `h2`. Express the relevant statement in the definitionally equal form `eval z (map (Int.castRingHom ℂ) _) = 0`.

Rewrite using `[map_mul, map_mul]`. Express the relevant statement in the definitionally equal form `_ * evC z _ = 0`. Rewrite using `[h3, mul_zero]`.
-/
theorem mem_mcPts_span (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω) (β : MRing ι) {N : ℕ}
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (Gz : MvPolynomial (Fin (N + 1)) ℤ)
    (hβ : ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 →
      eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0)
    (z : (Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal (joinPt y x')))
    (hb : evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) β) = 0) :
    z ∈ mcPts (Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}) := by
  have hw : (fun p => z (joinInl ι (fun _ : Unit => Fin (r + 1)) p)) ∈ mcPts (mCoordIdeal y) := by
    refine ⟨fun k => hz.1 (Sum.inl k), fun f hf => ?_⟩
    have h1 := hz.2 _ (rename_inl_mem y (fun p : (Σ _ : Unit, Fin (r + 1)) => x' p.2) hf)
    change evC _ _ = 0 at h1
    rw [evC_rename_inl] at h1
    exact h1
  rw [evC_rename_inl] at hb
  have h2 := hβ _ hw hb
  rw [eval_map_int] at h2
  refine ⟨hz.1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hf
  have h3 : evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)) = 0 := by
    rw [evC_rename_inl, evC, eval_map_int, aeval_segForm]
    exact h2
  change eval z (map (Int.castRingHom ℂ) _) = 0
  rw [map_mul, map_mul]
  change _ * evC z _ = 0
  rw [h3, mul_zero]

end Chart

/- English proof (translation)
Introduce `Ω _ _ K _ ι _ y e β N E d Gz r x' hG h0 hβ hx' hF hch`. Establish `hmem : rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz) ∈ Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}` using `Ideal.subset_span rfl`. Use `⟨fun p => x' p.2, Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}, ?_, blockFnField_joinPt y x' hF, ?_, ?_, isSncModel_joinPt y x' e E Gz hch, fun z hz hb => mem_mcPts_span y x' β E Gz hβ z hz hb⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `Function.ne_iff.1 hx'`. Conclude with `⟨i, hi⟩`.

Use `⟨{rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}, ?_, rfl⟩` and prove the remaining obligations. Introduce and unpack `f rfl`. Conclude with `⟨_, multiHomog_rename_inl (segForm_multiHomog E hG)⟩`. Introduce `hle`. Establish `h1` using `aeval_eq_zero_of_mem _ (hle hmem)`.

Rewrite `h1` using `[aeval_rename, joinVec_comp_inl, aeval_segForm]`. Conclude with `h0 h1`.
-/
theorem final_data_main : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (r : ℕ) (x' : Fin (r + 1) → Ω) (hG : Gz.IsHomogeneous (d + 1)) (h0 : aeval (fun j => ∏ k, y ⟨k, E j k⟩) Gz ≠ 0) (hβ : ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0) (hx' : x' ≠ 0) (hF : ∀ i l, x' l ≠ 0 → x' i / x' l ∈ blockFnField y) (hch : ∀ a l, (∏ k, y ⟨k, E a k⟩) ≠ 0 → x' l ≠ 0 → SncChart (Algebra.adjoin ℚ (Set.range (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) ∪ Set.range (fun k => x' k / x' l))) e (aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) (map (algebraMap ℤ ℚ) Gz))), ∃ (y' : (Σ _ : Unit, Fin (r + 1)) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin (r + 1)))), (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧ ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧ ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) β) = 0 → z ∈ mcPts J := by
  intro Ω _ _ K _ ι _ y e β N E d Gz r x' hG h0 hβ hx' hF hch
  have hmem : rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz) ∈
      Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)} :=
    Ideal.subset_span rfl
  refine ⟨fun p => x' p.2, Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}, ?_,
    blockFnField_joinPt y x' hF, ?_, ?_, isSncModel_joinPt y x' e E Gz hch,
    fun z hz hb => mem_mcPts_span y x' β E Gz hβ z hz hb⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx'
    exact ⟨i, hi⟩
  · refine ⟨{rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}, ?_, rfl⟩
    rintro f rfl
    exact ⟨_, multiHomog_rename_inl (segForm_multiHomog E hG)⟩
  · intro hle
    have h1 := aeval_eq_zero_of_mem _ (hle hmem)
    rw [aeval_rename, joinVec_comp_inl, aeval_segForm] at h1
    exact h0 h1

end GlobalTheory.CompanionTheory.Ar.SegreChart
