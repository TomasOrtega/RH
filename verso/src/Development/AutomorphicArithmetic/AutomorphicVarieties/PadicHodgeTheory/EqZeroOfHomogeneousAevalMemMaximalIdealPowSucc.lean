import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
open IsLocalRing UpperTheory.V.Alg

private def Cg {A : Type} [CommRing A] (I : Ideal A) (k : ℕ) (a b : A) : Prop :=
  b ∈ I ^ k ∧ a - b ∈ I ^ (k + 1)

/- English proof (translation)
Establish `hc : c ∈ I ^ l`. Use `(I ^ l).add_mem (Ideal.pow_le_pow_right (Nat.le_succ l) h2.2) h2.1` as an intermediate fact. Simplify using `using this`. Use `⟨by rw [pow_add]; exact Ideal.mul_mem_mul h1.1 h2.1, ?_⟩` and prove the remaining obligations. Establish `e : a * c - b * d = (a - b) * c + b * (c - d)` using `by ring`.

Rewrite using `[e]`. Use `Ideal.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[show k + l + 1 = (k + 1) + l by ring, pow_add]`. Conclude with `Ideal.mul_mem_mul h1.2 hc`. Rewrite using `[add_assoc, pow_add]`.

Conclude with `Ideal.mul_mem_mul h1.1 h2.2`.
-/
private theorem Cg.mul {A : Type} [CommRing A] {I : Ideal A} {k l : ℕ} {a b c d : A}
    (h1 : Cg I k a b) (h2 : Cg I l c d) : Cg I (k + l) (a * c) (b * d) := by
  have hc : c ∈ I ^ l := by
    have := (I ^ l).add_mem (Ideal.pow_le_pow_right (Nat.le_succ l) h2.2) h2.1
    simpa using this
  refine ⟨by rw [pow_add]; exact Ideal.mul_mem_mul h1.1 h2.1, ?_⟩
  have e : a * c - b * d = (a - b) * c + b * (c - d) := by ring
  rw [e]
  refine Ideal.add_mem _ ?_ ?_
  · rw [show k + l + 1 = (k + 1) + l by ring, pow_add]
    exact Ideal.mul_mem_mul h1.2 hc
  · rw [add_assoc, pow_add]
    exact Ideal.mul_mem_mul h1.1 h2.2

/- English proof (translation)
Assemble the required witnesses or components as `⟨by simp, by simp⟩`.
-/
private theorem Cg.refl {A : Type} [CommRing A] (I : Ideal A) (a : A) : Cg I 0 a a :=
  ⟨by simp, by simp⟩

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using Cg.refl I 1`. Consider the case `succ k ih => rw [pow_succ, pow_succ]`. Conclude with `ih.mul h`.
-/
private theorem Cg.pow {A : Type} [CommRing A] {I : Ideal A} {a b : A}
    (h : Cg I 1 a b) (k : ℕ) : Cg I k (a ^ k) (b ^ k) := by
  induction k with
  | zero => simpa using Cg.refl I 1
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using Cg.refl I 1`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]`. Conclude with `((h i).pow _).mul ih`.
-/
private theorem Cg.prod {A ι : Type} [CommRing A] {I : Ideal A} {a b : ι → A}
    (h : ∀ i, Cg I 1 (a i) (b i)) (d : ι → ℕ) (s : Finset ι) :
    Cg I (∑ i ∈ s, d i) (∏ i ∈ s, a i ^ d i) (∏ i ∈ s, b i ^ d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cg.refl I 1
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((h i).pow _).mul ih

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro f _`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `f hf`.

Rewrite `hf` using `[pow_succ]`. Use `Submodule.mul_induction_on hf ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`. Establish `h1 : ((1 : ℕ) : ℕ∞) ≤ b.order`. Use `MvPowerSeries.nat_le_order ?_` and prove the remaining obligations.

Introduce `d hd`. Establish `hd0 : d = 0`. Establish `: Finsupp.degree d = 0` using `by omega`. Conclude with `(Finsupp.degree_eq_zero_iff d).1 this`. Substitute `hd0` using the available equality.

Rewrite `hb` using `[mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]`. Simplify using `using hb`. Use `le_trans ?_ MvPowerSeries.le_order_mul` and prove the remaining obligations. Rewrite using `[Nat.cast_add]`. Conclude with `add_le_add (ih a ha) h1`.

Introduce `a b ha hb`. Conclude with `le_trans (le_min ha hb) MvPowerSeries.min_order_le_add`.
-/
private theorem order_of_mem_pow {σ E : Type} [Field E] (k : ℕ) :
    ∀ f : MvPowerSeries σ E, f ∈ maximalIdeal (MvPowerSeries σ E) ^ k → (k : ℕ∞) ≤ f.order := by
  induction k with
  | zero => intro f _; simp
  | succ k ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb
      have h1 : ((1 : ℕ) : ℕ∞) ≤ b.order := by
        refine MvPowerSeries.nat_le_order ?_
        intro d hd
        have hd0 : d = 0 := by
          have : Finsupp.degree d = 0 := by omega
          exact (Finsupp.degree_eq_zero_iff d).1 this
        subst hd0
        rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
          isUnit_iff_ne_zero, not_not] at hb
        simpa using hb
      refine le_trans ?_ MvPowerSeries.le_order_mul
      rw [Nat.cast_add]
      exact add_le_add (ih a ha) h1
    · intro a b ha hb
      exact le_trans (le_min ha hb) MvPowerSeries.min_order_le_add

/- English proof (translation)
Introduce `O E _ _ _ _ _ n u c hc hu N h hh hm`. Use `set I := maximalIdeal (MvPowerSeries (Fin n) E) with hI`. Set `v : Fin n → MvPowerSeries (Fin n) E` to `fun i => c • MvPowerSeries.X i`. Establish `hv : ∀ i, Cg I 1 (u i) (v i)`. Introduce `i`.

Use `⟨?_, hu i⟩` and prove the remaining obligations. Rewrite using `[pow_one]`. Establish `hX : (MvPowerSeries.X i : MvPowerSeries (Fin n) E) ∈ I`. Rewrite using `[hI, mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]`. Simplify using the standard rewrite rules.

Use `show c • MvPowerSeries.X i ∈ I`. Rewrite using `[Algebra.smul_def]`. Conclude with `I.mul_mem_left _ hX`. Establish `hdeg : ∀ d ∈ h.support, ∑ i, d i = N`. Introduce `d hd`.

Use `hh (MvPolynomial.mem_support_iff.1 hd)` as an intermediate fact. Rewrite using `[← this, ← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]`. Both sides reduce to the same expression. Establish `hdiff : MvPolynomial.aeval u h - MvPolynomial.aeval v h ∈ I ^ (N + 1)`. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', ← Finset.sum_sub_distrib]`.

Use `Ideal.sum_mem _ fun d hd => ?_` and prove the remaining obligations. Rewrite using `[← mul_sub]`. Use `Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations. Use `(Cg.prod hv d Finset.univ).2` as an intermediate fact. Rewrite `this` using `[hdeg d hd]`. Then use the resulting hypothesis.

Establish `hvm : MvPolynomial.aeval v h ∈ I ^ (N + 1)`. Use `(I ^ (N + 1)).sub_mem hm hdiff` as an intermediate fact. Simplify using `using this`. Establish `hval : MvPolynomial.aeval v h = ∑ d ∈ h.support, MvPowerSeries.monomial d (algebraMap O E (h.coeff d * c ^ N))`. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']`.

Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hX : (∏ i, (MvPowerSeries.X i : MvPowerSeries (Fin n) E) ^ d i) = MvPowerSeries.monomial d 1`. Establish `h1 : ((MvPolynomial.monomial d (1 : E) : MvPolynomial (Fin n) E) : MvPowerSeries (Fin n) E) = MvPowerSeries.monomial d 1` using `MvPolynomial.coe_monomial _ _`. Rewrite using `[← h1, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]`. Rewrite using `[← MvPolynomial.coeToMvPowerSeries.ringHom_apply]`.

Simplify using `[map_prod]`. Simplify using `only [v, Algebra.smul_def, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Rewrite using `[hdeg d hd, hX, ← mul_assoc, ← map_pow, ← map_mul, MvPowerSeries.algebraMap_apply, ← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial]`. Simplify using the standard rewrite rules. Assume the negation of the conclusion as `hne`.

Take `⟨d, hd⟩` from `MvPolynomial.support_nonempty.2 hne`. Establish `h0 : MvPowerSeries.coeff d (MvPolynomial.aeval v h) = 0`. Use `MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (order_of_mem_pow _ _ hvm))` and prove the remaining obligations. Rewrite using `[Finsupp.degree_eq_sum, hdeg d hd]`. Conclude with `Nat.lt_succ_self N` after adjusting the coercions.

Rewrite `h0` using `[hval, map_sum, Finset.sum_eq_single d]`. Rewrite `h0` using `[MvPowerSeries.coeff_monomial_same, map_eq_zero_iff _ (IsFractionRing.injective O E)]`. Conclude with `mul_ne_zero (MvPolynomial.mem_support_iff.1 hd) (pow_ne_zero _ hc) h0`. Introduce `e _ he`. Conclude with `MvPowerSeries.coeff_monomial_ne he.symm _`.

Introduce `h'`. Conclude with `absurd hd h'`.
-/
theorem UpperTheory.eq_zero_of_homogeneous_aeval_mem_maximalIdeal_pow_succ :
    ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (u : Fin n → MvPowerSeries (Fin n) E) (c : O), c ≠ 0 → (∀ i, u i - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2) → ∀ (N : ℕ) (h : MvPolynomial (Fin n) O), h.IsHomogeneous N → MvPolynomial.aeval u h ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ (N + 1) → h = 0 := by
  intro O E _ _ _ _ _ n u c hc hu N h hh hm
  classical
  set I := maximalIdeal (MvPowerSeries (Fin n) E) with hI
  let v : Fin n → MvPowerSeries (Fin n) E := fun i => c • MvPowerSeries.X i
  have hv : ∀ i, Cg I 1 (u i) (v i) := by
    intro i
    refine ⟨?_, hu i⟩
    rw [pow_one]
    have hX : (MvPowerSeries.X i : MvPowerSeries (Fin n) E) ∈ I := by
      rw [hI, mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
      simp
    show c • MvPowerSeries.X i ∈ I
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ hX
  have hdeg : ∀ d ∈ h.support, ∑ i, d i = N := by
    intro d hd
    have := hh (MvPolynomial.mem_support_iff.1 hd)
    rw [← this, ← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    rfl
  have hdiff : MvPolynomial.aeval u h - MvPolynomial.aeval v h ∈ I ^ (N + 1) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun d hd => ?_
    rw [← mul_sub]
    refine Ideal.mul_mem_left _ _ ?_
    have := (Cg.prod hv d Finset.univ).2
    rwa [hdeg d hd] at this
  have hvm : MvPolynomial.aeval v h ∈ I ^ (N + 1) := by
    have := (I ^ (N + 1)).sub_mem hm hdiff
    simpa using this
  have hval : MvPolynomial.aeval v h =
      ∑ d ∈ h.support, MvPowerSeries.monomial d (algebraMap O E (h.coeff d * c ^ N)) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun d hd => ?_
    have hX : (∏ i, (MvPowerSeries.X i : MvPowerSeries (Fin n) E) ^ d i)
        = MvPowerSeries.monomial d 1 := by
      have h1 : ((MvPolynomial.monomial d (1 : E) : MvPolynomial (Fin n) E) :
          MvPowerSeries (Fin n) E) = MvPowerSeries.monomial d 1 := MvPolynomial.coe_monomial _ _
      rw [← h1, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
      rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
      simp [map_prod]
    simp only [v, Algebra.smul_def, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [hdeg d hd, hX, ← mul_assoc, ← map_pow, ← map_mul, MvPowerSeries.algebraMap_apply,
      ← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial]
    simp
  by_contra hne
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.2 hne
  have h0 : MvPowerSeries.coeff d (MvPolynomial.aeval v h) = 0 := by
    refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (order_of_mem_pow _ _ hvm))
    rw [Finsupp.degree_eq_sum, hdeg d hd]
    exact_mod_cast Nat.lt_succ_self N
  rw [hval, map_sum, Finset.sum_eq_single d] at h0
  · rw [MvPowerSeries.coeff_monomial_same,
      map_eq_zero_iff _ (IsFractionRing.injective O E)] at h0
    exact mul_ne_zero (MvPolynomial.mem_support_iff.1 hd) (pow_ne_zero _ hc) h0
  · intro e _ he
    exact MvPowerSeries.coeff_monomial_ne he.symm _
  · intro h'; exact absurd hd h'
