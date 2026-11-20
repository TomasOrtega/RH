import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply

open Polynomial

namespace GlobalTheory.NewPrime.LocalRing

/- English proof (translation)
Assume the negation of the conclusion as `hu`. Take `⟨M, hM, hxM⟩` from `Ideal.exists_le_maximal (Ideal.span {x}) (by rwa [Ne, Ideal.span_singleton_eq_top])`. Establish `hxM' : x ∈ M` using `hxM (Ideal.mem_span_singleton_self x)`. Establish `hle : RingHom.ker ψ ≤ M`. Introduce `y hy`.

Take `⟨k, hk⟩` from `h y (RingHom.mem_ker.1 hy)`. Conclude with `hM.isPrime.mem_of_pow_mem k (hk ▸ M.zero_mem)`. Establish `: Finite (A ⧸ RingHom.ker ψ)` using `Finite.of_surjective _ Ideal.Quotient.mk_surjective`. Establish `: (RingHom.ker ψ).IsPrime` using `RingHom.ker_isPrime ψ`. Establish `hmax : (RingHom.ker ψ).IsMaximal` using `Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (A ⧸ RingHom.ker ψ))`.

Establish `hEq` using `hmax.eq_of_le hM.ne_top hle`. Conclude with `hx (RingHom.mem_ker.1 (hEq ▸ hxM'))`.
-/
theorem isUnit_of_map_ne_zero {A L : Type} [CommRing A] [Finite A] [CommRing L] [IsDomain L]
    (ψ : A →+* L) (h : ∀ x, ψ x = 0 → IsNilpotent x) {x : A} (hx : ψ x ≠ 0) : IsUnit x := by
  by_contra hu
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal (Ideal.span {x})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hxM' : x ∈ M := hxM (Ideal.mem_span_singleton_self x)
  have hle : RingHom.ker ψ ≤ M := by
    intro y hy
    obtain ⟨k, hk⟩ := h y (RingHom.mem_ker.1 hy)
    exact hM.isPrime.mem_of_pow_mem k (hk ▸ M.zero_mem)
  have : Finite (A ⧸ RingHom.ker ψ) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hmax : (RingHom.ker ψ).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (A ⧸ RingHom.ker ψ))
  have hEq := hmax.eq_of_le hM.ne_top hle
  exact hx (RingHom.mem_ker.1 (hEq ▸ hxM'))

/- English proof (translation)
Establish `: Nontrivial A` using `ψ.domain_nontrivial`. Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_` and prove the remaining obligations. Distinguish the cases in `ha : ψ a = 0`. Use `right`. Use `isUnit_of_map_ne_zero ψ h ?_` and prove the remaining obligations.

Rewrite using `[map_sub, map_one, ha, sub_zero]`. Conclude with `one_ne_zero`. Conclude with `Or.inl (isUnit_of_map_ne_zero ψ h ha)`.
-/
theorem isLocalRing_of_map {A L : Type} [CommRing A] [Finite A] [CommRing L] [IsDomain L]
    (ψ : A →+* L) (h : ∀ x, ψ x = 0 → IsNilpotent x) : IsLocalRing A := by
  have : Nontrivial A := ψ.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : ψ a = 0
  · right
    refine isUnit_of_map_ne_zero ψ h ?_
    rw [map_sub, map_one, ha, sub_zero]
    exact one_ne_zero
  · exact Or.inl (isUnit_of_map_ne_zero ψ h ha)

/- English proof (translation)
Use `nontriviality R`. Establish `h1 : AdjoinRoot.mk g (C r * X ^ j) = 0`. Rewrite using `[map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]`. Conclude with `h`. Rewrite `h1` using `[AdjoinRoot.mk_eq_zero, ← Polynomial.modByMonic_eq_zero_iff_dvd hg]`.

Establish `hdeg : (C r * X ^ j).degree < g.degree`. Use `lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le j r) ?_` and prove the remaining obligations. Rewrite using `[Polynomial.degree_eq_natDegree hg.ne_zero]`. Conclude with `hj` after adjusting the coercions. Rewrite `h1` using `[(Polynomial.modByMonic_eq_self_iff hg).2 hdeg]`.

Simplify using `using congrArg (fun p => Polynomial.coeff p j) h1`.
-/
theorem adjoinRoot_eq_zero {R : Type} [CommRing R] {g : R[X]} (hg : g.Monic) {j : ℕ}
    (hj : j < g.natDegree) {r : R} (h : AdjoinRoot.of g r * AdjoinRoot.root g ^ j = 0) : r = 0 := by
  nontriviality R
  have h1 : AdjoinRoot.mk g (C r * X ^ j) = 0 := by
    rw [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    exact h
  rw [AdjoinRoot.mk_eq_zero, ← Polynomial.modByMonic_eq_zero_iff_dvd hg] at h1
  have hdeg : (C r * X ^ j).degree < g.degree := by
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le j r) ?_
    rw [Polynomial.degree_eq_natDegree hg.ne_zero]
    exact_mod_cast hj
  rw [(Polynomial.modByMonic_eq_self_iff hg).2 hdeg] at h1
  simpa using congrArg (fun p => Polynomial.coeff p j) h1

/- English proof (translation)
Use `conv_lhs => rw [F.as_sum]`. Rewrite using `[map_sum, Polynomial.finsetSum_coeff]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]`. Establish `hprod : (∏ q, (C (b q) * X : L[X]) ^ m q) = C (∏ q, b q ^ m q) * X ^ m.degree`.

Simplify using `[mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]`. Rewrite using `[hprod, Polynomial.algebraMap_eq, ← mul_assoc, ← map_mul, Polynomial.coeff_C_mul_X_pow]`. Break down `eq_or_ne m.degree d with hmd | hmd` into its components or cases. Simplify using `[hmd]`. Simplify using `[hmd, Ne.symm hmd]`.
-/
theorem aeval_C_mul_X_coeff {ι L : Type} [Fintype ι] [CommRing L] (F : MvPolynomial ι L) (b : ι → L)
    (d : ℕ) : (MvPolynomial.aeval (fun q => C (b q) * X) F : L[X]).coeff d =
      ∑ m ∈ F.support, if m.degree = d then F.coeff m * ∏ q, b q ^ m q else 0 := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  have hprod : (∏ q, (C (b q) * X : L[X]) ^ m q) = C (∏ q, b q ^ m q) * X ^ m.degree := by
    simp [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]
  rw [hprod, Polynomial.algebraMap_eq, ← mul_assoc, ← map_mul, Polynomial.coeff_C_mul_X_pow]
  rcases eq_or_ne m.degree d with hmd | hmd
  · simp [hmd]
  · simp [hmd, Ne.symm hmd]

/- English proof (translation)
Set `H : MvPolynomial ι L` to `∑ m' ∈ F.support.filter (fun m' => m'.degree = m.degree ∧ ∀ q ∈ K, m' q = 0), MvPolynomial.monomial m' (F.coeff m')`. Establish `hHm : H.coeff m = F.coeff m`. Simplify using `only [H, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]`. Rewrite using `[Finset.sum_eq_single m]`. Simplify using the standard rewrite rules.

Introduce `m' _ hm'`. Simplify using `[hm']`. Introduce `hnot`. It suffices to derive a contradiction. Conclude with `hnot (Finset.mem_filter.2 ⟨MvPolynomial.mem_support_iff.2 hm, rfl, hK⟩)`.

Set `P : MvPolynomial ι L` to `H * ∏ q ∈ Finset.univ.filter (fun q => q ∉ K), MvPolynomial.X q`. Establish `hP : P ≠ 0`. Apply `mul_ne_zero` to reduce the goal to its premises. Introduce `h0`. Apply `hm` to reduce the goal to its premises.

Rewrite using `[← hHm, h0, MvPolynomial.coeff_zero]`. Conclude with `Finset.prod_ne_zero_iff.2 fun q _ => MvPolynomial.X_ne_zero q`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, MvPolynomial.eval x P ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Conclude with `hP (MvPolynomial.funext fun x => by simpa using hcon x)`. Establish `hxH : MvPolynomial.eval x H ≠ 0` using `fun h0 => hx (by simp [P, h0])`. Establish `hxq : ∀ q ∉ K, x q ≠ 0`. Introduce `q hq h0`. Apply `hx` to reduce the goal to its premises.

Simplify using `only [P, map_mul, map_prod, MvPolynomial.eval_X]`. Rewrite using `[Finset.prod_eq_zero (i := q) (by simp [hq]) h0, mul_zero]`. Use `⟨fun q => if q ∈ K then 0 else x q, fun q hq => by simp [hq], fun q hq => by simp [hq, hxq q hq], ?_⟩` and prove the remaining obligations. Establish `key : MvPolynomial.eval x H = ∑ m' ∈ F.support, if m'.degree = m.degree then F.coeff m' * ∏ q, (if q ∈ K then 0 else x q) ^ m' q else 0`. Simplify using `only [H, Finset.sum_filter, map_sum]`.

Use `Finset.sum_congr rfl fun m' _ => ?_` and prove the remaining obligations. Distinguish the cases in `hd : m'.degree = m.degree`. Distinguish the cases in `hz : ∀ q ∈ K, m' q = 0`. Rewrite using `[if_pos ⟨hd, hz⟩, if_pos hd, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun q _ => ?_` and prove the remaining obligations. Distinguish the cases in `hq : q ∈ K`. Simplify using `[hq, hz q hq]`. Simplify using `[hq]`. Rewrite `hz` using `[if_neg (fun h => hz h.2), if_pos hd, map_zero] push Not`.

Take `⟨q, hq, hq0⟩` from `hz`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq, hq0]), mul_zero]`. Rewrite using `[if_neg (fun h => hd h.1), if_neg hd, map_zero]`. Rewrite using `[aeval_C_mul_X_coeff, ← key]`. Conclude with `hxH`.
-/
theorem exists_point {ι L : Type} [Fintype ι] [Field L] [Infinite L] (K : Set ι)
    (F : MvPolynomial ι L) (m : ι →₀ ℕ) (hK : ∀ q ∈ K, m q = 0) (hm : F.coeff m ≠ 0) :
    ∃ b : ι → L, (∀ q ∈ K, b q = 0) ∧ (∀ q ∉ K, b q ≠ 0) ∧
      (MvPolynomial.aeval (fun q => C (b q) * X) F : L[X]).coeff m.degree ≠ 0 := by
  classical
  let H : MvPolynomial ι L := ∑ m' ∈ F.support.filter
      (fun m' => m'.degree = m.degree ∧ ∀ q ∈ K, m' q = 0), MvPolynomial.monomial m' (F.coeff m')
  have hHm : H.coeff m = F.coeff m := by
    simp only [H, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single m]
    · simp
    · intro m' _ hm'
      simp [hm']
    · intro hnot
      exfalso
      exact hnot (Finset.mem_filter.2 ⟨MvPolynomial.mem_support_iff.2 hm, rfl, hK⟩)
  let P : MvPolynomial ι L := H * ∏ q ∈ Finset.univ.filter (fun q => q ∉ K), MvPolynomial.X q
  have hP : P ≠ 0 := by
    apply mul_ne_zero
    · intro h0
      apply hm
      rw [← hHm, h0, MvPolynomial.coeff_zero]
    · exact Finset.prod_ne_zero_iff.2 fun q _ => MvPolynomial.X_ne_zero q
  obtain ⟨x, hx⟩ : ∃ x, MvPolynomial.eval x P ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hP (MvPolynomial.funext fun x => by simpa using hcon x)
  have hxH : MvPolynomial.eval x H ≠ 0 := fun h0 => hx (by simp [P, h0])
  have hxq : ∀ q ∉ K, x q ≠ 0 := by
    intro q hq h0
    apply hx
    simp only [P, map_mul, map_prod, MvPolynomial.eval_X]
    rw [Finset.prod_eq_zero (i := q) (by simp [hq]) h0, mul_zero]
  refine ⟨fun q => if q ∈ K then 0 else x q, fun q hq => by simp [hq],
    fun q hq => by simp [hq, hxq q hq], ?_⟩
  have key : MvPolynomial.eval x H = ∑ m' ∈ F.support, if m'.degree = m.degree then
      F.coeff m' * ∏ q, (if q ∈ K then 0 else x q) ^ m' q else 0 := by
    simp only [H, Finset.sum_filter, map_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    by_cases hd : m'.degree = m.degree
    · by_cases hz : ∀ q ∈ K, m' q = 0
      · rw [if_pos ⟨hd, hz⟩, if_pos hd, MvPolynomial.eval_monomial,
          Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
        congr 1
        refine Finset.prod_congr rfl fun q _ => ?_
        by_cases hq : q ∈ K
        · simp [hq, hz q hq]
        · simp [hq]
      · rw [if_neg (fun h => hz h.2), if_pos hd, map_zero]
        push Not at hz
        obtain ⟨q, hq, hq0⟩ := hz
        rw [Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq, hq0]), mul_zero]
    · rw [if_neg (fun h => hd h.1), if_neg hd, map_zero]
  rw [aeval_C_mul_X_coeff, ← key]
  exact hxH

/- English proof (translation)
Set `E` to `IntermediateField.adjoin k (Set.range b)`. Use `haveI : FiniteDimensional k E := IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)`. Take `⟨α, hα⟩` from `Field.exists_primitive_element_of_finite_bot k E`. Use `⟨(α : L), fun q => ?_⟩` and prove the remaining obligations. Establish `hbq : b q ∈ E` using `IntermediateField.subset_adjoin k _ ⟨q, rfl⟩`.

Establish `hmem : (⟨b q, hbq⟩ : E) ∈ (IntermediateField.adjoin k {α}).toSubalgebra`. Rewrite using `[IntermediateField.mem_toSubalgebra, hα]`. Conclude with `IntermediateField.mem_top`. Rewrite `hmem` using `[IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite k α), Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨p, hp⟩` from `hmem`.

Use `⟨p, ?_⟩` and prove the remaining obligations. Establish `h1 : aeval (E.val α) p = E.val (aeval α p)` using `Polynomial.aeval_algHom_apply E.val α p`. Rewrite using `[show (α : L) = E.val α from rfl, h1]`. Establish `h2 : (aeval α) p = ⟨b q, hbq⟩` using `hp`. Rewrite using `[h2]`.

Both sides reduce to the same expression.
-/
theorem exists_primitive {k L ι : Type} [Field k] [Finite k] [Field L] [Algebra k L]
    [Algebra.IsAlgebraic k L] [Finite ι] (b : ι → L) :
    ∃ α : L, ∀ q, ∃ p : k[X], aeval α p = b q := by
  classical
  let E := IntermediateField.adjoin k (Set.range b)
  haveI : FiniteDimensional k E := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_bot k E
  refine ⟨(α : L), fun q => ?_⟩
  have hbq : b q ∈ E := IntermediateField.subset_adjoin k _ ⟨q, rfl⟩
  have hmem : (⟨b q, hbq⟩ : E) ∈ (IntermediateField.adjoin k {α}).toSubalgebra := by
    rw [IntermediateField.mem_toSubalgebra, hα]
    exact IntermediateField.mem_top
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite k α),
    Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := hmem
  refine ⟨p, ?_⟩
  have h1 : aeval (E.val α) p = E.val (aeval α p) := Polynomial.aeval_algHom_apply E.val α p
  rw [show (α : L) = E.val α from rfl, h1]
  have h2 : (aeval α) p = ⟨b q, hbq⟩ := hp
  rw [h2]
  rfl

/- English proof (translation)
Use `haveI := (AdjoinRoot.powerBasis' hg).finite`. Conclude with `Module.finite_of_finite R`.
-/
private theorem finite_adjoinRoot_of_monic {R : Type} [CommRing R] [Finite R] {g : R[X]}
    (hg : g.Monic) : Finite (AdjoinRoot g) := by
  haveI := (AdjoinRoot.powerBasis' hg).finite
  exact Module.finite_of_finite R

/- English proof (translation)
Take `⟨α, hα⟩` from `exists_primitive (k := k) b`. Use `choose p hp using hα`. Establish `hint : IsIntegral k α` using `(Algebra.IsAlgebraic.isAlgebraic α).isIntegral`. Take `⟨g, hgmap, hgdeg, hgmon⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic ((Polynomial.mem_lifts _).2 (Polynomial.map_surjective φ hφ (minpoly k α))) (minpoly.monic hint)`. Establish `hdegpos : 0 < g.natDegree`.

Rewrite using `[hgdeg]`. Conclude with `minpoly.natDegree_pos hint`. Establish `hg0 : g.eval₂ ((algebraMap k L).comp φ) α = 0`. Rewrite using `[← Polynomial.eval₂_map, hgmap, ← Polynomial.aeval_def]`. Conclude with `minpoly.aeval k α`.

Use `⟨AdjoinRoot g, inferInstance, finite_adjoinRoot_of_monic hgmon, AdjoinRoot.of g, AdjoinRoot.lift ((algebraMap k L).comp φ) α hg0, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`. Establish `h0 : AdjoinRoot.of g (x - y) * AdjoinRoot.root g ^ 0 = 0`. Rewrite using `[map_sub, hxy, sub_self, zero_mul]`. Conclude with `sub_eq_zero.1 (adjoinRoot_eq_zero hgmon hdegpos h0)`.

Introduce `x`. Rewrite using `[AdjoinRoot.lift_of]`. Both sides reduce to the same expression. Introduce `s hs`. Take `⟨h, rfl⟩` from `AdjoinRoot.mk_surjective s`.

Rewrite `hs` using `[AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← Polynomial.aeval_def]`. Take `⟨t, ht⟩` from `minpoly.dvd k α hs`. Take `⟨t', rfl⟩` from `Polynomial.map_surjective φ hφ t`. Establish `he : ∀ n, (h - g * t').coeff n ∈ Ideal.span {π}`. Introduce `n`.

Use `Ideal.mem_span_singleton.2 (hπ _ ?_)` and prove the remaining obligations. Rewrite using `[← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, hgmap, ht, sub_self, Polynomial.coeff_zero]`. Establish `he' : h - g * t' ∈ Ideal.span {C π}`. Establish `h3` using `(Ideal.mem_map_C_iff (I := Ideal.span {π})).2 he`. Rewrite `h3` using `[Ideal.map_span, Set.image_singleton]`. Then use the resulting hypothesis.

Take `⟨u, hu⟩` from `Ideal.mem_span_singleton.1 he'`. Use `⟨AdjoinRoot.mk g u, ?_⟩` and prove the remaining obligations. Establish `hsplit : h = C π * u + g * t'`. Rewrite using `[← hu]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsplit, map_add, map_mul, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero, AdjoinRoot.mk_C]`. Introduce `q`. Take `⟨r, hr⟩` from `Polynomial.map_surjective φ hφ (p q)`. Use `⟨AdjoinRoot.mk g r, ?_⟩` and prove the remaining obligations. Rewrite using `[AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, hr, ← Polynomial.aeval_def, hp q]`.
-/
theorem exists_lift {R k L ι : Type} [CommRing R] [Finite R] [Field k] [Finite k] [Field L]
    [Algebra k L] [Algebra.IsAlgebraic k L] [Finite ι] (φ : R →+* k) (hφ : Function.Surjective φ)
    (π : R) (hπ : ∀ x, φ x = 0 → π ∣ x) (b : ι → L) :
    ∃ (S : Type) (_ : CommRing S) (_ : Finite S) (f : R →+* S) (ψ : S →+* L),
      Function.Injective f ∧ (∀ x, ψ (f x) = algebraMap k L (φ x)) ∧
      (∀ x, ψ x = 0 → f π ∣ x) ∧ ∀ q, ∃ s, ψ s = b q := by
  classical
  obtain ⟨α, hα⟩ := exists_primitive (k := k) b
  choose p hp using hα
  have hint : IsIntegral k α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  obtain ⟨g, hgmap, hgdeg, hgmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts _).2 (Polynomial.map_surjective φ hφ (minpoly k α))) (minpoly.monic hint)
  have hdegpos : 0 < g.natDegree := by
    rw [hgdeg]
    exact minpoly.natDegree_pos hint
  have hg0 : g.eval₂ ((algebraMap k L).comp φ) α = 0 := by
    rw [← Polynomial.eval₂_map, hgmap, ← Polynomial.aeval_def]
    exact minpoly.aeval k α
  refine ⟨AdjoinRoot g, inferInstance, finite_adjoinRoot_of_monic hgmon, AdjoinRoot.of g,
    AdjoinRoot.lift ((algebraMap k L).comp φ) α hg0, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have h0 : AdjoinRoot.of g (x - y) * AdjoinRoot.root g ^ 0 = 0 := by
      rw [map_sub, hxy, sub_self, zero_mul]
    exact sub_eq_zero.1 (adjoinRoot_eq_zero hgmon hdegpos h0)
  · intro x
    rw [AdjoinRoot.lift_of]
    rfl
  · intro s hs
    obtain ⟨h, rfl⟩ := AdjoinRoot.mk_surjective s
    rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← Polynomial.aeval_def] at hs
    obtain ⟨t, ht⟩ := minpoly.dvd k α hs
    obtain ⟨t', rfl⟩ := Polynomial.map_surjective φ hφ t
    have he : ∀ n, (h - g * t').coeff n ∈ Ideal.span {π} := by
      intro n
      refine Ideal.mem_span_singleton.2 (hπ _ ?_)
      rw [← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, hgmap, ht, sub_self,
        Polynomial.coeff_zero]
    have he' : h - g * t' ∈ Ideal.span {C π} := by
      have h3 := (Ideal.mem_map_C_iff (I := Ideal.span {π})).2 he
      rwa [Ideal.map_span, Set.image_singleton] at h3
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 he'
    refine ⟨AdjoinRoot.mk g u, ?_⟩
    have hsplit : h = C π * u + g * t' := by
      rw [← hu]
      ring
    rw [hsplit, map_add, map_mul, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero, AdjoinRoot.mk_C]
  · intro q
    obtain ⟨r, hr⟩ := Polynomial.map_surjective φ hφ (p q)
    refine ⟨AdjoinRoot.mk g r, ?_⟩
    rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, hr, ← Polynomial.aeval_def, hp q]

/- English proof (translation)
Establish `hnil : ∀ x, ψ x = 0 → IsNilpotent x` using `fun x hx => by`. Take `⟨c, rfl⟩` from `hπ x hx`. Conclude with `⟨n, by rw [mul_pow, hn, zero_mul]⟩`. Establish `hT : (X ^ (N + 1) : R[X]).Monic` using `Polynomial.monic_X_pow _`. Use `finite_adjoinRoot_of_monic hT` as an intermediate fact.

Establish `hT0 : (X ^ (N + 1) : R[X]).eval₂ ψ 0 = 0` using `by simp`. Establish `hroot : AdjoinRoot.root (X ^ (N + 1) : R[X]) ^ (N + 1) = 0`. Rewrite using `[← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]`. Establish `hnil' : ∀ z, AdjoinRoot.lift ψ (0 : L) hT0 z = 0 → IsNilpotent z`. Introduce `z hz`.

Take `⟨h, rfl⟩` from `AdjoinRoot.mk_surjective z`. Rewrite `hz` using `[AdjoinRoot.lift_mk, Polynomial.eval₂_at_zero]`. Establish `hsplit : h = C (h.coeff 0) + X * h.divX` using `(Polynomial.X_mul_divX_add h).symm.trans (add_comm _ _)`. Rewrite using `[hsplit, map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]`. Use `Commute.isNilpotent_add (Commute.all _ _) ((hnil _ hz).map _) ?_` and prove the remaining obligations.

Conclude with `⟨N + 1, by rw [mul_pow, hroot, zero_mul]⟩`. Use `⟨isLocalRing_of_map _ hnil', ?_⟩` and prove the remaining obligations. Establish `hex : ∃ i, ψ (P.coeff i) ≠ 0` using `⟨d, hP⟩`. Take `⟨d0, hd0, hmin⟩ : ∃ d0, ψ (P.coeff d0) ≠ 0 ∧ ∀ i < d0, ψ (P.coeff i) = 0` from `⟨Nat.find hex, Nat.find_spec hex, fun i hi => not_not.1 (Nat.find_min hex hi)⟩`. Establish `hd0le : d0 ≤ d`.

Assume the negation of the conclusion as `hlt`. Conclude with `hP (hmin d (by omega))`. Establish `hbelow : ∀ i, ∃ c, i < d0 → P.coeff i = π * c`. Introduce `i`. Distinguish the cases in `hi : i < d0`.

Take `⟨c, hc⟩` from `hπ _ (hmin i hi)`. Conclude with `⟨c, fun _ => hc⟩`. Conclude with `⟨0, fun h => absurd h hi⟩`. Use `choose c hc using hbelow`. Take `⟨A', hA'⟩ : ∃ A' : R[X], A' = ∑ i ∈ Finset.range d0, C (c i) * X ^ i` from `⟨_, rfl⟩`.

Establish `hA'coeff : ∀ j, A'.coeff j = if j < d0 then c j else 0`. Introduce `j`. Rewrite using `[hA', Polynomial.finsetSum_coeff]`. Simplify using `[Polynomial.coeff_C_mul_X_pow]`. Establish `hQ : X ^ d0 ∣ P - C π * A'`.

Rewrite using `[Polynomial.X_pow_dvd_iff]`. Introduce `j hj`. Rewrite using `[Polynomial.coeff_sub, Polynomial.coeff_C_mul, hc j hj, hA'coeff, if_pos hj, sub_self]`. Take `⟨V, hV⟩` from `hQ`. Establish `hV0 : V.coeff 0 = P.coeff d0`.

Establish `h1 : (X ^ d0 * V).coeff d0 = V.coeff 0`. Rewrite using `[Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]`. Rewrite using `[← h1, ← hV, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hA'coeff, if_neg (lt_irrefl d0), mul_zero, sub_zero]`. Establish `hu : IsUnit (AdjoinRoot.mk (X ^ (N + 1) : R[X]) V)`. Use `isUnit_of_map_ne_zero _ hnil' ?_` and prove the remaining obligations.

Rewrite using `[AdjoinRoot.lift_mk, Polynomial.eval₂_at_zero, hV0]`. Conclude with `hd0`. Establish `hy : AdjoinRoot.mk (X ^ (N + 1) : R[X]) P = AdjoinRoot.of (X ^ (N + 1) : R[X]) π * AdjoinRoot.mk (X ^ (N + 1) : R[X]) A' + AdjoinRoot.root (X ^ (N + 1) : R[X]) ^ d0 * AdjoinRoot.mk (X ^ (N + 1) : R[X]) V`. Establish `hP' : P = C π * A' + X ^ d0 * V`. Rewrite using `[← hV]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hP', map_add, map_mul, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]`. Establish `hπ0 : AdjoinRoot.of (X ^ (N + 1) : R[X]) π ^ n = 0`. Rewrite using `[← map_pow, hn, map_zero]`. Rewrite using `[← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]`.

Use `set J := Ideal.span {AdjoinRoot.mk (X ^ (N + 1) : R[X]) P} with hJ`. Establish `h1 : Ideal.Quotient.mk J (AdjoinRoot.mk (X ^ (N + 1) : R[X]) P) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)`. Rewrite `h1` using `[hy, map_add]`. Establish `h2` using `eq_neg_of_add_eq_zero_right h1`. Establish `h3 : Ideal.Quotient.mk J ((AdjoinRoot.root (X ^ (N + 1) : R[X]) ^ d0 * AdjoinRoot.mk (X ^ (N + 1) : R[X]) V) ^ n) = 0`.

Rewrite using `[map_pow, h2, neg_pow, ← map_pow, mul_pow, hπ0, zero_mul, map_zero, mul_zero]`. Rewrite `h3` using `[mul_pow, ← pow_mul, map_mul]`. Establish `h4` using `((hu.pow n).map (Ideal.Quotient.mk J)).mul_left_eq_zero.1 h3`. Establish `hw : n * w = d0 * n + n * (w - d0)`. Establish `hdw : d0 ≤ w` using `hd0le.trans hd`.

Rewrite using `[mul_comm d0 n, ← mul_add, Nat.add_sub_cancel' hdw]`. Rewrite using `[hw, pow_add (AdjoinRoot.root (X ^ (N + 1) : R[X])) (d0 * n) (n * (w - d0)), map_mul, h4, zero_mul]`.
-/
theorem exists_truncation {R L : Type} [CommRing R] [Finite R] [Field L] (ψ : R →+* L) (π : R)
    (n w N : ℕ) (hn : π ^ n = 0) (hπ : ∀ x, ψ x = 0 → π ∣ x) (P : R[X]) (d : ℕ) (hd : d ≤ w)
    (hP : ψ (P.coeff d) ≠ 0) :
    IsLocalRing (AdjoinRoot (X ^ (N + 1) : R[X])) ∧
      AdjoinRoot.mk (X ^ (N + 1) : R[X]) P ∣ AdjoinRoot.root (X ^ (N + 1) : R[X]) ^ (n * w) := by
  classical
  have hnil : ∀ x, ψ x = 0 → IsNilpotent x := fun x hx => by
    obtain ⟨c, rfl⟩ := hπ x hx
    exact ⟨n, by rw [mul_pow, hn, zero_mul]⟩
  have hT : (X ^ (N + 1) : R[X]).Monic := Polynomial.monic_X_pow _
  have := finite_adjoinRoot_of_monic hT
  have hT0 : (X ^ (N + 1) : R[X]).eval₂ ψ 0 = 0 := by simp
  have hroot : AdjoinRoot.root (X ^ (N + 1) : R[X]) ^ (N + 1) = 0 := by
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  have hnil' : ∀ z, AdjoinRoot.lift ψ (0 : L) hT0 z = 0 → IsNilpotent z := by
    intro z hz
    obtain ⟨h, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [AdjoinRoot.lift_mk, Polynomial.eval₂_at_zero] at hz
    have hsplit : h = C (h.coeff 0) + X * h.divX :=
      (Polynomial.X_mul_divX_add h).symm.trans (add_comm _ _)
    rw [hsplit, map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    refine Commute.isNilpotent_add (Commute.all _ _) ((hnil _ hz).map _) ?_
    exact ⟨N + 1, by rw [mul_pow, hroot, zero_mul]⟩
  refine ⟨isLocalRing_of_map _ hnil', ?_⟩
  have hex : ∃ i, ψ (P.coeff i) ≠ 0 := ⟨d, hP⟩
  obtain ⟨d0, hd0, hmin⟩ : ∃ d0, ψ (P.coeff d0) ≠ 0 ∧ ∀ i < d0, ψ (P.coeff i) = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => not_not.1 (Nat.find_min hex hi)⟩
  have hd0le : d0 ≤ d := by
    by_contra hlt
    exact hP (hmin d (by omega))
  have hbelow : ∀ i, ∃ c, i < d0 → P.coeff i = π * c := by
    intro i
    by_cases hi : i < d0
    · obtain ⟨c, hc⟩ := hπ _ (hmin i hi)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose c hc using hbelow
  obtain ⟨A', hA'⟩ : ∃ A' : R[X], A' = ∑ i ∈ Finset.range d0, C (c i) * X ^ i := ⟨_, rfl⟩
  have hA'coeff : ∀ j, A'.coeff j = if j < d0 then c j else 0 := by
    intro j
    rw [hA', Polynomial.finsetSum_coeff]
    simp [Polynomial.coeff_C_mul_X_pow]
  have hQ : X ^ d0 ∣ P - C π * A' := by
    rw [Polynomial.X_pow_dvd_iff]
    intro j hj
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, hc j hj, hA'coeff, if_pos hj, sub_self]
  obtain ⟨V, hV⟩ := hQ
  have hV0 : V.coeff 0 = P.coeff d0 := by
    have h1 : (X ^ d0 * V).coeff d0 = V.coeff 0 := by
      rw [Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
    rw [← h1, ← hV, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hA'coeff, if_neg (lt_irrefl d0),
      mul_zero, sub_zero]
  have hu : IsUnit (AdjoinRoot.mk (X ^ (N + 1) : R[X]) V) := by
    refine isUnit_of_map_ne_zero _ hnil' ?_
    rw [AdjoinRoot.lift_mk, Polynomial.eval₂_at_zero, hV0]
    exact hd0
  have hy : AdjoinRoot.mk (X ^ (N + 1) : R[X]) P =
      AdjoinRoot.of (X ^ (N + 1) : R[X]) π * AdjoinRoot.mk (X ^ (N + 1) : R[X]) A' +
        AdjoinRoot.root (X ^ (N + 1) : R[X]) ^ d0 * AdjoinRoot.mk (X ^ (N + 1) : R[X]) V := by
    have hP' : P = C π * A' + X ^ d0 * V := by
      rw [← hV]
      ring
    rw [hP', map_add, map_mul, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  have hπ0 : AdjoinRoot.of (X ^ (N + 1) : R[X]) π ^ n = 0 := by
    rw [← map_pow, hn, map_zero]
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  set J := Ideal.span {AdjoinRoot.mk (X ^ (N + 1) : R[X]) P} with hJ
  have h1 : Ideal.Quotient.mk J (AdjoinRoot.mk (X ^ (N + 1) : R[X]) P) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  rw [hy, map_add] at h1
  have h2 := eq_neg_of_add_eq_zero_right h1
  have h3 : Ideal.Quotient.mk J ((AdjoinRoot.root (X ^ (N + 1) : R[X]) ^ d0 *
      AdjoinRoot.mk (X ^ (N + 1) : R[X]) V) ^ n) = 0 := by
    rw [map_pow, h2, neg_pow, ← map_pow, mul_pow, hπ0, zero_mul, map_zero, mul_zero]
  rw [mul_pow, ← pow_mul, map_mul] at h3
  have h4 := ((hu.pow n).map (Ideal.Quotient.mk J)).mul_left_eq_zero.1 h3
  have hw : n * w = d0 * n + n * (w - d0) := by
    have hdw : d0 ≤ w := hd0le.trans hd
    rw [mul_comm d0 n, ← mul_add, Nat.add_sub_cancel' hdw]
  rw [hw, pow_add (AdjoinRoot.root (X ^ (N + 1) : R[X])) (d0 * n) (n * (w - d0)), map_mul, h4,
    zero_mul]

/- English proof (translation)
Take `⟨m, hmw, hmK, hmu⟩` from `hF`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hl0 : l ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hl`.

Take `⟨e', u, hlu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ`. Establish `he' : e' = e`. Establish `h1` using `IsDiscreteValuationRing.addVal_def l u hϖ e' hlu`. Rewrite `h1` using `[hl]`. Conclude with `h1.symm` after adjusting the coercions.

Rewrite `hlu` using `[he']`. Establish `hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}` using `hϖ.maximalIdeal_eq`. Take `⟨I, hI⟩ : ∃ I : Ideal O, I = Ideal.span {l} * IsLocalRing.maximalIdeal O` from `⟨_, rfl⟩`. Establish `hϖmem : ϖ ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hϖ.not_isUnit)`. Establish `hϖI : ϖ ^ (e + 1) ∈ I`.

Establish `h1 : ϖ ^ (e + 1) = ((↑u⁻¹ : O) * l) * ϖ`. Rewrite using `[hlu, ← mul_assoc (↑u⁻¹ : O), Units.inv_mul, one_mul, pow_succ]`. Rewrite using `[h1, hI]`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_span_singleton.2 (dvd_mul_left l _)) hϖmem`. Establish `hpow : IsLocalRing.maximalIdeal O ^ (e + 1) ≤ I`.

Rewrite using `[hmax, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hϖI`. Establish `: Finite (O ⧸ IsLocalRing.maximalIdeal O)` using `(inferInstance : Finite (IsLocalRing.ResidueField O))`. Establish `: Finite (O ⧸ IsLocalRing.maximalIdeal O ^ (e + 1))` using `Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _`. Establish `: Finite (O ⧸ I)` using `Finite.of_surjective (Ideal.Quotient.factor hpow) (Ideal.Quotient.factor_surjective hpow)`.

Establish `hIm : I ≤ IsLocalRing.maximalIdeal O`. Rewrite using `[hI]`. Conclude with `Ideal.mul_le_inf.trans inf_le_right`. Establish `hIle : ∀ x ∈ I, IsLocalRing.residue O x = 0` using `fun x hx => (IsLocalRing.residue_eq_zero_iff x).2 (hIm hx)`. Take `⟨φ, hφdef⟩ : ∃ φ : O ⧸ I →+* IsLocalRing.ResidueField O, ∀ x, φ (Ideal.Quotient.mk I x) = IsLocalRing.residue O x` from `⟨Ideal.Quotient.lift I (IsLocalRing.residue O) hIle, fun x => Ideal.Quotient.lift_mk I _ hIle⟩`.

Establish `hφsurj : Function.Surjective φ`. Introduce `y`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective y`. Conclude with `⟨Ideal.Quotient.mk I x, hφdef x⟩`. Establish `hker : ∀ x : O ⧸ I, φ x = 0 → Ideal.Quotient.mk I ϖ ∣ x`.

Introduce `x hx`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite `hx` using `[hφdef, IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton]`. Conclude with `map_dvd _ hx`. Take `⟨χ, hχdef⟩ : ∃ χ : O →+* AlgebraicClosure (IsLocalRing.ResidueField O), ∀ x, χ x = algebraMap _ _ (IsLocalRing.residue O x)` from `⟨(algebraMap _ _).comp (IsLocalRing.residue O), fun x => rfl⟩`.

Establish `hcoef : (F.map χ).coeff m ≠ 0`. Rewrite using `[MvPolynomial.coeff_map, hχdef]`. Introduce `h0`. Conclude with `(hmu.map (IsLocalRing.residue O)).ne_zero ((map_eq_zero_iff _ (algebraMap _ _).injective).1 h0)`. Take `⟨b, hbK, hbnK, hbcoef⟩` from `exists_point K (F.map χ) m hmK hcoef`.

Take `⟨S, _, _, f, ψ, hfinj, hψf, hψker, hψsurj⟩` from `exists_lift φ hφsurj (Ideal.Quotient.mk I ϖ) hker b`. Use `choose s hs using hψsurj`. Establish `: Nontrivial S` using `ψ.domain_nontrivial`. Take `⟨a, haK, hanK⟩ : ∃ a : ι → S, (∀ q ∈ K, a q = 0) ∧ (∀ q ∉ K, a q = s q)` from `⟨fun q => if q ∈ K then 0 else s q, fun q hq => if_pos hq, fun q hq => if_neg hq⟩`. Establish `hψa : ∀ q, ψ (a q) = b q`.

Introduce `q`. Distinguish the cases in `hq : q ∈ K`. Rewrite using `[haK q hq, map_zero, hbK q hq]`. Rewrite using `[hanK q hq, hs]`. Establish `hfπ : f (Ideal.Quotient.mk I ϖ) ^ (e + 1) = 0`.

Rewrite using `[← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 hϖI, map_zero]`. Establish `hnilS : ∀ x, ψ x = 0 → IsNilpotent x`. Introduce `x hx`. Take `⟨c, rfl⟩` from `hψker x hx`. Conclude with `⟨e + 1, by rw [mul_pow, hfπ, zero_mul]⟩`.

Establish `haU : ∀ q ∉ K, IsUnit (a q)`. Introduce `q hq`. Use `isUnit_of_map_ne_zero ψ hnilS ?_` and prove the remaining obligations. Rewrite using `[hψa]`. Conclude with `hbnK q hq`.

Take `⟨hOS, hOSdef⟩ : ∃ h : O →+* S, ∀ x, h x = f (Ideal.Quotient.mk I x)` from `⟨f.comp (Ideal.Quotient.mk I), fun _ => rfl⟩`. Take `⟨Pp, hPp⟩ : ∃ P : S[X], P = MvPolynomial.eval₂ (C.comp hOS) (fun q => C (a q) * X) F` from `⟨_, rfl⟩`. Establish `hmapP : Pp.map ψ = MvPolynomial.aeval (fun q => C (b q) * X) (F.map χ)`. Establish `e1 : (Polynomial.mapRingHom ψ).comp (C.comp hOS) = C.comp χ`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, hOSdef, hψf, hφdef, hχdef]`. Establish `e2 : (⇑(Polynomial.mapRingHom ψ) ∘ fun q => C (a q) * X) = fun q => C (b q) * X`. Use function extensionality and compare the values at `q`. Simplify using `[hψa]`. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.eval₂_map, Polynomial.algebraMap_eq, hPp, ← Polynomial.coe_mapRingHom, MvPolynomial.eval₂_comp_left, e1, e2]`.

Establish `hcoefP : ψ (Pp.coeff m.degree) ≠ 0`. Rewrite using `[← Polynomial.coeff_map, hmapP]`. Conclude with `hbcoef`. Take `⟨hloc, hdiv⟩` from `exists_truncation ψ (f (Ideal.Quotient.mk I ϖ)) (e + 1) w (2 * (e + 1) * w + 1) hfπ hψker Pp m.degree (by omega) hcoefP`. Establish `hTmon : (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]).Monic` using `Polynomial.monic_X_pow _`.

Use `finite_adjoinRoot_of_monic hTmon` as an intermediate fact. Set `alg : Algebra O (AdjoinRoot (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]))` to `((AdjoinRoot.of _).comp hOS).toAlgebra`. Use `⟨AdjoinRoot (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]), inferInstance, hloc, inferInstance, alg, AdjoinRoot.root _, fun q => AdjoinRoot.of _ (a q), ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[RingHom.algebraMap_toAlgebra, RingHom.comp_apply, hOSdef, Ideal.Quotient.eq_zero_iff_mem.2 (hI ▸ hx), map_zero, map_zero]`.

Rewrite using `[show 2 * (e + 1) * w + 2 = 2 * (e + 1) * w + 1 + 1 by ring, ← AdjoinRoot.mk_X, ← map_pow]`. Conclude with `AdjoinRoot.mk_self`. Introduce `h0`. Rewrite `h0` using `[RingHom.algebraMap_toAlgebra, RingHom.comp_apply]`. Establish `h1` using `adjoinRoot_eq_zero (r := hOS l) (j := 2 * (e + 1) * w + 1) hTmon (by rw [Polynomial.natDegree_X_pow]; omega) h0`.

Rewrite `h1` using `[hOSdef, ← map_zero f]`. Establish `hlI : l ∈ I` using `Ideal.Quotient.eq_zero_iff_mem.1 (hfinj h1)`. Rewrite `hlI` using `[hI, hmax, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `hlI`. Apply `hϖ.not_isUnit` to reduce the goal to its premises.

Establish `h2 : l * 1 = l * (ϖ * c)`. Rewrite using `[mul_one, ← mul_assoc]`. Conclude with `hc`. Establish `h3` using `mul_left_cancel₀ hl0 h2`. Conclude with `⟨⟨ϖ, c, h3.symm, by rw [mul_comm]; exact h3.symm⟩, rfl⟩`.

Introduce `q hq dsimp only`. Rewrite using `[haK q hq, map_zero]`. Introduce `q hq`. Conclude with `(haU q hq).map _`. Establish `hev : MvPolynomial.aeval (fun q => AdjoinRoot.of (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]) (a q) * AdjoinRoot.root _) F = AdjoinRoot.mk (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]) Pp`.

Establish `e3 : (AdjoinRoot.mk (X ^ (2 * (e + 1) * w + 1 + 1) : S[X])).comp (C.comp hOS) = (AdjoinRoot.of _).comp hOS`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, AdjoinRoot.mk_C]`. Establish `e4 : (⇑(AdjoinRoot.mk (X ^ (2 * (e + 1) * w + 1 + 1) : S[X])) ∘ fun q => C (a q) * X) = fun q => AdjoinRoot.of (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]) (a q) * AdjoinRoot.root _`. Use function extensionality and compare the values at `q`.

Simplify using `[AdjoinRoot.mk_C, AdjoinRoot.mk_X]`. Rewrite using `[MvPolynomial.aeval_def, RingHom.algebraMap_toAlgebra, hPp, MvPolynomial.eval₂_comp_left, e3, e4]`. Rewrite using `[hev]`. Conclude with `hdiv`.
-/
theorem exists_finite_local_ring (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (l : O) (e w : ℕ) (ι : Type) [Fintype ι] (K : Set ι)
    (F : MvPolynomial ι O) (hl : IsDiscreteValuationRing.addVal O l = e)
    (hF : ∃ m : ι →₀ ℕ, m.degree < w + 1 ∧ (∀ q ∈ K, m q = 0) ∧ IsUnit (F.coeff m)) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (_ : Finite A) (_ : Algebra O A) (t : A)
      (a : ι → A), (∀ x ∈ Ideal.span {l} * IsLocalRing.maximalIdeal O, algebraMap O A x = 0) ∧
      t ^ (2 * (e + 1) * w + 2) = 0 ∧ algebraMap O A l * t ^ (2 * (e + 1) * w + 1) ≠ 0 ∧
      (∀ q ∈ K, a q = 0) ∧ (∀ q ∉ K, IsUnit (a q)) ∧
      MvPolynomial.aeval (fun q => a q * t) F ∣ t ^ ((e + 1) * w) := by
  classical
  obtain ⟨m, hmw, hmK, hmu⟩ := hF
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl
  obtain ⟨e', u, hlu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have he' : e' = e := by
    have h1 := IsDiscreteValuationRing.addVal_def l u hϖ e' hlu
    rw [hl] at h1
    exact_mod_cast h1.symm
  rw [he'] at hlu
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  obtain ⟨I, hI⟩ : ∃ I : Ideal O, I = Ideal.span {l} * IsLocalRing.maximalIdeal O := ⟨_, rfl⟩
  have hϖmem : ϖ ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hϖ.not_isUnit)
  have hϖI : ϖ ^ (e + 1) ∈ I := by
    have h1 : ϖ ^ (e + 1) = ((↑u⁻¹ : O) * l) * ϖ := by
      rw [hlu, ← mul_assoc (↑u⁻¹ : O), Units.inv_mul, one_mul, pow_succ]
    rw [h1, hI]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton.2 (dvd_mul_left l _)) hϖmem
  have hpow : IsLocalRing.maximalIdeal O ^ (e + 1) ≤ I := by
    rw [hmax, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact hϖI
  have : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    (inferInstance : Finite (IsLocalRing.ResidueField O))
  have : Finite (O ⧸ IsLocalRing.maximalIdeal O ^ (e + 1)) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _
  have : Finite (O ⧸ I) := Finite.of_surjective (Ideal.Quotient.factor hpow)
    (Ideal.Quotient.factor_surjective hpow)
  have hIm : I ≤ IsLocalRing.maximalIdeal O := by
    rw [hI]
    exact Ideal.mul_le_inf.trans inf_le_right
  have hIle : ∀ x ∈ I, IsLocalRing.residue O x = 0 := fun x hx =>
    (IsLocalRing.residue_eq_zero_iff x).2 (hIm hx)
  obtain ⟨φ, hφdef⟩ : ∃ φ : O ⧸ I →+* IsLocalRing.ResidueField O,
      ∀ x, φ (Ideal.Quotient.mk I x) = IsLocalRing.residue O x :=
    ⟨Ideal.Quotient.lift I (IsLocalRing.residue O) hIle, fun x => Ideal.Quotient.lift_mk I _ hIle⟩
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨Ideal.Quotient.mk I x, hφdef x⟩
  have hker : ∀ x : O ⧸ I, φ x = 0 → Ideal.Quotient.mk I ϖ ∣ x := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hφdef, IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton] at hx
    exact map_dvd _ hx
  obtain ⟨χ, hχdef⟩ : ∃ χ : O →+* AlgebraicClosure (IsLocalRing.ResidueField O),
      ∀ x, χ x = algebraMap _ _ (IsLocalRing.residue O x) :=
    ⟨(algebraMap _ _).comp (IsLocalRing.residue O), fun x => rfl⟩
  have hcoef : (F.map χ).coeff m ≠ 0 := by
    rw [MvPolynomial.coeff_map, hχdef]
    intro h0
    exact (hmu.map (IsLocalRing.residue O)).ne_zero
      ((map_eq_zero_iff _ (algebraMap _ _).injective).1 h0)
  obtain ⟨b, hbK, hbnK, hbcoef⟩ := exists_point K (F.map χ) m hmK hcoef
  obtain ⟨S, _, _, f, ψ, hfinj, hψf, hψker, hψsurj⟩ :=
    exists_lift φ hφsurj (Ideal.Quotient.mk I ϖ) hker b
  choose s hs using hψsurj
  have : Nontrivial S := ψ.domain_nontrivial
  obtain ⟨a, haK, hanK⟩ : ∃ a : ι → S, (∀ q ∈ K, a q = 0) ∧ (∀ q ∉ K, a q = s q) :=
    ⟨fun q => if q ∈ K then 0 else s q, fun q hq => if_pos hq, fun q hq => if_neg hq⟩
  have hψa : ∀ q, ψ (a q) = b q := by
    intro q
    by_cases hq : q ∈ K
    · rw [haK q hq, map_zero, hbK q hq]
    · rw [hanK q hq, hs]
  have hfπ : f (Ideal.Quotient.mk I ϖ) ^ (e + 1) = 0 := by
    rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 hϖI, map_zero]
  have hnilS : ∀ x, ψ x = 0 → IsNilpotent x := by
    intro x hx
    obtain ⟨c, rfl⟩ := hψker x hx
    exact ⟨e + 1, by rw [mul_pow, hfπ, zero_mul]⟩
  have haU : ∀ q ∉ K, IsUnit (a q) := by
    intro q hq
    refine isUnit_of_map_ne_zero ψ hnilS ?_
    rw [hψa]
    exact hbnK q hq
  obtain ⟨hOS, hOSdef⟩ : ∃ h : O →+* S, ∀ x, h x = f (Ideal.Quotient.mk I x) :=
    ⟨f.comp (Ideal.Quotient.mk I), fun _ => rfl⟩
  obtain ⟨Pp, hPp⟩ : ∃ P : S[X], P = MvPolynomial.eval₂ (C.comp hOS) (fun q => C (a q) * X) F :=
    ⟨_, rfl⟩
  have hmapP : Pp.map ψ = MvPolynomial.aeval (fun q => C (b q) * X) (F.map χ) := by
    have e1 : (Polynomial.mapRingHom ψ).comp (C.comp hOS) = C.comp χ := by
      refine RingHom.ext fun x => ?_
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, hOSdef, hψf,
        hφdef, hχdef]
    have e2 : (⇑(Polynomial.mapRingHom ψ) ∘ fun q => C (a q) * X) = fun q => C (b q) * X := by
      funext q
      simp [hψa]
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, Polynomial.algebraMap_eq, hPp,
      ← Polynomial.coe_mapRingHom, MvPolynomial.eval₂_comp_left, e1, e2]
  have hcoefP : ψ (Pp.coeff m.degree) ≠ 0 := by
    rw [← Polynomial.coeff_map, hmapP]
    exact hbcoef
  obtain ⟨hloc, hdiv⟩ := exists_truncation ψ (f (Ideal.Quotient.mk I ϖ)) (e + 1) w
    (2 * (e + 1) * w + 1) hfπ hψker Pp m.degree (by omega) hcoefP
  have hTmon : (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]).Monic := Polynomial.monic_X_pow _
  have := finite_adjoinRoot_of_monic hTmon
  let alg : Algebra O (AdjoinRoot (X ^ (2 * (e + 1) * w + 1 + 1) : S[X])) :=
    ((AdjoinRoot.of _).comp hOS).toAlgebra
  refine ⟨AdjoinRoot (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]), inferInstance, hloc, inferInstance, alg,
    AdjoinRoot.root _, fun q => AdjoinRoot.of _ (a q), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, hOSdef, Ideal.Quotient.eq_zero_iff_mem.2 (hI ▸ hx), map_zero, map_zero]
  · rw [show 2 * (e + 1) * w + 2 = 2 * (e + 1) * w + 1 + 1 by ring, ← AdjoinRoot.mk_X, ← map_pow]
    exact AdjoinRoot.mk_self
  · intro h0
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] at h0
    have h1 := adjoinRoot_eq_zero (r := hOS l) (j := 2 * (e + 1) * w + 1) hTmon
      (by rw [Polynomial.natDegree_X_pow]; omega) h0
    rw [hOSdef, ← map_zero f] at h1
    have hlI : l ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (hfinj h1)
    rw [hI, hmax, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton] at hlI
    obtain ⟨c, hc⟩ := hlI
    apply hϖ.not_isUnit
    have h2 : l * 1 = l * (ϖ * c) := by
      rw [mul_one, ← mul_assoc]
      exact hc
    have h3 := mul_left_cancel₀ hl0 h2
    exact ⟨⟨ϖ, c, h3.symm, by rw [mul_comm]; exact h3.symm⟩, rfl⟩
  · intro q hq
    dsimp only
    rw [haK q hq, map_zero]
  · intro q hq
    exact (haU q hq).map _
  · have hev : MvPolynomial.aeval (fun q => AdjoinRoot.of (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]) (a q) *
        AdjoinRoot.root _) F = AdjoinRoot.mk (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]) Pp := by
      have e3 : (AdjoinRoot.mk (X ^ (2 * (e + 1) * w + 1 + 1) : S[X])).comp (C.comp hOS) =
          (AdjoinRoot.of _).comp hOS := by
        refine RingHom.ext fun x => ?_
        simp only [RingHom.comp_apply, AdjoinRoot.mk_C]
      have e4 : (⇑(AdjoinRoot.mk (X ^ (2 * (e + 1) * w + 1 + 1) : S[X])) ∘ fun q => C (a q) * X) =
          fun q => AdjoinRoot.of (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]) (a q) * AdjoinRoot.root _ := by
        funext q
        simp [AdjoinRoot.mk_C, AdjoinRoot.mk_X]
      rw [MvPolynomial.aeval_def, RingHom.algebraMap_toAlgebra, hPp, MvPolynomial.eval₂_comp_left,
        e3, e4]
    rw [hev]
    exact hdiv

end GlobalTheory.NewPrime.LocalRing
