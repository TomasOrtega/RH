import Mathlib
open NumberField Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `i hi`. Use `set s := Q.roots with hs`. Establish `hprod : (s.map fun z => X - C z).prod = Q`. Establish `h` using `C_leadingCoeff_mul_prod_multiset_X_sub_C (p := Q) IsAlgClosed.card_roots_eq_natDegree`. Rewrite `h` using `[hQ.leadingCoeff, C_1, one_mul]`. Then use the resulting hypothesis.

Establish `hrevX : ∀ z ∈ s, (X - C z : ℂ[X]).reverse = C (-z) * (X - C (starRingEnd ℂ z))`. Introduce `z hz`. Establish `hz1 : z * starRingEnd ℂ z = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hroots z hz]`. Simplify using the standard rewrite rules.

Rewrite using `[sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, ← one_mul (X : ℂ[X]), reverse_mul_X, ← C_1, reverse_C]`. Rewrite using `[mul_sub, ← C_mul, neg_mul, hz1]`. Simplify using `only [C_1, C_neg, one_mul, pow_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hrev : Q.reverse = C (Q.coeff 0) * Q.map (starRingEnd ℂ)`.

Establish `key : ∀ t : Multiset ℂ, (∀ z ∈ t, (X - C z : ℂ[X]).reverse = C (-z) * (X - C (starRingEnd ℂ z))) → (t.map fun z => X - C z).prod.reverse = (t.map fun z => C (-z) * (X - C (starRingEnd ℂ z))).prod`. Introduce `t`. Proceed by induction on `t using Multiset.induction_on with`. Consider the case `empty => intro _`. Simplify using `using reverse_C (1 : ℂ)`.

Consider the case `cons a t ih`. Introduce `h`. Rewrite using `[Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, reverse_mul_of_domain, ih (fun z hz => h z (Multiset.mem_cons_of_mem hz)), h a (Multiset.mem_cons_self a t)]`. Use `conv_lhs => rw [← hprod]`. Rewrite using `[key s hrevX, Multiset.prod_map_mul]`.

Use `conv_rhs => rw [← hprod]`. Use `congr 1`. Rewrite using `[coeff_zero_multiset_prod, Multiset.map_map, map_multiset_prod, Multiset.map_map]`. Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises.

Introduce `z _`. Simplify using the standard rewrite rules. Rewrite using `[Polynomial.map_multiset_prod, Multiset.map_map]`. Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises.

Introduce `z _`. Simplify using the standard rewrite rules. Establish `h1` using `congrArg (fun p => p.coeff i) hrev`. Simplify using `only [coeff_reverse, coeff_C_mul, coeff_map] at h1`. Rewrite `h1` using `[revAt_le hi]`. Then use the resulting hypothesis.
-/
theorem coeff_natDegree_sub_eq_of_roots_norm_one (Q : ℂ[X]) (hQ : Q.Monic)
    (hroots : ∀ z ∈ Q.roots, ‖z‖ = 1) :
    ∀ i ≤ Q.natDegree, Q.coeff (Q.natDegree - i) = Q.coeff 0 * starRingEnd ℂ (Q.coeff i) := by
  intro i hi
  set s := Q.roots with hs
  have hprod : (s.map fun z => X - C z).prod = Q := by
    have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := Q) IsAlgClosed.card_roots_eq_natDegree
    rwa [hQ.leadingCoeff, C_1, one_mul] at h
  have hrevX : ∀ z ∈ s, (X - C z : ℂ[X]).reverse = C (-z) * (X - C (starRingEnd ℂ z)) := by
    intro z hz
    have hz1 : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hroots z hz]; simp
    rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, ← one_mul (X : ℂ[X]), reverse_mul_X, ← C_1, reverse_C]
    rw [mul_sub, ← C_mul, neg_mul, hz1]
    simp only [C_1, C_neg, one_mul, pow_one]
    ring
  have hrev : Q.reverse = C (Q.coeff 0) * Q.map (starRingEnd ℂ) := by
    have key : ∀ t : Multiset ℂ, (∀ z ∈ t, (X - C z : ℂ[X]).reverse = C (-z) * (X - C (starRingEnd ℂ z))) →
        (t.map fun z => X - C z).prod.reverse
          = (t.map fun z => C (-z) * (X - C (starRingEnd ℂ z))).prod := by
      intro t
      induction t using Multiset.induction_on with
      | empty => intro _; simpa using reverse_C (1 : ℂ)
      | cons a t ih =>
        intro h
        rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
          reverse_mul_of_domain, ih (fun z hz => h z (Multiset.mem_cons_of_mem hz)),
          h a (Multiset.mem_cons_self a t)]
    conv_lhs => rw [← hprod]
    rw [key s hrevX, Multiset.prod_map_mul]
    conv_rhs => rw [← hprod]
    congr 1
    · rw [coeff_zero_multiset_prod, Multiset.map_map, map_multiset_prod, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro z _
      simp
    · rw [Polynomial.map_multiset_prod, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro z _
      simp
  have h1 := congrArg (fun p => p.coeff i) hrev
  simp only [coeff_reverse, coeff_C_mul, coeff_map] at h1
  rwa [revAt_le hi] at h1

/- English proof (translation)
Introduce `E _ _ _ n P hP hn hroots i hi`. Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom`. Establish `hQ : (P.map τ).Monic` using `hP.map τ`. Establish `hdeg : (P.map τ).natDegree = n` using `by rw [hP.natDegree_map, hn]`. Establish `h` using `coeff_natDegree_sub_eq_of_roots_norm_one (P.map τ) hQ (hroots τ) i (hdeg ▸ hi)`.

Rewrite `h` using `[hdeg, coeff_map, coeff_map, coeff_map, ← IsCMField.complexEmbedding_complexConj E τ, ← map_mul]`. Conclude with `τ.injective h`.
-/
theorem monic_coeff_natDegree_sub_eq_mul_complexConj :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Polynomial E),
    P.Monic → P.natDegree = n → (∀ (τ : E →+* ℂ), ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) →
    ∀ i ≤ n, P.coeff (n - i) = P.coeff 0 * IsCMField.complexConj E (P.coeff i) := by
  intro E _ _ _ n P hP hn hroots i hi
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  have hQ : (P.map τ).Monic := hP.map τ
  have hdeg : (P.map τ).natDegree = n := by rw [hP.natDegree_map, hn]
  have h := coeff_natDegree_sub_eq_of_roots_norm_one (P.map τ) hQ (hroots τ) i (hdeg ▸ hi)
  rw [hdeg, coeff_map, coeff_map, coeff_map, ← IsCMField.complexEmbedding_complexConj E τ,
    ← map_mul] at h
  exact τ.injective h

end GlobalTheory
