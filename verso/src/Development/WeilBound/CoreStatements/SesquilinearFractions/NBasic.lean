import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

/- English proof (translation)
Use `letI : Algebra k k' := f.toAlgebra`. Conclude with `IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`.
-/
theorem isScalarTower_rat_of_ringHom {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') :
    letI : Algebra k k' := f.toAlgebra
    IsScalarTower ℚ k k' := by
  letI : Algebra k k' := f.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

/- English proof (translation)
Introduce `k k' A _ _ _ _ _ _ _ f j`. Use `letI : Algebra k k' := f.toAlgebra`. Use `letI : Algebra k A := j.toAlgebra`. Use `haveI : IsScalarTower ℚ k k' := isScalarTower_rat_of_ringHom f`. Use `haveI : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'`.

Use `haveI : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'`. Use `⟨(IsAlgClosed.lift : k' →ₐ[k] A).toRingHom, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Conclude with `(IsAlgClosed.lift : k' →ₐ[k] A).commutes x`.
-/
theorem exists_extension_embedding_alg_closed : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (j : k →+* A), ∃ j' : k' →+* A, j'.comp f = j := by
  intro k k' A _ _ _ _ _ _ _ f j
  letI : Algebra k k' := f.toAlgebra
  letI : Algebra k A := j.toAlgebra
  haveI : IsScalarTower ℚ k k' := isScalarTower_rat_of_ringHom f
  haveI : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'
  haveI : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  refine ⟨(IsAlgClosed.lift : k' →ₐ[k] A).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : k' →ₐ[k] A).commutes x

open Classical in
/- English proof (translation)
Use `letI : Algebra k k' := f.toAlgebra`. Use `letI : Algebra k A := j.toAlgebra`. Use `haveI : IsScalarTower ℚ k k' := isScalarTower_rat_of_ringHom f`. Use `haveI : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'`. Rewrite using `[← Fintype.card_subtype, Fintype.card_eq_nat_card, ← AlgHom.natCard_of_splits k k' A (fun _ => IsAlgClosed.splits _)]`.

Use `Nat.card_congr { toFun := fun ψ => { ψ.1 with commutes' := fun r => RingHom.congr_fun ψ.2 r } invFun := fun φ => ⟨φ.toRingHom, RingHom.ext φ.commutes⟩ left_inv := fun ψ => rfl right_inv := fun φ => rfl }` and prove the remaining obligations.
-/
theorem card_embeddings_extending {k k' A : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A]
    [IsAlgClosed A] (f : k →+* k') (j : k →+* A) :
    letI : Algebra k k' := f.toAlgebra
    (Finset.univ.filter fun j' : k' →+* A => j'.comp f = j).card = Module.finrank k k' := by
  letI : Algebra k k' := f.toAlgebra
  letI : Algebra k A := j.toAlgebra
  haveI : IsScalarTower ℚ k k' := isScalarTower_rat_of_ringHom f
  haveI : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'
  rw [← Fintype.card_subtype, Fintype.card_eq_nat_card,
    ← AlgHom.natCard_of_splits k k' A (fun _ => IsAlgClosed.splits _)]
  refine Nat.card_congr
    { toFun := fun ψ => { ψ.1 with commutes' := fun r => RingHom.congr_fun ψ.2 r }
      invFun := fun φ => ⟨φ.toRingHom, RingHom.ext φ.commutes⟩
      left_inv := fun ψ => rfl
      right_inv := fun φ => rfl }

/- English proof (translation)
Introduce `k k' A _ _ _ _ _ _ _ f F`. Use `letI : Algebra k k' := f.toAlgebra`. Use `haveI : IsScalarTower ℚ k k' := isScalarTower_rat_of_ringHom f`. Establish `hsum : ∑ j' : k' →+* A, F (j'.comp f) = (Module.finrank k k' : ℝ) * ∑ j : k →+* A, F j`. Rewrite using `[← Finset.sum_fiberwise Finset.univ (fun j' : k' →+* A => j'.comp f), Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (g := fun _ => F j) (fun j' hj' => by rw [(Finset.mem_filter.1 hj').2]), Finset.sum_const, nsmul_eq_mul]`. Use `congr 2`. Use `card_embeddings_extending f j` and compare the differences between its conclusion and the goal. Rewrite using `[hsum, ← Module.finrank_mul_finrank ℚ k k']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_embeddings_base_change : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (F : (k →+* A) → ℝ), (Module.finrank ℚ k : ℝ) * ∑ j : k' →+* A, F (j.comp f) = (Module.finrank ℚ k' : ℝ) * ∑ j : k →+* A, F j := by
  intro k k' A _ _ _ _ _ _ _ f F
  classical
  letI : Algebra k k' := f.toAlgebra
  haveI : IsScalarTower ℚ k k' := isScalarTower_rat_of_ringHom f
  have hsum : ∑ j' : k' →+* A, F (j'.comp f) = (Module.finrank k k' : ℝ) * ∑ j : k →+* A, F j := by
    rw [← Finset.sum_fiberwise Finset.univ (fun j' : k' →+* A => j'.comp f), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => F j) (fun j' hj' => by rw [(Finset.mem_filter.1 hj').2]),
      Finset.sum_const, nsmul_eq_mul]
    congr 2
    convert card_embeddings_extending f j
  rw [hsum, ← Module.finrank_mul_finrank ℚ k k']
  push_cast
  ring

/- English proof (translation)
The claim follows from `(mul_finsum g c).symm`.
-/
theorem finsum_const_mul {α : Type} (c : ℝ) (_hc : c ≠ 0) (g : α → ℝ) : ∑ᶠ p, c * g p = c * ∑ᶠ p, g p :=
  (mul_finsum g c).symm

/- English proof (translation)
Introduce `k k' _ _ _ _ f N`. Establish `hd : (0:ℝ) < Module.finrank ℚ k` using `by exact_mod_cast Module.finrank_pos`. Establish `hd' : (0:ℝ) < Module.finrank ℚ k'` using `by exact_mod_cast Module.finrank_pos`. Use `set c : ℝ := (Module.finrank ℚ k' : ℝ) / Module.finrank ℚ k with hc_def`. Establish `hc : c ≠ 0` using `(div_pos hd' hd).ne'`.

Establish `hinf : ∑ s : k' →+* ℂ, N.inf (s.comp f) = c * ∑ s : k →+* ℂ, N.inf s`. Rewrite using `[hc_def, div_mul_eq_mul_div, eq_div_iff hd.ne', ← sum_embeddings_base_change k k' ℂ f N.inf]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfin : ∀ p : Nat.Primes, (N.ext f).finSum p = c * N.finSum p`. Introduce `p`.

Use `show ∑ ι : k' →+* ℂ_[(p:ℕ)], N.fin p (ι.comp f) = c * ∑ ι : k →+* ℂ_[(p:ℕ)], N.fin p ι`. Rewrite using `[hc_def, div_mul_eq_mul_div, eq_div_iff hd.ne', ← sum_embeddings_base_change k k' ℂ_[(p:ℕ)] f (N.fin p)]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show -(∑ s : k' →+* ℂ, N.inf (s.comp f) + ∑ᶠ p, (N.ext f).finSum p) / (Module.finrank ℚ k' : ℝ) = N.deg`.

Rewrite using `[hinf, finsum_congr hfin, finsum_const_mul c hc, ← mul_add, LogNorms.deg, hc_def]`. Clear the denominators using the available nonvanishing facts. Establish `hset : {p : Nat.Primes | ∃ ι : k' →+* ℂ_[(p:ℕ)], (N.ext f).fin p ι ≠ 0} = {p : Nat.Primes | ∃ ι : k →+* ℂ_[(p:ℕ)], N.fin p ι ≠ 0}`. Use extensionality with `p`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨ι, h⟩`. Conclude with `⟨ι.comp f, h⟩`. Introduce and unpack `⟨ι, h⟩`. Take `⟨ι', hι'⟩` from `exists_extension_embedding_alg_closed k k' ℂ_[(p:ℕ)] f ι`. Use `⟨ι', ?_⟩` and prove the remaining obligations.

Use `show N.fin p (ι'.comp f) ≠ 0`. Rewrite using `[hι']`. Conclude with `h`. Unfold `LogNorms.IsAdelic`. Rewrite using `[hset]`.
-/
theorem logNorms_ext_degree_adelic : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') (N : LogNorms k), (N.ext f).deg = N.deg ∧ ((N.ext f).IsAdelic ↔ N.IsAdelic) := by
  intro k k' _ _ _ _ f N
  have hd : (0:ℝ) < Module.finrank ℚ k := by exact_mod_cast Module.finrank_pos
  have hd' : (0:ℝ) < Module.finrank ℚ k' := by exact_mod_cast Module.finrank_pos
  set c : ℝ := (Module.finrank ℚ k' : ℝ) / Module.finrank ℚ k with hc_def
  have hc : c ≠ 0 := (div_pos hd' hd).ne'
  have hinf : ∑ s : k' →+* ℂ, N.inf (s.comp f) = c * ∑ s : k →+* ℂ, N.inf s := by
    rw [hc_def, div_mul_eq_mul_div, eq_div_iff hd.ne', ← sum_embeddings_base_change k k' ℂ f N.inf]
    ring
  have hfin : ∀ p : Nat.Primes, (N.ext f).finSum p = c * N.finSum p := by
    intro p
    show ∑ ι : k' →+* ℂ_[(p:ℕ)], N.fin p (ι.comp f) = c * ∑ ι : k →+* ℂ_[(p:ℕ)], N.fin p ι
    rw [hc_def, div_mul_eq_mul_div, eq_div_iff hd.ne', ← sum_embeddings_base_change k k' ℂ_[(p:ℕ)] f (N.fin p)]
    ring
  refine ⟨?_, ?_⟩
  · show -(∑ s : k' →+* ℂ, N.inf (s.comp f) + ∑ᶠ p, (N.ext f).finSum p) / (Module.finrank ℚ k' : ℝ) = N.deg
    rw [hinf, finsum_congr hfin, finsum_const_mul c hc, ← mul_add, LogNorms.deg, hc_def]
    field_simp
  · have hset : {p : Nat.Primes | ∃ ι : k' →+* ℂ_[(p:ℕ)], (N.ext f).fin p ι ≠ 0} =
        {p : Nat.Primes | ∃ ι : k →+* ℂ_[(p:ℕ)], N.fin p ι ≠ 0} := by
      ext p
      constructor
      · rintro ⟨ι, h⟩
        exact ⟨ι.comp f, h⟩
      · rintro ⟨ι, h⟩
        obtain ⟨ι', hι'⟩ := exists_extension_embedding_alg_closed k k' ℂ_[(p:ℕ)] f ι
        refine ⟨ι', ?_⟩
        show N.fin p (ι'.comp f) ≠ 0
        rw [hι']
        exact h
    unfold LogNorms.IsAdelic
    rw [hset]

end PositivityTheory.Xgf
