import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

/- English proof (translation)
Equip the data with the indicated structure. A detailed English derivation is pending.
-/
theorem isScalarTower_rat_of_ringHom {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') :
    letI : Algebra k k' := f.toAlgebra
    IsScalarTower ℚ k k' := by
  letI : Algebra k k' := f.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

A detailed English derivation is pending.
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
Equip the data with the indicated structure. Equip the data with the indicated structure. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem finsum_const_mul {α : Type} (c : ℝ) (_hc : c ≠ 0) (g : α → ℝ) : ∑ᶠ p, c * g p = c * ∑ᶠ p, g p :=
  (mul_finsum g c).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Establish an intermediate fact.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
