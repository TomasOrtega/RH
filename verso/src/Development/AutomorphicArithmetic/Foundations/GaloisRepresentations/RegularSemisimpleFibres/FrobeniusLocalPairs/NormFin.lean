import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinety

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
private theorem UpperTheory.Gal.InertialTypesAlt.L.range_eq_ker_of_exact {U : Type} [CommGroup U] [Finite U]
    (N D : U →* U) (h1 : N.range ≤ D.ker) (h2 : N.ker = D.range) : N.range = D.ker := by
  apply Subgroup.eq_of_le_of_card_ge h1
  have c1 := Subgroup.card_mul_index N.ker
  have c2 := Subgroup.card_mul_index D.ker
  rw [Subgroup.index_ker, h2] at c1
  rw [Subgroup.index_ker] at c2
  have hp : 0 < Nat.card D.range := Nat.card_pos
  have e : Nat.card D.range * Nat.card N.range = Nat.card D.range * Nat.card D.ker := by
    nlinarith
  exact (Nat.eq_of_mul_eq_mul_left hp e).ge

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Both sides reduce to the same expression. Treat this case separately. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.normFin :
    UpperTheory.Gal.InertialTypesAlt.L.NormFin := by
  intro F₀ F₁ _ _ _ _ _ sb hsb A _ _ _ τ hτ hper x hx hfix
  have H := UpperTheory.Gal.InertialTypesAlt.L.hilbert_ninety_frobenius_twisted_finite_algebra F₀ F₁ sb hsb A τ hτ hper
  generalize Module.finrank F₀ F₁ = d at hper H ⊢
  have hit : ∀ i (a b : A), (⇑τ)^[i] (a * b) = (⇑τ)^[i] a * (⇑τ)^[i] b := by
    intro i
    induction i with
    | zero => intro a b; rfl
    | succ n ih => intro a b; simp only [Function.iterate_succ_apply', ih, map_mul]
  have hit1 : ∀ i, (⇑τ)^[i] (1 : A) = 1 := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_one]
  have hmul : ∀ a b : A, UpperTheory.Gal.InertialTypesAlt.L.itN τ d (a * b)
      = UpperTheory.Gal.InertialTypesAlt.L.itN τ d a * UpperTheory.Gal.InertialTypesAlt.L.itN τ d b := by
    intro a b
    simp only [UpperTheory.Gal.InertialTypesAlt.L.itN, hit, Finset.prod_mul_distrib]
  have hone : UpperTheory.Gal.InertialTypesAlt.L.itN τ d 1 = 1 := by
    simp only [UpperTheory.Gal.InertialTypesAlt.L.itN, hit1, Finset.prod_const_one]
  have hinv : ∀ a : A, τ (UpperTheory.Gal.InertialTypesAlt.L.itN τ d a) = UpperTheory.Gal.InertialTypesAlt.L.itN τ d a := by
    intro a
    have ha := hper a
    simp only [UpperTheory.Gal.InertialTypesAlt.L.itN, map_prod]
    have e : ∀ i, τ ((⇑τ)^[i] a) = (⇑τ)^[i + 1] a :=
      fun i => (Function.iterate_succ_apply' _ _ _).symm
    simp only [e]
    cases d with
    | zero => simp
    | succ k =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun i => (⇑τ)^[i] a), ha]
      rfl
  have hτN : ∀ a : A, UpperTheory.Gal.InertialTypesAlt.L.itN τ d (τ a) = UpperTheory.Gal.InertialTypesAlt.L.itN τ d a := by
    intro a
    rw [← hinv a]
    simp only [UpperTheory.Gal.InertialTypesAlt.L.itN, map_prod]
    exact Finset.prod_congr rfl (fun i _ => by
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply'])
  obtain ⟨N, hN⟩ : ∃ N : Aˣ →* Aˣ, ∀ u, (N u : A) = UpperTheory.Gal.InertialTypesAlt.L.itN τ d u :=
    ⟨Units.map { toFun := UpperTheory.Gal.InertialTypesAlt.L.itN τ d, map_one' := hone, map_mul' := hmul },
      fun u => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Aˣ →* Aˣ, ∀ u, (T u : A) = τ u :=
    ⟨Units.map (MonoidHomClass.toMonoidHom τ), fun u => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Aˣ →* Aˣ, ∀ u, D u = u / T u := ⟨MonoidHom.id _ / T, fun u => rfl⟩
  have hr : N.range ≤ D.ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker, hD, div_eq_one]
    ext
    rw [hT, hN, hinv]
  have hk : N.ker = D.range := by
    ext c
    constructor
    · intro hc
      rw [MonoidHom.mem_ker, Units.ext_iff, hN, Units.val_one] at hc
      obtain ⟨y, hy⟩ := H c hc
      refine ⟨y, ?_⟩
      rw [hD, div_eq_iff_eq_mul]
      ext
      rw [Units.val_mul, hT]
      exact hy.symm
    · rintro ⟨y, rfl⟩
      rw [MonoidHom.mem_ker, hD, map_div, div_eq_one]
      ext
      rw [hN, hN, hT, hτN]
  have heq := UpperTheory.Gal.InertialTypesAlt.L.range_eq_ker_of_exact N D hr hk
  have hu : hx.unit ∈ D.ker := by
    rw [MonoidHom.mem_ker, hD, div_eq_one]
    ext
    rw [hT, IsUnit.unit_spec, hfix]
  rw [← heq] at hu
  obtain ⟨y, hy⟩ := hu
  exact ⟨y, by rw [← hN, hy, IsUnit.unit_spec]⟩
