import Mathlib

noncomputable section

open AddMonoidAlgebra

namespace GlobalTheory.GroupAlg

variable (R : Type*) [CommRing R] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X)

abbrev mapAlgebra : Algebra R[Y] R[X] := (mapDomainRingHom R u).toAlgebra

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mapAlgebra_tower : letI := mapAlgebra R u; IsScalarTower R R[Y] R[X] :=
  letI := mapAlgebra R u
  IsScalarTower.of_algebraMap_eq fun a => ((mapDomainAlgHom R R u).commutes a).symm

def cosetComb : letI := mapAlgebra R u; ((X ⧸ u.range) →₀ R[Y]) →ₗ[R[Y]] R[X] :=
  letI := mapAlgebra R u
  Finsupp.linearCombination R[Y] (fun c : X ⧸ u.range => (single c.out 1 : R[X]))

/- English proof (translation)
Equip the data with the indicated structure. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem cosetComb_single (c : X ⧸ u.range) (y : Y) (r : R) :
    cosetComb R u (Finsupp.single c (single y r)) = single (u y + c.out) r := by
  letI := mapAlgebra R u
  rw [cosetComb, Finsupp.linearCombination_single, Algebra.smul_def]
  change mapDomain u (single y r) * _ = _
  rw [mapDomain_single, single_mul_single, mul_one]

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_add_out (x : X) :
    ∃ y, u y + (QuotientAddGroup.mk x : X ⧸ u.range).out = x := by
  obtain ⟨⟨_, y, rfl⟩, h⟩ := QuotientAddGroup.mk_out_eq_mul u.range x
  exact ⟨-y, by rw [h]; simp⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem cosetComb_surjective : Function.Surjective (cosetComb R u) := by
  intro p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add s t hs ht =>
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := ht
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    obtain ⟨y, hy⟩ := exists_add_out u x
    exact ⟨_, (cosetComb_single R u _ y r).trans (by rw [hy])⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify by unfolding definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Both sides reduce to the same expression. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem coset_bijective (hu : Function.Injective u) :
    Function.Bijective (fun p : (Σ _ : X ⧸ u.range, Y) => u p.2 + p.1.out) := by
  refine ⟨?_, fun x => ?_⟩
  · rintro ⟨c, y⟩ ⟨d, z⟩ h
    dsimp only at h
    have h1 : ∀ (c : X ⧸ u.range) y, (QuotientAddGroup.mk (u y + c.out) : X ⧸ u.range) = c := by
      intro c y
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff (N := u.range) (u y)).2 ⟨y, rfl⟩, zero_add,
        QuotientAddGroup.out_eq']
    obtain rfl : c = d := by rw [← h1 c y, h, h1]
    obtain rfl : y = z := hu (add_right_cancel h)
    rfl
  · obtain ⟨y, hy⟩ := exists_add_out u x
    exact ⟨⟨_, y⟩, hy⟩

/- English proof (translation)
Equip the data with the indicated structure. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem cosetComb_injective (hu : Function.Injective u) : Function.Injective (cosetComb R u) := by
  letI := mapAlgebra R u
  haveI := mapAlgebra_tower R u
  let b : Module.Basis (Σ _ : X ⧸ u.range, Y) R ((X ⧸ u.range) →₀ R[Y]) :=
    Finsupp.basis fun _ => AddMonoidAlgebra.basis Y R
  let e := b.equiv (AddMonoidAlgebra.basis X R) (Equiv.ofBijective _ (coset_bijective u hu))
  have : (cosetComb R u).restrictScalars R = e.toLinearMap := by
    refine b.ext fun p => ?_
    obtain ⟨c, y⟩ := p
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
    simp [b, cosetComb_single]
  have h2 : ⇑(cosetComb R u) = e := congrArg DFunLike.coe this
  rw [h2]
  exact e.injective

def cosetBasis (hu : Function.Injective u) :
    letI := mapAlgebra R u; Module.Basis (X ⧸ u.range) R[Y] R[X] :=
  letI := mapAlgebra R u
  .ofRepr (LinearEquiv.ofBijective (cosetComb R u)
    ⟨cosetComb_injective R u hu, cosetComb_surjective R u⟩).symm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem free_of_injective (hu : Function.Injective u) :
    letI := mapAlgebra R u; Module.Free R[Y] R[X] :=
  letI := mapAlgebra R u
  .of_basis (cosetBasis R u hu)

/- English proof (translation)
Equip the data with the indicated structure. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem faithfullyFlat_of_injective (hu : Function.Injective u) :
    (mapDomainRingHom R u).FaithfullyFlat := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  change Module.FaithfullyFlat R[Y] R[X]
  rcases subsingleton_or_nontrivial R with h | h
  · have : Subsingleton R[Y] := Module.subsingleton R _
    exact ⟨fun m hm => (hm.ne_top (Subsingleton.elim _ _)).elim⟩
  · infer_instance

/- English proof (translation)
Equip the data with the indicated structure. A detailed English derivation is pending.
-/
theorem finite_of_finiteIndex [u.range.FiniteIndex] : (mapDomainRingHom R u).Finite := by
  letI := mapAlgebra R u
  exact Module.Finite.of_surjective (cosetComb R u) (cosetComb_surjective R u)

/- English proof (translation)
Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem finitePresentation_of_injective (hu : Function.Injective u) [u.range.FiniteIndex] :
    (mapDomainRingHom R u).FinitePresentation := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  have : Module.Finite R[Y] R[X] := finite_of_finiteIndex R u
  have : Module.FinitePresentation R[Y] R[X] := Module.finitePresentation_of_projective _ _
  exact (inferInstance : Algebra.FinitePresentation R[Y] R[X])

/- English proof (translation)
Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem finrank_of_injective (hu : Function.Injective u) [u.range.FiniteIndex]
    (p : PrimeSpectrum R[Y]) : (mapDomainRingHom R u).finrank p = u.range.index := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  have : Module.Finite R[Y] R[X] := finite_of_finiteIndex R u
  have : Nontrivial R[Y] := p.nontrivial
  change Module.rankAtStalk (R := R[Y]) R[X] p = _
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_nat_card_basis (cosetBasis R u hu)]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem surjective_of_surjective (hu : Function.Surjective u) :
    Function.Surjective (mapDomainRingHom R u) := by
  intro p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add s t hs ht =>
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := ht
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    obtain ⟨y, rfl⟩ := hu x
    exact ⟨single y r, mapDomain_single⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem formallyUnramified_of_isUnit (n : ℕ) (hn : IsUnit (n : R)) (hX : ∀ x : X, n • x = 0) :
    Algebra.FormallyUnramified R R[X] := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI f g h
  ext x
  have hB : IsUnit (n : B) := by simpa using hn.map (algebraMap R B)
  have hfg : f (single x 1) - g (single x 1) ∈ I := by
    rw [← Ideal.Quotient.eq]
    exact DFunLike.congr_fun h (single x 1)
  have hp : ∀ k : R[X] →ₐ[R] B, k (single x 1) ^ n = 1 := fun k => by
    rw [← map_pow, single_pow, hX, one_pow, ← one_def, map_one]
  set a := f (single x 1)
  set b := g (single x 1)
  have hi : (a - b) * (a - b) = 0 := by
    have := Ideal.mul_mem_mul hfg hfg
    rwa [← pow_two, hI, Ideal.mem_bot] at this
  have key : ∀ m : ℕ, b * a ^ m = b ^ (m + 1) + m * b ^ m * (a - b) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ a, ← mul_assoc, ih]
      push_cast
      linear_combination (m * b ^ m) * hi
  have h3 := key n
  rw [pow_succ b, hp f, hp g] at h3
  have h4 : (n : B) * (a - b) = 0 := by linear_combination -h3
  have h5 : a - b = 0 := (hB.mul_right_eq_zero).1 h4
  exact sub_eq_zero.1 h5

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem etale_of_isUnit_card [Finite X] (hn : IsUnit (Nat.card X : R)) : Algebra.Etale R R[X] := by
  have := formallyUnramified_of_isUnit R (X := X) _ hn fun x => card_nsmul_eq_zero'
  have : Module.FinitePresentation R R[X] := Module.finitePresentation_of_projective _ _
  exact Algebra.Etale.of_formallyUnramified_of_flat

end GlobalTheory.GroupAlg
