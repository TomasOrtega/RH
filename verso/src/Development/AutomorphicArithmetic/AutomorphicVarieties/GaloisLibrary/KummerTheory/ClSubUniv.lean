import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Substitute using the available equality.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Kum.clSubUniv :
    ∀ (K : Type) [Field K] [NumberField K], clSub (Set.univ : Set (HeightOneSpectrum (𝓞 K))) = ⊤ := by
  intro K _ _
  classical
  have key : ∀ I : Ideal (𝓞 K), ∀ hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)),
      ClassGroup.mk0 ⟨I, hI⟩ ∈ clSub (Set.univ : Set (HeightOneSpectrum (𝓞 K))) := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro hI
      exact absurd hI (zero_notMem_nonZeroDivisors)
    | h₂ u hu =>
      intro hI
      have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
      subst hu'
      have : (⟨⊤, hI⟩ : nonZeroDivisors (Ideal (𝓞 K))) = 1 := Subtype.ext Ideal.one_eq_top.symm
      rw [this, map_one]
      exact Subgroup.one_mem _
    | h₃ a p ha hp ih =>
      intro hI
      have ha' : a ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero ha
      have hp0 : p ≠ 0 := hp.ne_zero
      have hp' : p ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hp0
      have hsplit : (⟨p * a, hI⟩ : nonZeroDivisors (Ideal (𝓞 K))) = ⟨p, hp'⟩ * ⟨a, ha'⟩ := rfl
      rw [hsplit, map_mul]
      refine Subgroup.mul_mem _ ?_ (ih ha')
      have hpr : p.IsPrime := (Ideal.prime_iff_isPrime hp0).mp hp
      let v : HeightOneSpectrum (𝓞 K) := ⟨p, hpr, hp0⟩
      have hv : primeCl v = ClassGroup.mk0 ⟨p, hp'⟩ := rfl
      rw [← hv]
      exact Subgroup.subset_closure ⟨v, Set.mem_univ _, rfl⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective x
  exact key I hI
