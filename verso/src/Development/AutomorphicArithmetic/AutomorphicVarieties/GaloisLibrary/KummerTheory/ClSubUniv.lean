import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

/- English proof (translation)
Introduce `K _ _`. Establish `key : ∀ I : Ideal (𝓞 K), ∀ hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)), ClassGroup.mk0 ⟨I, hI⟩ ∈ clSub (Set.univ : Set (HeightOneSpectrum (𝓞 K)))`. Introduce `I`. Proceed by induction on `I using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁`.

Introduce `hI`. Conclude with `absurd hI (zero_notMem_nonZeroDivisors)`. Consider the case `h₂ u hu`. Introduce `hI`. Establish `hu' : u = ⊤` using `Ideal.isUnit_iff.mp hu`.

Substitute `hu'` using the available equality. Establish `: (⟨⊤, hI⟩ : nonZeroDivisors (Ideal (𝓞 K))) = 1` using `Subtype.ext Ideal.one_eq_top.symm`. Rewrite using `[this, map_one]`. Conclude with `Subgroup.one_mem _`. Consider the case `h₃ a p ha hp ih`.

Introduce `hI`. Establish `ha' : a ∈ nonZeroDivisors (Ideal (𝓞 K))` using `mem_nonZeroDivisors_of_ne_zero ha`. Establish `hp0 : p ≠ 0` using `hp.ne_zero`. Establish `hp' : p ∈ nonZeroDivisors (Ideal (𝓞 K))` using `mem_nonZeroDivisors_of_ne_zero hp0`. Establish `hsplit : (⟨p * a, hI⟩ : nonZeroDivisors (Ideal (𝓞 K))) = ⟨p, hp'⟩ * ⟨a, ha'⟩` using `rfl`.

Rewrite using `[hsplit, map_mul]`. Use `Subgroup.mul_mem _ ?_ (ih ha')` and prove the remaining obligations. Establish `hpr : p.IsPrime` using `(Ideal.prime_iff_isPrime hp0).mp hp`. Set `v : HeightOneSpectrum (𝓞 K)` to `⟨p, hpr, hp0⟩`. Establish `hv : primeCl v = ClassGroup.mk0 ⟨p, hp'⟩` using `rfl`.

Rewrite using `[← hv]`. Conclude with `Subgroup.subset_closure ⟨v, Set.mem_univ _, rfl⟩`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨⟨I, hI⟩, rfl⟩` from `ClassGroup.mk0_surjective x`.

Conclude with `key I hI`.
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
