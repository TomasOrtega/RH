import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.FinrankAdjoinRootsEqRootDeg

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ f σ hσ`. Establish `hc : ∀ g : G F' Ω', ∀ x : F, ((σ.trans g.toRingEquiv).trans σ.symm) (algebraMap F Ω x) = algebraMap F Ω x`. Introduce `g x`. Simplify using `only [RingEquiv.trans_apply, hσ, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]`. Rewrite using `[← hσ, RingEquiv.symm_apply_apply]`.

Set `φ : G F' Ω' →* G F Ω` to `{ toFun := fun g => AlgEquiv.ofRingEquiv (hc g) map_one' := by`. Use extensionality with `x`. Simplify using the standard rewrite rules. Use the proof step `map_mul' := by`. Introduce `a b`.

Use extensionality with `x`. Simplify using `}`. Establish `hφ : ∀ g x, φ g x = σ.symm (g (σ x))` using `fun _ _ => rfl`. Use `haveI : Algebra.IsAlgebraic F' Ω' := IsAlgClosure.isAlgebraic`. Use `⟨φ, ?_, fun g x => by rw [hφ, σ.apply_symm_apply], ?_, ?_, ?_⟩` and prove the remaining obligations.

Apply `continuous_of_continuousAt_one` to reduce the goal to its premises. Rewrite using `[ContinuousAt, map_one, Filter.tendsto_def]`. Introduce `U hU`. Take `⟨E, hE, hEU⟩` from `(krullTopology_mem_nhds_one_iff F Ω U).1 hU`. Set `b` to `Module.finBasis F E`.

Establish `hV : (⋂ i, {g : G F' Ω' | g (σ (b i)) = σ (b i)}) ∈ nhds (1 : G F' Ω')` using `Filter.iInter_mem.2 fun i => IsOpen.mem_nhds (isOpen_setOf_apply (σ (b i)) (fun y => y = σ (b i))) rfl`. Use `Filter.mem_of_superset hV ?_` and prove the remaining obligations. Introduce `g hg`. Apply `hEU` to reduce the goal to its premises. Establish `hb : ∀ i, φ g (b i) = b i`.

Introduce `i`. Rewrite using `[hφ, Set.mem_iInter.1 hg i, RingEquiv.symm_apply_apply]`. Use `show φ g ∈ fixingSubgroup (G F Ω) (E : Set Ω)`. Rewrite using `[mem_fixingSubgroup_iff]`. Introduce `y hy`.

Rewrite using `[AlgEquiv.smul_def]`. Establish `hs` using `congrArg (fun z : E => (z : Ω)) (b.sum_repr ⟨y, hy⟩)`. Simplify using `only [IntermediateField.coe_sum, IntermediateField.coe_smul] at hs`. Rewrite using `[← hs, map_sum]`. Simplify using `[map_smul, hb]`.

Introduce `l _ g haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap F' Ω').injective haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F haveI : IsAlgClosed Ω' := IsAlgClosure.isAlgClosed F'`. Simplify using `only [cycZ, MonoidHom.comp_apply]`. Use `(KStar.TotallyRealRoots.cyclotomicCharacter_conj σ _ _ fun x => ?_).symm` and prove the remaining obligations. Use `show g (σ x) = σ (φ g x)`. Rewrite using `[hφ, σ.apply_symm_apply]`.

Introduce `a b h`. Use extensionality with `y`. Use `congrArg (fun k : G F Ω => k (σ.symm y)) h` as an intermediate fact. Simplify `this` using `[hφ]`. Introduce `hf h`.

Establish `hc' : ∀ y : F', ((σ.symm.trans h.toRingEquiv).trans σ) (algebraMap F' Ω' y) = algebraMap F' Ω' y`. Introduce `y`. Take `⟨x, rfl⟩` from `hf y`. Rewrite using `[← hσ]`. Simplify using the standard rewrite rules.

Conclude with `⟨AlgEquiv.ofRingEquiv hc', by ext x; simp [hφ]⟩`.
-/
theorem UpperTheory.V.LDataCardLeFinrank.galTransport :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (f : F →+* F') (σ : Ω ≃+* Ω'), (∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) →
      ∃ φ : G F' Ω' →* G F Ω, Continuous φ ∧ (∀ g x, σ (φ g x) = g (σ x)) ∧ (∀ (l : ℕ) [Fact l.Prime] (g : G F' Ω'), cycZ F Ω l (φ g) = cycZ F' Ω' l g) ∧ Function.Injective φ ∧ (Function.Surjective f → Function.Surjective φ) := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ f σ hσ
  have hc : ∀ g : G F' Ω', ∀ x : F,
      ((σ.trans g.toRingEquiv).trans σ.symm) (algebraMap F Ω x) = algebraMap F Ω x := by
    intro g x
    simp only [RingEquiv.trans_apply, hσ, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes]
    rw [← hσ, RingEquiv.symm_apply_apply]
  let φ : G F' Ω' →* G F Ω :=
    { toFun := fun g => AlgEquiv.ofRingEquiv (hc g)
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro a b
        ext x
        simp }
  have hφ : ∀ g x, φ g x = σ.symm (g (σ x)) := fun _ _ => rfl
  haveI : Algebra.IsAlgebraic F' Ω' := IsAlgClosure.isAlgebraic
  refine ⟨φ, ?_, fun g x => by rw [hφ, σ.apply_symm_apply], ?_, ?_, ?_⟩
  · apply continuous_of_continuousAt_one
    rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro U hU
    obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff F Ω U).1 hU
    let b := Module.finBasis F E
    have hV : (⋂ i, {g : G F' Ω' | g (σ (b i)) = σ (b i)}) ∈ nhds (1 : G F' Ω') :=
      Filter.iInter_mem.2 fun i =>
        IsOpen.mem_nhds (isOpen_setOf_apply (σ (b i)) (fun y => y = σ (b i))) rfl
    refine Filter.mem_of_superset hV ?_
    intro g hg
    apply hEU
    have hb : ∀ i, φ g (b i) = b i := by
      intro i
      rw [hφ, Set.mem_iInter.1 hg i, RingEquiv.symm_apply_apply]
    show φ g ∈ fixingSubgroup (G F Ω) (E : Set Ω)
    rw [mem_fixingSubgroup_iff]
    intro y hy
    rw [AlgEquiv.smul_def]
    have hs := congrArg (fun z : E => (z : Ω)) (b.sum_repr ⟨y, hy⟩)
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at hs
    rw [← hs, map_sum]
    simp [map_smul, hb]
  · intro l _ g
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
    haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap F' Ω').injective
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
    haveI : IsAlgClosed Ω' := IsAlgClosure.isAlgClosed F'
    simp only [cycZ, MonoidHom.comp_apply]
    refine (KStar.TotallyRealRoots.cyclotomicCharacter_conj σ _ _ fun x => ?_).symm
    show g (σ x) = σ (φ g x)
    rw [hφ, σ.apply_symm_apply]
  · intro a b h
    ext y
    have := congrArg (fun k : G F Ω => k (σ.symm y)) h
    simpa [hφ] using this
  · intro hf h
    have hc' : ∀ y : F', ((σ.symm.trans h.toRingEquiv).trans σ) (algebraMap F' Ω' y) =
        algebraMap F' Ω' y := by
      intro y
      obtain ⟨x, rfl⟩ := hf y
      rw [← hσ]
      simp
    exact ⟨AlgEquiv.ofRingEquiv hc', by ext x; simp [hφ]⟩
