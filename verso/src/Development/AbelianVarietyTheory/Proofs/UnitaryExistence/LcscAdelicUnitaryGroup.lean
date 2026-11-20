import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterMem

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct RestrictedProduct

namespace GlobalTheory.AdelicUnitaryTop

section Restricted

/- English proof (translation)
Establish `hS : ∀ T : Finset ι, cofinite ≤ 𝓟 ((T : Set ι)ᶜ)` using `fun T => le_principal_iff.2 (T.finite_toSet.compl_mem_cofinite)`. Establish `hsc : ∀ T : Finset ι, SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 ((T : Set ι)ᶜ)])` using `fun T => RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology`. Establish `he` using `fun T : Finset ι => RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hS T)`. Use `haveI : ∀ T : Finset ι, SecondCountableTopology (Set.range (RestrictedProduct.inclusion R A (hS T))) := fun T => (he T).isEmbedding.toHomeomorph.symm.secondCountableTopology`. Use `TopologicalSpace.secondCountableTopology_of_countable_cover (fun T => (he T).isOpen_range) ?_` and prove the remaining obligations.

Use `Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_` and prove the remaining obligations. Establish `hx : {i | ¬ x i ∈ A i}.Finite` using `eventually_cofinite.1 x.2`. Use `⟨hx.toFinset, ?_⟩` and prove the remaining obligations. Use `RestrictedProduct.exists_inclusion_eq_of_eventually R A (hS _) ?_` and prove the remaining obligations. Introduce `i hi`.

Assume the negation of the conclusion as `h`. Conclude with `hi (by simpa using h)`.
-/
theorem secondCountable_restrictedProduct {ι : Type} [Countable ι] (R : ι → Type)
    [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)] (A : ∀ i, Set (R i))
    (hA : ∀ i, IsOpen (A i)) : SecondCountableTopology (Πʳ i, [R i, A i]) := by
  have hS : ∀ T : Finset ι, cofinite ≤ 𝓟 ((T : Set ι)ᶜ) := fun T =>
    le_principal_iff.2 (T.finite_toSet.compl_mem_cofinite)
  have hsc : ∀ T : Finset ι, SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 ((T : Set ι)ᶜ)]) :=
    fun T => RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
  have he := fun T : Finset ι => RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hS T)
  haveI : ∀ T : Finset ι, SecondCountableTopology
      (Set.range (RestrictedProduct.inclusion R A (hS T))) := fun T =>
    (he T).isEmbedding.toHomeomorph.symm.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun T => (he T).isOpen_range) ?_
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  have hx : {i | ¬ x i ∈ A i}.Finite := eventually_cofinite.1 x.2
  refine ⟨hx.toFinset, ?_⟩
  refine RestrictedProduct.exists_inclusion_eq_of_eventually R A (hS _) ?_
  intro i hi
  by_contra h
  exact hi (by simpa using h)

end Restricted

section Adeles

variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
Use `Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2 ⟨inferInstance, ?_, ?_⟩` and prove the remaining obligations. Conclude with `inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))`. Conclude with `Formalism.UG.P.glint_finite_residueField v`.
-/
theorem properSpace_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    ProperSpace (v.adicCompletion F) := by
  refine Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2
    ⟨inferInstance, ?_, ?_⟩
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  · exact Formalism.UG.P.glint_finite_residueField v

/- English proof (translation)
The claim follows from `Valued.integer.properSpace_iff_compactSpace_integer.1 (properSpace_adicCompletion F v)`.
-/
theorem compactSpace_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) :=
  Valued.integer.properSpace_iff_compactSpace_integer.1 (properSpace_adicCompletion F v)

/- English proof (translation)
Use `haveI : Countable (𝓞 F) := by haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable`. Conclude with `RingOfIntegers.coe_injective.countable`. Use `haveI : Countable (Ideal (𝓞 F)) := by`. Use `Function.Surjective.countable (f := fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) ?_` and prove the remaining obligations. Introduce `I`.

Conclude with `(IsNoetherian.noetherian I : I.FG)`. Conclude with `Function.Injective.countable (f := fun la : HeightOneSpectrum (𝓞 F) => la.asIdeal) fun a b h => HeightOneSpectrum.ext h`.
-/
theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable (𝓞 F) := by
    haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact RingOfIntegers.coe_injective.countable
  haveI : Countable (Ideal (𝓞 F)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) ?_
    intro I
    exact (IsNoetherian.noetherian I : I.FG)
  exact Function.Injective.countable (f := fun la : HeightOneSpectrum (𝓞 F) => la.asIdeal)
      fun a b h => HeightOneSpectrum.ext h

/- English proof (translation)
Use `haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩`. Use `haveI := properSpace_adicCompletion F`. Conclude with `RestrictedProduct.locallyCompactSpace_of_addGroup (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (.of_forall fun v => isCompact_iff_compactSpace.2 (compactSpace_adicCompletionIntegers F v))`.
-/
theorem locallyCompact_finiteAdele : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  haveI := properSpace_adicCompletion F
  exact RestrictedProduct.locallyCompactSpace_of_addGroup
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (.of_forall fun v => isCompact_iff_compactSpace.2 (compactSpace_adicCompletionIntegers F v))

/- English proof (translation)
Use `haveI := properSpace_adicCompletion F`. Use `haveI := countable_heightOneSpectrum F`. Conclude with `secondCountable_restrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) fun _ ↦ Valued.isOpen_valuationSubring _`.
-/
theorem secondCountable_finiteAdele : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  haveI := properSpace_adicCompletion F
  haveI := countable_heightOneSpectrum F
  exact secondCountable_restrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun _ ↦ Valued.isOpen_valuationSubring _

/- English proof (translation)
The claim follows from `inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))`.
-/
theorem t2Space_finiteAdeleRing_of_numberField : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

/- English proof (translation)
Use `haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v => (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology`. Conclude with `inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))`.
-/
theorem secondCountable_infiniteAdele : SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))

/- English proof (translation)
The claim follows from `inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))`.
-/
theorem t2Space_infiniteAdeleRing_of_numberField_field : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))

/- English proof (translation)
The claim follows from `haveI := locallyCompact_finiteAdele F inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))`.
-/
theorem locallyCompact_adele : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  haveI := locallyCompact_finiteAdele F
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

/- English proof (translation)
The claim follows from `haveI := secondCountable_finiteAdele F haveI := secondCountable_infiniteAdele F inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))`.
-/
theorem secondCountable_adele : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  haveI := secondCountable_finiteAdele F
  haveI := secondCountable_infiniteAdele F
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

/- English proof (translation)
The claim follows from `haveI := t2Space_finiteAdeleRing_of_numberField F haveI := t2Space_infiniteAdeleRing_of_numberField_field F inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))`.
-/
theorem t2Space_adeleRing_numberField : T2Space (AdeleRing (𝓞 F) F) :=
  haveI := t2Space_finiteAdeleRing_of_numberField F
  haveI := t2Space_infiniteAdeleRing_of_numberField_field F
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end Adeles

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

/- English proof (translation)
Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _`. Set `e` to `(Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun`. Conclude with `⟨{ e.toEquiv with continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩`.
-/
theorem nonempty_homeomorph :
    Nonempty (R ⊗[F] E ≃ₜ (Fin (Module.finrank F E) → R)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact ⟨{ e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩

/- English proof (translation)
Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _`. Conclude with `IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap`.
-/
theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.Yzd4.lcsc_HA <;> assumption`.
-/
theorem lcsc_HA [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    LocallyCompactSpace (HA R σ J) ∧ SecondCountableTopology (HA R σ J) ∧ T2Space (HA R σ J) :=
  by apply _root_.UpperTheory.Reformulated.B.Yzd4.lcsc_HA <;> assumption

end Tensor

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M J`. Use `haveI := locallyCompact_adele F`. Use `haveI := secondCountable_adele F`. Use `haveI := t2Space_adeleRing_numberField F`. Conclude with `lcsc_HA (AF F) σ M J`.
-/
theorem lcsc_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), LocallyCompactSpace (HA (AF F) σ J) ∧ SecondCountableTopology (HA (AF F) σ J) ∧ T2Space (HA (AF F) σ J) := by
  intro F E _ _ _ _ _ σ M J
  haveI := locallyCompact_adele F
  haveI := secondCountable_adele F
  haveI := t2Space_adeleRing_numberField F
  exact lcsc_HA (AF F) σ M J

end GlobalTheory.AdelicUnitaryTop
