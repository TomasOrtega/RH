import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
import GroundTheory.GlobalFields.CompletionAtPlace.Inertia
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.ExistsCen

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

open CompanionTheory.PlaceDict in
/- English proof (translation)
Establish `: Algebra.IsIntegral (𝓞 L) (𝓞 Ω)` using `⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩`. Use `w.isMaximal` as an intermediate fact. Take `⟨Q, hQ, hw⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 Ω) w.asIdeal (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 Ω))]`. Conclude with `bot_le)`.

Take `⟨A, rfl⟩` from `exists_cen Q`. Conclude with `⟨A, hQ, hw⟩`.
-/
private theorem exists_over {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [Algebra.IsAlgebraic E Ω] (L : IntermediateField E Ω) [NumberField L]
    (w : HeightOneSpectrum (𝓞 L)) : ∃ A : ValuationSubring Ω, (cen A).IsMaximal ∧ (cen A).under (𝓞 L) = w.asIdeal := by
  have : Algebra.IsIntegral (𝓞 L) (𝓞 Ω) := ⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩
  have := w.isMaximal
  obtain ⟨Q, hQ, hw⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 Ω) w.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 Ω))]
    exact bot_le)
  obtain ⟨A, rfl⟩ := exists_cen Q
  exact ⟨A, hQ, hw⟩

open CompanionTheory.PlaceDict in
/- English proof (translation)
Take `⟨A, hm, hw⟩` from `exists_over L w`. Take `⟨φ, h1, h2⟩` from `lift L (cen A) τ (RingHom.id _) fun x => by`. Rewrite using `[RingHom.id_apply, Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap]`. Conclude with `(hw.ge (hτ x) :)`. Take `⟨h3, h4⟩` from `of_cong A φ one_ne_zero fun b => by`.

Rewrite using `[pow_one]`. Conclude with `Ideal.Quotient.eq.1 (h2 b)`. Conclude with `⟨A, φ, h1, h3, fun x hx => by`. Simplify using `using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩`.
-/
private theorem lift_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsGalois E Ω] (L : IntermediateField E Ω) [FiniteDimensional E L] [Normal E L] [NumberField L]
    (w : HeightOneSpectrum (𝓞 L)) (τ : L ≃ₐ[E] L) (hτ : τ ∈ w.asIdeal.inertia (L ≃ₐ[E] L)) :
    ∃ (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), AlgEquiv.restrictNormalHom L φ = τ ∧ φ ∈ Ine (F := E) A := by
  obtain ⟨A, hm, hw⟩ := exists_over L w
  obtain ⟨φ, h1, h2⟩ := lift L (cen A) τ (RingHom.id _) fun x => by
    rw [RingHom.id_apply, Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap]
    exact (hw.ge (hτ x) :)
  obtain ⟨h3, h4⟩ := of_cong A φ one_ne_zero fun b => by
    rw [pow_one]
    exact Ideal.Quotient.eq.1 (h2 b)
  exact ⟨A, φ, h1, h3, fun x hx => by
    simpa using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩

/- English proof (translation)
Set `_ : Algebra L ℂ` to `j₀.toAlgebra`. Set `_ : Algebra E ℂ` to `(j₀.comp (algebraMap E L)).toAlgebra`. Establish `: IsScalarTower E L ℂ` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: Algebra.IsAlgebraic L Ω` using `Algebra.IsAlgebraic.tower_top (K := E) L`. Set `j : Ω →ₐ[L] ℂ` to `IsAlgClosed.lift`.

Set `j₁ : Ω →ₐ[E] ℂ` to `j.restrictScalars E`. Set `j₂ : Ω →ₐ[E] ℂ` to `{ (starRingEnd ℂ).comp j₁.toRingHom with commutes' := fun y => by show starRingEnd ℂ (j₁ (algebraMap E Ω y)) = _`. Rewrite using `[j₁.commutes]`. Conclude with `DFunLike.congr_fun (ComplexEmbedding.isReal_iff.1 hE) y }`. Set `_ : Algebra Ω ℂ` to `j₁.toRingHom.toAlgebra`.

Establish `: IsScalarTower E Ω ℂ` using `IsScalarTower.of_algebraMap_eq fun y => (j₁.commutes y).symm`. Establish `hc : ∀ x, j₁ (j₂.restrictNormal' Ω x) = starRingEnd ℂ (j₁ x)` using `fun x => j₂.restrictNormal_commutes Ω x`. Use `⟨j₂.restrictNormal' Ω, ⟨j₁.toRingHom, hc⟩, fun x hx => ?_⟩` and prove the remaining obligations. Use `hc x` as an intermediate fact. Rewrite `this` using `[hx]`.

Establish `e : j₁ x = j₀ x` using `j.commutes x`. Rewrite using `[← e]`. Conclude with `this.symm`.
-/
private theorem exists_conj {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (L : IntermediateField E Ω) (j₀ : L →+* ℂ)
    (hE : ComplexEmbedding.IsReal (j₀.comp (algebraMap E L))) :
    ∃ c : Ω ≃ₐ[E] Ω, IsConjOm c.toRingEquiv ∧ ∀ x : L, c x = x → starRingEnd ℂ (j₀ x) = j₀ x := by
  let _ : Algebra L ℂ := j₀.toAlgebra
  let _ : Algebra E ℂ := (j₀.comp (algebraMap E L)).toAlgebra
  have : IsScalarTower E L ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := E) L
  let j : Ω →ₐ[L] ℂ := IsAlgClosed.lift
  let j₁ : Ω →ₐ[E] ℂ := j.restrictScalars E
  let j₂ : Ω →ₐ[E] ℂ :=
    { (starRingEnd ℂ).comp j₁.toRingHom with
      commutes' := fun y => by
        show starRingEnd ℂ (j₁ (algebraMap E Ω y)) = _
        rw [j₁.commutes]
        exact DFunLike.congr_fun (ComplexEmbedding.isReal_iff.1 hE) y }
  let _ : Algebra Ω ℂ := j₁.toRingHom.toAlgebra
  have : IsScalarTower E Ω ℂ := IsScalarTower.of_algebraMap_eq fun y => (j₁.commutes y).symm
  have hc : ∀ x, j₁ (j₂.restrictNormal' Ω x) = starRingEnd ℂ (j₁ x) := fun x => j₂.restrictNormal_commutes Ω x
  refine ⟨j₂.restrictNormal' Ω, ⟨j₁.toRingHom, hc⟩, fun x hx => ?_⟩
  have := hc x
  rw [hx] at this
  have e : j₁ x = j₀ x := j.commutes x
  rw [← e]
  exact this.symm

open GroundTheory.Global IntermediateField in
/- English proof (translation)
Establish `: IsGalois E Ω` using `IsAlgClosure.isGalois E Ω`. Set `Hc : ClosedSubgroup (Ω ≃ₐ[E] Ω)` to `⟨H, H.isClosed_of_isOpen ho⟩`. Establish `hfix : (fixedField H).fixingSubgroup = H` using `InfiniteGalois.fixingSubgroup_fixedField Hc`. Generalize the expression as in `fixedField H = L at hfix`. Substitute `hfix` using the available equality.

Establish `: FiniteDimensional E L` using `(InfiniteGalois.isOpen_iff_finite _).1 ho`. Establish `: IsGalois E L` using `(InfiniteGalois.normal_iff_isGalois _).1 (Subgroup.Normal.of_commutator_le _ hcm)`. Establish `: NumberField L` using `NumberField.of_module_finite E _`. Establish `hker : ∀ g ∈ L.fixingSubgroup, AlgEquiv.restrictNormalHom L g = 1` using `fun g hg => by`. Rewrite using `[← MonoidHom.mem_ker, restrictNormalHom_ker]`.

Conclude with `hg`. Establish `: IsAbelianGalois E L` using `{ is_comm := ⟨fun a b => by`. Take `⟨a, rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) (E := Ω) a`. Take `⟨b, rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) (E := Ω) b`. Rewrite using `[← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]`.

Conclude with `hker _ (hcm (Subgroup.commutator_mem_commutator trivial trivial))⟩ }`. Use `fixingSubgroup_le ((le_hilbertClassField_iff E Ω L).2 ⟨fun v => ?_, fun v w hw => ?_⟩)` and prove the remaining obligations. Rewrite using `[isUnramifiedIn_iff_ramificationIdx]`. Introduce `w hw`. Rewrite using `[← natCard_inertia v w, Subgroup.card_eq_one, eq_bot_iff]`.

Introduce `τ hτ`. Take `⟨A, φ, h1, h2⟩` from `lift_ine L w τ hτ`. Rewrite using `[Subgroup.mem_bot, ← h1]`. Conclude with `hker _ (hI A h2)`. Rewrite using `[InfinitePlace.isUnramified_iff, ← InfinitePlace.not_isReal_iff_isComplex, ← w.mk_embedding, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff, InfinitePlace.isReal_mk_iff, or_iff_not_imp_right, not_not]`.

Introduce `hE`. Take `⟨c, hc', h⟩` from `exists_conj L w.embedding hE`. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `y`. Conclude with `h y ((mem_fixingSubgroup_iff _ _).1 (hc c hc') _ y.2)`.
-/
private theorem hilbert_le {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] [IsAlgClosed Ω] (H : Subgroup (Ω ≃ₐ[E] Ω)) (ho : IsOpen (H : Set (Ω ≃ₐ[E] Ω)))
    (hcm : commutator (Ω ≃ₐ[E] Ω) ≤ H) (hI : ∀ A : ValuationSubring Ω, Ine (F := E) A ≤ H)
    (hc : ∀ c : Ω ≃ₐ[E] Ω, IsConjOm c.toRingEquiv → c ∈ H) :
    (hilbertClassField E Ω).fixingSubgroup ≤ H := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  let Hc : ClosedSubgroup (Ω ≃ₐ[E] Ω) := ⟨H, H.isClosed_of_isOpen ho⟩
  have hfix : (fixedField H).fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField Hc
  generalize fixedField H = L at hfix
  subst hfix
  have : FiniteDimensional E L := (InfiniteGalois.isOpen_iff_finite _).1 ho
  have : IsGalois E L := (InfiniteGalois.normal_iff_isGalois _).1 (Subgroup.Normal.of_commutator_le _ hcm)
  have : NumberField L := NumberField.of_module_finite E _
  have hker : ∀ g ∈ L.fixingSubgroup, AlgEquiv.restrictNormalHom L g = 1 := fun g hg => by
    rw [← MonoidHom.mem_ker, restrictNormalHom_ker]
    exact hg
  have : IsAbelianGalois E L :=
    { is_comm := ⟨fun a b => by
        obtain ⟨a, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) (E := Ω) a
        obtain ⟨b, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) (E := Ω) b
        rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
        exact hker _ (hcm (Subgroup.commutator_mem_commutator trivial trivial))⟩ }
  refine fixingSubgroup_le ((le_hilbertClassField_iff E Ω L).2 ⟨fun v => ?_, fun v w hw => ?_⟩)
  · rw [isUnramifiedIn_iff_ramificationIdx]
    intro w hw
    rw [← natCard_inertia v w, Subgroup.card_eq_one, eq_bot_iff]
    intro τ hτ
    obtain ⟨A, φ, h1, h2⟩ := lift_ine L w τ hτ
    rw [Subgroup.mem_bot, ← h1]
    exact hker _ (hI A h2)
  · rw [InfinitePlace.isUnramified_iff, ← InfinitePlace.not_isReal_iff_isComplex, ← w.mk_embedding,
      InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff, InfinitePlace.isReal_mk_iff, or_iff_not_imp_right, not_not]
    intro hE
    obtain ⟨c, hc', h⟩ := exists_conj L w.embedding hE
    rw [ComplexEmbedding.isReal_iff]
    ext y
    exact h y ((mem_fixingSubgroup_iff _ _).1 (hc c hc') _ y.2)

/- English proof (translation)
Introduce `K Ω _ _ _ _ _ C _ χ ho hI hc g hg`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed K`. Use `hilbert_le χ.ker ho (Abelianization.commutator_subset_ker χ) hI hc ?_` and prove the remaining obligations. Rewrite using `[← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker]`. Conclude with `(GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm.map_eq_one_iff.1 hg`.
-/
theorem UpperTheory.V.Kum.artKer :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (C : Type) [CommGroup C] (χ : G K Ω →* C), IsOpen (χ.ker : Set (G K Ω)) → (∀ A : ValuationSubring Ω, Ine (F := K) A ≤ χ.ker) →
    (∀ c : G K Ω, IsConjOm c.toRingEquiv → χ c = 1) → (artCl K Ω).ker ≤ χ.ker := by
  intro K Ω _ _ _ _ _ C _ χ ho hI hc g hg
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  refine hilbert_le χ.ker ho (Abelianization.commutator_subset_ker χ) hI hc ?_
  rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker]
  exact (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm.map_eq_one_iff.1 hg
