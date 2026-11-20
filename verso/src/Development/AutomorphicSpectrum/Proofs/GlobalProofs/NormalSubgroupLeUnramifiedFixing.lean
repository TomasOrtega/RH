import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.GlobalFiniteness

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] [Algebra F Ω] [Field F] in

/- English proof (translation)
Establish `h1 : IsIntegral A y` using `hy.tower_top`. Take `⟨z, hz⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1`. Rewrite using `[← hz]`. Conclude with `z.2`.
-/
theorem mem_of_isIntegral_int (A : ValuationSubring Ω) {y : Ω} (hy : IsIntegral ℤ y) : y ∈ A := by
  have h1 : IsIntegral A y := hy.tower_top
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hz]
  exact z.2

noncomputable def intToVal (A : ValuationSubring Ω) (M : IntermediateField F Ω) : 𝓞 M →+* A :=
  ((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A fun z =>
    mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe z).map (IsScalarTower.toAlgHom ℤ M Ω))

noncomputable def cutPrime (A : ValuationSubring Ω) (M : IntermediateField F Ω) : Ideal (𝓞 M) :=
  (IsLocalRing.maximalIdeal A).comap (intToVal A M)

instance (A : ValuationSubring Ω) (M : IntermediateField F Ω) : (cutPrime A M).IsPrime :=
  Ideal.comap_isPrime _ _

/- English proof (translation)
Rewrite using `[cutPrime, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]`. Both sides reduce to the same expression.
-/
theorem mem_cutPrime_iff (A : ValuationSubring Ω) (M : IntermediateField F Ω) (z : 𝓞 M) :
    z ∈ cutPrime A M ↔ A.valuation ((z : M) : Ω) < 1 := by
  rw [cutPrime, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use extensionality with `x`. Rewrite using `[Ideal.under_def, Ideal.mem_comap, mem_cutPrime_iff, ← hA x]`. Both sides reduce to the same expression.
-/
theorem cutPrime_liesOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) (M : IntermediateField F Ω) : (cutPrime A M).LiesOver v.asIdeal := by
  constructor
  ext x
  rw [Ideal.under_def, Ideal.mem_comap, mem_cutPrime_iff, ← hA x]
  rfl

/- English proof (translation)
Use `haveI hM : IsGalois F (maxUnramifiedOutside F Ω S) := isGalois_maxUnramifiedOutside S`. Use `haveI : FiniteDimensional F (IntermediateField.adjoin F ({x} : Set Ω)) := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)`. Use `set E : IntermediateField F Ω := IntermediateField.normalClosure F (IntermediateField.adjoin F ({x} : Set Ω)) Ω with hE`. Use `haveI : FiniteDimensional F E := normalClosure.is_finiteDimensional F (IntermediateField.adjoin F ({x} : Set Ω)) Ω`. Use `haveI : Normal F E := normalClosure.normal F (IntermediateField.adjoin F ({x} : Set Ω)) Ω`.

Use `haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_algHom F Ω E.val`. Use `haveI : IsGalois F E := ⟨⟩`. Establish `hxE : x ∈ E` using `IntermediateField.le_normalClosure (IntermediateField.adjoin F ({x} : Set Ω)) (IntermediateField.mem_adjoin_simple_self F x)`. Establish `hEM : E ≤ maxUnramifiedOutside F Ω S`. Rewrite using `[hE, IntermediateField.normalClosure_le_iff_of_normal]`.

Conclude with `IntermediateField.adjoin_simple_le_iff.2 hx`. Establish `hEun : IsUnramifiedOutside S E` using `(isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hEM`. Use `haveI hPl : (cutPrime A E).LiesOver v.asIdeal := cutPrime_liesOver hA E`. Use `haveI : NumberField E := NumberField.of_module_finite F E`. Use `haveI : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)`.

Use `haveI : Algebra.FiniteType (𝓞 F) (𝓞 E) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ (𝓞 F) (𝓞 E)`. Use `haveI : IsGaloisGroup Gal(E/F) (𝓞 F) (𝓞 E) := IsGaloisGroup.of_isFractionRing (G := Gal(E/F)) (A := 𝓞 F) (B := 𝓞 E) (K := F) (L := E)`. Establish `he : (cutPrime A E).ramificationIdx (𝓞 F) = 1` using `Algebra.IsUnramifiedIn.ramificationIdx_eq_one (hEun v hv) hPl`. Establish `hcard : Nat.card ((cutPrime A E).inertia Gal(E/F)) = 1`. Rewrite using `[Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/F)) v.asIdeal (cutPrime A E), Ideal.ramificationIdxIn_eq_ramificationIdx (G := Gal(E/F)) v.asIdeal (cutPrime A E), he]`.

Use `set σ' : Gal(E/F) := σ.restrictNormal E with hσ'`. Establish `hmem : σ' ∈ (cutPrime A E).inertia Gal(E/F)`. Introduce `z`. Use `show σ' • z - z ∈ cutPrime A E`. Rewrite using `[mem_cutPrime_iff]`.

Take `⟨-, hσ2⟩` from `hσ`. Establish `hy : ((z : E) : Ω) ∈ A` using `mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe z).map (IsScalarTower.toAlgHom ℤ E Ω))`. Establish `hc : (((σ' • z - z : 𝓞 E) : E) : Ω) = σ ((z : E) : Ω) - ((z : E) : Ω)`. Establish `h1` using `AlgEquiv.restrictNormal_commutes σ E (z : E)`. Simplify using `only [IntermediateField.algebraMap_apply] at h1`.

Rewrite using `[← h1, hσ']`. Both sides reduce to the same expression. Rewrite using `[hc]`. Conclude with `hσ2 _ (A.valuation_le_one ⟨_, hy⟩)`. Establish `hσ'1 : σ' = 1` using `by haveI hsub : Subsingleton ((cutPrime A E).inertia Gal(E/F)) := (Nat.card_eq_one_iff_unique.1 hcard).1`.

Use `Subsingleton.elim (⟨σ', hmem⟩ : (cutPrime A E).inertia Gal(E/F)) ⟨1, Subgroup.one_mem _⟩` as an intermediate fact. Conclude with `congrArg Subtype.val this`. Establish `h1` using `AlgEquiv.restrictNormal_commutes σ E ⟨x, hxE⟩`. Rewrite `h1` using `[← hσ', hσ'1]`. Conclude with `h1.symm`.
-/
theorem inertia_apply_eq [IsGalois F Ω] {S : Set (HeightOneSpectrum (𝓞 F))}
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Inertia (F := F) A) {x : Ω} (hx : x ∈ maxUnramifiedOutside F Ω S) :
    σ x = x := by
  classical
  haveI hM : IsGalois F (maxUnramifiedOutside F Ω S) := isGalois_maxUnramifiedOutside S
  haveI : FiniteDimensional F (IntermediateField.adjoin F ({x} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  set E : IntermediateField F Ω := IntermediateField.normalClosure F (IntermediateField.adjoin F ({x} : Set Ω)) Ω with hE
  haveI : FiniteDimensional F E := normalClosure.is_finiteDimensional F (IntermediateField.adjoin F ({x} : Set Ω)) Ω
  haveI : Normal F E := normalClosure.normal F (IntermediateField.adjoin F ({x} : Set Ω)) Ω
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_algHom F Ω E.val
  haveI : IsGalois F E := ⟨⟩
  have hxE : x ∈ E := IntermediateField.le_normalClosure (IntermediateField.adjoin F ({x} : Set Ω)) (IntermediateField.mem_adjoin_simple_self F x)
  have hEM : E ≤ maxUnramifiedOutside F Ω S := by
    rw [hE, IntermediateField.normalClosure_le_iff_of_normal]
    exact IntermediateField.adjoin_simple_le_iff.2 hx
  have hEun : IsUnramifiedOutside S E := (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hEM
  haveI hPl : (cutPrime A E).LiesOver v.asIdeal := cutPrime_liesOver hA E
  haveI : NumberField E := NumberField.of_module_finite F E
  haveI : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)
  haveI : Algebra.FiniteType (𝓞 F) (𝓞 E) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ (𝓞 F) (𝓞 E)
  haveI : IsGaloisGroup Gal(E/F) (𝓞 F) (𝓞 E) := IsGaloisGroup.of_isFractionRing (G := Gal(E/F)) (A := 𝓞 F) (B := 𝓞 E) (K := F) (L := E)
  have he : (cutPrime A E).ramificationIdx (𝓞 F) = 1 :=
    Algebra.IsUnramifiedIn.ramificationIdx_eq_one (hEun v hv) hPl
  have hcard : Nat.card ((cutPrime A E).inertia Gal(E/F)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/F)) v.asIdeal (cutPrime A E),
      Ideal.ramificationIdxIn_eq_ramificationIdx (G := Gal(E/F)) v.asIdeal (cutPrime A E), he]
  set σ' : Gal(E/F) := σ.restrictNormal E with hσ'
  have hmem : σ' ∈ (cutPrime A E).inertia Gal(E/F) := by
    intro z
    show σ' • z - z ∈ cutPrime A E
    rw [mem_cutPrime_iff]
    obtain ⟨-, hσ2⟩ := hσ
    have hy : ((z : E) : Ω) ∈ A :=
      mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe z).map (IsScalarTower.toAlgHom ℤ E Ω))
    have hc : (((σ' • z - z : 𝓞 E) : E) : Ω) = σ ((z : E) : Ω) - ((z : E) : Ω) := by
      have h1 := AlgEquiv.restrictNormal_commutes σ E (z : E)
      simp only [IntermediateField.algebraMap_apply] at h1
      rw [← h1, hσ']
      rfl
    rw [hc]
    exact hσ2 _ (A.valuation_le_one ⟨_, hy⟩)
  have hσ'1 : σ' = 1 := by
    haveI hsub : Subsingleton ((cutPrime A E).inertia Gal(E/F)) := (Nat.card_eq_one_iff_unique.1 hcard).1
    have := Subsingleton.elim (⟨σ', hmem⟩ : (cutPrime A E).inertia Gal(E/F)) ⟨1, Subgroup.one_mem _⟩
    exact congrArg Subtype.val this
  have h1 := AlgEquiv.restrictNormal_commutes σ E ⟨x, hxE⟩
  rw [← hσ', hσ'1] at h1
  exact h1.symm

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ S`. Use `haveI : IsGalois F Ω := ⟨⟩`. Use `haveI hM : IsGalois F (maxUnramifiedOutside F Ω S) := isGalois_maxUnramifiedOutside S`. Use `haveI : (maxUnramifiedOutside F Ω S).fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois _).2 hM`. Establish `hsub : (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F` using `F) A) ⊆ ((maxUnramifiedOutside F Ω S).fixingSubgroup : Set (G F Ω)) := by`.

Introduce `σ hσ`. Simplify using `only [Set.mem_iUnion] at hσ`. Take `⟨v, hv, A, hA, hσA⟩` from `hσ`. Use `show σ ∈ (maxUnramifiedOutside F Ω S).fixingSubgroup`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `x hx`. Conclude with `inertia_apply_eq hv hA hσA hx`. Use `show (Subgroup.normalClosure _).topologicalClosure ≤ _`. Conclude with `Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hsub) (InfiniteGalois.fixingSubgroup_isClosed _)`.
-/
theorem NS_le_fixingSubgroup : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))),
    NS Ω S ≤ (maxUnramifiedOutside F Ω S).fixingSubgroup := by
  intro F Ω _ _ _ _ _ S
  haveI : IsGalois F Ω := ⟨⟩
  haveI hM : IsGalois F (maxUnramifiedOutside F Ω S) := isGalois_maxUnramifiedOutside S
  haveI : (maxUnramifiedOutside F Ω S).fixingSubgroup.Normal :=
    (InfiniteGalois.normal_iff_isGalois _).2 hM
  have hsub : (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F := F) A) ⊆
      ((maxUnramifiedOutside F Ω S).fixingSubgroup : Set (G F Ω)) := by
    intro σ hσ
    simp only [Set.mem_iUnion] at hσ
    obtain ⟨v, hv, A, hA, hσA⟩ := hσ
    show σ ∈ (maxUnramifiedOutside F Ω S).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact inertia_apply_eq hv hA hσA hx
  show (Subgroup.normalClosure _).topologicalClosure ≤ _
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hsub)
    (InfiniteGalois.fixingSubgroup_isClosed _)

end GlobalTheory.CompanionTheory.GlobalFiniteness
