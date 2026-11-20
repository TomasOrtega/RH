import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrimeLeNotMemRingKrullDimEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteIntegralClosureOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.NormCurve

/- English proof (translation)
Take `⟨x, r, c, hc, hr, e⟩` from `(RingHom.surjective_localRingHom_iff (⊥ : Ideal R)).mp (h ⊥ inferInstance) z`. Rewrite `hc`, `hr` using `[Ideal.mem_bot]`. Use `⟨x, r, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_div_iff hr]`. Apply `mul_left_cancel₀ hc` to reduce the goal to its premises.

Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_eq_div {B R : Type} [CommRing B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) (z : R) :
    ∃ x y : B, z = algebraMap B R x / algebraMap B R y := by
  obtain ⟨x, r, c, hc, hr, e⟩ := (RingHom.surjective_localRingHom_iff (⊥ : Ideal R)).mp
    (h ⊥ inferInstance) z
  rw [Ideal.mem_bot] at hc hr
  refine ⟨x, r, ?_⟩
  rw [eq_div_iff hr]
  apply mul_left_cancel₀ hc
  rw [← e]
  ring

/- English proof (translation)
Use `haveI : IsFractionRing (integralClosure B R) R := IsFractionRing.of_field _ _ fun z => by`. Take `⟨x, y, e⟩` from `exists_eq_div h z`. Conclude with `⟨algebraMap B _ x, algebraMap B _ y, e⟩`. Conclude with `(isIntegrallyClosed_iff R).mpr fun {x} hx => ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩`.
-/
theorem isIntegrallyClosed_integralClosure {B R : Type} [CommRing B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) : IsIntegrallyClosed (integralClosure B R) := by
  haveI : IsFractionRing (integralClosure B R) R := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, e⟩ := exists_eq_div h z
    exact ⟨algebraMap B _ x, algebraMap B _ y, e⟩
  exact (isIntegrallyClosed_iff R).mpr fun {x} hx => ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩

/- English proof (translation)
Set `A` to `B ⧸ RingHom.ker (algebraMap B R)`. Use `haveI : (RingHom.ker (algebraMap B R)).IsPrime := RingHom.ker_isPrime _`. Use `letI : Algebra A R := (RingHom.kerLift (algebraMap B R)).toAlgebra`. Use `haveI : IsScalarTower B A R := .of_algebraMap_eq fun x => (RingHom.kerLift_mk _ x).symm`. Use `haveI : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective _)`.

Use `haveI : IsFractionRing A R := IsFractionRing.of_field _ _ fun z => by`. Take `⟨x, y, e⟩` from `exists_eq_div h z`. Conclude with `⟨algebraMap B _ x, algebraMap B _ y, by`. Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]⟩` and apply the resulting hypothesis. Prove the components needed by the constructor for the conclusion.

Use `haveI := NormFin.finite_integralClosure_of_perfectField k A R R haveI : Module.Finite B (integralClosure A R) := Module.Finite.trans A _`. Establish `h' : Module.Finite B ((integralClosure A R).restrictScalars B)` using `this`. Rewrite `h'` using `[integralClosure_restrictScalars_of_isIntegral]`. Then use the resulting hypothesis. Introduce `_ _ hd haveI : IsScalarTower k A R := .of_algebraMap_eq fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply k B R, IsScalarTower.algebraMap_apply k B A, ← IsScalarTower.algebraMap_apply B A R]`.

Take `⟨s, hs1, hs2⟩` from `ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)`. Use `haveI : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap k A).injective`. Use `haveI : Algebra.IsAlgebraic A R := IsLocalization.isAlgebraic R (nonZeroDivisors A)`. Rewrite using `[← trdeg_add_eq k A (A := R), trdeg_eq_zero (R := A) (A := R), add_zero, hs2]`. Rewrite `hd` using `[hs1]`.

Conclude with `hd` after adjusting the coercions.
-/
theorem finite_integralClosure (k : Type) {B R : Type} [Field k] [PerfectField k] [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) :
    Module.Finite B (integralClosure B R) ∧ ∀ [Algebra k R] [IsScalarTower k B R],
      ringKrullDim (B ⧸ RingHom.ker (algebraMap B R)) ≤ 1 → Algebra.trdeg k R ≤ 1 := by
  let A := B ⧸ RingHom.ker (algebraMap B R)
  haveI : (RingHom.ker (algebraMap B R)).IsPrime := RingHom.ker_isPrime _
  letI : Algebra A R := (RingHom.kerLift (algebraMap B R)).toAlgebra
  haveI : IsScalarTower B A R := .of_algebraMap_eq fun x => (RingHom.kerLift_mk _ x).symm
  haveI : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (RingHom.kerLift_injective _)
  haveI : IsFractionRing A R := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, e⟩ := exists_eq_div h z
    exact ⟨algebraMap B _ x, algebraMap B _ y, by
      rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]⟩
  constructor
  · haveI := NormFin.finite_integralClosure_of_perfectField k A R R
    haveI : Module.Finite B (integralClosure A R) := Module.Finite.trans A _
    have h' : Module.Finite B ((integralClosure A R).restrictScalars B) := this
    rwa [integralClosure_restrictScalars_of_isIntegral] at h'
  · intro _ _ hd
    haveI : IsScalarTower k A R := .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k B R, IsScalarTower.algebraMap_apply k B A,
        ← IsScalarTower.algebraMap_apply B A R]
    obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)
    haveI : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap k A).injective
    haveI : Algebra.IsAlgebraic A R := IsLocalization.isAlgebraic R (nonZeroDivisors A)
    rw [← trdeg_add_eq k A (A := R), trdeg_eq_zero (R := A) (A := R), add_zero, hs2]
    rw [hs1] at hd
    exact_mod_cast hd

/- English proof (translation)
Take `⟨s, hs1, hs2⟩` from `ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)`. Establish `h1` using `(trdeg_le_of_injective g hg).trans h`. Rewrite `h1` using `[hs2]`. Establish `h2 : s ≤ 1` using `by exact_mod_cast h1`. Establish `h3 : Ring.KrullDimLE 1 A`.

Rewrite using `[Ring.krullDimLE_iff, hs1]`. Conclude with `h2` after adjusting the coercions. Conclude with `⟨fun {p} hp hp' => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h3 p hp hp'⟩`.
-/
theorem dimensionLEOne_of_injective {k A R : Type} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [Algebra k R] (g : A →ₐ[k] R)
    (hg : Function.Injective g) (h : Algebra.trdeg k R ≤ 1) : Ring.DimensionLEOne A := by
  obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)
  have h1 := (trdeg_le_of_injective g hg).trans h
  rw [hs2] at h1
  have h2 : s ≤ 1 := by exact_mod_cast h1
  have h3 : Ring.KrullDimLE 1 A := by
    rw [Ring.krullDimLE_iff, hs1]
    exact_mod_cast h2
  exact ⟨fun {p} hp hp' => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h3 p hp hp'⟩

/- English proof (translation)
Distinguish the cases in `hh : h ∈ m`. Take `⟨p, h1, h2, h3, h4⟩` from `exists_prime_le_notMem_ringKrullDim_eq_one k B m h hm h0 hh`. Conclude with `⟨p, h1, h2, h3, h4.le⟩`. Use `⟨m, hm.isPrime, le_rfl, hh, ?_⟩` and prove the remaining obligations. Use `letI := Ideal.Quotient.field m`.

Rewrite using `[ringKrullDim_eq_zero_of_field]`. Conclude with `zero_le_one`.
-/
theorem exists_prime (k : Type) {B : Type} [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (m : Ideal B) (hm : m.IsMaximal) (h : B) (h0 : h ≠ 0) :
    ∃ p : Ideal B, p.IsPrime ∧ p ≤ m ∧ h ∉ p ∧ ringKrullDim (B ⧸ p) ≤ 1 := by
  by_cases hh : h ∈ m
  · obtain ⟨p, h1, h2, h3, h4⟩ := exists_prime_le_notMem_ringKrullDim_eq_one k B m h hm h0 hh
    exact ⟨p, h1, h2, h3, h4.le⟩
  · refine ⟨m, hm.isPrime, le_rfl, hh, ?_⟩
    letI := Ideal.Quotient.field m
    rw [ringKrullDim_eq_zero_of_field]
    exact zero_le_one

section Scheme

variable {k : Type} [Field k] {X Z : Scheme.{0}}

noncomputable def constHom (s : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ U le_top).hom

/- English proof (translation)
Establish `h : (s.appLE ⊤ U le_top).hom.FiniteType` using `HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top`. Conclude with `h.comp (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)`.
-/
theorem finiteType_constHom (s : X ⟶ Sp k) [LocallyOfFiniteType s] {U : X.Opens}
    (hU : IsAffineOpen U) : (constHom s U).FiniteType := by
  have h : (s.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
      le_top
  exact h.comp (.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)

/- English proof (translation)
Rewrite using `[constHom, constHom, ← Scheme.Hom.appLE_comp_appLE f s ⊤ U V le_top e]`. Both sides reduce to the same expression.
-/
theorem appLE_comp_constHom (s : X ⟶ Sp k) (f : Z ⟶ X) (U : X.Opens) (V : Z.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : (f.appLE U V e).hom.comp (constHom s U) = constHom (f ≫ s) V := by
  rw [constHom, constHom, ← Scheme.Hom.appLE_comp_appLE f s ⊤ U V le_top e]
  rfl

/- English proof (translation)
Use `⟨exists_pair_ne _, mul_comm, fun {a} ha => IsUnit.exists_right_inv ?_⟩` and prove the remaining obligations. Use `Z.toRingedSpace.isUnit_of_isUnit_germ V a fun x hx => ?_` and prove the remaining obligations. Establish `h : Z.basicOpen a ≠ ⊥` using `fun h => ha ((basicOpen_eq_bot_iff a).mp h)`. Take `⟨y, hy⟩` from `(TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp h`. Rewrite `hy` using `[Subsingleton.elim y x]`.

Conclude with `(Z.mem_basicOpen a x hx).mp hy`.
-/
theorem isField_sections [IsIntegral Z] [Subsingleton Z] (V : Z.Opens) [hV : Nonempty V] :
    IsField Γ(Z, V) := by
  refine ⟨exists_pair_ne _, mul_comm, fun {a} ha => IsUnit.exists_right_inv ?_⟩
  refine Z.toRingedSpace.isUnit_of_isUnit_germ V a fun x hx => ?_
  have h : Z.basicOpen a ≠ ⊥ := fun h => ha ((basicOpen_eq_bot_iff a).mp h)
  obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp h
  rw [Subsingleton.elim y x] at hy
  exact (Z.mem_basicOpen a x hx).mp hy

/- English proof (translation)
Take `⟨y, hy⟩` from `hV`. Establish `: V = ⊤` using `eq_top_iff.mpr fun x _ => Subsingleton.elim y x ▸ hy`. Rewrite using `[this]`. Conclude with `isAffineOpen_top Z`.
-/
theorem isAffineOpen_of_subsingleton [IsAffine Z] [Subsingleton Z] (V : Z.Opens)
    [hV : Nonempty V] : IsAffineOpen V := by
  obtain ⟨y, hy⟩ := hV
  have : V = ⊤ := eq_top_iff.mpr fun x _ => Subsingleton.elim y x ▸ hy
  rw [this]
  exact isAffineOpen_top Z

variable [IsIntegral Z] [Subsingleton Z] [IsAffine Z] (f : Z ⟶ X) [SurjectiveOnStalks f]

/- English proof (translation)
The claim follows from `HasRingHomProperty.appLE @SurjectiveOnStalks f inferInstance ⟨U, hU⟩ ⟨V, isAffineOpen_of_subsingleton V⟩ e`.
-/
theorem surjectiveOnStalks_appLE {U : X.Opens} (hU : IsAffineOpen U) (V : Z.Opens) [Nonempty V]
    (e : V ≤ f ⁻¹ᵁ U) : (f.appLE U V e).hom.SurjectiveOnStalks :=
  HasRingHomProperty.appLE @SurjectiveOnStalks f inferInstance ⟨U, hU⟩
    ⟨V, isAffineOpen_of_subsingleton V⟩ e

variable [QuasiCompact f] [QuasiSeparated f]

/- English proof (translation)
Use `⟨fun U hU => ?_⟩` and prove the remaining obligations. Rewrite using `[f.fromNormalization_app hU]`. Use `letI := (f.app U).hom.toAlgebra`. Establish `h : Module.Finite Γ(X, U) (integralClosure Γ(X, U) Γ(Z, f ⁻¹ᵁ U))`. Distinguish the cases in `hne : Nonempty (f ⁻¹ᵁ U)`.

Use `letI := (isField_sections (f ⁻¹ᵁ U)).toField`. Use `letI := (constHom s U).toAlgebra`. Use `haveI : Algebra.FiniteType k Γ(X, U) := finiteType_constHom s hU`. Use `(finite_integralClosure k ?_).1` and prove the remaining obligations. Use `surjectiveOnStalks_appLE f hU (f ⁻¹ᵁ U) le_rfl` as an intermediate fact.

Rewrite `this` using `[← Scheme.Hom.app_eq_appLE]`. Then use the resulting hypothesis. Establish `: f ⁻¹ᵁ U = ⊥` using `eq_bot_iff.mpr fun x hx => (hne ⟨⟨x, hx⟩⟩).elim`. Establish `: Subsingleton Γ(Z, f ⁻¹ᵁ U)` using `by rw [this]; infer_instance`. Use `infer_instance`. Conclude with `RingHom.Finite.comp (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2) (RingHom.finite_algebraMap.mpr h)`.
-/
theorem isFinite_fromNormalization [PerfectField k] (s : X ⟶ Sp k) [LocallyOfFiniteType s] :
    IsFinite f.fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  rw [f.fromNormalization_app hU]
  letI := (f.app U).hom.toAlgebra
  have h : Module.Finite Γ(X, U) (integralClosure Γ(X, U) Γ(Z, f ⁻¹ᵁ U)) := by
    by_cases hne : Nonempty (f ⁻¹ᵁ U)
    · letI := (isField_sections (f ⁻¹ᵁ U)).toField
      letI := (constHom s U).toAlgebra
      haveI : Algebra.FiniteType k Γ(X, U) := finiteType_constHom s hU
      refine (finite_integralClosure k ?_).1
      have := surjectiveOnStalks_appLE f hU (f ⁻¹ᵁ U) le_rfl
      rwa [← Scheme.Hom.app_eq_appLE] at this
    · have : f ⁻¹ᵁ U = ⊥ := eq_bot_iff.mpr fun x hx => (hne ⟨⟨x, hx⟩⟩).elim
      have : Subsingleton Γ(Z, f ⁻¹ᵁ U) := by rw [this]; infer_instance
      infer_instance
  exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr h)

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hyU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.fromNormalization y)) isOpen_univ`. Establish `hy : y ∈ f.fromNormalization ⁻¹ᵁ U` using `hyU`. Establish `hne : Nonempty (f ⁻¹ᵁ U)`. Take `⟨z, hz⟩` from `f.toNormalization.denseRange.exists_mem_open (f.fromNormalization ⁻¹ᵁ U).isOpen ⟨y, hy⟩`. Use `⟨⟨z, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← f.toNormalization_fromNormalization]`. Conclude with `hz`. Use `letI := (f.app U).hom.toAlgebra`. Establish `h1 : IsIntegrallyClosed (integralClosure Γ(X, U) Γ(Z, f ⁻¹ᵁ U))`. Use `letI := (isField_sections (f ⁻¹ᵁ U)).toField`.

Use `isIntegrallyClosed_integralClosure ?_` and prove the remaining obligations. Use `surjectiveOnStalks_appLE f hU (f ⁻¹ᵁ U) le_rfl` as an intermediate fact. Rewrite `this` using `[← Scheme.Hom.app_eq_appLE]`. Then use the resulting hypothesis. Establish `h2 : IsIntegrallyClosed Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U)` using `IsIntegrallyClosed.of_equiv (f.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv`. Establish `hV` using `hU.preimage f.fromNormalization`.

Use `haveI : Nonempty (f.fromNormalization ⁻¹ᵁ U) := ⟨⟨y, hy⟩⟩`. Use `letI := f.normalization.presheaf.algebra_section_stalk (⟨y, hy⟩ : f.fromNormalization ⁻¹ᵁ U)`. Use `haveI := hV.isLocalization_stalk ⟨y, hy⟩`. Conclude with `isIntegrallyClosed_of_isLocalization (R := Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U)) _ (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)`.
-/
theorem isIntegrallyClosed_stalk (y : f.normalization) :
    IsIntegrallyClosed (f.normalization.presheaf.stalk y) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.fromNormalization y)) isOpen_univ
  have hy : y ∈ f.fromNormalization ⁻¹ᵁ U := hyU
  have hne : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨z, hz⟩ := f.toNormalization.denseRange.exists_mem_open
      (f.fromNormalization ⁻¹ᵁ U).isOpen ⟨y, hy⟩
    refine ⟨⟨z, ?_⟩⟩
    rw [← f.toNormalization_fromNormalization]
    exact hz
  letI := (f.app U).hom.toAlgebra
  have h1 : IsIntegrallyClosed (integralClosure Γ(X, U) Γ(Z, f ⁻¹ᵁ U)) := by
    letI := (isField_sections (f ⁻¹ᵁ U)).toField
    refine isIntegrallyClosed_integralClosure ?_
    have := surjectiveOnStalks_appLE f hU (f ⁻¹ᵁ U) le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  have h2 : IsIntegrallyClosed Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    IsIntegrallyClosed.of_equiv (f.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv
  have hV := hU.preimage f.fromNormalization
  haveI : Nonempty (f.fromNormalization ⁻¹ᵁ U) := ⟨⟨y, hy⟩⟩
  letI := f.normalization.presheaf.algebra_section_stalk (⟨y, hy⟩ : f.fromNormalization ⁻¹ᵁ U)
  haveI := hV.isLocalization_stalk ⟨y, hy⟩
  exact isIntegrallyClosed_of_isLocalization (R := Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U)) _
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)

/- English proof (translation)
Use `haveI := isFinite_fromNormalization f s`. Use `letI := (constHom (f ≫ s) ⊤).toAlgebra`. Use `letI := (constHom (f.fromNormalization ≫ s) U).toAlgebra`. Use `haveI : Algebra.FiniteType k Γ(f.normalization, U) := finiteType_constHom _ hU`. Establish `e : ⊤ ≤ f.toNormalization ⁻¹ᵁ U`.

Take `⟨y, hy⟩` from `hne`. Take `⟨z, hz⟩` from `f.toNormalization.denseRange.exists_mem_open U.isOpen ⟨y, hy⟩`. Conclude with `fun x _ => Subsingleton.elim z x ▸ hz`. Establish `hc` using `appLE_comp_constHom (f.fromNormalization ≫ s) f.toNormalization U ⊤ e`. Rewrite `hc` using `[f.toNormalization_fromNormalization_assoc]`.

Set `g : Γ(f.normalization, U) →ₐ[k] Γ(Z, ⊤)` to `{ (f.toNormalization.appLE U ⊤ e).hom with commutes' := fun a => congr($hc a) }`. Establish `hg : Function.Injective g`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `h0`.

Establish `h : f.normalization.basicOpen a ≠ ⊥` using `fun h => h0 ((basicOpen_eq_bot_iff a).mp h)`. Take `⟨z, hz⟩` from `f.toNormalization.denseRange.exists_mem_open (f.normalization.basicOpen a).isOpen ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp h)`. Establish `h1 : z ∈ Z.basicOpen (f.toNormalization.appLE U ⊤ e a)`. Rewrite using `[Scheme.basicOpen_appLE]`. Conclude with `⟨trivial, hz⟩`.

Establish `ha' : f.toNormalization.appLE U ⊤ e a = 0` using `ha`. Rewrite `h1` using `[ha', Scheme.basicOpen_zero]`. Conclude with `h1`. Conclude with `{ Algebra.FiniteType.isNoetherianRing k _, dimensionLEOne_of_injective g hg hd, isIntegrallyClosed_sections_of_stalks (isIntegrallyClosed_stalk f) hU with }`.
-/
theorem isDedekindDomain_sections [PerfectField k] (s : X ⟶ Sp k) [LocallyOfFiniteType s]
    (hd : letI := (constHom (f ≫ s) ⊤).toAlgebra; Algebra.trdeg k Γ(Z, ⊤) ≤ 1)
    (U : f.normalization.Opens) (hU : IsAffineOpen U) [hne : Nonempty U] :
    IsDedekindDomain Γ(f.normalization, U) := by
  haveI := isFinite_fromNormalization f s
  letI := (constHom (f ≫ s) ⊤).toAlgebra
  letI := (constHom (f.fromNormalization ≫ s) U).toAlgebra
  haveI : Algebra.FiniteType k Γ(f.normalization, U) := finiteType_constHom _ hU
  have e : ⊤ ≤ f.toNormalization ⁻¹ᵁ U := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨z, hz⟩ := f.toNormalization.denseRange.exists_mem_open U.isOpen ⟨y, hy⟩
    exact fun x _ => Subsingleton.elim z x ▸ hz
  have hc := appLE_comp_constHom (f.fromNormalization ≫ s) f.toNormalization U ⊤ e
  rw [f.toNormalization_fromNormalization_assoc] at hc
  let g : Γ(f.normalization, U) →ₐ[k] Γ(Z, ⊤) :=
    { (f.toNormalization.appLE U ⊤ e).hom with commutes' := fun a => congr($hc a) }
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have h : f.normalization.basicOpen a ≠ ⊥ := fun h => h0 ((basicOpen_eq_bot_iff a).mp h)
    obtain ⟨z, hz⟩ := f.toNormalization.denseRange.exists_mem_open
      (f.normalization.basicOpen a).isOpen ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp h)
    have h1 : z ∈ Z.basicOpen (f.toNormalization.appLE U ⊤ e a) := by
      rw [Scheme.basicOpen_appLE]
      exact ⟨trivial, hz⟩
    have ha' : f.toNormalization.appLE U ⊤ e a = 0 := ha
    rw [ha', Scheme.basicOpen_zero] at h1
    exact h1
  exact { Algebra.FiniteType.isNoetherianRing k _, dimensionLEOne_of_injective g hg hd,
    isIntegrallyClosed_sections_of_stalks (isIntegrallyClosed_stalk f) hU with }

end Scheme

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Use `replace hU : IsAffineOpen U := hU`. Use `haveI : Nonempty U := ⟨⟨x, hxU⟩⟩`. Take `⟨w, hw⟩` from `hW`. Take `⟨y, hyU, hyW⟩` from `nonempty_preirreducible_inter U.isOpen W.isOpen ⟨x, hxU⟩ ⟨w, hw⟩`.

Take `⟨h, hhW, hy⟩` from `hU.exists_basicOpen_le ⟨y, hyW⟩ hyU`. Establish `h0 : h ≠ 0`. Introduce and unpack `rfl`. Rewrite `hy` using `[Scheme.basicOpen_zero]`. Conclude with `hy`.

Use `letI := (constHom s U).toAlgebra`. Use `haveI : Algebra.FiniteType k Γ(X, U) := finiteType_constHom s hU`. Take `⟨p, hp, hpm, hhp, hd⟩` from `exists_prime k _ (hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hxU⟩ hx) h h0`. Set `P : Spec Γ(X, U)` to `⟨p, hp⟩`. Establish `hmem (b : Γ(X, U)) : hU.fromSpec P ∈ X.basicOpen b ↔ b ∉ p`.

Express the relevant statement in the definitionally equal form `P ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen b ↔ _`. Rewrite using `[hU.fromSpec_preimage_basicOpen]`. Both sides reduce to the same expression. Use `⟨hU.fromSpec P, hhW ((hmem h).mpr hhp), ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : P ⤳ hU.primeIdealOf ⟨x, hxU⟩` using `(PrimeSpectrum.le_iff_specializes _ _).mp hpm`.

Establish `h2` using `h1.map hU.fromSpec.continuous`. Rewrite `h2` using `[hU.fromSpec_primeIdealOf]`. Then use the resulting hypothesis. Set `f` to `X.fromSpecResidueField (hU.fromSpec P)`. Establish `e : ⊤ ≤ f ⁻¹ᵁ U` using `fun z _ => by`. Express the relevant statement in the definitionally equal form `f z ∈ U`.

Rewrite using `[Scheme.fromSpecResidueField_apply]`. Conclude with `hU.range_fromSpec.le ⟨P, rfl⟩`. Use `haveI : Nonempty (⊤ : (Spec (X.residueField (hU.fromSpec P))).Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩`. Use `letI := (isField_sections (⊤ : (Spec (X.residueField (hU.fromSpec P))).Opens)).toField`. Use `letI := (constHom (f ≫ s) ⊤).toAlgebra`.

Use `letI := (f.appLE U ⊤ e).hom.toAlgebra`. Use `haveI : IsScalarTower k Γ(X, U) Γ(Spec (X.residueField (hU.fromSpec P)), ⊤) := .of_algebraMap_eq' (appLE_comp_constHom s f U ⊤ e).symm`. Use `(finite_integralClosure k (surjectiveOnStalks_appLE f hU ⊤ e)).2 ?_` and prove the remaining obligations. Establish `hk : RingHom.ker (f.appLE U ⊤ e).hom = p`. Use extensionality with `b`.

Rewrite using `[RingHom.mem_ker, ← basicOpen_eq_bot_iff, Scheme.basicOpen_appLE, top_inf_eq, ← not_iff_not, ← hmem b, ← Ne, TopologicalSpace.Opens.ne_bot_iff_nonempty]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Establish `hz' : f z ∈ X.basicOpen b` using `hz`. Rewrite `hz'` using `[Scheme.fromSpecResidueField_apply]`. Then use the resulting hypothesis.

Introduce `hz`. Use `⟨Nonempty.some inferInstance, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f _ ∈ X.basicOpen b`. Rewrite using `[Scheme.fromSpecResidueField_apply]` and apply the resulting hypothesis. Rewrite using `[RingHom.algebraMap_toAlgebra, hk]`.

Conclude with `hd`.
-/
theorem exists_point {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X]
    (s : X ⟶ Sp k) [LocallyOfFiniteType s] (x : X) (hx : IsClosed ({x} : Set X)) (W : X.Opens)
    (hW : Nonempty W) : ∃ ξ : X, ξ ∈ W ∧ ξ ⤳ x ∧
      letI := (constHom (X.fromSpecResidueField ξ ≫ s) ⊤).toAlgebra
      Algebra.trdeg k Γ(Spec (X.residueField ξ), ⊤) ≤ 1 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  replace hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨w, hw⟩ := hW
  obtain ⟨y, hyU, hyW⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen ⟨x, hxU⟩ ⟨w, hw⟩
  obtain ⟨h, hhW, hy⟩ := hU.exists_basicOpen_le ⟨y, hyW⟩ hyU
  have h0 : h ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hy
    exact hy
  letI := (constHom s U).toAlgebra
  haveI : Algebra.FiniteType k Γ(X, U) := finiteType_constHom s hU
  obtain ⟨p, hp, hpm, hhp, hd⟩ := exists_prime k _ (hU.primeIdealOf_isMaximal_of_isClosed
    ⟨x, hxU⟩ hx) h h0
  let P : Spec Γ(X, U) := ⟨p, hp⟩
  have hmem (b : Γ(X, U)) : hU.fromSpec P ∈ X.basicOpen b ↔ b ∉ p := by
    change P ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen b ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    rfl
  refine ⟨hU.fromSpec P, hhW ((hmem h).mpr hhp), ?_, ?_⟩
  · have h1 : P ⤳ hU.primeIdealOf ⟨x, hxU⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hpm
    have h2 := h1.map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf] at h2
  · let f := X.fromSpecResidueField (hU.fromSpec P)
    have e : ⊤ ≤ f ⁻¹ᵁ U := fun z _ => by
      change f z ∈ U
      rw [Scheme.fromSpecResidueField_apply]
      exact hU.range_fromSpec.le ⟨P, rfl⟩
    haveI : Nonempty (⊤ : (Spec (X.residueField (hU.fromSpec P))).Opens) :=
      ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
    letI := (isField_sections (⊤ : (Spec (X.residueField (hU.fromSpec P))).Opens)).toField
    letI := (constHom (f ≫ s) ⊤).toAlgebra
    letI := (f.appLE U ⊤ e).hom.toAlgebra
    haveI : IsScalarTower k Γ(X, U) Γ(Spec (X.residueField (hU.fromSpec P)), ⊤) :=
      .of_algebraMap_eq' (appLE_comp_constHom s f U ⊤ e).symm
    refine (finite_integralClosure k (surjectiveOnStalks_appLE f hU ⊤ e)).2 ?_
    have hk : RingHom.ker (f.appLE U ⊤ e).hom = p := by
      ext b
      rw [RingHom.mem_ker, ← basicOpen_eq_bot_iff, Scheme.basicOpen_appLE, top_inf_eq,
        ← not_iff_not, ← hmem b, ← Ne, TopologicalSpace.Opens.ne_bot_iff_nonempty]
      constructor
      · rintro ⟨z, hz⟩
        have hz' : f z ∈ X.basicOpen b := hz
        rwa [Scheme.fromSpecResidueField_apply] at hz'
      · intro hz
        refine ⟨Nonempty.some inferInstance, ?_⟩
        change f _ ∈ X.basicOpen b
        rwa [Scheme.fromSpecResidueField_apply]
    rw [RingHom.algebraMap_toAlgebra, hk]
    exact hd

end GlobalTheory.NormCurve
