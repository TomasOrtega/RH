import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc

namespace UpperTheory.V.Z.Bc

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, rfl⟩ x`. Conclude with `t.commutes x`. Introduce `h`. Conclude with `⟨{ s.toRingEquiv with commutes' := h }, AlgEquiv.ext fun _ => rfl⟩`.
-/
private theorem mem_range_resG_iff (k L Ω : Type) [Field k] [Field L] [Field Ω] [Algebra k L] [Algebra k Ω] [Algebra L Ω]
    [IsScalarTower k L Ω] (s : G k Ω) :
    s ∈ (resG k L Ω).range ↔ ∀ x : L, s (algebraMap L Ω x) = algebraMap L Ω x := by
  constructor
  · rintro ⟨t, rfl⟩ x
    exact t.commutes x
  · intro h
    exact ⟨{ s.toRingEquiv with commutes' := h }, AlgEquiv.ext fun _ => rfl⟩

/- English proof (translation)
Rewrite using `[← AlgEquiv.restrictNormal_commutes, ← AlgEquiv.restrictNormal_commutes]`. Express the relevant statement in the definitionally equal form `algebraMap K M (AlgEquiv.restrictNormalHom K (σ * τ) x) = algebraMap K M (AlgEquiv.restrictNormalHom K (τ * σ) x)`. Rewrite using `[map_mul, map_mul, h.is_comm.comm]`.
-/
private theorem comm_on (k K M : Type) [Field k] [Field K] [Field M] [Algebra k K] [Algebra k M] [Algebra K M]
    [IsScalarTower k K M] [h : IsAbelianGalois k K] (σ τ : M ≃ₐ[k] M) (x : K) :
    (σ * τ) (algebraMap K M x) = (τ * σ) (algebraMap K M x) := by
  rw [← AlgEquiv.restrictNormal_commutes, ← AlgEquiv.restrictNormal_commutes]
  change algebraMap K M (AlgEquiv.restrictNormalHom K (σ * τ) x) = algebraMap K M (AlgEquiv.restrictNormalHom K (τ * σ) x)
  rw [map_mul, map_mul, h.is_comm.comm]

/- English proof (translation)
Set `a` to `IsScalarTower.toAlgHom k K Ω`. Set `b` to `IsScalarTower.toAlgHom k K' Ω`. Set `M : IntermediateField k Ω` to `a.fieldRange ⊔ b.fieldRange`. Establish `hM : M = IntermediateField.adjoin k ((a.fieldRange : Set Ω) ∪ b.fieldRange)` using `IntermediateField.sup_def _ _`. Establish `ha : ∀ x, a x ∈ M` using `fun x => (le_sup_left : a.fieldRange ≤ M) ⟨x, rfl⟩`.

Establish `hb : ∀ x, b x ∈ M` using `fun x => (le_sup_right : b.fieldRange ≤ M) ⟨x, rfl⟩`. Use `letI iK : Algebra K M := (a.toRingHom.codRestrict M ha).toAlgebra`. Use `letI iK' : Algebra K' M := (b.toRingHom.codRestrict M hb).toAlgebra`. Use `haveI t1 : IsScalarTower k K M := IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (a.commutes x).symm`. Use `haveI t2 : IsScalarTower k K' M := IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (b.commutes x).symm`.

Use `haveI t3 : IsScalarTower K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl`. Use `haveI t4 : IsScalarTower K' M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl`. Establish `hext : ∀ f g : M →ₐ[k] Ω, (∀ x : K, f (algebraMap K M x) = g (algebraMap K M x)) → (∀ x : K', f (algebraMap K' M x) = g (algebraMap K' M x)) → f = g`. Introduce `f g h1 h2`. Use `IntermediateField.algHom_ext_of_eq_adjoin k hM ?_` and prove the remaining obligations.

Introduce and unpack `x (⟨y, rfl⟩ | ⟨y, rfl⟩)`. Conclude with `h1 y`. Conclude with `h2 y`. Use `haveI : FiniteDimensional k a.fieldRange := a.equivFieldRange.toLinearEquiv.finiteDimensional`. Use `haveI : FiniteDimensional k b.fieldRange := b.equivFieldRange.toLinearEquiv.finiteDimensional`.

Use `haveI : IsGalois k a.fieldRange := IsGalois.of_algEquiv a.equivFieldRange`. Use `haveI : IsGalois k b.fieldRange := IsGalois.of_algEquiv b.equivFieldRange`. Use `haveI : FiniteDimensional k M := IntermediateField.finiteDimensional_sup _ _`. Use `haveI : Normal k M := IntermediateField.normal_sup k Ω _ _`. Use `haveI : Algebra.IsSeparable k M := inferInstance`.

Use `haveI : IsGalois k M := ⟨⟩`. Use `⟨M, inferInstance, inferInstance, iK, iK', inferInstance, t1, t2, t3, t4, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Use `{ is_comm := ⟨fun σ τ => ?_⟩ }` and prove the remaining obligations. Use `hext (M.val.comp (σ * τ : M ≃ₐ[k] M)) (M.val.comp (τ * σ : M ≃ₐ[k] M)) (fun x => congrArg Subtype.val (comm_on k K M σ τ x)) (fun x => congrArg Subtype.val (comm_on k K' M σ τ x))` as an intermediate fact. Conclude with `AlgEquiv.ext fun x => Subtype.ext (DFunLike.congr_fun this x)`.

Introduce `s h1 h2 x`. Conclude with `DFunLike.congr_fun (hext ((s : Ω →ₐ[k] Ω).comp M.val) M.val h1 h2) x`.
-/
private theorem exists_compositum (k K K' Ω : Type) [Field k] [Field K] [Field K'] [Field Ω] [Algebra k K] [Algebra k K']
    [Algebra k Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower k K Ω] [IsScalarTower k K' Ω]
    [FiniteDimensional k K] [FiniteDimensional k K'] [IsAbelianGalois k K] [IsAbelianGalois k K'] :
    ∃ (M : Type) (_ : Field M) (_ : Algebra k M) (_ : Algebra K M) (_ : Algebra K' M) (_ : Algebra M Ω)
      (_ : IsScalarTower k K M) (_ : IsScalarTower k K' M) (_ : IsScalarTower K M Ω) (_ : IsScalarTower K' M Ω),
      FiniteDimensional k M ∧ IsAbelianGalois k M ∧
      ∀ s : Ω ≃ₐ[k] Ω, (∀ x : K, s (algebraMap K Ω x) = algebraMap K Ω x) → (∀ x : K', s (algebraMap K' Ω x) = algebraMap K' Ω x) →
        ∀ x : M, s (algebraMap M Ω x) = algebraMap M Ω x := by
  let a := IsScalarTower.toAlgHom k K Ω
  let b := IsScalarTower.toAlgHom k K' Ω
  let M : IntermediateField k Ω := a.fieldRange ⊔ b.fieldRange
  have hM : M = IntermediateField.adjoin k ((a.fieldRange : Set Ω) ∪ b.fieldRange) := IntermediateField.sup_def _ _
  have ha : ∀ x, a x ∈ M := fun x => (le_sup_left : a.fieldRange ≤ M) ⟨x, rfl⟩
  have hb : ∀ x, b x ∈ M := fun x => (le_sup_right : b.fieldRange ≤ M) ⟨x, rfl⟩
  letI iK : Algebra K M := (a.toRingHom.codRestrict M ha).toAlgebra
  letI iK' : Algebra K' M := (b.toRingHom.codRestrict M hb).toAlgebra
  haveI t1 : IsScalarTower k K M := IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (a.commutes x).symm
  haveI t2 : IsScalarTower k K' M := IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (b.commutes x).symm
  haveI t3 : IsScalarTower K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI t4 : IsScalarTower K' M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hext : ∀ f g : M →ₐ[k] Ω, (∀ x : K, f (algebraMap K M x) = g (algebraMap K M x)) →
      (∀ x : K', f (algebraMap K' M x) = g (algebraMap K' M x)) → f = g := by
    intro f g h1 h2
    refine IntermediateField.algHom_ext_of_eq_adjoin k hM ?_
    rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact h1 y
    · exact h2 y
  haveI : FiniteDimensional k a.fieldRange := a.equivFieldRange.toLinearEquiv.finiteDimensional
  haveI : FiniteDimensional k b.fieldRange := b.equivFieldRange.toLinearEquiv.finiteDimensional
  haveI : IsGalois k a.fieldRange := IsGalois.of_algEquiv a.equivFieldRange
  haveI : IsGalois k b.fieldRange := IsGalois.of_algEquiv b.equivFieldRange
  haveI : FiniteDimensional k M := IntermediateField.finiteDimensional_sup _ _
  haveI : Normal k M := IntermediateField.normal_sup k Ω _ _
  haveI : Algebra.IsSeparable k M := inferInstance
  haveI : IsGalois k M := ⟨⟩
  refine ⟨M, inferInstance, inferInstance, iK, iK', inferInstance, t1, t2, t3, t4, inferInstance, ?_, ?_⟩
  · refine { is_comm := ⟨fun σ τ => ?_⟩ }
    have := hext (M.val.comp (σ * τ : M ≃ₐ[k] M)) (M.val.comp (τ * σ : M ≃ₐ[k] M))
      (fun x => congrArg Subtype.val (comm_on k K M σ τ x)) (fun x => congrArg Subtype.val (comm_on k K' M σ τ x))
    exact AlgEquiv.ext fun x => Subtype.ext (DFunLike.congr_fun this x)
  · intro s h1 h2 x
    exact DFunLike.congr_fun (hext ((s : Ω →ₐ[k] Ω).comp M.val) M.val h1 h2) x

/- English proof (translation)
Use `haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h⟩`. Use `haveI : IsCyclic (K ≃ₐ[ℚ] K) := inferInstance`. Conclude with `IsAbelianGalois.of_isCyclic ℚ K`.
-/
private theorem abelian_of_two (K : Type) [Field K] [NumberField K] (h : Module.finrank ℚ K = 2) : IsAbelianGalois ℚ K := by
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h⟩
  haveI : IsCyclic (K ≃ₐ[ℚ] K) := inferInstance
  exact IsAbelianGalois.of_isCyclic ℚ K

end UpperTheory.V.Z.Bc

/- English proof (translation)
Introduce `K K' Ω _ _ _ _ _ _ _ _ _ _ _ _ _ h h'`. Use `haveI := abelian_of_two K h`. Use `haveI := abelian_of_two K' h'`. Take `⟨M, fM, iQ, iK, iK', iΩ, t1, t2, t3, t4, hfin, hab, hfix⟩` from `exists_compositum ℚ K K' Ω`. Use `haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective`.

Take `rfl : iQ = DivisionRing.toRatAlgebra` from `Subsingleton.elim _ _`. Use `haveI nM : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := hfin }`. Use `haveI : IsTotallyComplex M := isTotallyComplex_of_algebra K M`. Use `haveI cM : IsCMField M := IsCMField.of_isAbelianGalois M`. Use `haveI a1 : IsAbelianGalois K M := IsAbelianGalois.tower_top ℚ K M`.

Use `haveI a2 : IsAbelianGalois K' M := IsAbelianGalois.tower_top ℚ K' M`. Use `⟨M, fM, nM, cM, iK, iK', iΩ, t3, t4, a1.toIsGalois, a2.toIsGalois, isSolvable_of_comm a1.is_comm.comm, isSolvable_of_comm a2.is_comm.comm, fun s => ?_, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_range_resG_iff, mem_range_resG_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hs x`.

Rewrite using `[IsScalarTower.algebraMap_apply K' M Ω]`. Conclude with `hs _`. Introduce `hs`. Conclude with `hfix (resG ℚ K Ω s) s.commutes hs`. Rewrite using `[mem_range_resG_iff, mem_range_resG_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `hs x`. Rewrite using `[IsScalarTower.algebraMap_apply K M Ω]`. Conclude with `hs _`. Introduce `hs`.

Conclude with `hfix (resG ℚ K' Ω s) hs s.commutes`.
-/
theorem UpperTheory.V.Z.Bc.biQuad :
    BiQuad := by
  intro K K' Ω _ _ _ _ _ _ _ _ _ _ _ _ _ h h'
  haveI := abelian_of_two K h
  haveI := abelian_of_two K' h'
  obtain ⟨M, fM, iQ, iK, iK', iΩ, t1, t2, t3, t4, hfin, hab, hfix⟩ := exists_compositum ℚ K K' Ω
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  obtain rfl : iQ = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  haveI nM : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  haveI : IsTotallyComplex M := isTotallyComplex_of_algebra K M
  haveI cM : IsCMField M := IsCMField.of_isAbelianGalois M
  haveI a1 : IsAbelianGalois K M := IsAbelianGalois.tower_top ℚ K M
  haveI a2 : IsAbelianGalois K' M := IsAbelianGalois.tower_top ℚ K' M
  refine ⟨M, fM, nM, cM, iK, iK', iΩ, t3, t4, a1.toIsGalois, a2.toIsGalois,
    isSolvable_of_comm a1.is_comm.comm, isSolvable_of_comm a2.is_comm.comm, fun s => ?_, fun s => ?_⟩
  · rw [mem_range_resG_iff, mem_range_resG_iff]
    constructor
    · intro hs x
      rw [IsScalarTower.algebraMap_apply K' M Ω]
      exact hs _
    · intro hs
      exact hfix (resG ℚ K Ω s) s.commutes hs
  · rw [mem_range_resG_iff, mem_range_resG_iff]
    constructor
    · intro hs x
      rw [IsScalarTower.algebraMap_apply K M Ω]
      exact hs _
    · intro hs
      exact hfix (resG ℚ K' Ω s) hs s.commutes
