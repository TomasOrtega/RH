import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.InvariantLevels
import GroundTheory.ProfiniteCohomology.CohomologyTwoIntAddEquivQZSymmApply
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel

variable (F Ω : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω] in

/- English proof (translation)
Establish `e` using `congrArg (fun φ => φ.hom y) (unitsInflationOfLE_comp_unitsInflation (L := Ω) h 2)`. Simplify `e` using `only [ModuleCat.hom_comp, LinearMap.comp_apply]`.
-/
theorem brauerInflation_unitsInflationOfLE {E E' : IntermediateField F Ω} (h : E ≤ E')
    [FiniteDimensional F E] [Normal F E] [FiniteDimensional F E'] [Normal F E']
    (y : groupCohomology (galUnits F E) 2) :
    (brauerInflation E').hom ((unitsInflationOfLE h 2).hom y) = (brauerInflation E).hom y := by
  have e := congrArg (fun φ => φ.hom y) (unitsInflationOfLE_comp_unitsInflation (L := Ω) h 2)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using e

/- English proof (translation)
Use `set n := Module.finrank F E with hn_def`. Establish `hn : n ≠ 0` using `Module.finrank_pos.ne'`. Establish `hNn : (N : ℕ) = n` using `hEN.symm`. Use `set q := Nat.card 𝓀[F] with hq_def`. Use `set f := Module.finrank 𝓀[F] 𝓀[E] with hf_def`.

Establish `hQ : Nat.card 𝓀[E] = q ^ f`. Use `Fintype.ofFinite 𝓀[F]` as an intermediate fact. Use `Fintype.ofFinite 𝓀[E]` as an intermediate fact. Rewrite using `[hq_def, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := 𝓀[F]) (V := 𝓀[E])]`. Establish `hf : f ≠ 0`.

Use `ramificationIndex_mul_residueDegree F E` as an intermediate fact. Rewrite `this` using `[residueDegree_eq_finrank]`. Conclude with `right_ne_zero_of_mul (this.trans_ne hn)`. Use `IsSepClosure.sep_closed F (K := Ω)` as an intermediate fact. Take `⟨ζ, hζE⟩` from `exists_isPrimitiveRoot_card_pow_sub_one (K := E) (Ksep := Ω) hn`.

Establish `hζ : IsPrimitiveRoot ζ (q ^ (f * n) - 1)` using `by rwa [hQ, ← pow_mul] at hζE`. Establish `hKζ` using `(isUnramifiedSubextension_adjoin (K := F) (Ksep := Ω) (mul_ne_zero hf hn) hζ).1`. Establish `: FiniteDimensional F F⟮ζ⟯` using `hKζ.1`. Establish `: IsGalois F F⟮ζ⟯` using `IsUnramifiedSubextension.isGalois hKζ`. Use `set M : IntermediateField F Ω := E ⊔ F⟮ζ⟯ with hM_def`.

Establish `hEM : E ≤ M` using `le_sup_left`. Set `_ : Algebra E M` to `(IntermediateField.inclusion hEM).toRingHom.toAlgebra`. Establish `: IsScalarTower F E M` using `IsScalarTower.of_algebraMap_eq' rfl`. Establish `: FiniteDimensional E M` using `Module.Finite.of_restrictScalars_finite F E M`. Establish `: ValuativeExtension E M` using `IntermediateField.valuativeExtension_inclusion hEM`.

Set `ζM : M` to `⟨ζ, (le_sup_right : F⟮ζ⟯ ≤ M) (mem_adjoin_simple_self F ζ)⟩`. Establish `hζM : IsPrimitiveRoot ζM (Nat.card 𝓀[E] ^ n - 1)` using `(IsPrimitiveRoot.map_iff_of_injective (f := M.val) M.val.injective).1 hζE`. Establish `htop : E⟮ζM⟯ = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`.

Establish `hle : M ≤ ((E⟮ζM⟯).restrictScalars F).map M.val`. Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce `y hy`. Conclude with `⟨algebraMap E M ⟨y, hy⟩, (E⟮ζM⟯).algebraMap_mem _, rfl⟩`. Rewrite using `[adjoin_simple_le_iff]`.

Conclude with `⟨ζM, mem_adjoin_simple_self E ζM, rfl⟩`. Take `⟨y, hy, hyx⟩` from `hle x.2`. Establish `: y = x` using `Subtype.ext hyx`. Conclude with `this ▸ hy`. Establish `: IsUnramified E M` using `⟨ramificationIndex_eq_one_of_adjoin_eq_top hζM (natCast_card_pow_sub_one_ne_zero (K := E) hn) htop⟩`.

Establish `hNM : unramifiedLevel F Ω N ≤ M` using `(IsUnramifiedSubextension.le_adjoin (isUnramifiedSubextension_unramifiedLevel F Ω N) (mul_ne_zero hf hn) (by rw [finrank_unramifiedLevel, hNn]; exact dvd_mul_left n f) hζ).trans le_sup_right`. Set `_ : Algebra (unramifiedLevel F Ω N) M` to `(IntermediateField.inclusion hNM).toRingHom.toAlgebra`. Establish `: IsScalarTower F (unramifiedLevel F Ω N) M` using `IsScalarTower.of_algebraMap_eq' rfl`. Establish `: ValuativeExtension (unramifiedLevel F Ω N) M` using `IntermediateField.valuativeExtension_inclusion hNM`. Establish `hvanish` using `unitsInfl_comp_unitsRes_eq_zero F E (unramifiedLevel F Ω N) M (by rw [finrank_unramifiedLevel, hNn])`.

Establish `hAB : LinearMap.range (unitsInfl F (unramifiedLevel F Ω N) M 2).hom ≤ LinearMap.range (unitsInfl F E M 2).hom`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[range_unitsInfl_two_eq_ker_unitsRes F E M, LinearMap.mem_ker]`. Conclude with `congrArg (fun φ => φ.hom w) hvanish`. Establish `hcardA : Nat.card (LinearMap.range (unitsInfl F (unramifiedLevel F Ω N) M 2).hom) = n`.

Rewrite using `[← Nat.card_congr (LinearEquiv.ofInjective _ (unitsInfl_two_injective F (unramifiedLevel F Ω N) M)).toEquiv, natCard_groupCohomology_two_galUnits, finrank_unramifiedLevel, hNn]`. Establish `hcardB : Nat.card (LinearMap.range (unitsInfl F E M 2).hom) = n`. Rewrite using `[← Nat.card_congr (LinearEquiv.ofInjective _ (unitsInfl_two_injective F E M)).toEquiv, natCard_groupCohomology_two_galUnits]`. Establish `: Finite (LinearMap.range (unitsInfl F E M 2).hom)` using `Nat.finite_of_card_ne_zero (hcardB.trans_ne hn)`. Establish `hBA : LinearMap.range (unitsInfl F E M 2).hom ≤ LinearMap.range (unitsInfl F (unramifiedLevel F Ω N) M 2).hom`.

Establish `: Finite (LinearMap.range (unitsInfl F E M 2).hom).toAddSubgroup` using `this`. Establish `h` using `AddSubgroup.eq_of_le_of_card_ge (H := (LinearMap.range (unitsInfl F (unramifiedLevel F Ω N) M 2).hom).toAddSubgroup) (K := (LinearMap.range (unitsInfl F E M 2).hom).toAddSubgroup) hAB (by`. Express the relevant statement in the definitionally equal form `Nat.card (LinearMap.range (unitsInfl F E M 2).hom) ≤ Nat.card (LinearMap.range (unitsInfl F (unramifiedLevel F Ω N) M 2).hom)`. Rewrite using `[hcardA, hcardB])`. Introduce `v hv`.

Establish `hv' : v ∈ (LinearMap.range (unitsInfl F E M 2).hom).toAddSubgroup` using `hv`. Rewrite `hv'` using `[← h]`. Conclude with `hv'`. Take `⟨z, hz⟩` from `hBA ⟨y, rfl⟩`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Rewrite using `[← brauerInflation_unitsInflationOfLE F Ω hNM, ← brauerInflation_unitsInflationOfLE F Ω hEM]`. Conclude with `congrArg (brauerInflation M).hom hz`.
-/
theorem exists_unramifiedLevel_brauerInflation_eq (E : IntermediateField F Ω) [FiniteDimensional F E]
    [IsGalois F E] (N : ℕ+) (hEN : Module.finrank F E = N) (y : groupCohomology (galUnits F E) 2) :
    ∃ z : groupCohomology (galUnits F (unramifiedLevel F Ω N)) 2,
      (brauerInflation (unramifiedLevel F Ω N)).hom z = (brauerInflation E).hom y := by
  classical
  set n := Module.finrank F E with hn_def
  have hn : n ≠ 0 := Module.finrank_pos.ne'
  have hNn : (N : ℕ) = n := hEN.symm

  set q := Nat.card 𝓀[F] with hq_def
  set f := Module.finrank 𝓀[F] 𝓀[E] with hf_def
  have hQ : Nat.card 𝓀[E] = q ^ f := by
    have := Fintype.ofFinite 𝓀[F]
    have := Fintype.ofFinite 𝓀[E]
    rw [hq_def, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := 𝓀[F]) (V := 𝓀[E])]
  have hf : f ≠ 0 := by
    have := ramificationIndex_mul_residueDegree F E
    rw [residueDegree_eq_finrank] at this
    exact right_ne_zero_of_mul (this.trans_ne hn)

  have := IsSepClosure.sep_closed F (K := Ω)
  obtain ⟨ζ, hζE⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := E) (Ksep := Ω) hn
  have hζ : IsPrimitiveRoot ζ (q ^ (f * n) - 1) := by rwa [hQ, ← pow_mul] at hζE
  have hKζ := (isUnramifiedSubextension_adjoin (K := F) (Ksep := Ω) (mul_ne_zero hf hn) hζ).1
  have : FiniteDimensional F F⟮ζ⟯ := hKζ.1
  have : IsGalois F F⟮ζ⟯ := IsUnramifiedSubextension.isGalois hKζ
  set M : IntermediateField F Ω := E ⊔ F⟮ζ⟯ with hM_def
  have hEM : E ≤ M := le_sup_left
  let _ : Algebra E M := (IntermediateField.inclusion hEM).toRingHom.toAlgebra
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite F E M
  have : ValuativeExtension E M := IntermediateField.valuativeExtension_inclusion hEM

  let ζM : M := ⟨ζ, (le_sup_right : F⟮ζ⟯ ≤ M) (mem_adjoin_simple_self F ζ)⟩
  have hζM : IsPrimitiveRoot ζM (Nat.card 𝓀[E] ^ n - 1) :=
    (IsPrimitiveRoot.map_iff_of_injective (f := M.val) M.val.injective).1 hζE
  have htop : E⟮ζM⟯ = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hle : M ≤ ((E⟮ζM⟯).restrictScalars F).map M.val := by
      refine sup_le ?_ ?_
      · intro y hy
        exact ⟨algebraMap E M ⟨y, hy⟩, (E⟮ζM⟯).algebraMap_mem _, rfl⟩
      · rw [adjoin_simple_le_iff]
        exact ⟨ζM, mem_adjoin_simple_self E ζM, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have : IsUnramified E M :=
    ⟨ramificationIndex_eq_one_of_adjoin_eq_top hζM (natCast_card_pow_sub_one_ne_zero (K := E) hn)
      htop⟩

  have hNM : unramifiedLevel F Ω N ≤ M :=
    (IsUnramifiedSubextension.le_adjoin (isUnramifiedSubextension_unramifiedLevel F Ω N)
      (mul_ne_zero hf hn) (by rw [finrank_unramifiedLevel, hNn]; exact dvd_mul_left n f) hζ).trans
      le_sup_right
  let _ : Algebra (unramifiedLevel F Ω N) M := (IntermediateField.inclusion hNM).toRingHom.toAlgebra
  have : IsScalarTower F (unramifiedLevel F Ω N) M := IsScalarTower.of_algebraMap_eq' rfl
  have : ValuativeExtension (unramifiedLevel F Ω N) M :=
    IntermediateField.valuativeExtension_inclusion hNM

  have hvanish := unitsInfl_comp_unitsRes_eq_zero F E (unramifiedLevel F Ω N) M
    (by rw [finrank_unramifiedLevel, hNn])

  have hAB : LinearMap.range (unitsInfl F (unramifiedLevel F Ω N) M 2).hom ≤
      LinearMap.range (unitsInfl F E M 2).hom := by
    rintro _ ⟨w, rfl⟩
    rw [range_unitsInfl_two_eq_ker_unitsRes F E M, LinearMap.mem_ker]
    exact congrArg (fun φ => φ.hom w) hvanish
  have hcardA : Nat.card (LinearMap.range (unitsInfl F (unramifiedLevel F Ω N) M 2).hom) = n := by
    rw [← Nat.card_congr (LinearEquiv.ofInjective _
      (unitsInfl_two_injective F (unramifiedLevel F Ω N) M)).toEquiv,
      natCard_groupCohomology_two_galUnits, finrank_unramifiedLevel, hNn]
  have hcardB : Nat.card (LinearMap.range (unitsInfl F E M 2).hom) = n := by
    rw [← Nat.card_congr (LinearEquiv.ofInjective _ (unitsInfl_two_injective F E M)).toEquiv,
      natCard_groupCohomology_two_galUnits]
  have : Finite (LinearMap.range (unitsInfl F E M 2).hom) :=
    Nat.finite_of_card_ne_zero (hcardB.trans_ne hn)
  have hBA : LinearMap.range (unitsInfl F E M 2).hom ≤
      LinearMap.range (unitsInfl F (unramifiedLevel F Ω N) M 2).hom := by
    have : Finite (LinearMap.range (unitsInfl F E M 2).hom).toAddSubgroup := this
    have h := AddSubgroup.eq_of_le_of_card_ge (H := (LinearMap.range
      (unitsInfl F (unramifiedLevel F Ω N) M 2).hom).toAddSubgroup)
      (K := (LinearMap.range (unitsInfl F E M 2).hom).toAddSubgroup) hAB
      (by
        change Nat.card (LinearMap.range (unitsInfl F E M 2).hom) ≤
          Nat.card (LinearMap.range (unitsInfl F (unramifiedLevel F Ω N) M 2).hom)
        rw [hcardA, hcardB])
    intro v hv
    have hv' : v ∈ (LinearMap.range (unitsInfl F E M 2).hom).toAddSubgroup := hv
    rw [← h] at hv'
    exact hv'
  obtain ⟨z, hz⟩ := hBA ⟨y, rfl⟩
  refine ⟨z, ?_⟩
  rw [← brauerInflation_unitsInflationOfLE F Ω hNM, ← brauerInflation_unitsInflationOfLE F Ω hEM]
  exact congrArg (brauerInflation M).hom hz

/- English proof (translation)
Take `⟨E, y, rfl⟩` from `exists_brauerInflation_eq x`. Take `⟨z, hz⟩` from `exists_unramifiedLevel_brauerInflation_eq F Ω E.toIntermediateField ⟨Module.finrank F E.toIntermediateField, Module.finrank_pos⟩ rfl y`. Conclude with `⟨_, z, hz⟩`.
-/
theorem exists_brauerInflation_unramifiedLevel (x : galoisBrauerGroup F Ω) :
    ∃ (n : ℕ+) (y : groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2),
      (brauerInflation (unramifiedLevel F Ω n)).hom y = x := by
  obtain ⟨E, y, rfl⟩ := exists_brauerInflation_eq x
  obtain ⟨z, hz⟩ := exists_unramifiedLevel_brauerInflation_eq F Ω E.toIntermediateField
    ⟨Module.finrank F E.toIntermediateField, Module.finrank_pos⟩ rfl y
  exact ⟨_, z, hz⟩

noncomputable def brauerInv : galoisBrauerGroup F Ω →+ QZ where
  toFun := brauerInvFun F Ω
  map_zero' := by
    have h := brauerInvFun_brauerInflation F Ω 1 0
    rwa [map_zero, map_zero] at h
  map_add' x₁ x₂ := by
    obtain ⟨m, y, rfl⟩ := exists_brauerInflation_unramifiedLevel F Ω x₁
    obtain ⟨n, z, rfl⟩ := exists_brauerInflation_unramifiedLevel F Ω x₂
    have hm : (m : ℕ) ∣ ((m * n : ℕ+) : ℕ) := ⟨n, by simp⟩
    have hn : (n : ℕ) ∣ ((m * n : ℕ+) : ℕ) := ⟨m, by simp [mul_comm]⟩
    rw [← brauerInflation_unitsInflationOfLE F Ω (unramifiedLevel_le F Ω hm) y,
      ← brauerInflation_unitsInflationOfLE F Ω (unramifiedLevel_le F Ω hn) z,
      ← LinearMap.map_add]
    simp only [brauerInvFun_brauerInflation]
    exact map_add _ _ _

/- English proof (translation)
The claim follows from `brauerInvFun_brauerInflation F Ω n y`.
-/
theorem brauerInv_brauerInflation (n : ℕ+)
    (y : groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2) :
    brauerInv F Ω ((brauerInflation (unramifiedLevel F Ω n)).hom y) = unramifiedLevelInv F Ω n y :=
  brauerInvFun_brauerInflation F Ω n y

/- English proof (translation)
The claim follows from `(unramifiedInv_injective F (unramifiedLevel F Ω n)).comp (h2GalUnitsAddEquiv F _).injective`.
-/
theorem unramifiedLevelInv_injective (n : ℕ+) : Function.Injective (unramifiedLevelInv F Ω n) :=
  (unramifiedInv_injective F (unramifiedLevel F Ω n)).comp (h2GalUnitsAddEquiv F _).injective

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨n, y, rfl⟩` from `exists_brauerInflation_unramifiedLevel F Ω x`. Rewrite `hx` using `[brauerInv_brauerInflation]`. Establish `hy : y = 0` using `unramifiedLevelInv_injective F Ω n (hx.trans (map_zero _).symm)`.

Rewrite using `[hy, map_zero]`.
-/
theorem brauerInv_injective : Function.Injective (brauerInv F Ω) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨n, y, rfl⟩ := exists_brauerInflation_unramifiedLevel F Ω x
  rw [brauerInv_brauerInflation] at hx
  have hy : y = 0 := unramifiedLevelInv_injective F Ω n (hx.trans (map_zero _).symm)
  rw [hy, map_zero]

/- English proof (translation)
Introduce `a`. Choose the witnesses or unpack the hypotheses as in `⟨n, hna⟩ : ∃ n : ℕ+, (n : ℕ) • a = 0 := by`. Take `⟨k, hk, hka⟩` from `isOfFinAddOrder_iff_nsmul_eq_zero.1 (isAddTorsion_QZ a)`. Conclude with `⟨⟨k, hk⟩, hka⟩`. Establish `hmem : a ∈ (unramifiedInv F (unramifiedLevel F Ω n)).range`.

Rewrite using `[mem_range_unramifiedInv_iff, finrank_unramifiedLevel]`. Conclude with `hna`. Take `⟨w, hw⟩` from `hmem`. Use `⟨(brauerInflation (unramifiedLevel F Ω n)).hom ((h2GalUnitsAddEquiv F _).symm w), ?_⟩` and prove the remaining obligations. Rewrite using `[brauerInv_brauerInflation, unramifiedLevelInv_apply, AddEquiv.apply_symm_apply, hw]`.
-/
theorem brauerInv_surjective : Function.Surjective (brauerInv F Ω) := by
  intro a
  obtain ⟨n, hna⟩ : ∃ n : ℕ+, (n : ℕ) • a = 0 := by
    obtain ⟨k, hk, hka⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (isAddTorsion_QZ a)
    exact ⟨⟨k, hk⟩, hka⟩
  have hmem : a ∈ (unramifiedInv F (unramifiedLevel F Ω n)).range := by
    rw [mem_range_unramifiedInv_iff, finrank_unramifiedLevel]
    exact hna
  obtain ⟨w, hw⟩ := hmem
  refine ⟨(brauerInflation (unramifiedLevel F Ω n)).hom ((h2GalUnitsAddEquiv F _).symm w), ?_⟩
  rw [brauerInv_brauerInflation, unramifiedLevelInv_apply, AddEquiv.apply_symm_apply, hw]

/- English proof (translation)
Assemble the required witnesses or components as `⟨brauerInv_injective F Ω, brauerInv_surjective F Ω⟩`.
-/
theorem brauerInv_bijective : Function.Bijective (brauerInv F Ω) :=
  ⟨brauerInv_injective F Ω, brauerInv_surjective F Ω⟩

noncomputable def brauerInvEquiv : galoisBrauerGroup F Ω ≃+ QZ :=
  AddEquiv.ofBijective (brauerInv F Ω) (brauerInv_bijective F Ω)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem brauerInvEquiv_apply (x : galoisBrauerGroup F Ω) : brauerInvEquiv F Ω x = brauerInv F Ω x :=
  rfl

end GroundTheory.ProfCoh
