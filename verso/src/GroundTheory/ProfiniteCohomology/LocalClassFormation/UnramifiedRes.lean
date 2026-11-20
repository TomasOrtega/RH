import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.Unramified
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory GroundTheory.LocalField ValuativeRel

instance valuativeExtension_self (F : Type*) [Field F] [ValuativeRel F] : ValuativeExtension F F :=
  ⟨fun _ _ => Iff.rfl⟩

section Tower

variable (K K' L L' : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [IsUnramified K L] [Field K'] [Field L'] [Algebra K K'] [Algebra K L'] [Algebra K' L']
  [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']

noncomputable def galRestrict : Gal(L'/K') →* Gal(L/K) :=
  haveI : IsGalois K L := isGalois_of_unramified K L IsUnramified.ramificationIndex_eq_one
  (AlgEquiv.restrictNormalHom L).comp
    { toFun := fun σ : Gal(L'/K') => AlgEquiv.restrictScalars K σ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/- English proof (translation)
Establish `: IsGalois K L` using `isGalois_of_unramified K L IsUnramified.ramificationIndex_eq_one`. Conclude with `AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K σ) L x`.
-/
theorem algebraMap_galRestrict_apply (σ : Gal(L'/K')) (x : L) :
    algebraMap L L' (galRestrict K K' L L' σ x) = σ (algebraMap L L' x) := by
  have : IsGalois K L := isGalois_of_unramified K L IsUnramified.ramificationIndex_eq_one
  exact AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K σ) L x

noncomputable def unitsResHom :
    Rep.res (galRestrict K K' L L') (galUnitsZ K L) ⟶ galUnitsZ K' L' :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map (algebraMap L L' : L →* L'))).toIntLinearMap,
    fun σ => by
      ext x
      exact algebraMap_galRestrict_apply K K' L L' σ _⟩

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unitsResHom_hom_apply (x : Additive Lˣ) :
    ((Additive.toMul ((unitsResHom K K' L L').hom x) : L'ˣ) : L') =
      algebraMap L L' (x.toMul : L) :=
  rfl

noncomputable abbrev unitsResH2 :
    groupCohomology (galUnitsZ K L) 2 ⟶ groupCohomology (galUnitsZ K' L') 2 :=
  groupCohomology.map (galRestrict K K' L L') (unitsResHom K K' L L') 2

variable [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] [ValuativeRel L']
  [TopologicalSpace L'] [IsNonarchimedeanLocalField L'] [ValuativeExtension K K']
  [ValuativeExtension K' L'] [ValuativeExtension L L'] [FiniteDimensional K K']
  [FiniteDimensional K' L'] [IsUnramified K' L']

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L] in

/- English proof (translation)
Establish `: ValuativeExtension K L'` using `valuativeExtension_trans K K' L'`. Establish `: FiniteDimensional K L'` using `FiniteDimensional.trans K K' L'`. Establish `: FiniteDimensional L L'` using `FiniteDimensional.right K L L'`. Establish `h1` using `ramificationIndex_tower K L L'`. Establish `h2` using `ramificationIndex_tower K K' L'`.

Rewrite `h1` using `[IsUnramified.ramificationIndex_eq_one (K := K) (L := L), one_mul]`. Rewrite `h2` using `[IsUnramified.ramificationIndex_eq_one (K := K') (L := L'), mul_one]`. Rewrite using `[← h1, h2]`.
-/
theorem ramificationIndex_right_eq :
    ramificationIndex L L' = ramificationIndex K K' := by
  have : ValuativeExtension K L' := valuativeExtension_trans K K' L'
  have : FiniteDimensional K L' := FiniteDimensional.trans K K' L'
  have : FiniteDimensional L L' := FiniteDimensional.right K L L'
  have h1 := ramificationIndex_tower K L L'
  have h2 := ramificationIndex_tower K K' L'
  rw [IsUnramified.ramificationIndex_eq_one (K := K) (L := L), one_mul] at h1
  rw [IsUnramified.ramificationIndex_eq_one (K := K') (L := L'), mul_one] at h2
  rw [← h1, h2]

/- English proof (translation)
Set `` to `Fintype.ofFinite 𝓀[K]`. Set `` to `Fintype.ofFinite 𝓀[K']`. Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[K']), residueDegree_eq_finrank]`.
-/
theorem card_residueField_eq_pow : Nat.card 𝓀[K'] = Nat.card 𝓀[K] ^ residueDegree K K' := by
  let := Fintype.ofFinite 𝓀[K]
  let := Fintype.ofFinite 𝓀[K']
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[K']), residueDegree_eq_finrank]

/- English proof (translation)
Establish `he` using `IsUnramified.ramificationIndex_eq_one (K := K) (L := L)`. Apply `residueAlgEquiv_injective_of_unramified K L he` to reduce the goal to its premises. Use extensionality with `y`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective y`. Establish `hpow : ∀ n : ℕ, residueAlgEquiv K L (frob K L ^ n) (IsLocalRing.residue 𝒪[L] x) = IsLocalRing.residue 𝒪[L] x ^ (Nat.card 𝓀[K] ^ n)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ', map_mul, AlgEquiv.mul_apply, ih, map_pow, residueAlgEquiv_frobenius_apply, ← pow_mul, pow_succ, mul_comm]`.

Rewrite using `[hpow, ← card_residueField_eq_pow K K', residueAlgEquiv_residue]`. Apply `(algebraMap 𝓀[L] 𝓀[L']).injective` to reduce the goal to its premises. Rewrite using `[map_pow, IsLocalRing.ResidueField.algebraMap_residue, IsLocalRing.ResidueField.algebraMap_residue]`. Establish `hx : algebraMap 𝒪[L] 𝒪[L'] (integerAlgEquiv K L (galRestrict K K' L L' (frob K' L')) x) = integerAlgEquiv K' L' (frob K' L') (algebraMap 𝒪[L] 𝒪[L'] x)` using `Subtype.ext (algebraMap_galRestrict_apply K K' L L' _ _)`. Rewrite using `[hx, residue_frobenius_apply]`.
-/
theorem galRestrict_frob : galRestrict K K' L L' (frob K' L') = frob K L ^ residueDegree K K' := by
  have he := IsUnramified.ramificationIndex_eq_one (K := K) (L := L)
  apply residueAlgEquiv_injective_of_unramified K L he
  ext y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hpow : ∀ n : ℕ, residueAlgEquiv K L (frob K L ^ n) (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L] x ^ (Nat.card 𝓀[K] ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', map_mul, AlgEquiv.mul_apply, ih, map_pow, residueAlgEquiv_frobenius_apply,
        ← pow_mul, pow_succ, mul_comm]
  rw [hpow, ← card_residueField_eq_pow K K', residueAlgEquiv_residue]
  apply (algebraMap 𝓀[L] 𝓀[L']).injective
  rw [map_pow, IsLocalRing.ResidueField.algebraMap_residue,
    IsLocalRing.ResidueField.algebraMap_residue]
  have hx : algebraMap 𝒪[L] 𝒪[L'] (integerAlgEquiv K L (galRestrict K K' L L' (frob K' L')) x) =
      integerAlgEquiv K' L' (frob K' L') (algebraMap 𝒪[L] 𝒪[L'] x) :=
    Subtype.ext (algebraMap_galRestrict_apply K K' L L' _ _)
  rw [hx, residue_frobenius_apply]

/- English proof (translation)
Establish `: FiniteDimensional K L'` using `FiniteDimensional.trans K K' L'`. Establish `: FiniteDimensional L L'` using `FiniteDimensional.right K L L'`. Simplify using `only [h2Valuation, groupCohomology.functor_map]`. Rewrite using `[← groupCohomology.map_comp, ← groupCohomology.map_comp]`. Use `groupCohomology.map_congr (by ext; rfl) (LinearMap.ext fun x => ?_) 2` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `ord (algebraMap L L' ((Additive.toMul x : Lˣ) : L)) = (ramificationIndex K K' : ℤ) * ord ((Additive.toMul x : Lˣ) : L)`. Rewrite using `[ord_algebraMap, ramificationIndex_right_eq K K' L L']`.
-/
theorem unitsResH2_comp_h2Valuation :
    unitsResH2 K K' L L' ≫ h2Valuation K' L' =
      h2Valuation K L ≫ groupCohomology.map (galRestrict K K' L L')
        (intMulRes (galRestrict K K' L L') (ramificationIndex K K')) 2 := by
  have : FiniteDimensional K L' := FiniteDimensional.trans K K' L'
  have : FiniteDimensional L L' := FiniteDimensional.right K L L'
  simp only [h2Valuation, groupCohomology.functor_map]
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr (by ext; rfl) (LinearMap.ext fun x => ?_) 2
  change ord (algebraMap L L' ((Additive.toMul x : Lˣ) : L)) =
    (ramificationIndex K K' : ℤ) * ord ((Additive.toMul x : Lˣ) : L)
  rw [ord_algebraMap, ramificationIndex_right_eq K K' L L']

/- English proof (translation)
Establish `hsq` using `congrArg (fun h => h.hom x) (unitsResH2_comp_h2Valuation K K' L L')`. Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply] at hsq`. Rewrite using `[unramifiedInv_apply, hsq, h2IntAddEquiv_map_intMulRes, unramifiedInv_apply, AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply, toMul_ofMul, galRestrict_frob, ofMul_pow, map_nsmul, map_zsmul, map_nsmul, ← ramificationIndex_mul_residueDegree K K', …`.
-/
theorem unramifiedInv_unitsResH2 (x : groupCohomology (galUnitsZ K L) 2) :
    unramifiedInv K' L' ((unitsResH2 K K' L L').hom x) =
      Module.finrank K K' • unramifiedInv K L x := by
  have hsq := congrArg (fun h => h.hom x) (unitsResH2_comp_h2Valuation K K' L L')
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hsq
  rw [unramifiedInv_apply, hsq, h2IntAddEquiv_map_intMulRes, unramifiedInv_apply,
    AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply,
    toMul_ofMul, galRestrict_frob, ofMul_pow, map_nsmul, map_zsmul, map_nsmul,
    ← ramificationIndex_mul_residueDegree K K', mul_nsmul', natCast_zsmul]

end Tower

section Inflation

variable (K L L' : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Field L'] [ValuativeRel L'] [TopologicalSpace L']
  [IsNonarchimedeanLocalField L'] [Algebra K L] [Algebra K L'] [Algebra L L']
  [IsScalarTower K L L'] [ValuativeExtension K L] [ValuativeExtension K L']
  [ValuativeExtension L L'] [FiniteDimensional K L] [FiniteDimensional K L'] [IsUnramified K L]
  [IsUnramified K L']

/- English proof (translation)
Rewrite using `[unramifiedInv_unitsResH2, Module.finrank_self, one_smul]`.
-/
theorem unramifiedInv_inflation (x : groupCohomology (galUnitsZ K L) 2) :
    unramifiedInv K L' ((unitsResH2 K K L L').hom x) = unramifiedInv K L x := by
  rw [unramifiedInv_unitsResH2, Module.finrank_self, one_smul]

end Inflation

end GroundTheory.ProfCoh
