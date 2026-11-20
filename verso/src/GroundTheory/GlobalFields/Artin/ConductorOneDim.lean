import Mathlib
import GroundTheory.GlobalFields.Artin.ConductorInflation
import GroundTheory.GlobalFields.Artin.OneDim
import GroundTheory.LocalFields.ArtinConductorMax
import GroundTheory.LocalFields.SeparableClosure

noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

open IdeleGroup

section LocalConductor

variable {k M : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra k M] [ValuativeExtension k M] [FiniteDimensional k M] [IsGalois k M]

/- English proof (translation)
Set `ι : M →ₐ[k] SeparableClosure k` to `IsSepClosed.lift`. Set `M' : IntermediateField k (SeparableClosure k)` to `ι.fieldRange`. Set `e : M ≃ₐ[k] M'` to `AlgEquiv.ofInjectiveField ι`. Establish `: FiniteDimensional k M'` using `LinearEquiv.finiteDimensional e.toLinearEquiv`. Establish `: IsGalois k M'` using `IsGalois.of_algEquiv e`.

Establish `hcomm : IsMulCommutative (M' ≃ₐ[k] M')` using `⟨⟨fun a b ↦ e.autCongr.symm.injective (hψ (by rw [map_mul, map_mul, map_mul, map_mul, mul_comm]))⟩⟩`. Establish `: IsAbelianGalois k M'` using `{}`. Set `ψ' : (M' ≃ₐ[k] M') →* ℂˣ` to `ψ.comp e.autCongr.symm.toMonoidHom`. Establish `hψ' : Function.Injective ψ'` using `hψ.comp e.autCongr.symm.injective`. Establish `h1` using `artinConductor_charRep_eq_conductor M' ψ' hψ'`.

Establish `h2 : artinConductor (charRep ψ) = artinConductor (charRep ψ')`. Apply `Rat.cast_injective (α := ℂ)` to reduce the goal to its premises. Rewrite using `[artinConductor_eq_charArtinConductor, artinConductor_eq_charArtinConductor, ← charArtinConductor_autCongr e]`. Use `congr 1`. Use function extensionality and compare the values at `σ`.

Rewrite using `[character_charRep, character_charRep]`. Use `show ((ψ σ : ℂˣ) : ℂ) = ψ (e.autCongr.symm (e.autCongr σ))`. Rewrite using `[MulEquiv.symm_apply_apply]`. Establish `h3 : (normUnits k M').range = (normUnits k M).range`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Use `⟨Units.map e.symm.toMonoidHom y, Units.ext ?_⟩` and prove the remaining obligations. Simplify using `only [coe_normUnits, Units.coe_map]`. Rewrite using `[← Algebra.norm_eq_of_algEquiv e]`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨y, rfl⟩`. Use `⟨Units.map e.toMonoidHom y, Units.ext ?_⟩` and prove the remaining obligations. Simplify using `only [coe_normUnits, Units.coe_map]`. Conclude with `Algebra.norm_eq_of_algEquiv e _`.

Rewrite using `[h2, h1, GroundTheory.LocalField.conductor, h3]`.
-/
theorem artinConductor_charRep_eq_sInf (ψ : (M ≃ₐ[k] M) →* ℂˣ) (hψ : Function.Injective ψ) :
    artinConductor (charRep ψ) =
      (sInf {n : ℕ | unitFiltrationUnits k n ≤ (normUnits k M).range} : ℕ) := by
  let ι : M →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let M' : IntermediateField k (SeparableClosure k) := ι.fieldRange
  let e : M ≃ₐ[k] M' := AlgEquiv.ofInjectiveField ι
  have : FiniteDimensional k M' := LinearEquiv.finiteDimensional e.toLinearEquiv
  have : IsGalois k M' := IsGalois.of_algEquiv e
  have hcomm : IsMulCommutative (M' ≃ₐ[k] M') :=
    ⟨⟨fun a b ↦ e.autCongr.symm.injective (hψ (by rw [map_mul, map_mul, map_mul, map_mul,
      mul_comm]))⟩⟩
  have : IsAbelianGalois k M' := {}
  let ψ' : (M' ≃ₐ[k] M') →* ℂˣ := ψ.comp e.autCongr.symm.toMonoidHom
  have hψ' : Function.Injective ψ' := hψ.comp e.autCongr.symm.injective
  have h1 := artinConductor_charRep_eq_conductor M' ψ' hψ'
  have h2 : artinConductor (charRep ψ) = artinConductor (charRep ψ') := by
    apply Rat.cast_injective (α := ℂ)
    rw [artinConductor_eq_charArtinConductor, artinConductor_eq_charArtinConductor,
      ← charArtinConductor_autCongr e]
    congr 1
    funext σ
    rw [character_charRep, character_charRep]
    show ((ψ σ : ℂˣ) : ℂ) = ψ (e.autCongr.symm (e.autCongr σ))
    rw [MulEquiv.symm_apply_apply]
  have h3 : (normUnits k M').range = (normUnits k M).range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨Units.map e.symm.toMonoidHom y, Units.ext ?_⟩
      simp only [coe_normUnits, Units.coe_map]
      rw [← Algebra.norm_eq_of_algEquiv e]
      simp
    · rintro ⟨y, rfl⟩
      refine ⟨Units.map e.toMonoidHom y, Units.ext ?_⟩
      simp only [coe_normUnits, Units.coe_map]
      exact Algebra.norm_eq_of_algEquiv e _
  rw [h2, h1, GroundTheory.LocalField.conductor, h3]

end LocalConductor

section Units

open ValuativeRel

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `unitFiltrationUnits_zero_eq_unitsLevel_zero v`. Use extensionality with `x`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]`. Rewrite using `[mem_unitFiltrationUnits_iff hn hϖ, mem_unitsLevel_of_one_le hn, ← map_pow, (isEquiv_valuation_valued v).le_iff_le, map_pow, valued_irreducible_valuationInteger v hϖ, ← WithZero.exp_nsmul]`.

Simplify using the standard rewrite rules.
-/
theorem unitFiltrationUnits_eq_unitsLevel (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    unitFiltrationUnits (v.adicCompletion K) n = unitsLevel v n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact unitFiltrationUnits_zero_eq_unitsLevel_zero v
  ext x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]
  rw [mem_unitFiltrationUnits_iff hn hϖ, mem_unitsLevel_of_one_le hn, ← map_pow,
    (isEquiv_valuation_valued v).le_iff_le, map_pow, valued_irreducible_valuationInteger v hϖ,
    ← WithZero.exp_nsmul]
  simp

end Units

section OneDim

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)

/- English proof (translation)
Use extensionality with `g`. Simplify using `[charRep_apply, charBar_restrictNormalHom]`.
-/
theorem charRep_eq_comp_restrictNormalHom :
    charRep χ = (charRep (charBar χ)).comp (AlgEquiv.restrictNormalHom (charField χ)) := by
  ext g
  simp [charRep_apply, charBar_restrictNormalHom]

/- English proof (translation)
Rewrite using `[charRep_eq_comp_restrictNormalHom, artinExponent_comp_restrictNormalHom]`. Set `u` to `placeAbove (L := charField χ) v`. Establish `hinj : Function.Injective ((charBar χ).comp (localToGlobal v u))` using `(charBar_injective χ).comp (Subtype.val_injective.comp (decompositionMulEquiv v u).symm.injective)`. Establish `h` using `artinExponent_eq v (charRep (charBar χ)) u`. Rewrite `h` using `[localArtinConductor]`.

Express the relevant statement in the definitionally equal form `_ = artinConductor (charRep ((charBar χ).comp (localToGlobal v u))) at h`. Rewrite `h` using `[artinConductor_charRep_eq_sInf _ hinj]`. Establish `h'` using `Nat.cast_injective (R := ℚ) h`. Rewrite using `[h', localConductorExponent, ker_localSymbol (charField χ) v ⟨u, inferInstance⟩]`. Repeatedly rewrite using `[unitFiltrationUnits_eq_unitsLevel]`.
-/
theorem artinExponent_charRep (v : HeightOneSpectrum (𝓞 K)) :
    artinExponent v (charRep χ) = localConductorExponent (charField χ) v := by
  rw [charRep_eq_comp_restrictNormalHom, artinExponent_comp_restrictNormalHom]
  let u := placeAbove (L := charField χ) v
  have hinj : Function.Injective ((charBar χ).comp (localToGlobal v u)) :=
    (charBar_injective χ).comp (Subtype.val_injective.comp (decompositionMulEquiv v u).symm.injective)
  have h := artinExponent_eq v (charRep (charBar χ)) u
  rw [localArtinConductor] at h
  change _ = artinConductor (charRep ((charBar χ).comp (localToGlobal v u))) at h
  rw [artinConductor_charRep_eq_sInf _ hinj] at h
  have h' := Nat.cast_injective (R := ℚ) h
  rw [h', localConductorExponent, ker_localSymbol (charField χ) v ⟨u, inferInstance⟩]
  simp_rw [unitFiltrationUnits_eq_unitsLevel]

/- English proof (translation)
Establish `h : ((heckeCharacterOfChar χ).toIdele.comp ofFinite).comp (finiteUnitsSingle v) = ((heckeCharacterOfChar χ).localComponent v : (v.adicCompletion K)ˣ →* Circle)`. Use extensionality with `a`. Simplify using `only [MonoidHom.comp_apply, ofFinite_finiteUnitsSingle]`. Both sides reduce to the same expression. Rewrite using `[conductorExponentAt, conductorExponent, h, ker_localComponent_heckeCharacterOfChar]`.

Both sides reduce to the same expression.
-/
theorem conductorExponentAt_heckeCharacterOfChar (v : HeightOneSpectrum (𝓞 K)) :
    conductorExponentAt ((heckeCharacterOfChar χ).toIdele.comp ofFinite) v =
      localConductorExponent (charField χ) v := by
  have h : ((heckeCharacterOfChar χ).toIdele.comp ofFinite).comp (finiteUnitsSingle v) =
      ((heckeCharacterOfChar χ).localComponent v : (v.adicCompletion K)ˣ →* Circle) := by
    ext a
    simp only [MonoidHom.comp_apply, ofFinite_finiteUnitsSingle]
    rfl
  rw [conductorExponentAt, conductorExponent, h, ker_localComponent_heckeCharacterOfChar]
  rfl

/- English proof (translation)
The claim follows from `finprod_congr fun v ↦ by rw [artinExponent_charRep, ← conductorExponentAt_heckeCharacterOfChar]`.
-/
theorem artinConductorIdeal_charRep_eq_conductor :
    artinConductorIdeal (charRep χ) = (heckeCharacterOfChar χ).conductor :=
  finprod_congr fun v ↦ by
    rw [artinExponent_charRep, ← conductorExponentAt_heckeCharacterOfChar]

end OneDim

end GroundTheory.Global
