import Formalism.LogFactorialIndices.SubspaceIndexSigned
import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxBase
import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxDet
import Formalism.LogFactorialIndices.SignedSubspaceIndex.SubspaceLatticeIndex

noncomputable section

open Module
open scoped Pointwise

namespace Formalism.LatticeIndexTer.LatticeIndexValuation

/- English proof (translation)
Establish `e : (Q.comap P.subtype).map (Submodule.equivMapOfInjective ι hι P).toLinearMap = (Q.map ι).comap (P.map ι).subtype`. Use extensionality with `⟨z, hz⟩`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hz`. Simplify using `only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, LinearEquiv.coe_coe]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨w, hw⟩, hwQ, hwe⟩`. Use `⟨w, hwQ, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hwe` as an intermediate fact. Use `first`. Consider the case `exact this`.

Consider the case `simpa using this`. Introduce and unpack `⟨w, hwQ, hwe⟩`. Use `⟨⟨y, hy⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `: w = y` using `hι hwe`. Simplify `hwQ` using `[this]`.

Use `ext`. Both sides reduce to the same expression. Conclude with `(Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective ι hι P) e).length_eq`.
-/
theorem length_map_inj {O Y X : Type} [CommRing O] [AddCommGroup Y] [Module O Y]
    [AddCommGroup X] [Module O X] (ι : Y →ₗ[O] X) (hι : Function.Injective ι)
    (P Q : Submodule O Y) :
    Module.length O (P ⧸ Q.comap P.subtype) =
      Module.length O (P.map ι ⧸ (Q.map ι).comap (P.map ι).subtype) := by
  have e : (Q.comap P.subtype).map (Submodule.equivMapOfInjective ι hι P).toLinearMap =
      (Q.map ι).comap (P.map ι).subtype := by
    ext ⟨z, hz⟩
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨⟨w, hw⟩, hwQ, hwe⟩
      refine ⟨w, hwQ, ?_⟩
      have := congrArg Subtype.val hwe
      first
        | exact this
        | simpa using this
    · rintro ⟨w, hwQ, hwe⟩
      refine ⟨⟨y, hy⟩, ?_, ?_⟩
      · have : w = y := hι hwe
        simpa [this] using hwQ
      · ext
        rfl
  exact (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective ι hι P) e).length_eq

end Formalism.LatticeIndexTer.LatticeIndexValuation

namespace Formalism.LatticeIndexTer.LatticeIndexValuation

section Sub

variable {O K X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X]
  [IsScalarTower O K X]

/- English proof (translation)
Set `ι : W →ₗ[O] X` to `(W.subtype).restrictScalars O`. Establish `hι : Function.Injective ι` using `Subtype.val_injective`. Prove the components needed by the constructor for the conclusion. Establish `: Module.Finite O A` using `Module.Finite.iff_fg.mpr hA.1`. Establish `hle : (A.comap ι).map ι ≤ A` using `Submodule.map_comap_le ι A`.

Establish `: IsNoetherian O ((A.comap ι).map ι)` using `isNoetherian_of_le hle`. Establish `hfg : ((A.comap ι).map ι).FG` using `Module.Finite.iff_fg.mp inferInstance`. Conclude with `Submodule.fg_of_fg_map_injective ι hι hfg`. Rewrite using `[eq_top_iff]`. Introduce and unpack `w -`.

Take `⟨d, hd, hdw⟩` from `LatticeIndexLength.exists_smul_mem_of_span (K := K) A hA.2 (w : X)`. Establish `hdK : algebraMap O K d ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hd`. Establish `hmem : d • w ∈ Submodule.span K (A.comap ι : Set W)`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `show ((d • w : W) : X) ∈ A`.

Rewrite using `[Submodule.coe_smul_of_tower]`. Conclude with `hdw`. Establish `hw : w = (algebraMap O K d)⁻¹ • (d • w)`. Rewrite using `[← algebraMap_smul K d w, smul_smul, inv_mul_cancel₀ hdK, one_smul]`. Rewrite using `[hw]`.

Conclude with `Submodule.smul_mem _ _ hmem`.
-/
theorem isLat_comap (A : Submodule O X) (hA : IsLat O K X A) (W : Submodule K X) :
    IsLat O K W (A.comap ((W.subtype).restrictScalars O)) := by
  let ι : W →ₗ[O] X := (W.subtype).restrictScalars O
  have hι : Function.Injective ι := Subtype.val_injective
  constructor
  · have : Module.Finite O A := Module.Finite.iff_fg.mpr hA.1
    have hle : (A.comap ι).map ι ≤ A := Submodule.map_comap_le ι A
    have : IsNoetherian O ((A.comap ι).map ι) := isNoetherian_of_le hle
    have hfg : ((A.comap ι).map ι).FG := Module.Finite.iff_fg.mp inferInstance
    exact Submodule.fg_of_fg_map_injective ι hι hfg
  · rw [eq_top_iff]
    rintro w -
    obtain ⟨d, hd, hdw⟩ := LatticeIndexLength.exists_smul_mem_of_span (K := K) A hA.2 (w : X)
    have hdK : algebraMap O K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hd
    have hmem : d • w ∈ Submodule.span K (A.comap ι : Set W) := by
      apply Submodule.subset_span
      show ((d • w : W) : X) ∈ A
      rw [Submodule.coe_smul_of_tower]
      exact hdw
    have hw : w = (algebraMap O K d)⁻¹ • (d • w) := by
      rw [← algebraMap_smul K d w, smul_smul, inv_mul_cancel₀ hdK, one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ hmem

end Sub

end Formalism.LatticeIndexTer.LatticeIndexValuation

namespace Formalism.LatticeIndexTer

open LatticeIndexValuation

end Formalism.LatticeIndexTer
