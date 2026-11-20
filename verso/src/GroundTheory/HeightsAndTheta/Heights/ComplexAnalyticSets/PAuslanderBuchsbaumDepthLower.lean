import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAuslanderBuchsbaumDepthLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory Limits Abelian RingTheory.Sequence

universe u

namespace AuslanderBuchsbaumDepthLower

variable {R : Type u} [CommRing R] [IsLocalRing R]

noncomputable abbrev residueModule (R : Type u) [CommRing R] [IsLocalRing R] : ModuleCat.{u} R :=
  ModuleCat.of R (Shrink.{u} (R ⧸ maximalIdeal R))

instance (R : Type u) [CommRing R] [IsLocalRing R] : Module.Finite R (residueModule R) :=
  Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).symm

/- English proof (translation)
Rewrite using `[(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus, Ideal.annihilator_quotient]`.
-/
theorem support_residueModule :
    Module.support R (residueModule R) = PrimeSpectrum.zeroLocus (maximalIdeal R) := by
  rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus, Ideal.annihilator_quotient]

/- English proof (translation)
Use `(Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator ?_).symm.lt_top` and prove the remaining obligations. Establish `H : Module.annihilator R M ≠ ⊤` using `fun h => not_subsingleton M (Module.annihilator_eq_top_iff.mp h)`. Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal _ H]`.
-/
theorem maximalIdeal_smul_top_lt_top (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] : maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
  refine (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator ?_).symm.lt_top
  have H : Module.annihilator R M ≠ ⊤ := fun h =>
    not_subsingleton M (Module.annihilator_eq_top_iff.mp h)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ H]

/- English proof (translation)
Introduce `i hi`. Break down `subsingleton_or_nontrivial P with hP | hP` into its components or cases. Establish `hZ : IsZero P` using `ModuleCat.isZero_of_subsingleton P`. Establish `: Injective P` using `hZ.injective`. Consider the cases of `i with`.

Consider the case `zero => exact Ext.addEquiv₀.subsingleton_congr.mpr ⟨fun a b => hZ.eq_of_tgt a b⟩`. Consider the case `succ j => exact Ext.subsingleton_of_injective _ _ j`. Establish `hreg : IsWeaklyRegular P rs` using `(LinearEquiv.isWeaklyRegular_congr (TensorProduct.rid R P) rs).mp (hrs.isWeaklyRegular_lTensor (M₂ := P))`. Establish `hreg' : IsRegular P rs` using `(IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr hreg`. Conclude with `ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) (residueModule R) support_residueModule.le P (maximalIdeal_smul_top_lt_top P) rs hmem hreg' i hi`.
-/
theorem subsingleton_ext_of_flat [IsNoetherianRing R] (rs : List R) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (hrs : IsWeaklyRegular R rs) (P : ModuleCat.{u} R) [Module.Finite R P] [Module.Flat R P] :
    ∀ i < rs.length, Subsingleton (Ext (residueModule R) P i) := by
  intro i hi
  rcases subsingleton_or_nontrivial P with hP | hP
  · have hZ : IsZero P := ModuleCat.isZero_of_subsingleton P
    have : Injective P := hZ.injective
    cases i with
    | zero => exact Ext.addEquiv₀.subsingleton_congr.mpr ⟨fun a b => hZ.eq_of_tgt a b⟩
    | succ j => exact Ext.subsingleton_of_injective _ _ j
  · have hreg : IsWeaklyRegular P rs :=
      (LinearEquiv.isWeaklyRegular_congr (TensorProduct.rid R P) rs).mp
        (hrs.isWeaklyRegular_lTensor (M₂ := P))
    have hreg' : IsRegular P rs :=
      (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr hreg
    exact ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) (residueModule R)
      support_residueModule.le P (maximalIdeal_smul_top_lt_top P) rs hmem hreg' i hi

/- English proof (translation)
Proceed by induction on `ℓ with`. Consider the case `zero`. Introduce `M _ hM i hi`. Establish `: Projective M` using `(projective_iff_hasProjectiveDimensionLE_zero M).mpr hM`. Conclude with `subsingleton_ext_of_flat rs hmem hrs M i (by omega)`.

Consider the case `succ ℓ ih`. Introduce `M _ hM i hi`. Take `⟨n, f, hf⟩` from `Module.Finite.exists_fin' R M`. Establish `hS : f.shortComplexKer.ShortExact` using `LinearMap.shortExact_shortComplexKer hf`. Establish `h₂ : HasProjectiveDimensionLT f.shortComplexKer.X₂ (ℓ + 1)` using `hasProjectiveDimensionLT_of_ge _ 1 (ℓ + 1) (by omega)`.

Establish `hK : HasProjectiveDimensionLE f.shortComplexKer.X₁ ℓ` using `hS.hasProjectiveDimensionLT_X₁ (ℓ + 1) h₂ hM`. Establish `e₂ : Subsingleton (Ext (residueModule R) f.shortComplexKer.X₂ i)` using `subsingleton_ext_of_flat rs hmem hrs _ i (by omega)`. Establish `e₁ : Subsingleton (Ext (residueModule R) f.shortComplexKer.X₁ (i + 1))` using `ih _ hK (i + 1) (by omega)`. Conclude with `AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros ((Ext.covariant_sequence_exact₃' (residueModule R) hS) i (i + 1) rfl) ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr e₂).eq_zero_of_src _) ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr e₁).eq_zero_of …`.
-/
theorem subsingleton_ext_of_hasProjectiveDimensionLE [IsNoetherianRing R] (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R) (hrs : IsWeaklyRegular R rs) (ℓ : ℕ) :
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M], HasProjectiveDimensionLE M ℓ →
      ∀ i, i + ℓ < rs.length → Subsingleton (Ext (residueModule R) M i) := by
  induction ℓ with
  | zero =>
    intro M _ hM i hi
    have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr hM
    exact subsingleton_ext_of_flat rs hmem hrs M i (by omega)
  | succ ℓ ih =>
    intro M _ hM i hi
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
    have hS : f.shortComplexKer.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have h₂ : HasProjectiveDimensionLT f.shortComplexKer.X₂ (ℓ + 1) :=
      hasProjectiveDimensionLT_of_ge _ 1 (ℓ + 1) (by omega)
    have hK : HasProjectiveDimensionLE f.shortComplexKer.X₁ ℓ :=
      hS.hasProjectiveDimensionLT_X₁ (ℓ + 1) h₂ hM
    have e₂ : Subsingleton (Ext (residueModule R) f.shortComplexKer.X₂ i) :=
      subsingleton_ext_of_flat rs hmem hrs _ i (by omega)
    have e₁ : Subsingleton (Ext (residueModule R) f.shortComplexKer.X₁ (i + 1)) :=
      ih _ hK (i + 1) (by omega)
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      ((Ext.covariant_sequence_exact₃' (residueModule R) hS) i (i + 1) rfl)
      ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr e₂).eq_zero_of_src _)
      ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr e₁).eq_zero_of_tgt _)

end AuslanderBuchsbaumDepthLower

/- English proof (translation)
Introduce `R _ _ _ M _ _ _ _ ℓ rs hpd hmem hrs`. Take `⟨ms, hlen, hms, hreg⟩` from `ModuleCat.exists_isRegular_of_exists_subsingleton_ext (maximalIdeal R) (rs.length - ℓ) (ModuleCat.of R M) (AuslanderBuchsbaumDepthLower.maximalIdeal_smul_top_lt_top M) (AuslanderBuchsbaumDepthLower.residueModule R) AuslanderBuchsbaumDepthLower.support_residueModule (fun i hi => A …`. Conclude with `⟨ms, hms, hreg.toIsWeaklyRegular, hlen⟩`.
-/
theorem AuslanderBuchsbaumDepthLower.proof : AuslanderBuchsbaumDepthLower.Statement.{u} := by
  intro R _ _ _ M _ _ _ _ ℓ rs hpd hmem hrs
  obtain ⟨ms, hlen, hms, hreg⟩ := ModuleCat.exists_isRegular_of_exists_subsingleton_ext
    (maximalIdeal R) (rs.length - ℓ) (ModuleCat.of R M)
    (AuslanderBuchsbaumDepthLower.maximalIdeal_smul_top_lt_top M)
    (AuslanderBuchsbaumDepthLower.residueModule R)
    AuslanderBuchsbaumDepthLower.support_residueModule
    (fun i hi => AuslanderBuchsbaumDepthLower.subsingleton_ext_of_hasProjectiveDimensionLE rs hmem hrs ℓ
      (ModuleCat.of R M) hpd i (by omega))
  exact ⟨ms, hms, hreg.toIsWeaklyRegular, hlen⟩

end GroundTheory.Heights₂.Heights
