import Mathlib
import GroundTheory.GlobalFields.Artin.Conductor
import GroundTheory.GlobalFields.Artin.InflationTower
import GroundTheory.LocalFields.LowerIndexQuotient
import GroundTheory.LocalFields.IntermediateField

noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

section LocalInflation

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

/- English proof (translation)
Use `set r : (L ≃ₐ[K] L) →* (E ≃ₐ[K] E) := AlgEquiv.restrictNormalHom E with hr_def`. Rewrite using `[charArtinConductor_eq_sum_lowerIndex, charArtinConductor_eq_sum_lowerIndex, card_lowerRamificationGroup_zero, card_lowerRamificationGroup_zero, ramificationIndex_tower K E L, map_one, ← Finset.sum_fiberwise Finset.univ (fun σ ↦ r σ)]`. Establish `key : ∀ s : E ≃ₐ[K] E, ∑ σ ∈ Finset.univ.filter (fun σ ↦ r σ = s), ((lowerIndex K L σ).toNat : ℂ) * (χ 1 - χ (r σ)) = (ramificationIndex E L : ℂ) * (((lowerIndex K E s).toNat : ℂ) * (χ 1 - χ s))`. Introduce `s`. Rewrite using `[Finset.sum_congr rfl (fun σ hσ ↦ by rw [(Finset.mem_filter.1 hσ).2]), ← Finset.sum_mul]`.

Break down `eq_or_ne s 1 with rfl | hs` into its components or cases. Simplify using the standard rewrite rules. Establish `hfin : ∀ σ ∈ Finset.univ.filter (fun σ ↦ r σ = s), lowerIndex K L σ ≠ ⊤`. Introduce `σ hσ`. Use `lowerIndex_ne_top fun h1 ↦ hs ?_` and prove the remaining obligations.

Rewrite using `[← (Finset.mem_filter.1 hσ).2, h1, map_one]`. Establish `h` using `ramificationIndex_mul_lowerIndex_eq_sum_fiber E s`. Establish `h2 : ramificationIndex E L * (lowerIndex K E s).toNat = ∑ σ ∈ Finset.univ.filter (fun σ ↦ r σ = s), (lowerIndex K L σ).toNat`. Establish `h3` using `congrArg ENat.toNat h`. Rewrite `h3` using `[ENat.toNat_mul, ENat.toNat_natCast]`.

Rewrite using `[h3, ENat.toNat_sum fun σ hσ ↦ hfin σ hσ]`. Rewrite using `[← Nat.cast_sum, ← h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl (fun s _ ↦ key s), ← Finset.mul_sum]`.

Establish `hpos : (ramificationIndex E L : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (ramificationIndex_pos E L).ne'`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem charArtinConductor_comp_restrictNormalHom (E : IntermediateField K L) [Normal K E]
    [IsGalois K E] (χ : (E ≃ₐ[K] E) → ℂ) :
    charArtinConductor K L (fun σ ↦ χ (AlgEquiv.restrictNormalHom E σ)) =
      charArtinConductor K E χ := by
  classical
  set r : (L ≃ₐ[K] L) →* (E ≃ₐ[K] E) := AlgEquiv.restrictNormalHom E with hr_def
  rw [charArtinConductor_eq_sum_lowerIndex, charArtinConductor_eq_sum_lowerIndex,
    card_lowerRamificationGroup_zero, card_lowerRamificationGroup_zero,
    ramificationIndex_tower K E L, map_one,
    ← Finset.sum_fiberwise Finset.univ (fun σ ↦ r σ)]
  have key : ∀ s : E ≃ₐ[K] E,
      ∑ σ ∈ Finset.univ.filter (fun σ ↦ r σ = s),
          ((lowerIndex K L σ).toNat : ℂ) * (χ 1 - χ (r σ)) =
        (ramificationIndex E L : ℂ) * (((lowerIndex K E s).toNat : ℂ) * (χ 1 - χ s)) := by
    intro s
    rw [Finset.sum_congr rfl (fun σ hσ ↦ by rw [(Finset.mem_filter.1 hσ).2]), ← Finset.sum_mul]
    rcases eq_or_ne s 1 with rfl | hs
    · simp
    have hfin : ∀ σ ∈ Finset.univ.filter (fun σ ↦ r σ = s), lowerIndex K L σ ≠ ⊤ := by
      intro σ hσ
      refine lowerIndex_ne_top fun h1 ↦ hs ?_
      rw [← (Finset.mem_filter.1 hσ).2, h1, map_one]
    have h := ramificationIndex_mul_lowerIndex_eq_sum_fiber E s
    have h2 : ramificationIndex E L * (lowerIndex K E s).toNat =
        ∑ σ ∈ Finset.univ.filter (fun σ ↦ r σ = s), (lowerIndex K L σ).toNat := by
      have h3 := congrArg ENat.toNat h
      rw [ENat.toNat_mul, ENat.toNat_natCast] at h3
      rw [h3, ENat.toNat_sum fun σ hσ ↦ hfin σ hσ]
    rw [← Nat.cast_sum, ← h2]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun s _ ↦ key s), ← Finset.mul_sum]
  have hpos : (ramificationIndex E L : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (ramificationIndex_pos E L).ne'
  push_cast
  field_simp

variable {M : Type*} [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M] [FiniteDimensional K M] [IsGalois K M] [Algebra M L]
  [IsScalarTower K M L]

/- English proof (translation)
Use `set E := (IsScalarTower.toAlgHom K M L).fieldRange`. Set `e : M ≃ₐ[K] E` to `AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K M L)`. Establish `: Normal K E` using `Normal.of_algEquiv e`. Establish `: IsGalois K E` using `IsGalois.of_algEquiv e`. Establish `h1 : ∀ y : E, algebraMap M L (e.symm y) = (y : L)` using `fun y ↦ by conv_rhs => rw [← e.apply_symm_apply y]`.

Both sides reduce to the same expression. Establish `hr : ∀ σ : L ≃ₐ[K] L, e.symm.autCongr (AlgEquiv.restrictNormalHom E σ) = AlgEquiv.restrictNormalHom M σ`. Introduce `σ`. Use extensionality with `m`. Apply `(algebraMap M L).injective` to reduce the goal to its premises.

Rewrite using `[AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.symm_symm, h1]`. Express the relevant statement in the definitionally equal form `((σ.restrictNormal E (e m) : E) : L) = algebraMap M L (σ.restrictNormal M m)`. Rewrite using `[AlgEquiv.restrictNormal_commutes]`. Conclude with `AlgEquiv.restrictNormal_commutes σ E (e m)`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [hr]`. Use `_ = charArtinConductor K E (fun τ ↦ χ (e.symm.autCongr τ)) := charArtinConductor_comp_restrictNormalHom E (fun τ ↦ χ (e.symm.autCongr τ))`. Use `_ = charArtinConductor K M χ := charArtinConductor_autCongr e.symm χ`.
-/
theorem charArtinConductor_comp_restrictNormalHom' (χ : (M ≃ₐ[K] M) → ℂ) :
    charArtinConductor K L (fun σ ↦ χ (AlgEquiv.restrictNormalHom M σ)) =
      charArtinConductor K M χ := by
  set E := (IsScalarTower.toAlgHom K M L).fieldRange
  let e : M ≃ₐ[K] E := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K M L)
  have : Normal K E := Normal.of_algEquiv e
  have : IsGalois K E := IsGalois.of_algEquiv e
  have h1 : ∀ y : E, algebraMap M L (e.symm y) = (y : L) := fun y ↦ by
    conv_rhs => rw [← e.apply_symm_apply y]
    rfl
  have hr : ∀ σ : L ≃ₐ[K] L,
      e.symm.autCongr (AlgEquiv.restrictNormalHom E σ) = AlgEquiv.restrictNormalHom M σ := by
    intro σ
    ext m
    apply (algebraMap M L).injective
    rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.symm_symm,
      h1]
    change ((σ.restrictNormal E (e m) : E) : L) = algebraMap M L (σ.restrictNormal M m)
    rw [AlgEquiv.restrictNormal_commutes]
    exact AlgEquiv.restrictNormal_commutes σ E (e m)
  calc charArtinConductor K L (fun σ ↦ χ (AlgEquiv.restrictNormalHom M σ))
      = charArtinConductor K L
          (fun σ ↦ χ (e.symm.autCongr (AlgEquiv.restrictNormalHom E σ))) := by
        simp only [hr]
    _ = charArtinConductor K E (fun τ ↦ χ (e.symm.autCongr τ)) :=
        charArtinConductor_comp_restrictNormalHom E (fun τ ↦ χ (e.symm.autCongr τ))
    _ = charArtinConductor K M χ := charArtinConductor_autCongr e.symm χ

end LocalInflation

section GlobalInflation

variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]

section Tower

variable (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 L))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal] [w.asIdeal.LiesOver v.asIdeal]

/- English proof (translation)
Establish `h` using `(HeightOneSpectrum.denseRange_algebraMap K v).equalizer ((SemiLocal.continuous_completionMap u w).comp (SemiLocal.continuous_completionMap v u)) (SemiLocal.continuous_completionMap v w) (funext fun x ↦ ?_)`. Conclude with `congrFun h a`. Simplify using `only [Function.comp_apply, SemiLocal.completionMap_algebraMap]`. Rewrite using `[IsScalarTower.algebraMap_apply K F (u.adicCompletion F), SemiLocal.completionMap_algebraMap, IsScalarTower.algebraMap_apply F L (w.adicCompletion L), IsScalarTower.algebraMap_apply K L (w.adicCompletion L), ← IsScalarTower.algebraMap_apply K F L]`.
-/
theorem completionMap_completionMap (a : v.adicCompletion K) :
    SemiLocal.completionMap u w (SemiLocal.completionMap v u a) =
      SemiLocal.completionMap v w a := by
  have h := (HeightOneSpectrum.denseRange_algebraMap K v).equalizer
    ((SemiLocal.continuous_completionMap u w).comp (SemiLocal.continuous_completionMap v u))
    (SemiLocal.continuous_completionMap v w) (funext fun x ↦ ?_)
  · exact congrFun h a
  · simp only [Function.comp_apply, SemiLocal.completionMap_algebraMap]
    rw [IsScalarTower.algebraMap_apply K F (u.adicCompletion F),
      SemiLocal.completionMap_algebraMap, IsScalarTower.algebraMap_apply F L (w.adicCompletion L),
      IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
      ← IsScalarTower.algebraMap_apply K F L]

/- English proof (translation)
The claim follows from `IsScalarTower.of_algebraMap_eq fun a ↦ (completionMap_completionMap v u w a).symm`.
-/
theorem isScalarTower_adicCompletion :
    IsScalarTower (v.adicCompletion K) (u.adicCompletion F) (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun a ↦ (completionMap_completionMap v u w a).symm

attribute [local instance] isScalarTower_adicCompletion

variable [IsGalois K F] [IsGalois K L]

/- English proof (translation)
Use `AlgEquiv.ext fun y ↦ ?_` and prove the remaining obligations. Apply `(algebraMap (u.adicCompletion F) (w.adicCompletion L)).injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap (u.adicCompletion F) (w.adicCompletion L) (AlgEquiv.restrictNormal (decompositionMulEquiv v w τ) (u.adicCompletion F) y) = _`. Rewrite using `[AlgEquiv.restrictNormal_commutes]`. Establish `h` using `(HeightOneSpectrum.denseRange_algebraMap F u).equalizer ((continuous_decompositionAlgEquiv v w τ).comp (SemiLocal.continuous_completionMap u w)) ((SemiLocal.continuous_completionMap u w).comp (continuous_decompositionAlgEquiv v u ⟨AlgEquiv.restrictNormalHom F (τ : Gal(L/K)), hτ⟩) …`.

Conclude with `congrFun h y`. Simplify using `only [Function.comp_apply]`. Establish `h1 : ∀ z : F, SemiLocal.completionMap u w (algebraMap F (u.adicCompletion F) z) = algebraMap L (w.adicCompletion L) (algebraMap F L z)` using `fun z ↦ by`. Rewrite using `[SemiLocal.completionMap_algebraMap, IsScalarTower.algebraMap_apply F L (w.adicCompletion L)]`. Rewrite using `[h1, decompositionAlgEquiv_algebraMap, decompositionAlgEquiv_algebraMap, h1]`.

Use `congr 1`. Conclude with `(AlgEquiv.restrictNormal_commutes (τ : Gal(L/K)) F x).symm`.
-/
theorem restrictNormalHom_decompositionMulEquiv (τ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (hτ : AlgEquiv.restrictNormalHom F (τ : Gal(L/K)) ∈ MulAction.stabilizer Gal(F/K) u.asIdeal) :
    AlgEquiv.restrictNormalHom (u.adicCompletion F) (decompositionMulEquiv v w τ) =
      decompositionMulEquiv v u ⟨AlgEquiv.restrictNormalHom F (τ : Gal(L/K)), hτ⟩ := by
  refine AlgEquiv.ext fun y ↦ ?_
  apply (algebraMap (u.adicCompletion F) (w.adicCompletion L)).injective
  change algebraMap (u.adicCompletion F) (w.adicCompletion L)
    (AlgEquiv.restrictNormal (decompositionMulEquiv v w τ) (u.adicCompletion F) y) = _
  rw [AlgEquiv.restrictNormal_commutes]
  have h := (HeightOneSpectrum.denseRange_algebraMap F u).equalizer
    ((continuous_decompositionAlgEquiv v w τ).comp (SemiLocal.continuous_completionMap u w))
    ((SemiLocal.continuous_completionMap u w).comp (continuous_decompositionAlgEquiv v u
      ⟨AlgEquiv.restrictNormalHom F (τ : Gal(L/K)), hτ⟩)) (funext fun x ↦ ?_)
  · exact congrFun h y
  · simp only [Function.comp_apply]
    have h1 : ∀ z : F, SemiLocal.completionMap u w (algebraMap F (u.adicCompletion F) z) =
        algebraMap L (w.adicCompletion L) (algebraMap F L z) := fun z ↦ by
      rw [SemiLocal.completionMap_algebraMap, IsScalarTower.algebraMap_apply F L (w.adicCompletion L)]
    rw [h1, decompositionAlgEquiv_algebraMap, decompositionAlgEquiv_algebraMap, h1]
    congr 1
    exact (AlgEquiv.restrictNormal_commutes (τ : Gal(L/K)) F x).symm

/- English proof (translation)
Take `⟨τ, rfl⟩` from `(decompositionMulEquiv v w).surjective T`. Establish `hτ : AlgEquiv.restrictNormalHom F (τ : Gal(L/K)) ∈ MulAction.stabilizer Gal(F/K) u.asIdeal`. Rewrite using `[(inferInstance : w.asIdeal.LiesOver u.asIdeal).over]`. Conclude with `restrictNormalHom_mem_stabilizer τ.2`. Rewrite using `[restrictNormalHom_decompositionMulEquiv v u w τ hτ, localToGlobal_decompositionMulEquiv, localToGlobal_decompositionMulEquiv]`.
-/
theorem restrictNormalHom_localToGlobal (T : Gal(w.adicCompletion L/v.adicCompletion K)) :
    AlgEquiv.restrictNormalHom F (localToGlobal v w T) =
      localToGlobal v u (AlgEquiv.restrictNormalHom (u.adicCompletion F) T) := by
  obtain ⟨τ, rfl⟩ := (decompositionMulEquiv v w).surjective T
  have hτ : AlgEquiv.restrictNormalHom F (τ : Gal(L/K)) ∈
      MulAction.stabilizer Gal(F/K) u.asIdeal := by
    rw [(inferInstance : w.asIdeal.LiesOver u.asIdeal).over]
    exact restrictNormalHom_mem_stabilizer τ.2
  rw [restrictNormalHom_decompositionMulEquiv v u w τ hτ, localToGlobal_decompositionMulEquiv,
    localToGlobal_decompositionMulEquiv]

end Tower

variable [IsGalois K F] [IsGalois K L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- English proof (translation)
Set `w` to `placeAbove (L := L) v`. Set `u : HeightOneSpectrum (𝓞 F)` to `HeightOneSpectrum.under (𝓞 F) w`. Establish `: w.asIdeal.LiesOver u.asIdeal` using `⟨rfl⟩`. Establish `: u.asIdeal.LiesOver v.asIdeal` using `Ideal.LiesOver.tower_bot w.asIdeal u.asIdeal v.asIdeal`. Use `isScalarTower_adicCompletion v u w` as an intermediate fact.

Apply `Nat.cast_injective (R := ℂ)` to reduce the goal to its premises. Rewrite using `[natCast_artinExponent v _ w, natCast_artinExponent v ρ u, ← charArtinConductor_comp_restrictNormalHom' (L := w.adicCompletion L) (M := u.adicCompletion F)]`. Use `congr 1`. Use function extensionality and compare the values at `T`. Use `show ρ.character (AlgEquiv.restrictNormalHom F (localToGlobal v w T)) = _`.

Rewrite using `[restrictNormalHom_localToGlobal v u w]`.
-/
theorem artinExponent_comp_restrictNormalHom (v : HeightOneSpectrum (𝓞 K))
    (ρ : Representation ℂ Gal(F/K) V) :
    artinExponent v (ρ.comp (AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K))) =
      artinExponent v ρ := by
  let w := placeAbove (L := L) v
  let u : HeightOneSpectrum (𝓞 F) := HeightOneSpectrum.under (𝓞 F) w
  have : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  have : u.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.tower_bot w.asIdeal u.asIdeal v.asIdeal
  have := isScalarTower_adicCompletion v u w
  apply Nat.cast_injective (R := ℂ)
  rw [natCast_artinExponent v _ w, natCast_artinExponent v ρ u,
    ← charArtinConductor_comp_restrictNormalHom' (L := w.adicCompletion L)
      (M := u.adicCompletion F)]
  congr 1
  funext T
  show ρ.character (AlgEquiv.restrictNormalHom F (localToGlobal v w T)) = _
  rw [restrictNormalHom_localToGlobal v u w]

end GlobalInflation

end GroundTheory.Global
