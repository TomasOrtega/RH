import Mathlib
import GroundTheory.GlobalFields.Artin.ConductorInflation
import GroundTheory.GlobalFields.Artin.GammaInduction
import GroundTheory.GlobalFields.Artin.Places
import GroundTheory.GlobalFields.Artin.RelativeDiscriminantLocal
import GroundTheory.GlobalFields.Artin.PlacesFrobenius
import GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierFinite
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module IntermediateField

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

section LocalLinear

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

/- English proof (translation)
Simplify using `only [charArtinConductor, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun σ _ ↦ by ring`.
-/
theorem charArtinConductor_const_mul_sum {ι : Type*} (s : Finset ι) (c : ℂ)
    (χ : ι → (L ≃ₐ[K] L) → ℂ) :
    charArtinConductor K L (fun σ ↦ c * ∑ i ∈ s, χ i σ) =
      c * ∑ i ∈ s, charArtinConductor K L (χ i) := by
  simp only [charArtinConductor, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun σ _ ↦ by ring

end LocalLinear

section LocalTower

variable {K F L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
  [ValuativeExtension K F] [ValuativeExtension F L] [ValuativeExtension K L]
  [FiniteDimensional K F] [FiniteDimensional F L] [FiniteDimensional K L] [IsGalois K L]

omit [ValuativeExtension K F] [FiniteDimensional K F] [IsGalois K L] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lowerIndex_restrictScalars_tower (σ : L ≃ₐ[F] L) :
    lowerIndex K L (σ.restrictScalars K) = lowerIndex F L σ :=
  rfl

open Classical in

/- English proof (translation)
Establish `: IsGalois F L` using `IsGalois.tower_top_of_isGalois K F L`. Distinguish the cases in `h1 : h = 1`. Substitute `h1` using the available equality. Rewrite using `[if_pos rfl, show (1 : L ≃ₐ[F] L).restrictScalars K = 1 from AlgEquiv.ext fun _ ↦ rfl, artinCharacter_one, artinCharacter_one, IsGalois.card_aut_eq_finrank, ← ramificationIndex_mul_residueDegree F L, residueDegree_tower K F L, differentExponent_tower K F L]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `h1' : h.restrictScalars K ≠ 1`. Introduce `h'`. Apply `h1` to reduce the goal to its premises. Use extensionality with `x`.

Conclude with `congrArg (fun σ : L ≃ₐ[K] L ↦ σ x) h'`. Rewrite using `[if_neg h1, artinCharacter_of_ne_one h1', artinCharacter_of_ne_one h1, lowerIndex_restrictScalars_tower, residueDegree_tower K F L]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem artinCharacter_restrictScalars_tower (h : L ≃ₐ[F] L) :
    (artinCharacter K L (h.restrictScalars K) : ℂ) =
      residueDegree K F * artinCharacter F L h +
        if h = 1 then (Nat.card (L ≃ₐ[F] L) : ℂ) * (residueDegree K F * differentExponent K F : ℕ)
        else 0 := by
  have : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  by_cases h1 : h = 1
  · subst h1
    rw [if_pos rfl, show (1 : L ≃ₐ[F] L).restrictScalars K = 1 from AlgEquiv.ext fun _ ↦ rfl,
      artinCharacter_one, artinCharacter_one, IsGalois.card_aut_eq_finrank,
      ← ramificationIndex_mul_residueDegree F L, residueDegree_tower K F L,
      differentExponent_tower K F L]
    push_cast
    ring
  · have h1' : h.restrictScalars K ≠ 1 := by
      intro h'
      apply h1
      ext x
      exact congrArg (fun σ : L ≃ₐ[K] L ↦ σ x) h'
    rw [if_neg h1, artinCharacter_of_ne_one h1', artinCharacter_of_ne_one h1,
      lowerIndex_restrictScalars_tower, residueDegree_tower K F L]
    push_cast
    ring

/- English proof (translation)
Establish `hH : (Nat.card (L ≃ₐ[F] L) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Repeatedly rewrite using `[artinCharacter_restrictScalars_tower, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]`. Establish `hs : ∑ h : L ≃ₐ[F] L, ψ h * ((residueDegree K F : ℂ) * artinCharacter F L h) = residueDegree K F * ∑ h : L ≃ₐ[F] L, ψ h * artinCharacter F L h`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun h _ ↦ by ring`.

Rewrite using `[hs, charArtinConductor]`. Clear the denominators using the available nonvanishing facts.
-/
theorem sum_mul_artinCharacter_restrictScalars (ψ : (L ≃ₐ[F] L) → ℂ) :
    ∑ h : L ≃ₐ[F] L, ψ h * (artinCharacter K L (h.restrictScalars K) : ℂ) =
      Nat.card (L ≃ₐ[F] L) * (residueDegree K F * charArtinConductor F L ψ +
        ((residueDegree K F * differentExponent K F : ℕ) : ℂ) * ψ 1) := by
  classical
  have hH : (Nat.card (L ≃ₐ[F] L) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  simp_rw [artinCharacter_restrictScalars_tower, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have hs : ∑ h : L ≃ₐ[F] L, ψ h * ((residueDegree K F : ℂ) * artinCharacter F L h) =
      residueDegree K F * ∑ h : L ≃ₐ[F] L, ψ h * artinCharacter F L h := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ ↦ by ring
  rw [hs, charArtinConductor]
  field_simp

end LocalTower

section Tower

open Artin

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (u : HeightOneSpectrum (𝓞 (fixedField H))) (w : HeightOneSpectrum (𝓞 L))

omit [IsGalois K L] in

/- English proof (translation)
Rewrite using `[MulAction.mem_stabilizer_iff]`. Establish `h` using `fixedFieldMulEquiv_smul_ideal H ((fixedFieldMulEquiv H).symm τ) w.asIdeal`. Rewrite `h` using `[MulEquiv.apply_symm_apply]`. Express the relevant statement in the definitionally equal form `_ = (((fixedFieldMulEquiv H).symm τ : H) : Gal(L/K)) • w.asIdeal at h`. Rewrite using `[← h]`.

Conclude with `τ.2`.
-/
theorem coe_symm_fixedFieldMulEquiv_mem_stabilizer
    (τ : MulAction.stabilizer Gal(L/fixedField H) w.asIdeal) :
    (((fixedFieldMulEquiv H).symm τ : H) : Gal(L/K)) ∈ MulAction.stabilizer Gal(L/K) w.asIdeal := by
  rw [MulAction.mem_stabilizer_iff]
  have h := fixedFieldMulEquiv_smul_ideal H ((fixedFieldMulEquiv H).symm τ) w.asIdeal
  rw [MulEquiv.apply_symm_apply] at h
  change _ = (((fixedFieldMulEquiv H).symm τ : H) : Gal(L/K)) • w.asIdeal at h
  rw [← h]
  exact τ.2

variable [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal] [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] isScalarTower_adicCompletion

/- English proof (translation)
Use `algEquiv_ext_adicCompletion v w (continuous_decompositionAlgEquiv v w _) (by exact continuous_decompositionAlgEquiv u w τ) fun x ↦ ?_` and prove the remaining obligations. Rewrite using `[decompositionMulEquiv_apply, AlgEquiv.restrictScalars_apply, decompositionMulEquiv_apply, decompositionToLocal_algebraMap, decompositionToLocal_algebraMap]`. Both sides reduce to the same expression.
-/
theorem decompositionMulEquiv_restrictScalars
    (τ : MulAction.stabilizer Gal(L/fixedField H) w.asIdeal) :
    decompositionMulEquiv v w ⟨(((fixedFieldMulEquiv H).symm τ : H) : Gal(L/K)),
        coe_symm_fixedFieldMulEquiv_mem_stabilizer H w τ⟩ =
      (decompositionMulEquiv u w τ).restrictScalars (v.adicCompletion K) := by
  refine algEquiv_ext_adicCompletion v w (continuous_decompositionAlgEquiv v w _)
    (by exact continuous_decompositionAlgEquiv u w τ) fun x ↦ ?_
  rw [decompositionMulEquiv_apply, AlgEquiv.restrictScalars_apply, decompositionMulEquiv_apply,
    decompositionToLocal_algebraMap, decompositionToLocal_algebraMap]
  rfl

/- English proof (translation)
Take `⟨τ, rfl⟩` from `(decompositionMulEquiv u w).surjective S`. Rewrite using `[← decompositionMulEquiv_restrictScalars H v u w τ, localToGlobal_decompositionMulEquiv, localToGlobal_decompositionMulEquiv]`. Both sides reduce to the same expression.
-/
theorem localToGlobal_restrictScalars
    (S : Gal(w.adicCompletion L/u.adicCompletion (fixedField H))) :
    localToGlobal v w (S.restrictScalars (v.adicCompletion K)) =
      (localToGlobal u w S).restrictScalars K := by
  obtain ⟨τ, rfl⟩ := (decompositionMulEquiv u w).surjective S
  rw [← decompositionMulEquiv_restrictScalars H v u w τ, localToGlobal_decompositionMulEquiv,
    localToGlobal_decompositionMulEquiv]
  rfl

omit [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal] in

/- English proof (translation)
The claim follows from `fun _ _ h ↦ (decompositionMulEquiv v w).symm.injective (Subtype.ext h)`.
-/
theorem localToGlobal_injective : Function.Injective (localToGlobal v w) :=
  fun _ _ h ↦ (decompositionMulEquiv v w).symm.injective (Subtype.ext h)

/- English proof (translation)
Use `set g : H := ⟨localToGlobal v w T, hT⟩`. Establish `hg : fixedFieldMulEquiv H g ∈ MulAction.stabilizer Gal(L/fixedField H) w.asIdeal`. Rewrite using `[MulAction.mem_stabilizer_iff, fixedFieldMulEquiv_smul_ideal]`. Conclude with `((decompositionMulEquiv v w).symm T).2`. Use `⟨decompositionMulEquiv u w ⟨_, hg⟩, localToGlobal_injective v w ?_⟩` and prove the remaining obligations.

Rewrite using `[localToGlobal_restrictScalars H v u w, localToGlobal_decompositionMulEquiv]`. Conclude with `AlgEquiv.ext fun _ ↦ rfl`.
-/
theorem exists_restrictScalars_eq {T : Gal(w.adicCompletion L/v.adicCompletion K)}
    (hT : localToGlobal v w T ∈ H) :
    ∃ S : Gal(w.adicCompletion L/u.adicCompletion (fixedField H)),
      S.restrictScalars (v.adicCompletion K) = T := by
  set g : H := ⟨localToGlobal v w T, hT⟩
  have hg : fixedFieldMulEquiv H g ∈ MulAction.stabilizer Gal(L/fixedField H) w.asIdeal := by
    rw [MulAction.mem_stabilizer_iff, fixedFieldMulEquiv_smul_ideal]
    exact ((decompositionMulEquiv v w).symm T).2
  refine ⟨decompositionMulEquiv u w ⟨_, hg⟩, localToGlobal_injective v w ?_⟩
  rw [localToGlobal_restrictScalars H v u w, localToGlobal_decompositionMulEquiv]
  exact AlgEquiv.ext fun _ ↦ rfl

/- English proof (translation)
Use `set F : Gal(w.adicCompletion L/v.adicCompletion K) → ℂ := fun T ↦ extendByZero H χ (localToGlobal v w T) * (artinCharacter (v.adicCompletion K) (w.adicCompletion L) T : ℂ) with hF`. Establish `hinj : Function.Injective (fun S : Gal(w.adicCompletion L/u.adicCompletion (fixedField H)) ↦ S.restrictScalars (v.adicCompletion K))` using `AlgEquiv.restrictScalars_injective _`. Establish `hterm : ∀ S : Gal(w.adicCompletion L/u.adicCompletion (fixedField H)), χ ((fixedFieldMulEquiv H).symm (localToGlobal u w S)) * (artinCharacter (v.adicCompletion K) (w.adicCompletion L) (S.restrictScalars (v.adicCompletion K)) : ℂ) = F (S.restrictScalars (v.adicCompletion K))`. Introduce `S`. Rewrite using `[hF]`.

Simplify using `only`. Rewrite using `[localToGlobal_restrictScalars H v u w, extendByZero_of_mem H χ (restrictScalars_mem H (localToGlobal u w S))]`. Both sides reduce to the same expression. Use `symm`. Rewrite using `[Finset.sum_congr rfl fun S _ ↦ hterm S, ← Finset.sum_image fun _ _ _ _ h ↦ hinj h]`.

Use `Finset.sum_subset (Finset.subset_univ _) fun T _ hT ↦ ?_` and prove the remaining obligations. Distinguish the cases in `hmem : localToGlobal v w T ∈ H`. Take `⟨S, hS⟩` from `exists_restrictScalars_eq H v u w hmem`. Conclude with `absurd (Finset.mem_image.2 ⟨S, Finset.mem_univ _, hS⟩) hT`. Rewrite using `[hF]`.

Simplify using `only`. Rewrite using `[extendByZero_of_notMem H χ hmem, zero_mul]`.
-/
theorem sum_extendByZero_mul_artinCharacter (χ : H → ℂ) :
    ∑ T : Gal(w.adicCompletion L/v.adicCompletion K),
        extendByZero H χ (localToGlobal v w T) *
          (artinCharacter (v.adicCompletion K) (w.adicCompletion L) T : ℂ) =
      ∑ S : Gal(w.adicCompletion L/u.adicCompletion (fixedField H)),
        χ ((fixedFieldMulEquiv H).symm (localToGlobal u w S)) *
          (artinCharacter (v.adicCompletion K) (w.adicCompletion L)
            (S.restrictScalars (v.adicCompletion K)) : ℂ) := by
  classical
  set F : Gal(w.adicCompletion L/v.adicCompletion K) → ℂ := fun T ↦
    extendByZero H χ (localToGlobal v w T) *
      (artinCharacter (v.adicCompletion K) (w.adicCompletion L) T : ℂ) with hF
  have hinj : Function.Injective
      (fun S : Gal(w.adicCompletion L/u.adicCompletion (fixedField H)) ↦
        S.restrictScalars (v.adicCompletion K)) := AlgEquiv.restrictScalars_injective _
  have hterm : ∀ S : Gal(w.adicCompletion L/u.adicCompletion (fixedField H)),
      χ ((fixedFieldMulEquiv H).symm (localToGlobal u w S)) *
        (artinCharacter (v.adicCompletion K) (w.adicCompletion L)
          (S.restrictScalars (v.adicCompletion K)) : ℂ) =
        F (S.restrictScalars (v.adicCompletion K)) := by
    intro S
    rw [hF]
    simp only
    rw [localToGlobal_restrictScalars H v u w,
      extendByZero_of_mem H χ (restrictScalars_mem H (localToGlobal u w S))]
    rfl
  symm
  rw [Finset.sum_congr rfl fun S _ ↦ hterm S, ← Finset.sum_image fun _ _ _ _ h ↦ hinj h]
  refine Finset.sum_subset (Finset.subset_univ _) fun T _ hT ↦ ?_
  by_cases hmem : localToGlobal v w T ∈ H
  · obtain ⟨S, hS⟩ := exists_restrictScalars_eq H v u w hmem
    exact absurd (Finset.mem_image.2 ⟨S, Finset.mem_univ _, hS⟩) hT
  · rw [hF]
    simp only
    rw [extendByZero_of_notMem H χ hmem, zero_mul]

/- English proof (translation)
Establish `hχ : ∀ σ, charOnSubgroup H ρ ((fixedFieldMulEquiv H).symm σ) = ρ.character σ` using `fun σ ↦ by`. Simplify using `only [charOnSubgroup, MulEquiv.apply_symm_apply]`. Repeatedly rewrite using `[charArtinConductor, sum_extendByZero_mul_artinCharacter H v u w, hχ]`. Rewrite using `[ sum_mul_artinCharacter_restrictScalars (ψ := fun S ↦ ρ.character (localToGlobal u w S)), ← natCast_artinExponent u ρ w, map_one, Representation.char_one]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem charArtinConductor_extendByZero {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ Gal(L/fixedField H) V) :
    charArtinConductor (v.adicCompletion K) (w.adicCompletion L)
        (fun T ↦ extendByZero H (charOnSubgroup H ρ) (localToGlobal v w T)) =
      (Nat.card Gal(w.adicCompletion L/v.adicCompletion K) : ℂ)⁻¹ *
        Nat.card Gal(w.adicCompletion L/u.adicCompletion (fixedField H)) *
        (residueDegree (v.adicCompletion K) (u.adicCompletion (fixedField H)) *
          ((differentExponent (v.adicCompletion K) (u.adicCompletion (fixedField H)) *
            finrank ℂ V + artinExponent u ρ : ℕ) : ℂ)) := by
  have hχ : ∀ σ, charOnSubgroup H ρ ((fixedFieldMulEquiv H).symm σ) = ρ.character σ := fun σ ↦ by
    simp only [charOnSubgroup, MulEquiv.apply_symm_apply]
  simp_rw [charArtinConductor, sum_extendByZero_mul_artinCharacter H v u w, hχ]
  rw [
    sum_mul_artinCharacter_restrictScalars (ψ := fun S ↦ ρ.character (localToGlobal u w S)),
    ← natCast_artinExponent u ρ w, map_one, Representation.char_one]
  push_cast
  ring

end Tower

section Global

open Artin

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/- English proof (translation)
Rewrite using `[← Nat.card_congr (decompositionMulEquiv v w).toEquiv, Ideal.card_stabilizer_eq v.asIdeal w.asIdeal]`.
-/
theorem natCard_gal_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Nat.card Gal(w.adicCompletion L/v.adicCompletion K) =
      v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) := by
  rw [← Nat.card_congr (decompositionMulEquiv v w).toEquiv,
    Ideal.card_stabilizer_eq v.asIdeal w.asIdeal]

/- English proof (translation)
Rewrite using `[← charArtinConductor_autCongr (SemiLocal.galEquiv v σ w w' h)]`. Use `congr 1`. Use function extensionality and compare the values at `T`. Rewrite using `[localToGlobal_autCongr v σ w w' h]`.
-/
theorem charArtinConductor_conj (v : HeightOneSpectrum (𝓞 K)) (σ : Gal(L/K))
    (w w' : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal]
    (h : w' = σ • w) (F : Gal(L/K) → ℂ) :
    charArtinConductor (v.adicCompletion K) (w.adicCompletion L)
        (fun T ↦ F (σ * localToGlobal v w T * σ⁻¹)) =
      charArtinConductor (v.adicCompletion K) (w'.adicCompletion L)
        (fun T ↦ F (localToGlobal v w' T)) := by
  rw [← charArtinConductor_autCongr (SemiLocal.galEquiv v σ w w' h)]
  congr 1
  funext T
  rw [localToGlobal_autCongr v σ w w' h]

open Classical in

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise Finset.univ (DoubleCoset.mk H D) F]`. Use `Finset.sum_congr rfl fun q _ ↦ ?_` and prove the remaining obligations. Establish `key` using `sum_mul_mul_eq H D q.out F`. Rewrite `key` using `[DoubleCoset.out_eq']`. Establish `hE0 : (Nat.card ((MulAut.conj q.out⁻¹ • H : Subgroup G).subgroupOf D) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`.

Establish `hL : ∑ h : H, ∑ e : D, F (h * q.out * e) = (Nat.card H * Nat.card D : ℂ) * F q.out`. Rewrite using `[Finset.sum_congr rfl fun (h : H) _ ↦ Finset.sum_congr rfl fun (e : D) _ ↦ hF q.out h h.2 e e.2, Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[hL]`. Rewrite using `[div_mul_eq_mul_div, key]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem sum_eq_sum_doubleCoset {G : Type*} [Group G] [Fintype G] (H D : Subgroup G) (F : G → ℂ)
    (hF : ∀ x : G, ∀ h ∈ H, ∀ e ∈ D, F (h * x * e) = F x) :
    ∑ t : G, F t = ∑ q : DoubleCoset.Quotient (H : Set G) D,
      (Nat.card H * Nat.card D : ℂ) /
        Nat.card ((MulAut.conj q.out⁻¹ • H : Subgroup G).subgroupOf D) * F q.out := by
  rw [← Finset.sum_fiberwise Finset.univ (DoubleCoset.mk H D) F]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have key := sum_mul_mul_eq H D q.out F
  rw [DoubleCoset.out_eq'] at key
  have hE0 : (Nat.card ((MulAut.conj q.out⁻¹ • H : Subgroup G).subgroupOf D) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hL : ∑ h : H, ∑ e : D, F (h * q.out * e) = (Nat.card H * Nat.card D : ℂ) * F q.out := by
    rw [Finset.sum_congr rfl fun (h : H) _ ↦ Finset.sum_congr rfl fun (e : D) _ ↦ hF q.out h h.2 e e.2,
      Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, nsmul_eq_mul,
      nsmul_eq_mul, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    ring
  rw [hL] at key
  rw [div_mul_eq_mul_div, key]
  field_simp

variable (H : Subgroup Gal(L/K)) {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ Gal(L/fixedField H) V)

/- English proof (translation)
Use `set w := placeAbove (L := L) v with hw`. Use `set D := MulAction.stabilizer Gal(L/K) w.asIdeal with hD`. Use `set c : SemiLocal.PlacesOver (fixedField H) v → ℂ := fun u ↦ (residueDegree (v.adicCompletion K) (u.1.adicCompletion (fixedField H)) : ℂ) * ((differentExponent (v.adicCompletion K) (u.1.adicCompletion (fixedField H)) * finrank ℂ V + artinExponent u.1 ρ : ℕ) : ℂ) with hc`. Use `set U : Gal(L/K) → SemiLocal.PlacesOver (fixedField H) v := fun t ↦ ⟨subfieldPlace H w t, subfieldPlace_liesOver H v w t⟩ with hU`. Use `set g : SemiLocal.PlacesOver (fixedField H) v → ℕ := fun u ↦ u.1.asIdeal.ramificationIdxIn (𝓞 L) * u.1.asIdeal.inertiaDegIn (𝓞 L) with hg`.

Use `set χ := charOnSubgroup H ρ with hχ`. Establish `hDcard : Nat.card D = v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L)` using `Ideal.card_stabilizer_eq v.asIdeal w.asIdeal`. Establish `hterm : ∀ t : Gal(L/K), charArtinConductor (v.adicCompletion K) (w.adicCompletion L) (fun T ↦ extendByZero H χ (t * localToGlobal v w T * t⁻¹)) = (Nat.card D : ℂ)⁻¹ * (g (U t) * c (U t))`. Introduce `t`. Establish `: (t • w).asIdeal.LiesOver v.asIdeal` using `(inferInstance : (t • w.asIdeal).LiesOver v.asIdeal)`.

Establish `: (t • w).asIdeal.LiesOver (U t).1.asIdeal` using `liesOver_subfieldPlace H w t`. Establish `: (U t).1.asIdeal.LiesOver v.asIdeal` using `(U t).2`. Rewrite using `[charArtinConductor_conj v t w (t • w) rfl (extendByZero H χ), charArtinConductor_extendByZero H v (U t).1 (t • w) ρ, natCard_gal_adicCompletion v (t • w), natCard_gal_adicCompletion (U t).1 (t • w), hDcard]`. Simplify using `only [hg, hc]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hgd : ∀ x : Gal(L/K), (g (U x) : ℂ) = Nat.card ((MulAut.conj x⁻¹ • H : Subgroup Gal(L/K)).subgroupOf D)`. Introduce `x`. Establish `: (x • w.asIdeal).LiesOver (U x).1.asIdeal` using `liesOver_subfieldPlace H w x`. Rewrite using `[Nat.card_congr (conjSubgroupOfEquiv H D x), ← Subgroup.card_map_of_injective (f := (fixedFieldMulEquiv H).toMonoidHom) (fixedFieldMulEquiv H).injective, ← stabilizer_fixedField_smul_eq H w x, Ideal.card_stabilizer_eq (U x).1.asIdeal (x • w.asIdeal)]`.

Establish `hinv : ∀ x : Gal(L/K), ∀ h ∈ H, ∀ e ∈ D, U (h * x * e) = U x`. Introduce `x h hh e he`. Conclude with `Subtype.ext ((subfieldPlace_eq_iff H w (h * x * e) x).2 ((DoubleCoset.eq H D _ _).2 ⟨h⁻¹, H.inv_mem hh, e⁻¹, D.inv_mem he, by group⟩))`. Rewrite using `[natCast_artinExponent v _ w, character_ind_restrictScalarsHom]`. Repeatedly rewrite using `[indFun_subtype_apply]`.

Rewrite using `[charArtinConductor_const_mul_sum]`. Establish `hsum : ∑ t : Gal(L/K), charArtinConductor (v.adicCompletion K) (w.adicCompletion L) (fun T ↦ extendByZero H χ (t⁻¹ * localToGlobal v w T * t)) = ∑ t : Gal(L/K), charArtinConductor (v.adicCompletion K) (w.adicCompletion L) (fun T ↦ extendByZero H χ (t * localToGlobal v w T * t⁻¹))` using `Fintype.sum_equiv (Equiv.inv _) _ _ fun t ↦ by simp only [Equiv.inv_apply, inv_inv]`. Rewrite using `[hsum, Finset.sum_congr rfl fun t _ ↦ hterm t, ← Finset.mul_sum, sum_eq_sum_doubleCoset H D (fun t ↦ (g (U t) : ℂ) * c (U t)) (fun x h hh e he ↦ by simp only [hinv x h hh e he])]`. Establish `hD0 : (Nat.card D : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Establish `hH0 : (Nat.card H : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`.

Establish `hq : ∀ q : DoubleCoset.Quotient (H : Set Gal(L/K)) D, (Nat.card H * Nat.card D : ℂ) / Nat.card ((MulAut.conj q.out⁻¹ • H : Subgroup Gal(L/K)).subgroupOf D) * ((g (U q.out) : ℂ) * c (U q.out)) = Nat.card H * Nat.card D * c (U q.out)`. Introduce `q`. Establish `hE0 : (Nat.card ((MulAut.conj q.out⁻¹ • H : Subgroup Gal(L/K)).subgroupOf D) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Rewrite using `[hgd q.out]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[Finset.sum_congr rfl fun q _ ↦ hq q, ← Finset.mul_sum]`. Establish `hequiv : ∑ q : DoubleCoset.Quotient (H : Set Gal(L/K)) D, c (U q.out) = ∑ u : SemiLocal.PlacesOver (fixedField H) v, c u`. Use `Fintype.sum_equiv (subfieldPlaceEquiv H v w) _ _ fun q ↦ ?_` and prove the remaining obligations. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `h` using `subfieldPlaceEquiv_mk H v w q.out`. Rewrite `h` using `[DoubleCoset.out_eq']`. Conclude with `h.symm`. Rewrite using `[hequiv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem natCast_artinExponent_ind (v : HeightOneSpectrum (𝓞 K)) :
    (artinExponent v (ρ.ind (AlgEquiv.restrictScalarsHom K)) : ℂ) =
      ∑ u : SemiLocal.PlacesOver (fixedField H) v,
        (residueDegree (v.adicCompletion K) (u.1.adicCompletion (fixedField H)) : ℂ) *
          ((differentExponent (v.adicCompletion K) (u.1.adicCompletion (fixedField H)) *
            finrank ℂ V + artinExponent u.1 ρ : ℕ) : ℂ) := by
  classical
  set w := placeAbove (L := L) v with hw
  set D := MulAction.stabilizer Gal(L/K) w.asIdeal with hD
  set c : SemiLocal.PlacesOver (fixedField H) v → ℂ := fun u ↦
    (residueDegree (v.adicCompletion K) (u.1.adicCompletion (fixedField H)) : ℂ) *
      ((differentExponent (v.adicCompletion K) (u.1.adicCompletion (fixedField H)) *
        finrank ℂ V + artinExponent u.1 ρ : ℕ) : ℂ) with hc
  set U : Gal(L/K) → SemiLocal.PlacesOver (fixedField H) v := fun t ↦
    ⟨subfieldPlace H w t, subfieldPlace_liesOver H v w t⟩ with hU
  set g : SemiLocal.PlacesOver (fixedField H) v → ℕ := fun u ↦
    u.1.asIdeal.ramificationIdxIn (𝓞 L) * u.1.asIdeal.inertiaDegIn (𝓞 L) with hg
  set χ := charOnSubgroup H ρ with hχ
  have hDcard : Nat.card D = v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) :=
    Ideal.card_stabilizer_eq v.asIdeal w.asIdeal

  have hterm : ∀ t : Gal(L/K), charArtinConductor (v.adicCompletion K) (w.adicCompletion L)
      (fun T ↦ extendByZero H χ (t * localToGlobal v w T * t⁻¹)) =
        (Nat.card D : ℂ)⁻¹ * (g (U t) * c (U t)) := by
    intro t
    have : (t • w).asIdeal.LiesOver v.asIdeal :=
      (inferInstance : (t • w.asIdeal).LiesOver v.asIdeal)
    have : (t • w).asIdeal.LiesOver (U t).1.asIdeal := liesOver_subfieldPlace H w t
    have : (U t).1.asIdeal.LiesOver v.asIdeal := (U t).2
    rw [charArtinConductor_conj v t w (t • w) rfl (extendByZero H χ),
      charArtinConductor_extendByZero H v (U t).1 (t • w) ρ, natCard_gal_adicCompletion v (t • w),
      natCard_gal_adicCompletion (U t).1 (t • w), hDcard]
    simp only [hg, hc]
    push_cast
    ring

  have hgd : ∀ x : Gal(L/K), (g (U x) : ℂ) =
      Nat.card ((MulAut.conj x⁻¹ • H : Subgroup Gal(L/K)).subgroupOf D) := by
    intro x
    have : (x • w.asIdeal).LiesOver (U x).1.asIdeal := liesOver_subfieldPlace H w x
    rw [Nat.card_congr (conjSubgroupOfEquiv H D x),
      ← Subgroup.card_map_of_injective (f := (fixedFieldMulEquiv H).toMonoidHom)
        (fixedFieldMulEquiv H).injective,
      ← stabilizer_fixedField_smul_eq H w x,
      Ideal.card_stabilizer_eq (U x).1.asIdeal (x • w.asIdeal)]
  have hinv : ∀ x : Gal(L/K), ∀ h ∈ H, ∀ e ∈ D, U (h * x * e) = U x := by
    intro x h hh e he
    exact Subtype.ext ((subfieldPlace_eq_iff H w (h * x * e) x).2
      ((DoubleCoset.eq H D _ _).2 ⟨h⁻¹, H.inv_mem hh, e⁻¹, D.inv_mem he, by group⟩))
  rw [natCast_artinExponent v _ w, character_ind_restrictScalarsHom]
  simp_rw [indFun_subtype_apply]
  rw [charArtinConductor_const_mul_sum]
  have hsum : ∑ t : Gal(L/K), charArtinConductor (v.adicCompletion K) (w.adicCompletion L)
      (fun T ↦ extendByZero H χ (t⁻¹ * localToGlobal v w T * t)) =
        ∑ t : Gal(L/K), charArtinConductor (v.adicCompletion K) (w.adicCompletion L)
          (fun T ↦ extendByZero H χ (t * localToGlobal v w T * t⁻¹)) :=
    Fintype.sum_equiv (Equiv.inv _) _ _ fun t ↦ by simp only [Equiv.inv_apply, inv_inv]
  rw [hsum, Finset.sum_congr rfl fun t _ ↦ hterm t, ← Finset.mul_sum,
    sum_eq_sum_doubleCoset H D (fun t ↦ (g (U t) : ℂ) * c (U t))
      (fun x h hh e he ↦ by simp only [hinv x h hh e he])]
  have hD0 : (Nat.card D : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hH0 : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hq : ∀ q : DoubleCoset.Quotient (H : Set Gal(L/K)) D,
      (Nat.card H * Nat.card D : ℂ) /
        Nat.card ((MulAut.conj q.out⁻¹ • H : Subgroup Gal(L/K)).subgroupOf D) *
          ((g (U q.out) : ℂ) * c (U q.out)) = Nat.card H * Nat.card D * c (U q.out) := by
    intro q
    have hE0 : (Nat.card ((MulAut.conj q.out⁻¹ • H : Subgroup Gal(L/K)).subgroupOf D) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [hgd q.out]
    field_simp
  rw [Finset.sum_congr rfl fun q _ ↦ hq q, ← Finset.mul_sum]
  have hequiv : ∑ q : DoubleCoset.Quotient (H : Set Gal(L/K)) D, c (U q.out) =
      ∑ u : SemiLocal.PlacesOver (fixedField H) v, c u := by
    refine Fintype.sum_equiv (subfieldPlaceEquiv H v w) _ _ fun q ↦ ?_
    congr 1
    apply Subtype.ext
    have h := subfieldPlaceEquiv_mk H v w q.out
    rw [DoubleCoset.out_eq'] at h
    exact h.symm
  rw [hequiv]
  field_simp

/- English proof (translation)
Apply `Nat.cast_injective (R := ℂ)` to reduce the goal to its premises. Rewrite using `[natCast_artinExponent_ind]`. Use `push_cast`. Use `Finset.sum_congr rfl fun u _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← inertiaDeg_integer v u.1]`.
-/
theorem artinExponent_ind (v : HeightOneSpectrum (𝓞 K)) :
    artinExponent v (ρ.ind (AlgEquiv.restrictScalarsHom K)) =
      ∑ u : SemiLocal.PlacesOver (fixedField H) v, u.1.asIdeal.inertiaDeg (𝓞 K) *
        (differentExponent (v.adicCompletion K) (u.1.adicCompletion (fixedField H)) * finrank ℂ V +
          artinExponent u.1 ρ) := by
  apply Nat.cast_injective (R := ℂ)
  rw [natCast_artinExponent_ind]
  push_cast
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [← inertiaDeg_integer v u.1]

omit [IsGalois K L] in

/- English proof (translation)
The claim follows from `multiplicity_finprod_asIdeal_pow (finite_support_artinExponent K σ) v`.
-/
theorem multiplicity_artinConductorIdeal [IsGalois K L] {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ Gal(L/K) W) (v : HeightOneSpectrum (𝓞 K)) :
    multiplicity v.asIdeal (artinConductorIdeal σ) = artinExponent v σ :=
  multiplicity_finprod_asIdeal_pow (finite_support_artinExponent K σ) v

/- English proof (translation)
Establish `hN : Ideal.relNorm (𝓞 K) (artinConductorIdeal ρ) ≠ ⊥` using `(Ideal.relNorm_eq_bot_iff (R := 𝓞 K)).not.2 (artinConductorIdeal_ne_bot ρ)`. Establish `hJ : relDiscr K (fixedField H) ^ finrank ℂ V * Ideal.relNorm (𝓞 K) (artinConductorIdeal ρ) ≠ ⊥` using `mul_ne_zero (pow_ne_zero _ (relDiscr_ne_bot K _)) hN`. Rewrite using `[← Ideal.finprod_heightOneSpectrum_pow_multiplicity hJ, artinConductorIdeal]`. Use `finprod_congr fun v ↦ congrArg (v.asIdeal ^ ·) ?_` and prove the remaining obligations. Establish `hp` using `prime_asIdeal v`.

Rewrite using `[multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp hJ), (FiniteMultiplicity.of_prime_left hp (relDiscr_ne_bot K _)).multiplicity_pow hp, multiplicity_relDiscr_semiLocal v, multiplicity_relNorm v _ (artinConductorIdeal_ne_bot ρ), artinExponent_ind]`. Simplify using `only [multiplicity_artinConductorIdeal]`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun u _ ↦ by ring`.
-/
theorem artinConductorIdeal_ind :
    artinConductorIdeal (ρ.ind (AlgEquiv.restrictScalarsHom K)) =
      relDiscr K (fixedField H) ^ finrank ℂ V * Ideal.relNorm (𝓞 K) (artinConductorIdeal ρ) := by
  have hN : Ideal.relNorm (𝓞 K) (artinConductorIdeal ρ) ≠ ⊥ :=
    (Ideal.relNorm_eq_bot_iff (R := 𝓞 K)).not.2 (artinConductorIdeal_ne_bot ρ)
  have hJ : relDiscr K (fixedField H) ^ finrank ℂ V * Ideal.relNorm (𝓞 K) (artinConductorIdeal ρ) ≠
      ⊥ := mul_ne_zero (pow_ne_zero _ (relDiscr_ne_bot K _)) hN
  rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity hJ, artinConductorIdeal]
  refine finprod_congr fun v ↦ congrArg (v.asIdeal ^ ·) ?_
  have hp := prime_asIdeal v
  rw [multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp hJ),
    (FiniteMultiplicity.of_prime_left hp (relDiscr_ne_bot K _)).multiplicity_pow hp,
    multiplicity_relDiscr_semiLocal v, multiplicity_relNorm v _ (artinConductorIdeal_ne_bot ρ),
    artinExponent_ind]
  simp only [multiplicity_artinConductorIdeal]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ ↦ by ring

end Global

end GroundTheory.Global
