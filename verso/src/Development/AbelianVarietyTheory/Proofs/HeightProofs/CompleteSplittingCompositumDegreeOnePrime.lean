import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardPrimesEqFinrankOfFrobeniusFixes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FrobeniusFixesOfSplitsCompletelyIntermediateStatement

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.SplitCompositum

/- English proof (translation)
Set `φ : 𝓞 M ≃+* 𝓞 M'` to `NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv`. Establish `hφ : ∀ x : 𝓞 K, φ (algebraMap (𝓞 K) (𝓞 M) x) = algebraMap (𝓞 K) (𝓞 M') x`. Introduce `x`. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Use `show e (algebraMap (𝓞 M) M (algebraMap (𝓞 K) (𝓞 M) x)) = algebraMap (𝓞 M') M' (algebraMap (𝓞 K) (𝓞 M') x)`.

Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K M, IsScalarTower.algebraMap_apply (𝓞 K) K M']`. Conclude with `e.commutes _`. Establish `hcomp : ∀ I : Ideal (𝓞 M'), (I.comap φ).comap (algebraMap (𝓞 K) (𝓞 M)) = I.comap (algebraMap (𝓞 K) (𝓞 M'))`. Introduce `I`. Use extensionality with `x`.

Simplify using `only [Ideal.mem_comap]`. Rewrite using `[hφ]`. Use `Set.ncard_congr (fun Q _ => (⟨Q.asIdeal.comap φ, Ideal.comap_isPrime φ Q.asIdeal, fun h => Q.ne_bot (by` and prove the remaining obligations. Establish `h'` using `congrArg (Ideal.map φ) h`. Rewrite using `[Ideal.map_comap_of_surjective φ φ.surjective, Ideal.map_bot] at h')⟩ : HeightOneSpectrum (𝓞 M)))` and apply the resulting hypothesis.

Use the proof step `?_ ?_ ?_`. Introduce `Q hQ`. Simplify using `only [Set.mem_setOf_eq] at hQ ⊢`. Rewrite using `[hcomp, hQ]`. Introduce `Q₁ Q₂ _ _ h`.

Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Establish `h'` using `congrArg HeightOneSpectrum.asIdeal h`. Conclude with `Ideal.comap_injective_of_surjective φ φ.surjective h'`. Introduce `Q hQ`. Use `⟨⟨Q.asIdeal.comap φ.symm, Ideal.comap_isPrime φ.symm Q.asIdeal, fun h => Q.ne_bot (by` and prove the remaining obligations.

Establish `h'` using `congrArg (Ideal.map φ.symm) h`. Rewrite using `[Ideal.map_comap_of_surjective φ.symm φ.symm.surjective, Ideal.map_bot] at h')⟩, ?_, ?_⟩` and apply the resulting hypothesis. Simplify using `only [Set.mem_setOf_eq] at hQ ⊢`. Rewrite using `[← hQ, ← hcomp]`. Use `congr 1`.

Use extensionality with `x`. Simplify using `[Ideal.mem_comap]`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `[Ideal.mem_comap]`.
-/
theorem ncard_over_congr {K M M' : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field M']
    [NumberField M'] [Algebra K M] [Algebra K M'] (e : M ≃ₐ[K] M') (𝔭 : HeightOneSpectrum (𝓞 K)) :
    {Q : HeightOneSpectrum (𝓞 M') | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M')) = 𝔭.asIdeal}.ncard =
      {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard := by
  classical
  let φ : 𝓞 M ≃+* 𝓞 M' := NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv
  have hφ : ∀ x : 𝓞 K, φ (algebraMap (𝓞 K) (𝓞 M) x) = algebraMap (𝓞 K) (𝓞 M') x := by
    intro x
    apply NumberField.RingOfIntegers.ext
    show e (algebraMap (𝓞 M) M (algebraMap (𝓞 K) (𝓞 M) x)) = algebraMap (𝓞 M') M' (algebraMap (𝓞 K) (𝓞 M') x)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) K M, IsScalarTower.algebraMap_apply (𝓞 K) K M']
    exact e.commutes _
  have hcomp : ∀ I : Ideal (𝓞 M'),
      (I.comap φ).comap (algebraMap (𝓞 K) (𝓞 M)) = I.comap (algebraMap (𝓞 K) (𝓞 M')) := by
    intro I
    ext x
    simp only [Ideal.mem_comap]
    rw [hφ]
  refine Set.ncard_congr (fun Q _ => (⟨Q.asIdeal.comap φ, Ideal.comap_isPrime φ Q.asIdeal, fun h => Q.ne_bot (by
      have h' := congrArg (Ideal.map φ) h
      rwa [Ideal.map_comap_of_surjective φ φ.surjective, Ideal.map_bot] at h')⟩ : HeightOneSpectrum (𝓞 M)))
    ?_ ?_ ?_
  · intro Q hQ
    simp only [Set.mem_setOf_eq] at hQ ⊢
    rw [hcomp, hQ]
  · intro Q₁ Q₂ _ _ h
    apply HeightOneSpectrum.ext
    have h' := congrArg HeightOneSpectrum.asIdeal h
    exact Ideal.comap_injective_of_surjective φ φ.surjective h'
  · intro Q hQ
    refine ⟨⟨Q.asIdeal.comap φ.symm, Ideal.comap_isPrime φ.symm Q.asIdeal, fun h => Q.ne_bot (by
      have h' := congrArg (Ideal.map φ.symm) h
      rwa [Ideal.map_comap_of_surjective φ.symm φ.symm.surjective, Ideal.map_bot] at h')⟩, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq] at hQ ⊢
      rw [← hQ, ← hcomp]
      congr 1
      ext x
      simp [Ideal.mem_comap]
    · apply HeightOneSpectrum.ext
      ext x
      simp [Ideal.mem_comap]

/- English proof (translation)
Use `haveI : IsGalois K (AlgebraicClosure M') := IsAlgClosure.isGalois K _`. Use `set N : IntermediateField K (AlgebraicClosure M') := IntermediateField.normalClosure K M' (AlgebraicClosure M') with hN`. Use `haveI : FiniteDimensional K N := normalClosure.is_finiteDimensional K M' (AlgebraicClosure M')`. Use `haveI : IsGalois K N := IsGalois.normalClosure K M' (AlgebraicClosure M')`. Use `haveI : IsScalarTower ℚ K N := IsScalarTower.of_algebraMap_eq (fun x => by`.

Rewrite using `[eq_ratCast (algebraMap ℚ N), eq_ratCast (algebraMap ℚ K), map_ratCast])`. Use `haveI : FiniteDimensional ℚ N := Module.Finite.trans K N`. Use `haveI : NumberField N := NumberField.mk`. Use `letI : Algebra L N := ((algebraMap M' N).comp (algebraMap L M')).toAlgebra`. Use `haveI : IsScalarTower L M' N := IsScalarTower.of_algebraMap_eq' rfl`.

Use `haveI : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq (fun x => by show algebraMap K N x = algebraMap M' N (algebraMap L M' (algebraMap K L x))`. Rewrite using `[← IsScalarTower.algebraMap_apply K L M', ← IsScalarTower.algebraMap_apply K M' N])`. Use `haveI : IsGalois L N := IsGalois.tower_top_of_isGalois K L N`. Set `ι : M' →ₐ[L] N` to `IsScalarTower.toAlgHom L M' N`. Set `g : M →ₐ[K] N` to `(IsScalarTower.toAlgHom K M' N).comp f`.

Establish `h1 : {Q : HeightOneSpectrum (𝓞 g.fieldRange) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 g.fieldRange)) = 𝔭.asIdeal}.ncard = Module.finrank K g.fieldRange`. Rewrite using `[ncard_over_congr g.equivFieldRange 𝔭, hsplit]`. Conclude with `g.equivFieldRange.toLinearEquiv.finrank_eq`. Establish `hfix1` using `GlobalTheory.T.frobenius_fixes_of_splitsCompletely_intermediate K N g.fieldRange 𝔭 h1`. Establish `hfix2 : ∀ σ : N ≃ₐ[L] N, GlobalTheory.NT.IsFrob N 𝔓 σ → ∀ x ∈ ι.fieldRange, σ x = x`.

Introduce `σ hσ`. Establish `hK : GlobalTheory.NT.IsFrob N 𝔭 (σ.restrictScalars K)`. Take `⟨P, hP, hPo, hx⟩` from `hσ`. Use `⟨P, hP, ⟨?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hover, hPo.over, Ideal.under, Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]`.

Introduce `x`. Rewrite using `[← hnorm]`. Conclude with `hx x`. Establish `hM1` using `hfix1 (σ.restrictScalars K) hK`. Establish `hg : (σ.toAlgHom.comp ι) = ι` using `hgen N _ _ (fun x => by`.

Use `hM1 (g x) ⟨x, rfl⟩` as an intermediate fact. Conclude with `this)`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `congrArg (fun h : M' →ₐ[L] N => h y) hg`. Establish `h2` using `GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix L N ι.fieldRange 𝔓 hfix2`.

Rewrite using `[← ncard_over_congr ι.equivFieldRange 𝔓, h2]`. Conclude with `ι.equivFieldRange.toLinearEquiv.finrank_eq.symm`.
-/
theorem ncard_eq_finrank_of_generated (K L M M' : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Field M'] [NumberField M'] [Algebra K L] [Algebra K M] [Algebra L M'] [Algebra K M']
    [IsScalarTower K L M'] (f : M →ₐ[K] M')
    (hgen : ∀ (N : Type) [Field N] [Algebra L N] (g g' : M' →ₐ[L] N), (∀ x, g (f x) = g' (f x)) → g = g')
    (𝔭 : HeightOneSpectrum (𝓞 K)) (𝔓 : HeightOneSpectrum (𝓞 L))
    (hover : 𝔓.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = 𝔭.asIdeal)
    (hnorm : Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal)
    (hsplit : {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard =
      Module.finrank K M) :
    {Q : HeightOneSpectrum (𝓞 M') | Q.asIdeal.comap (algebraMap (𝓞 L) (𝓞 M')) = 𝔓.asIdeal}.ncard =
      Module.finrank L M' := by
  classical
  haveI : IsGalois K (AlgebraicClosure M') := IsAlgClosure.isGalois K _
  set N : IntermediateField K (AlgebraicClosure M') :=
    IntermediateField.normalClosure K M' (AlgebraicClosure M') with hN
  haveI : FiniteDimensional K N := normalClosure.is_finiteDimensional K M' (AlgebraicClosure M')
  haveI : IsGalois K N := IsGalois.normalClosure K M' (AlgebraicClosure M')
  haveI : IsScalarTower ℚ K N := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [eq_ratCast (algebraMap ℚ N), eq_ratCast (algebraMap ℚ K), map_ratCast])
  haveI : FiniteDimensional ℚ N := Module.Finite.trans K N
  haveI : NumberField N := NumberField.mk
  letI : Algebra L N := ((algebraMap M' N).comp (algebraMap L M')).toAlgebra
  haveI : IsScalarTower L M' N := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap K N x = algebraMap M' N (algebraMap L M' (algebraMap K L x))
    rw [← IsScalarTower.algebraMap_apply K L M', ← IsScalarTower.algebraMap_apply K M' N])
  haveI : IsGalois L N := IsGalois.tower_top_of_isGalois K L N
  let ι : M' →ₐ[L] N := IsScalarTower.toAlgHom L M' N
  let g : M →ₐ[K] N := (IsScalarTower.toAlgHom K M' N).comp f
  have h1 : {Q : HeightOneSpectrum (𝓞 g.fieldRange) |
      Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 g.fieldRange)) = 𝔭.asIdeal}.ncard =
      Module.finrank K g.fieldRange := by
    rw [ncard_over_congr g.equivFieldRange 𝔭, hsplit]
    exact g.equivFieldRange.toLinearEquiv.finrank_eq
  have hfix1 := GlobalTheory.T.frobenius_fixes_of_splitsCompletely_intermediate K N g.fieldRange 𝔭 h1
  have hfix2 : ∀ σ : N ≃ₐ[L] N, GlobalTheory.NT.IsFrob N 𝔓 σ → ∀ x ∈ ι.fieldRange, σ x = x := by
    intro σ hσ
    have hK : GlobalTheory.NT.IsFrob N 𝔭 (σ.restrictScalars K) := by
      obtain ⟨P, hP, hPo, hx⟩ := hσ
      refine ⟨P, hP, ⟨?_⟩, ?_⟩
      · rw [← hover, hPo.over, Ideal.under, Ideal.under, Ideal.comap_comap,
          ← IsScalarTower.algebraMap_eq]
      · intro x
        rw [← hnorm]
        exact hx x
    have hM1 := hfix1 (σ.restrictScalars K) hK
    have hg : (σ.toAlgHom.comp ι) = ι := hgen N _ _ (fun x => by
      have := hM1 (g x) ⟨x, rfl⟩
      exact this)
    rintro _ ⟨y, rfl⟩
    exact congrArg (fun h : M' →ₐ[L] N => h y) hg
  have h2 := GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix L N ι.fieldRange 𝔓 hfix2
  rw [← ncard_over_congr ι.equivFieldRange 𝔓, h2]
  exact ι.equivFieldRange.toLinearEquiv.finrank_eq.symm

/- English proof (translation)
Introduce `K L _ _ h S _ _ 𝔭 𝔓 hover hnorm hsplit`. Use `letI : Algebra K L := (IntermediateField.inclusion h).toRingHom.toAlgebra`. Use `haveI : IsScalarTower K L ℂ := IsScalarTower.of_algebraMap_eq (fun x => rfl)`. Use `letI : Algebra K (IntermediateField.adjoin L S) := ((algebraMap L (IntermediateField.adjoin L S)).comp (algebraMap K L)).toAlgebra`. Use `haveI : IsScalarTower K L (IntermediateField.adjoin L S) := IsScalarTower.of_algebraMap_eq' rfl`.

Establish `hle : IntermediateField.adjoin K S ≤ (IntermediateField.adjoin L S).restrictScalars K` using `IntermediateField.adjoin_le_iff.mpr (fun z hz => IntermediateField.subset_adjoin L S hz)`. Set `f : IntermediateField.adjoin K S →ₐ[K] IntermediateField.adjoin L S` to `{ toFun := fun x => ⟨x.1, hle x.2⟩ map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl commutes' := fun _ => rfl }`. Establish `hgen : ∀ (N : Type) [Field N] [Algebra L N] (g g' : IntermediateField.adjoin L S →ₐ[L] N), (∀ x, g (f x) = g' (f x)) → g = g'`. Introduce `N _ _ g g' hgg`. Apply `IntermediateField.adjoin_algHom_ext` to reduce the goal to its premises.

Introduce `x hx`. Conclude with `hgg ⟨x, IntermediateField.subset_adjoin K S hx⟩`. Establish `hover' : 𝔓.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = 𝔭.asIdeal`. Rewrite using `[← hover]`. Both sides reduce to the same expression.

Conclude with `ncard_eq_finrank_of_generated K L (IntermediateField.adjoin K S) (IntermediateField.adjoin L S) f hgen 𝔭 𝔓 hover' hnorm hsplit`.
-/
theorem ncard_eq_finrank_adjoin : ∀ (K L : IntermediateField ℚ ℂ) [NumberField K] [NumberField L] (h : K ≤ L) (S : Set ℂ) [NumberField (IntermediateField.adjoin K S)] [NumberField (IntermediateField.adjoin L S)] (𝔭 : HeightOneSpectrum (𝓞 K)) (𝔓 : HeightOneSpectrum (𝓞 L)), 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom) = 𝔭.asIdeal → Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal → {Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin K S)) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 (IntermediateField.adjoin K S))) = 𝔭.asIdeal}.ncard = Module.finrank K (IntermediateField.adjoin K S) → {Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin L S)) | Q.asIdeal.comap (algebraMap (𝓞 L) (𝓞 (IntermediateField.adjoin L S))) = 𝔓.asIdeal}.ncard = Module.finrank L (IntermediateField.adjoin L S) := by
  intro K L _ _ h S _ _ 𝔭 𝔓 hover hnorm hsplit
  letI : Algebra K L := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower K L ℂ := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  letI : Algebra K (IntermediateField.adjoin L S) :=
    ((algebraMap L (IntermediateField.adjoin L S)).comp (algebraMap K L)).toAlgebra
  haveI : IsScalarTower K L (IntermediateField.adjoin L S) := IsScalarTower.of_algebraMap_eq' rfl
  have hle : IntermediateField.adjoin K S ≤ (IntermediateField.adjoin L S).restrictScalars K :=
    IntermediateField.adjoin_le_iff.mpr (fun z hz => IntermediateField.subset_adjoin L S hz)
  let f : IntermediateField.adjoin K S →ₐ[K] IntermediateField.adjoin L S :=
    { toFun := fun x => ⟨x.1, hle x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hgen : ∀ (N : Type) [Field N] [Algebra L N] (g g' : IntermediateField.adjoin L S →ₐ[L] N),
      (∀ x, g (f x) = g' (f x)) → g = g' := by
    intro N _ _ g g' hgg
    apply IntermediateField.adjoin_algHom_ext
    intro x hx
    exact hgg ⟨x, IntermediateField.subset_adjoin K S hx⟩
  have hover' : 𝔓.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = 𝔭.asIdeal := by
    rw [← hover]
    rfl
  exact ncard_eq_finrank_of_generated K L (IntermediateField.adjoin K S) (IntermediateField.adjoin L S) f hgen
    𝔭 𝔓 hover' hnorm hsplit

end GlobalTheory.SplitCompositum
