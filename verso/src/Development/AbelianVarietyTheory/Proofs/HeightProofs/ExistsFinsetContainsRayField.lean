import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldOfRay
open NumberField IsDedekindDomain GlobalTheory.Mem

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RayOnto

/- English proof (translation)
Introduce `P hP`. Use `letI : Algebra L L' := τ.toAlgebra`. Set `Q : HeightOneSpectrum (𝓞 L)` to `P.under (𝓞 L)`. Establish `hQ : Q.asIdeal = P.asIdeal.comap (RingOfIntegers.mapRingHom τ)` using `rfl`. Use `haveI hPo : P.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩`.

Establish `hn : ((n : ℕ) : 𝓞 L) ∉ Q.asIdeal` using `fun h' => hP (by`. Rewrite `h'` using `[hQ, Ideal.mem_comap, map_natCast]`. Conclude with `h')`. Take `⟨f, α, h1, h2, h3⟩` from `h Q hn`. Establish `hf` using `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal Q.asIdeal Q.isPrime Q.ne_bot`.

Establish `hcm : P.asIdeal.comap (RingOfIntegers.mapRingHom (τ.comp φ)) = Q.asIdeal.comap (RingOfIntegers.mapRingHom φ)`. Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[hcm]`. Use `⟨f * Q.asIdeal.inertiaDeg' P.asIdeal, α ^ Q.asIdeal.inertiaDeg' P.asIdeal, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hf, h1, ← pow_mul]`. Rewrite using `[pow_mul, h2, Ideal.span_singleton_pow]`. Use `sub_dvd_pow_sub_pow α 1 (Q.asIdeal.inertiaDeg' P.asIdeal)` as an intermediate fact. Rewrite `this` using `[one_pow]`. Conclude with `dvd_trans h3 this`.
-/
theorem containsRayField_comp {K L L' : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field L'] [NumberField L']
    (φ : K →+* L) (τ : L →+* L') (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (τ.comp φ) n := by
  intro P hP
  letI : Algebra L L' := τ.toAlgebra
  let Q : HeightOneSpectrum (𝓞 L) := P.under (𝓞 L)
  have hQ : Q.asIdeal = P.asIdeal.comap (RingOfIntegers.mapRingHom τ) := rfl
  haveI hPo : P.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  have hn : ((n : ℕ) : 𝓞 L) ∉ Q.asIdeal := fun h' => hP (by
    rw [hQ, Ideal.mem_comap, map_natCast] at h'
    exact h')
  obtain ⟨f, α, h1, h2, h3⟩ := h Q hn
  have hf := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal Q.asIdeal Q.isPrime Q.ne_bot
  have hcm : P.asIdeal.comap (RingOfIntegers.mapRingHom (τ.comp φ)) =
      Q.asIdeal.comap (RingOfIntegers.mapRingHom φ) := by
    ext x
    rfl
  rw [hcm]
  refine ⟨f * Q.asIdeal.inertiaDeg' P.asIdeal, α ^ Q.asIdeal.inertiaDeg' P.asIdeal, ?_, ?_, ?_⟩
  · rw [hf, h1, ← pow_mul]
  · rw [pow_mul, h2, Ideal.span_singleton_pow]
  · have := sub_dvd_pow_sub_pow α 1 (Q.asIdeal.inertiaDeg' P.asIdeal)
    rw [one_pow] at this
    exact dvd_trans h3 this

/- English proof (translation)
Introduce `hR P M hM`. Set `φK : P.host.K →+* ℂ` to `P.host.φ₀.comp (algebraMap P.host.K P.host.E)`. Take `⟨Rf, hRf⟩` from `GlobalTheory.Mem.Fld.exists_isRayFieldIn φK hR (GlobalTheory.Mem.Fld.natIdeal_ne_bot (E := P.host.K) hM)`. Use `haveI : NumberField Rf := hRf.numberField`. Set `b` to `Module.finBasis ℚ Rf`.

Use `⟨Finset.univ.image (fun i => (b i : ℂ)), ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hz`. Establish `h : IsAlgebraic ℚ (b i)` using `Algebra.IsAlgebraic.isAlgebraic _`. Conclude with `h.algHom Rf.val`.

Introduce `L _ _ σ φ hσφ hS`. Take `⟨hm, hNF, hray⟩` from `hRf`. Use `letI := GlobalTheory.Mem.Fld.algOf φK Rf hm`. Take `⟨hab, hun, -, hart⟩` from `hray`. Use `haveI : IsGalois P.host.K Rf := hab.toIsGalois`.

Establish `hc : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap P.host.K Rf) M` using `GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray (K := P.host.K) (L := Rf) M hun (fun I hI hc hχ => (hart I hI hc).1 hχ)`. Establish `hle : Rf ≤ σ.toRatAlgHom.fieldRange`. Introduce `z hz`. Establish `hsum` using `congrArg Subtype.val (b.sum_repr ⟨z, hz⟩)`. Rewrite `hsum` using `[IntermediateField.coe_sum]`.

Simplify using `only [IntermediateField.coe_smul] at hsum`. Rewrite using `[← hsum]`. Use `sum_mem fun i _ => IntermediateField.smul_mem _ ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `hS (b i) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)`. Conclude with `⟨y, hy⟩`.

Set `e : L ≃ₐ[ℚ] σ.toRatAlgHom.fieldRange` to `AlgEquiv.ofInjectiveField σ.toRatAlgHom`. Set `τ : Rf →+* L` to `(e.symm : σ.toRatAlgHom.fieldRange →+* L).comp (IntermediateField.inclusion hle : Rf →+* σ.toRatAlgHom.fieldRange)`. Establish `key : ∀ w, σ (e.symm w) = (w : ℂ)` using `fun w => by conv_rhs => rw [← e.apply_symm_apply w]`. Both sides reduce to the same expression. Establish `hτ : τ.comp (algebraMap P.host.K Rf) = φ`.

Use extensionality with `x`. Apply `σ.injective` to reduce the goal to its premises. Establish `h1 : σ (φ x) = φK x` using `RingHom.congr_fun hσφ x`. Rewrite using `[h1]`. Conclude with `key _`.

Rewrite using `[← hτ]`. Conclude with `containsRayField_comp _ τ M hc`.
-/
theorem exists_finset_containsRayField : GlobalTheory.NT.RayField → ∀ (P : Pre) (M : ℕ), M ≠ 0 → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (φ : P.host.K →+* L), σ.comp φ = P.host.φ₀.comp (algebraMap P.host.K P.host.E) → (∀ z ∈ S, ∃ x, σ x = z) → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ M := by
  intro hR P M hM
  let φK : P.host.K →+* ℂ := P.host.φ₀.comp (algebraMap P.host.K P.host.E)
  obtain ⟨Rf, hRf⟩ := GlobalTheory.Mem.Fld.exists_isRayFieldIn φK hR (GlobalTheory.Mem.Fld.natIdeal_ne_bot (E := P.host.K) hM)
  haveI : NumberField Rf := hRf.numberField
  let b := Module.finBasis ℚ Rf
  refine ⟨Finset.univ.image (fun i => (b i : ℂ)), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    have h : IsAlgebraic ℚ (b i) := Algebra.IsAlgebraic.isAlgebraic _
    exact h.algHom Rf.val
  · intro L _ _ σ φ hσφ hS
    obtain ⟨hm, hNF, hray⟩ := hRf
    letI := GlobalTheory.Mem.Fld.algOf φK Rf hm
    obtain ⟨hab, hun, -, hart⟩ := hray
    haveI : IsGalois P.host.K Rf := hab.toIsGalois
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap P.host.K Rf) M :=
      GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray (K := P.host.K) (L := Rf) M hun
        (fun I hI hc hχ => (hart I hI hc).1 hχ)
    have hle : Rf ≤ σ.toRatAlgHom.fieldRange := by
      intro z hz
      have hsum := congrArg Subtype.val (b.sum_repr ⟨z, hz⟩)
      rw [IntermediateField.coe_sum] at hsum
      simp only [IntermediateField.coe_smul] at hsum
      rw [← hsum]
      refine sum_mem fun i _ => IntermediateField.smul_mem _ ?_
      obtain ⟨y, hy⟩ := hS (b i) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
      exact ⟨y, hy⟩
    let e : L ≃ₐ[ℚ] σ.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField σ.toRatAlgHom
    let τ : Rf →+* L := (e.symm : σ.toRatAlgHom.fieldRange →+* L).comp
      (IntermediateField.inclusion hle : Rf →+* σ.toRatAlgHom.fieldRange)
    have key : ∀ w, σ (e.symm w) = (w : ℂ) := fun w => by
      conv_rhs => rw [← e.apply_symm_apply w]
      rfl
    have hτ : τ.comp (algebraMap P.host.K Rf) = φ := by
      ext x
      apply σ.injective
      have h1 : σ (φ x) = φK x := RingHom.congr_fun hσφ x
      rw [h1]
      exact key _
    rw [← hτ]
    exact containsRayField_comp _ τ M hc

end GlobalTheory.RayOnto
