import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.DetMap

section General

variable {R K U V : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup U] [Module K U] [Module R U] [IsScalarTower R K U]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem length_quot_map (f : U →ₗ[R] V) (hf : Function.Injective f) (A B : Submodule R U) :
    Module.length R ((A.map f) ⧸ (B.map f).comap (A.map f).subtype) =
      Module.length R (A ⧸ B.comap A.subtype) := by
  let e : A ≃ₗ[R] A.map f := Submodule.equivMapOfInjective f hf A
  have he : (B.comap A.subtype).map (e : A →ₗ[R] A.map f) = (B.map f).comap (A.map f).subtype := by
    ext z
    constructor
    · rintro ⟨⟨a, ha⟩, haB, rfl⟩
      exact ⟨a, haB, rfl⟩
    · intro hz
      obtain ⟨b, hb, hbz⟩ := hz
      obtain ⟨a, ha, haz⟩ := z.2
      obtain rfl : a = b := hf (haz.trans hbz.symm)
      exact ⟨⟨a, ha⟩, hb, Subtype.ext haz⟩
  exact (Submodule.Quotient.equiv _ _ e he).length_eq.symm

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem localization_map₂ (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A : Submodule R U) :
    Formalism.HermitianLatticesTheory.localization₂ p (A.map (i.restrictScalars R)) = (Formalism.HermitianLatticesTheory.localization₂ p A).map (i.restrictScalars R) := by
  ext x
  constructor
  · rintro ⟨s, hs, a, ha, hax⟩
    have hs0 : algebraMap R K s ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := hRK (by rw [h0, map_zero])
      rw [this]
      exact p.zero_mem
    refine ⟨(algebraMap R K s)⁻¹ • a, ⟨s, hs, ?_⟩, ?_⟩
    · rw [← algebraMap_smul K s ((algebraMap R K s)⁻¹ • a), smul_smul, mul_inv_cancel₀ hs0, one_smul]
      exact ha
    · rw [LinearMap.restrictScalars_apply] at hax ⊢
      rw [map_smul, hax, ← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  · rintro ⟨y, ⟨s, hs, hsy⟩, rfl⟩
    exact ⟨s, hs, s • y, hsy, LinearMap.map_smul _ s y⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem locLen_map (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A B : Submodule R U) :
    Formalism.HermitianLatticesTheory.locLen p (A.map (i.restrictScalars R)) (B.map (i.restrictScalars R)) =
      Formalism.HermitianLatticesTheory.locLen p A B := by
  unfold Formalism.HermitianLatticesTheory.locLen
  rw [localization_map₂ hRK i hi p A, localization_map₂ hRK i hi p B,
    length_quot_map (i.restrictScalars R) (by simpa using hi)]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem lidx_map (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A B : Submodule R U) :
    Formalism.HermitianLatticesTheory.lidx p (A.map (i.restrictScalars R)) (B.map (i.restrictScalars R)) =
      Formalism.HermitianLatticesTheory.lidx p A B := by
  have hi' : Function.Injective (i.restrictScalars R) := by simpa using hi
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [← Submodule.map_inf _ hi', locLen_map hRK i hi, locLen_map hRK i hi]

end General

section NumberField

variable {K U V : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem genIdxH_map (i : U →ₗ[K] V) (hi : Function.Injective i) (A B : Submodule (𝓞 K) U) :
    genIdxH (A.map (i.restrictScalars (𝓞 K))) (B.map (i.restrictScalars (𝓞 K))) = genIdxH A B := by
  have hRK : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  unfold genIdxH
  refine finprod_congr fun P => ?_
  haveI := P.isPrime
  rw [lidx_map hRK i hi]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dualInH_map (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V)
    (hiso : ∀ x y, hV (i x) (i y) = hU x y) (N : Submodule (𝓞 K) U) :
    dualInH hV (N.map (i.restrictScalars (𝓞 K))) =
      (dualInH hU N).map (i.restrictScalars (𝓞 K)) := by
  have hspan : (Submodule.span K ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) =
      (Submodule.span K (N : Set U)).map i := by
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image]
  ext x
  simp only [dualInH, Submodule.mem_inf, Submodule.restrictScalars_mem, hspan, mem_dual,
    Submodule.mem_map, LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    refine ⟨y, ⟨fun n hn => ?_, hy⟩, rfl⟩
    rw [← hiso]
    exact hx (i n) ⟨n, hn, rfl⟩
  · rintro ⟨y, ⟨hy, hys⟩, rfl⟩
    refine ⟨?_, y, hys, rfl⟩
    rintro _ ⟨n, hn, rfl⟩
    rw [hiso]
    exact hy n hn

end NumberField

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem latDetH_map : ∀ (K U V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V), Function.Injective i → (∀ x y, hV (i x) (i y) = hU x y) → ∀ N : Submodule (𝓞 K) U, latDetH hV (N.map (i.restrictScalars (𝓞 K))) = latDetH hU N := by
  intro K U V _ _ _ _ _ _ _ _ _ _ _ hU hV i hi hiso N
  unfold latDetH
  rw [dualInH_map hU hV i hiso, genIdxH_map i hi]

end GlobalTheory.LoopC.DetMap
