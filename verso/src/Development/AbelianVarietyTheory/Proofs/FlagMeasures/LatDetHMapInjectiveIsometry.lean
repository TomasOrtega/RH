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
Set `e : A ≃ₗ[R] A.map f` to `Submodule.equivMapOfInjective f hf A`. Establish `he : (B.comap A.subtype).map (e : A →ₗ[R] A.map f) = (B.map f).comap (A.map f).subtype`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, ha⟩, haB, rfl⟩`.

Conclude with `⟨a, haB, rfl⟩`. Introduce `hz`. Take `⟨b, hb, hbz⟩` from `hz`. Take `⟨a, ha, haz⟩` from `z.2`. Take `rfl : a = b` from `hf (haz.trans hbz.symm)`.

Conclude with `⟨⟨a, ha⟩, hb, Subtype.ext haz⟩`. Conclude with `(Submodule.Quotient.equiv _ _ e he).length_eq.symm`.
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
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, a, ha, hax⟩`. Establish `hs0 : algebraMap R K s ≠ 0`. Introduce `h0`.

Apply `hs` to reduce the goal to its premises. Establish `: s = 0` using `hRK (by rw [h0, map_zero])`. Rewrite using `[this]`. Conclude with `p.zero_mem`. Use `⟨(algebraMap R K s)⁻¹ • a, ⟨s, hs, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← algebraMap_smul K s ((algebraMap R K s)⁻¹ • a), smul_smul, mul_inv_cancel₀ hs0, one_smul]`. Conclude with `ha`. Rewrite `hax`, the goal using `[LinearMap.restrictScalars_apply]`. Rewrite using `[map_smul, hax, ← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]`. Introduce and unpack `⟨y, ⟨s, hs, hsy⟩, rfl⟩`.

Conclude with `⟨s, hs, s • y, hsy, LinearMap.map_smul _ s y⟩`.
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
Unfold `Formalism.HermitianLatticesTheory.locLen`. Rewrite using `[localization_map₂ hRK i hi p A, localization_map₂ hRK i hi p B, length_quot_map (i.restrictScalars R) (by simpa using hi)]`.
-/
theorem locLen_map (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A B : Submodule R U) :
    Formalism.HermitianLatticesTheory.locLen p (A.map (i.restrictScalars R)) (B.map (i.restrictScalars R)) =
      Formalism.HermitianLatticesTheory.locLen p A B := by
  unfold Formalism.HermitianLatticesTheory.locLen
  rw [localization_map₂ hRK i hi p A, localization_map₂ hRK i hi p B,
    length_quot_map (i.restrictScalars R) (by simpa using hi)]

/- English proof (translation)
Establish `hi' : Function.Injective (i.restrictScalars R)` using `by simpa using hi`. Unfold `Formalism.HermitianLatticesTheory.lidx`. Rewrite using `[← Submodule.map_inf _ hi', locLen_map hRK i hi, locLen_map hRK i hi]`.
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
Establish `hRK : Function.Injective (algebraMap (𝓞 K) K)` using `IsFractionRing.injective (𝓞 K) K`. Unfold `genIdxH`. Use `finprod_congr fun P => ?_` and prove the remaining obligations. Use `haveI := P.isPrime`. Rewrite using `[lidx_map hRK i hi]`.
-/
theorem genIdxH_map (i : U →ₗ[K] V) (hi : Function.Injective i) (A B : Submodule (𝓞 K) U) :
    genIdxH (A.map (i.restrictScalars (𝓞 K))) (B.map (i.restrictScalars (𝓞 K))) = genIdxH A B := by
  have hRK : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  unfold genIdxH
  refine finprod_congr fun P => ?_
  haveI := P.isPrime
  rw [lidx_map hRK i hi]

/- English proof (translation)
Simplify using `[Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]`.
-/
theorem mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

/- English proof (translation)
Establish `hspan : (Submodule.span K ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) = (Submodule.span K (N : Set U)).map i`. Rewrite using `[Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image]`. Use extensionality with `x`. Simplify using `only [dualInH, Submodule.mem_inf, Submodule.restrictScalars_mem, hspan, mem_dual, Submodule.mem_map, LinearMap.coe_restrictScalars]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hx, y, hy, rfl⟩`. Use `⟨y, ⟨fun n hn => ?_, hy⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[← hiso]`. Conclude with `hx (i n) ⟨n, hn, rfl⟩`. Introduce and unpack `⟨y, ⟨hy, hys⟩, rfl⟩`.

Use `⟨?_, y, hys, rfl⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Rewrite using `[hiso]`. Conclude with `hy n hn`.
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
Introduce `K U V _ _ _ _ _ _ _ _ _ _ _ hU hV i hi hiso N`. Unfold `latDetH`. Rewrite using `[dualInH_map hU hV i hiso, genIdxH_map i hi]`.
-/
theorem latDetH_map : ∀ (K U V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V), Function.Injective i → (∀ x y, hV (i x) (i y) = hU x y) → ∀ N : Submodule (𝓞 K) U, latDetH hV (N.map (i.restrictScalars (𝓞 K))) = latDetH hU N := by
  intro K U V _ _ _ _ _ _ _ _ _ _ _ hU hV i hi hiso N
  unfold latDetH
  rw [dualInH_map hU hV i hiso, genIdxH_map i hi]

end GlobalTheory.LoopC.DetMap
