import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open Matrix
open scoped TensorProduct

namespace GlobalTheory.FinIsoProof

open GlobalTheory.DefU.ClassFin GlobalTheory.AdeleBaseChange

/- English proof (translation)
Take `⟨ι, hι⟩` from `exists_toAd (maximalRealSubfield L) L`. Set `κ : AL L ≃+* FiniteAdeleRing (𝓞 L) L` to `RingEquiv.ofBijective ι ⟨map_injective hι, map_surjective hι⟩`. Establish `hκ : ∀ x a, κ (x ⊗ₜ a) = algebraMap L _ x * adMap (maximalRealSubfield L) L a` using `hι`. Establish `hc : ∀ y, κ (conjAL L y) = conjFin (cc L) (κ y)`. Introduce `y`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul x a`. Express the relevant statement in the definitionally equal form `κ ((IsCMField.complexConj L x) ⊗ₜ a) = _`.

Rewrite using `[hκ, hκ, map_mul, conjFin_adMap (cc L) (fun k => IsCMField.complexConj_apply_eq_self L k), conjFin_algebraMap]`. Both sides reduce to the same expression. Establish `hc' : ∀ y, κ.symm (conjFin (cc L) y) = conjAL L (κ.symm y)` using `fun y => by`. Rewrite using `[RingEquiv.symm_apply_eq, hc, RingEquiv.apply_symm_apply]`. Set `p : GAf L n →* GL (Fin n) (FiniteAdeleRing (𝓞 L) L)` to `(GeneralLinearGroup.map κ.toRingHom).comp (ReciprocityTheory.Aut.GA L n).subtype`.

Establish `hp : ∀ x, Formalism.UG.cT (conjFin (cc L)) (p x).val * (p x).val = 1` using `fun x => unitary_map κ.toRingHom (conjAL L) (conjFin (cc L)) hc x.1.val (mul_eq_one_comm.mp x.2)`. Set `j : GAf L n →* UA L n` to `((finGL L n).comp p).codRestrict (UA L n) fun x => finGL_mem_UA _ (hp x)`. Use `⟨⟨κ, map_tmul_one hι, ?_, j, fun x => MonoidHom.mem_ker.2 (pInf_finGL (p x)), ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `w v h`. Establish `hv : w.under (𝓞 (maximalRealSubfield L)) = v` using `HeightOneSpectrum.ext h`.

Substitute `hv` using the available equality. Use `⟨locMap _ w, GlobalTheory.LFun.InertChart.continuous_complMap (rfl : w.under (𝓞 (maximalRealSubfield L)) = _), fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hκ, map_one, one_mul]`. Both sides reduce to the same expression. Introduce `x w s t`.

Establish `h1 : (finGL L n (p x)).val.map (pFin L) = (p x).val` using `congrArg Units.val (pFin_finGL (p x))`. Conclude with `congrArg (pLoc L w) (congrFun₂ h1 s t)`. Introduce `y hy`. Set `z` to `GeneralLinearGroup.map (pFin L) y.1`. Establish `hz : Formalism.UG.cT (conjFin (cc L)) z.val * z.val = 1` using `cT_pFin y`.

Establish `hm : GeneralLinearGroup.map κ.symm.toRingHom z ∈ ReciprocityTheory.Aut.GA L n` using `mul_eq_one_comm.mp (unitary_map κ.symm.toRingHom _ _ hc' z.val hz)`. Use `⟨⟨_, hm⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `e : p ⟨_, hm⟩ = z` using `Units.ext (Matrix.ext fun i k => κ.apply_symm_apply _)`. Express the relevant statement in the definitionally equal form `finGL L n (p ⟨_, hm⟩) = _`. Rewrite using `[e]`.

Conclude with `finGL_pFin ⟨y, hy⟩`.
-/
theorem nonempty_finIso (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : Nonempty (FinIso L n) := by
  obtain ⟨ι, hι⟩ := exists_toAd (maximalRealSubfield L) L
  let κ : AL L ≃+* FiniteAdeleRing (𝓞 L) L := RingEquiv.ofBijective ι ⟨map_injective hι, map_surjective hι⟩
  have hκ : ∀ x a, κ (x ⊗ₜ a) = algebraMap L _ x * adMap (maximalRealSubfield L) L a := hι
  have hc : ∀ y, κ (conjAL L y) = conjFin (cc L) (κ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul x a =>
      change κ ((IsCMField.complexConj L x) ⊗ₜ a) = _
      rw [hκ, hκ, map_mul, conjFin_adMap (cc L) (fun k => IsCMField.complexConj_apply_eq_self L k), conjFin_algebraMap]
      rfl
  have hc' : ∀ y, κ.symm (conjFin (cc L) y) = conjAL L (κ.symm y) := fun y => by
    rw [RingEquiv.symm_apply_eq, hc, RingEquiv.apply_symm_apply]
  let p : GAf L n →* GL (Fin n) (FiniteAdeleRing (𝓞 L) L) :=
    (GeneralLinearGroup.map κ.toRingHom).comp (ReciprocityTheory.Aut.GA L n).subtype
  have hp : ∀ x, Formalism.UG.cT (conjFin (cc L)) (p x).val * (p x).val = 1 := fun x =>
    unitary_map κ.toRingHom (conjAL L) (conjFin (cc L)) hc x.1.val (mul_eq_one_comm.mp x.2)
  let j : GAf L n →* UA L n := ((finGL L n).comp p).codRestrict (UA L n) fun x => finGL_mem_UA _ (hp x)
  refine ⟨⟨κ, map_tmul_one hι, ?_, j, fun x => MonoidHom.mem_ker.2 (pInf_finGL (p x)), ?_, ?_⟩⟩
  · intro w v h
    have hv : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext h
    subst hv
    refine ⟨locMap _ w, GlobalTheory.LFun.InertChart.continuous_complMap (rfl : w.under (𝓞 (maximalRealSubfield L)) = _), fun a => ?_⟩
    rw [hκ, map_one, one_mul]
    rfl
  · intro x w s t
    have h1 : (finGL L n (p x)).val.map (pFin L) = (p x).val := congrArg Units.val (pFin_finGL (p x))
    exact congrArg (pLoc L w) (congrFun₂ h1 s t)
  · intro y hy
    let z := GeneralLinearGroup.map (pFin L) y.1
    have hz : Formalism.UG.cT (conjFin (cc L)) z.val * z.val = 1 := cT_pFin y
    have hm : GeneralLinearGroup.map κ.symm.toRingHom z ∈ ReciprocityTheory.Aut.GA L n :=
      mul_eq_one_comm.mp (unitary_map κ.symm.toRingHom _ _ hc' z.val hz)
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    have e : p ⟨_, hm⟩ = z := Units.ext (Matrix.ext fun i k => κ.apply_symm_apply _)
    change finGL L n (p ⟨_, hm⟩) = _
    rw [e]
    exact finGL_pFin ⟨y, hy⟩

/- English proof (translation)
Introduce `L _ _ _ n` and use `nonempty_finIso L n`.
-/
theorem finIso_nonempty : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), Nonempty (FinIso L n) :=
  fun L _ _ _ n => nonempty_finIso L n

end GlobalTheory.FinIsoProof
