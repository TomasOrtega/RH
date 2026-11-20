import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegralClosureOfFormallyUnramified
open IsLocalRing
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.NormFin

/- English proof (translation)
Introduce `S K L D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`. Set `K'` to `FractionRing D`. Use `haveI : IsScalarTower S D K' := inferInstance`. Establish `hSK' : Function.Injective (algebraMap S K')`. Rewrite using `[IsScalarTower.algebraMap_eq S D K']`.

Conclude with `(IsFractionRing.injective D K').comp (FaithfulSMul.algebraMap_injective S D)`. Use `letI : Algebra K K' := (IsFractionRing.lift hSK' : K →+* K').toAlgebra`. Use `haveI : IsScalarTower S K K' := IsScalarTower.of_algebraMap_eq (fun x => (IsFractionRing.lift_algebraMap hSK' x).symm)`. Use `haveI : SMulCommClass K D K' := ⟨fun a b c => by simp only [Algebra.smul_def]; ring⟩`. Use `haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L`.

Use `haveI : Algebra.FormallyUnramified K' (K' ⊗[K] L) := inferInstance`. Use `haveI : FiniteDimensional K' (K' ⊗[K] L) := inferInstance`. Use `haveI : IsScalarTower D K' (K' ⊗[K] L) := inferInstance`. Establish `hfinC : Module.Finite D (integralClosure D (K' ⊗[K] L))` using `GlobalTheory.AbhFin.finite_integralClosure_of_formallyUnramified D K' (K' ⊗[K] L)`. Use `haveI : Module.Flat S K := IsLocalization.flat K (nonZeroDivisors S)`.

Use `haveI : Module.Flat S L := Module.Flat.trans S K L`. Set `f : D →ₐ[S] K'` to `IsScalarTower.toAlgHom S D K'`. Set `Φ : D ⊗[S] L →ₐ[S] K' ⊗[S] L` to `Algebra.TensorProduct.map f (AlgHom.id S L)`. Establish `hΦ : Function.Injective Φ`. Establish `h1 : Function.Injective (f.toLinearMap.rTensor L)` using `Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective D K')`.

Establish `h2 : (Φ : D ⊗[S] L → K' ⊗[S] L) = f.toLinearMap.rTensor L`. Use function extensionality and compare the values at `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => rfl`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Rewrite using `[h2]`. Conclude with `h1`. Set `ι : K' ⊗[S] L ≃ₐ[K] K' ⊗[K] L` to `(IsLocalization.algebraTensorEquiv (nonZeroDivisors S) K K' L).symm`. Establish `hι : ∀ (a : K') (b : L), ι (a ⊗ₜ[S] b) = a ⊗ₜ[K] b`.

Introduce `a b`. Rewrite using `[AlgEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Set `Ψ : D ⊗[S] L →ₐ[D] K' ⊗[K] L` to `{ (ι.toRingEquiv.toRingHom.comp Φ.toRingHom) with commutes' := fun d => by show ι (Φ (d ⊗ₜ[S] 1)) = (algebraMap D K' d) ⊗ₜ[K] 1`. Rewrite using `[Algebra.TensorProduct.map_tmul]`.

Conclude with `hι _ _ }`. Establish `hΨ : Function.Injective Ψ` using `ι.injective.comp hΦ`. Set `M` to `integralClosure D (D ⊗[S] L)`. Set `lin : M →ₗ[D] integralClosure D (K' ⊗[K] L)` to `{ toFun := fun x => ⟨Ψ (x : D ⊗[S] L), (show IsIntegral D (x : D ⊗[S] L) from x.2).map Ψ⟩ map_add' := fun x y => Subtype.ext (map_add Ψ (x : D ⊗[S] L) y) map_smul' := fun r x => Subtype.ext (map_smul Ψ r (x : D ⊗[S] L)) }`. Conclude with `Module.Finite.of_injective lin (fun x y h => Subtype.ext (hΨ (congrArg Subtype.val h)))`.
-/
theorem main : ∀ (S K L D : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra S D] [Module.Finite S D] [FaithfulSMul S D],
    Module.Finite D (integralClosure D (TensorProduct S D L)) := by
  intro S K L D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  classical
  let K' := FractionRing D
  haveI : IsScalarTower S D K' := inferInstance
  have hSK' : Function.Injective (algebraMap S K') :=
    by
      rw [IsScalarTower.algebraMap_eq S D K']
      exact (IsFractionRing.injective D K').comp (FaithfulSMul.algebraMap_injective S D)
  letI : Algebra K K' := (IsFractionRing.lift hSK' : K →+* K').toAlgebra
  haveI : IsScalarTower S K K' :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsFractionRing.lift_algebraMap hSK' x).symm)
  haveI : SMulCommClass K D K' := ⟨fun a b c => by simp only [Algebra.smul_def]; ring⟩
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  haveI : Algebra.FormallyUnramified K' (K' ⊗[K] L) := inferInstance
  haveI : FiniteDimensional K' (K' ⊗[K] L) := inferInstance
  haveI : IsScalarTower D K' (K' ⊗[K] L) := inferInstance
  have hfinC : Module.Finite D (integralClosure D (K' ⊗[K] L)) :=
    GlobalTheory.AbhFin.finite_integralClosure_of_formallyUnramified D K' (K' ⊗[K] L)
  haveI : Module.Flat S K := IsLocalization.flat K (nonZeroDivisors S)
  haveI : Module.Flat S L := Module.Flat.trans S K L
  let f : D →ₐ[S] K' := IsScalarTower.toAlgHom S D K'
  let Φ : D ⊗[S] L →ₐ[S] K' ⊗[S] L := Algebra.TensorProduct.map f (AlgHom.id S L)
  have hΦ : Function.Injective Φ := by
    have h1 : Function.Injective (f.toLinearMap.rTensor L) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective D K')
    have h2 : (Φ : D ⊗[S] L → K' ⊗[S] L) = f.toLinearMap.rTensor L := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [h2]; exact h1
  let ι : K' ⊗[S] L ≃ₐ[K] K' ⊗[K] L := (IsLocalization.algebraTensorEquiv (nonZeroDivisors S) K K' L).symm
  have hι : ∀ (a : K') (b : L), ι (a ⊗ₜ[S] b) = a ⊗ₜ[K] b := by
    intro a b
    rw [AlgEquiv.symm_apply_eq]
    rfl
  let Ψ : D ⊗[S] L →ₐ[D] K' ⊗[K] L :=
    { (ι.toRingEquiv.toRingHom.comp Φ.toRingHom) with
      commutes' := fun d => by
        show ι (Φ (d ⊗ₜ[S] 1)) = (algebraMap D K' d) ⊗ₜ[K] 1
        rw [Algebra.TensorProduct.map_tmul]
        exact hι _ _ }
  have hΨ : Function.Injective Ψ := ι.injective.comp hΦ
  let M := integralClosure D (D ⊗[S] L)
  let lin : M →ₗ[D] integralClosure D (K' ⊗[K] L) :=
    { toFun := fun x => ⟨Ψ (x : D ⊗[S] L), (show IsIntegral D (x : D ⊗[S] L) from x.2).map Ψ⟩
      map_add' := fun x y => Subtype.ext (map_add Ψ (x : D ⊗[S] L) y)
      map_smul' := fun r x => Subtype.ext (map_smul Ψ r (x : D ⊗[S] L)) }
  exact Module.Finite.of_injective lin (fun x y h => Subtype.ext (hΨ (congrArg Subtype.val h)))

end GlobalTheory.NormFin
