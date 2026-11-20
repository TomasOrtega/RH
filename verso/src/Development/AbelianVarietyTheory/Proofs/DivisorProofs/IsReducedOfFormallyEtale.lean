import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularAdjoinRoots

open IsLocalRing TensorProduct

namespace GlobalTheory.RootFibre

section
variable (R K L : Type) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
include K

end

variable (R L Q : Type) [CommRing R] [CommRing L] [Algebra R L] [CommRing Q] [Algebra R Q] [IsDomain Q]

noncomputable def toFrac : Q ⊗[R] L →ₐ[Q] FractionRing Q ⊗[R] L :=
  Algebra.TensorProduct.map (Algebra.ofId Q (FractionRing Q)) (AlgHom.id R L)

/- English proof (translation)
Establish `h` using `Module.Flat.rTensor_preserves_injective_linearMap (M := L) ((IsScalarTower.toAlgHom R Q (FractionRing Q)).toLinearMap) (IsFractionRing.injective Q (FractionRing Q))`. Establish `e : ⇑(toFrac R L Q) = ⇑(LinearMap.rTensor L (IsScalarTower.toAlgHom R Q (FractionRing Q)).toLinearMap)`. Use function extensionality and compare the values at `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b => simp [toFrac]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem toFrac_injective [Module.Flat R L] : Function.Injective (toFrac R L Q) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := L)
    ((IsScalarTower.toAlgHom R Q (FractionRing Q)).toLinearMap)
    (IsFractionRing.injective Q (FractionRing Q))
  have e : ⇑(toFrac R L Q) =
      ⇑(LinearMap.rTensor L (IsScalarTower.toAlgHom R Q (FractionRing Q)).toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [toFrac]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [e]; exact h

/- English proof (translation)
Establish `: Algebra.EssFiniteType (FractionRing Q) (FractionRing Q ⊗[R] L)` using `Algebra.EssFiniteType.baseChange R L (FractionRing Q)`. Establish `hfin : Module.Finite (FractionRing Q) (FractionRing Q ⊗[R] L)` using `Algebra.FormallyUnramified.finite_of_free _ _`. Take `⟨I, _, A, _, _, e, hsep⟩` from `(Algebra.FormallyEtale.iff_exists_algEquiv_prod (FractionRing Q) (FractionRing Q ⊗[R] L)).1 inferInstance`. Use `letI : ∀ i, Algebra Q (A i) := fun i => ((algebraMap (FractionRing Q) (A i)).comp (algebraMap Q (FractionRing Q))).toAlgebra`. Use `haveI : ∀ i, IsScalarTower Q (FractionRing Q) (A i) := fun i => IsScalarTower.of_algebraMap_eq (fun _ => rfl)`.

Use `haveI : ∀ i, FiniteDimensional (FractionRing Q) (A i) := fun i => Module.Finite.of_surjective ((Pi.evalAlgHom (FractionRing Q) A i).comp e.toAlgHom).toLinearMap (fun a => ⟨e.symm (Pi.single i a), by simp⟩)`. Use `haveI : ∀ i, IsNoetherian Q (integralClosure Q (A i)) := fun i => IsIntegralClosure.isNoetherian Q (FractionRing Q) (A i) (integralClosure Q (A i))`. Set `g : Q ⊗[R] L →ₐ[Q] (∀ i, A i)` to `((e.toAlgHom).restrictScalars Q).comp (toFrac R L Q)`. Establish `hg : Function.Injective g` using `e.injective.comp (toFrac_injective R L Q)`. Set `ψ : integralClosure Q (Q ⊗[R] L) →ₗ[Q] (∀ i, integralClosure Q (A i))` to `{ toFun := fun y i => ⟨g y i, ((y.2.map g).map (Pi.evalAlgHom Q A i))⟩ map_add' := fun a b => by ext i; simp map_smul' := fun c a => by ext i; simp }`.

Establish `hψ : Function.Injective ψ`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hg` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Use `congrArg (fun f => ((f i : A i))) hab` as an intermediate fact. Simplify `this` using `[ψ]`. Establish `: IsNoetherian Q (integralClosure Q (Q ⊗[R] L))` using `isNoetherian_of_injective ψ hψ`. Conclude with `Module.IsNoetherian.finite Q _`.
-/
theorem finite_integralClosure [Module.Flat R L] [Algebra.FormallyEtale R L] [Algebra.EssFiniteType R L]
    [IsIntegrallyClosed Q] [IsNoetherianRing Q] :
    Module.Finite Q (integralClosure Q (Q ⊗[R] L)) := by
  classical
  have : Algebra.EssFiniteType (FractionRing Q) (FractionRing Q ⊗[R] L) :=
    Algebra.EssFiniteType.baseChange R L (FractionRing Q)
  have hfin : Module.Finite (FractionRing Q) (FractionRing Q ⊗[R] L) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  obtain ⟨I, _, A, _, _, e, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod (FractionRing Q) (FractionRing Q ⊗[R] L)).1
      inferInstance
  letI : ∀ i, Algebra Q (A i) := fun i =>
    ((algebraMap (FractionRing Q) (A i)).comp (algebraMap Q (FractionRing Q))).toAlgebra
  haveI : ∀ i, IsScalarTower Q (FractionRing Q) (A i) := fun i =>
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : ∀ i, FiniteDimensional (FractionRing Q) (A i) := fun i =>
    Module.Finite.of_surjective ((Pi.evalAlgHom (FractionRing Q) A i).comp e.toAlgHom).toLinearMap
      (fun a => ⟨e.symm (Pi.single i a), by simp⟩)
  haveI : ∀ i, IsNoetherian Q (integralClosure Q (A i)) := fun i =>
    IsIntegralClosure.isNoetherian Q (FractionRing Q) (A i) (integralClosure Q (A i))
  let g : Q ⊗[R] L →ₐ[Q] (∀ i, A i) :=
    ((e.toAlgHom).restrictScalars Q).comp (toFrac R L Q)
  have hg : Function.Injective g := e.injective.comp (toFrac_injective R L Q)
  let ψ : integralClosure Q (Q ⊗[R] L) →ₗ[Q] (∀ i, integralClosure Q (A i)) :=
    { toFun := fun y i => ⟨g y i, ((y.2.map g).map (Pi.evalAlgHom Q A i))⟩
      map_add' := fun a b => by ext i; simp
      map_smul' := fun c a => by ext i; simp }
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    apply hg
    funext i
    have := congrArg (fun f => ((f i : A i))) hab
    simpa [ψ] using this
  have : IsNoetherian Q (integralClosure Q (Q ⊗[R] L)) := isNoetherian_of_injective ψ hψ
  exact Module.IsNoetherian.finite Q _

end GlobalTheory.RootFibre
