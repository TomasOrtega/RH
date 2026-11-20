import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherianStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Establish `hsub : Subsingleton (Spec (CommRingCat.of k))` using `inferInstanceAs (Subsingleton (PrimeSpectrum k))`. Take `⟨p⟩ : Nonempty (Spec (CommRingCat.of k))` from `inferInstanceAs (Nonempty (PrimeSpectrum k))`. Establish `hZ : {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} = connectedComponent (e p)`. Use extensionality with `x`. Establish `h1 : (f ⁻¹' {f x} : Set X) = Set.univ` using `Set.eq_univ_of_forall fun y => Subsingleton.elim _ _`.

Establish `h2 : f x = p` using `Subsingleton.elim _ _`. Rewrite using `[Set.mem_setOf_eq, h1, h2, connectedComponentIn_univ]`. Rewrite using `[hZ]`. Establish `hN : IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian f`. Establish `hO : IsOpen (connectedComponent (e p))` using `GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' X hN (e p)`.

Use `⟨hO, ?_⟩` and prove the remaining obligations. Set `U : X.Opens` to `⟨connectedComponent (e p), hO⟩`. Establish `hc : ConnectedSpace U.toScheme` using `isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := e p))`. Establish `hi : IrreducibleSpace U.toScheme` using `GlobalTheory.T.irreducibleSpace_of_smooth_over_field_of_connected k U.toScheme (U.ι ≫ f) inferInstance hc`. Conclude with `isIrreducible_iff_irreducibleSpace.mpr hi`.
-/
theorem isOpen_and_isIrreducible_sectionComponent_of_smooth_field
    (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
    (e : Spec (CommRingCat.of k) ⟶ X) (hf : Smooth f) (he : e ≫ f = 𝟙 _) :
    IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} ∧
      IsIrreducible {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  have hsub : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  have hZ : {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}
      = connectedComponent (e p) := by
    ext x
    have h1 : (f ⁻¹' {f x} : Set X) = Set.univ :=
      Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
    have h2 : f x = p := Subsingleton.elim _ _
    rw [Set.mem_setOf_eq, h1, h2, connectedComponentIn_univ]
  rw [hZ]
  have hN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hO : IsOpen (connectedComponent (e p)) := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' X hN (e p)
  refine ⟨hO, ?_⟩
  let U : X.Opens := ⟨connectedComponent (e p), hO⟩
  have hc : ConnectedSpace U.toScheme :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := e p))
  have hi : IrreducibleSpace U.toScheme :=
    GlobalTheory.T.irreducibleSpace_of_smooth_over_field_of_connected k U.toScheme (U.ι ≫ f) inferInstance hc
  exact isIrreducible_iff_irreducibleSpace.mpr hi

end GlobalTheory
