import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularAtTranslateStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslateIntoSmallerOpenStatement

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

/- English proof (translation)
Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `f hf t g hg`. Conclude with `hf t g (hle hg)`. Introduce `f hf s g hg`. Take `⟨σ, t, hσ, hmem⟩` from `GlobalTheory.T.translate_into_smaller_open R T Γ U U' hU hU' hle g hg`.

Establish `hreg` using `hf (s * t⁻¹) _ hmem`. Establish `key` using `GlobalTheory.T.regular_at_translate R T Γ σ t hσ (fun h => algebraMap R (FractionRing R) (f (s * t⁻¹ * h))) g hreg`. Establish `heq : (fun h => algebraMap R (FractionRing R) (f (s * t⁻¹ * (t * h)))) = fun h => algebraMap R (FractionRing R) (f (s * h))`. Use function extensionality and compare the values at `h`. Use `congr 2`.

Rewrite using `[_root_.mul_assoc, inv_mul_cancel_left]`. Simplify `key` using `only [heq]`.
-/
theorem QFGroup.btSet_eq_of_le (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens)
    (hU : Γ.IsFinOpenSub U) (hU' : Γ.IsFinOpenSub U') (hle : U' ≤ U) :
    Γ.btSet U = Γ.btSet U' := by
  apply Set.Subset.antisymm
  · intro f hf t g hg
    exact hf t g (hle hg)
  · intro f hf s g hg
    obtain ⟨σ, t, hσ, hmem⟩ := GlobalTheory.T.translate_into_smaller_open R T Γ U U' hU hU' hle g hg
    have hreg := hf (s * t⁻¹) _ hmem
    have key := GlobalTheory.T.regular_at_translate R T Γ σ t hσ
      (fun h => algebraMap R (FractionRing R) (f (s * t⁻¹ * h))) g hreg
    have heq : (fun h => algebraMap R (FractionRing R) (f (s * t⁻¹ * (t * h)))) =
        fun h => algebraMap R (FractionRing R) (f (s * h)) := by
      funext h
      congr 2
      rw [_root_.mul_assoc, inv_mul_cancel_left]
    simpa only [heq] using key

/- English proof (translation)
Introduce `R _ _ _ T _ _ Γ U U' hU hU' hle`. Unfold `QFGroup.btOrder`. Rewrite using `[QFGroup.btSet_eq_of_le R T Γ U U' hU hU' hle]`.
-/
theorem QFGroup.btOrder_eq_of_le : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → Γ.btOrder U = Γ.btOrder U' := by
  intro R _ _ _ T _ _ Γ U U' hU hU' hle
  unfold QFGroup.btOrder
  rw [QFGroup.btSet_eq_of_le R T Γ U U' hU hU' hle]

end GlobalTheory.CompanionTheory.Ar.BT
