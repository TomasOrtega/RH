import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.FinPl

/- English proof (translation)
Unfold `idOff`. Conclude with `le_iInf fun w => iInf_le_of_le ⟨w.1, h w.1 w.2⟩ le_rfl`.
-/
theorem OffAnti.idOff_le (D : D7) {P Q : Pl D → Prop} (h : ∀ v, Q v → P v) : idOff D P ≤ idOff D Q := by
  unfold idOff
  exact le_iInf fun w => iInf_le_of_le ⟨w.1, h w.1 w.2⟩ le_rfl

/- English proof (translation)
Introduce `g hg`. Simplify using `only [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at hg ⊢`. Establish `key : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) (matHom V g) = Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hIJ) (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (matHom V g))`. Use extensionality with `i j`. Simplify using `[Ideal.Quotient.factor_mk]`.

Rewrite using `[key, hg, map_one]`.
-/
theorem OffAnti.congGrp_le {D : D7} (V : HSp D) {I J : Ideal (AE D)} (hIJ : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro g hg
  simp only [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at hg ⊢
  have key : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) (matHom V g) =
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hIJ)
        (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (matHom V g)) := by
    ext i j
    simp [Ideal.Quotient.factor_mk]
  rw [key, hg, map_one]

/- English proof (translation)
Introduce `D S _ _ h` and use `OffAnti.congGrp_le S (OffAnti.idOff_le D h)`.
-/
theorem grpOff_anti : ∀ (D : D7) (S : HSp D) (P Q : Pl D → Prop), (∀ v, Q v → P v) → grpOff S P ≤ grpOff S Q :=
  fun D S _ _ h => OffAnti.congGrp_le S (OffAnti.idOff_le D h)

end GlobalTheory.FinPl
