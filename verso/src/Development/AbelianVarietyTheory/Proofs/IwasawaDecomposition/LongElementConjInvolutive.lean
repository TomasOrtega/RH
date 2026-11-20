import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ n g`. Establish `hw : longElt n R * longElt n R = 1` using `Units.ext (antidiag_mul_self n R)`. Establish `hii : ∀ h : GL (Fin n) R, GlobalTheory.CuspRep.invT n R (GlobalTheory.CuspRep.invT n R h) = h` using `fun h => by`. Apply `Units.ext` to reduce the goal to its premises. Use `show (h.valᵀ)ᵀ = h.val`.

Conclude with `Matrix.transpose_transpose _`. Establish `hwT : GlobalTheory.CuspRep.invT n R (longElt n R) = longElt n R`. Apply `Units.ext` to reduce the goal to its premises. Use `show (Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0)ᵀ = Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0`. Use extensionality with `i j`.

Simplify using `only [Matrix.transpose_apply, Matrix.of_apply]`. Use `congr 1`. Conclude with `propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩`. Rewrite using `[map_mul, map_mul, hii, hwT, ← mul_assoc, ← mul_assoc, hw, one_mul, mul_assoc, hw, mul_one]`.
-/
theorem longElt_invT_involution : ∀ (R : Type) [CommRing R] (n : ℕ) (g : GL (Fin n) R), longElt n R * GlobalTheory.CuspRep.invT n R (longElt n R * GlobalTheory.CuspRep.invT n R g * longElt n R) * longElt n R = g := by
  intro R _ n g
  have hw : longElt n R * longElt n R = 1 := Units.ext (antidiag_mul_self n R)
  have hii : ∀ h : GL (Fin n) R, GlobalTheory.CuspRep.invT n R (GlobalTheory.CuspRep.invT n R h) = h := fun h => by
    apply Units.ext
    show (h.valᵀ)ᵀ = h.val
    exact Matrix.transpose_transpose _
  have hwT : GlobalTheory.CuspRep.invT n R (longElt n R) = longElt n R := by
    apply Units.ext
    show (Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0)ᵀ = Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    congr 1
    exact propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  rw [map_mul, map_mul, hii, hwT, ← mul_assoc, ← mul_assoc, hw, one_mul, mul_assoc, hw, mul_one]

end GlobalTheory
