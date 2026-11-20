import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

/- English proof (translation)
Introduce `Γ k _ _ _ _ N N' ρ ρ' hρ hρ' hcp c ⟨v, hv0, hv⟩`. Establish `hN : N = N'`. Establish `h` using `congrArg Polynomial.natDegree (hcp 1)`. Simplify `h` using `[cp, Matrix.charpoly_natDegree_eq_dim]`. Substitute `hN` using the available equality.

Take `⟨P, hP⟩` from `Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ ρ' hρ hρ' (fun g => hcp g)`. Use `⟨(P : Matrix (Fin N) (Fin N) k).mulVec v, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hv0` to reduce the goal to its premises. Use `congrArg (((P⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).mulVec) h` as an intermediate fact.

Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, Matrix.mulVec_zero]`. Conclude with `this`. Introduce `g`. Establish `hg : ρ g * P = P * ρ' g`. Rewrite using `[hP g]`.

Use `group`. Establish `hm : (ρ g : Matrix (Fin N) (Fin N) k) * P = P * ρ' g`. Rewrite using `[← Units.val_mul, hg, Units.val_mul]`. Rewrite using `[Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hv g, Matrix.mulVec_smul]`.
-/
theorem UpperTheory.Gal.TP.Sub.eigTransfer_holds :
    EigTransfer := by
  intro Γ k _ _ _ _ N N' ρ ρ' hρ hρ' hcp c ⟨v, hv0, hv⟩
  have hN : N = N' := by
    have h := congrArg Polynomial.natDegree (hcp 1)
    simpa [cp, Matrix.charpoly_natDegree_eq_dim] using h
  subst hN
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ ρ' hρ hρ' (fun g => hcp g)
  refine ⟨(P : Matrix (Fin N) (Fin N) k).mulVec v, ?_, ?_⟩
  · intro h
    apply hv0
    have := congrArg (((P⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).mulVec) h
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  · intro g
    have hg : ρ g * P = P * ρ' g := by
      rw [hP g]
      group
    have hm : (ρ g : Matrix (Fin N) (Fin N) k) * P = P * ρ' g := by
      rw [← Units.val_mul, hg, Units.val_mul]
    rw [Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hv g, Matrix.mulVec_smul]
