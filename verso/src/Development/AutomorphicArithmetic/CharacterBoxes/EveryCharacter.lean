import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ShapeOf
import Development.AutomorphicArithmetic.CharacterBoxes.ShapeWin
import Development.AutomorphicArithmetic.CharacterBoxes.SupplyChi
import Development.AutomorphicArithmetic.CharacterBoxes.Imprimitive

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc

/- English proof (authored)
Take a witness of the family hypotheses. The Green condition supplies the shape theorem for these families, and applying it to the witness gives TopG. For each primitive character ψ, the window input at ψ gives the required host existence by supplyChi. Use zeroFreeAll_of_topG with these two inputs and window parameter 3/2, which exceeds 1.
-/
theorem UpperTheory.Top.plugWin (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
    (h : Nonempty (Hyps (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DRS)) : Formalism.HC.ZeroFreeAll :=
  h.elim fun h => UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)
    (GlobalTheory.Fc.shape_of _ _ _ _ (UpperTheory.Top.shapeWin hG) trivial trivial h) fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)

def UpperTheory.EveryCharacter : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/- English proof (authored)
First apply plugWin to obtain the zero-free statement for primitive characters. Apply the imprimitive reduction to extend that statement to every Dirichlet character.
-/
theorem UpperTheory.Top.plugAll (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
    (h : Nonempty (Hyps (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DRS)) : UpperTheory.EveryCharacter :=
  UpperTheory.Top.imprimitive (UpperTheory.Top.plugWin hG hV h)
