import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SymOfMul

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Introduce `n x y`. Take `⟨-, -, -, -, -, -, hA, -⟩` from `cfBasic n`. Take `⟨-, -, -, hS, hN, -⟩` from `chRF n`. Rewrite using `[mul_comm, hA, mul_comm, hA]`. Use `Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ (fun w => ?_)` and prove the remaining obligations.

Establish `hs : sg (Equiv.inv (Equiv.Perm (Fin n)) w) = sg w`. Simplify using `[sg, Equiv.Perm.sign_inv]`. Rewrite using `[hs]`. Use `congr 1`. Establish `hc : cf (chR n) (x - y ∘ ⇑((Equiv.inv (Equiv.Perm (Fin n))) w)) = cf (chR n) ((x - y ∘ ⇑((Equiv.inv (Equiv.Perm (Fin n))) w)) ∘ ⇑w)` using `(hS w _).symm`.

Rewrite using `[hc, ← hN]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.RealTr.mSymm :
    ∀ (n : ℕ) (x y : Wt n), cf (chR n * alt x) y = cf (chR n * alt y) x := by
  intro n x y
  obtain ⟨-, -, -, -, -, -, hA, -⟩ := cfBasic n
  obtain ⟨-, -, -, hS, hN, -⟩ := chRF n
  rw [mul_comm, hA, mul_comm, hA]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ (fun w => ?_)
  have hs : sg (Equiv.inv (Equiv.Perm (Fin n)) w) = sg w := by
    simp [sg, Equiv.Perm.sign_inv]
  rw [hs]
  congr 1
  have hc : cf (chR n) (x - y ∘ ⇑((Equiv.inv (Equiv.Perm (Fin n))) w))
      = cf (chR n) ((x - y ∘ ⇑((Equiv.inv (Equiv.Perm (Fin n))) w)) ∘ ⇑w) :=
    (hS w _).symm
  rw [hc, ← hN]
  congr 1
  funext i
  simp
