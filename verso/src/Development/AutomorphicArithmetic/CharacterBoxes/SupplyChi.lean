import Development.AutomorphicArithmetic.CharacterBoxes.Supply
import Development.AutomorphicArithmetic.CharacterBoxes.Imports
import Development.AutomorphicArithmetic.CharacterBoxes.HostOfField
import Development.AutomorphicArithmetic.CoprimeRanks.AdmChi

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX UpperTheory.Top

/- English proof (translation)
Introduce `ψ hψ`. Use `supplyOfAdm ψ hψ ?_` and prove the remaining obligations. Introduce `eps he0 he1`. Take `⟨x0, hx0⟩` from `admissibleClassesTwistedChar eps he0 he1`. Use `⟨x0, fun s φ H0 hs hx hlo hhi _ _ => ?_⟩` and prove the remaining obligations.

Substitute `hs` using the available equality. Conclude with `hx0 s φ H0 rfl hx hlo hhi`.
-/
theorem UpperTheory.Top.supplyChi :
    ∀ ψ : PChar, VWinAt ψ 401 → HostExW (3 / 2) (GChi ψ).req := by
  intro ψ hψ
  refine supplyOfAdm ψ hψ ?_
  intro eps he0 he1
  obtain ⟨x0, hx0⟩ := admissibleClassesTwistedChar eps he0 he1
  refine ⟨x0, fun s φ H0 hs hx hlo hhi _ _ => ?_⟩
  subst hs
  exact hx0 s φ H0 rfl hx hlo hhi
