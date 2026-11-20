import Development.AutomorphicArithmetic.CharacterBoxes.Supply
import Development.AutomorphicArithmetic.CharacterBoxes.Imports
import Development.AutomorphicArithmetic.CharacterBoxes.HostOfField
import Development.AutomorphicArithmetic.CoprimeRanks.AdmChi

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX UpperTheory.Top

/- English proof (authored)
Fix ψ and its window input. The admissible-host supply theorem reduces the conclusion to producing an admitted rank datum for each sufficiently large scale with the specified order and character-kernel conditions. For each ε in the required range, choose the threshold from the twisted-character admissibility theorem. After identifying the scale parameter with ε, the scale, order, and host assumptions are exactly those used by that theorem. Its rank datum supplies the admissible rank data required for host existence.
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
