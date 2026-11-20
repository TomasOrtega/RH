import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModHomeo
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary

noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ r P T _ hP`. Establish `hσσ` using `sigma_invol hCM`. Establish `h2 : (2 : E) ≠ 0` using `two_ne_zero`. Take `⟨h1, -, -, -⟩` from `Lc.tensor_adele_topology_holds F E`. Use `⟨coordHomeo hσσ hJ hP h2, fun n₀ n => phi_mul hσσ hJ hP h2 n₀ n, fun h hh n n' hn => ?_⟩` and prove the remaining obligations.

Take `⟨e1, e2⟩` from `phi_conj hσσ hJ hP h2 hh n n' hn`. Conclude with `⟨fun a => congrFun e1 a, Subtype.ext e2⟩`.
-/
theorem heisenberg_coordinates_holds : HeisenbergCoordinates := by
  intro F E _ _ _ _ _ σ hCM M J hJ r P T _ hP
  have hσσ := sigma_invol hCM
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  obtain ⟨h1, -, -, -⟩ := Lc.tensor_adele_topology_holds F E
  refine ⟨coordHomeo hσσ hJ hP h2, fun n₀ n => phi_mul hσσ hJ hP h2 n₀ n, fun h hh n n' hn => ?_⟩
  obtain ⟨e1, e2⟩ := phi_conj hσσ hJ hP h2 hh n n' hn
  exact ⟨fun a => congrFun e1 a, Subtype.ext e2⟩

end PI.VolSemiDirect.W.Md
