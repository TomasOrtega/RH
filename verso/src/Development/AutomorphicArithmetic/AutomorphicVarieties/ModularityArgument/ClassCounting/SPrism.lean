import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ToInhPartialProd

namespace UpperTheory.V.ZK

/- English proof (translation)
Introduce `A _ G _ k m z`. Take `⟨y, rfl⟩` from `toInh_surjective A (m + 1) z`. Rewrite using `[prism_toInh, bd_toInh, bd_toInh, prism_toInh, conj_toInh, ← map_add, ← map_sub, hbd_hprism]`.
-/
theorem sPrism : SPrism := by
  intro A _ G _ k m z
  obtain ⟨y, rfl⟩ := toInh_surjective A (m + 1) z
  rw [prism_toInh, bd_toInh, bd_toInh, prism_toInh, conj_toInh, ← map_add, ← map_sub, hbd_hprism]

end UpperTheory.V.ZK
