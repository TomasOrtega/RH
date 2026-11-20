import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanIngredients
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanLibraryBounds
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.Bridge

namespace CompanionTheory.Zuck

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zuckerman_gap_small : ZuckSm thr := zuckSm_of zuckerman_ingredients zuckerman_library_bounds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zuckerman_gap : BranchingSupport.ZuckG := zuckG_of_sm (fun _ hn ε => thr_le hn ε) zuckerman_gap_small

end CompanionTheory.Zuck
