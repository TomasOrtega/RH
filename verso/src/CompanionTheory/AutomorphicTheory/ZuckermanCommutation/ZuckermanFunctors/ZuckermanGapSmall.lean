import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanIngredients
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanLibraryBounds
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.Bridge

namespace CompanionTheory.Zuck

/- English proof (translation)
The claim follows from `zuckSm_of zuckerman_ingredients zuckerman_library_bounds`.
-/
theorem zuckerman_gap_small : ZuckSm thr := zuckSm_of zuckerman_ingredients zuckerman_library_bounds

/- English proof (translation)
The claim follows from `zuckG_of_sm (fun _ hn ε => thr_le hn ε) zuckerman_gap_small`.
-/
theorem zuckerman_gap : BranchingSupport.ZuckG := zuckG_of_sm (fun _ hn ε => thr_le hn ε) zuckerman_gap_small

end CompanionTheory.Zuck
