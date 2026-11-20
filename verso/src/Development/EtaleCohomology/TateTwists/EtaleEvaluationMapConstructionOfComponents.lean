import Development.EtaleCohomology.TateTwists.EtaleChainCochainExistsOfEvalData

namespace LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation
/- English proof (translation)
Apply `LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data` to reduce the goal to its premises.
-/
theorem etale_evaluation_map_construction_of_components : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := by
  apply LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data
/- English proof (translation)
The claim follows from `etale_evaluation_map_construction_of_components`.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := etale_evaluation_map_construction_of_components
end LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation
