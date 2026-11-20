import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StabSplit

/- English proof (translation)
The claim follows from `PI.StabSplit.stabilizer_splitting_of_parts PI.StabSplit.fixed_point_subgroup PI.StabSplit.stabilizer_subgroup_flag PI.StabSplit.unipotent_nilpotent_radical PI.StabSplit.nilpotent_orthogonal_complement`.
-/
theorem Formalism.FourierDecayAlt.P.stabilizer_split : Formalism.FourierDecayAlt.C2.C1ii :=
  PI.StabSplit.stabilizer_splitting_of_parts PI.StabSplit.fixed_point_subgroup PI.StabSplit.stabilizer_subgroup_flag
    PI.StabSplit.unipotent_nilpotent_radical PI.StabSplit.nilpotent_orthogonal_complement
