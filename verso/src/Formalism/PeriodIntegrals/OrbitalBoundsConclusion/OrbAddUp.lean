import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.ConstantCoeffZeroOfBoundGeneral

/- English proof (translation)
The claim follows from `PI.OrbJet.AU.orbAddUp_main`.
-/
theorem PI.OrbAddUp : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitsAddLowerBound E :=
  PI.OrbJet.AU.orbAddUp_main
