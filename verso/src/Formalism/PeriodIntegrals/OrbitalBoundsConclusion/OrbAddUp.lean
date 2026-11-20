import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.ConstantCoeffZeroOfBoundGeneral

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PI.OrbAddUp : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitsAddLowerBound E :=
  PI.OrbJet.AU.orbAddUp_main
