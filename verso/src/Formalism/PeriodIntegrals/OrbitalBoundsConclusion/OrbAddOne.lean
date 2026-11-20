import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.OrbitsAddAtConjugate

/- English proof (translation)
The claim follows from `PI.OrbJet.AO.orbitsAddAtConjugate`.
-/
theorem PI.OrbAddOne : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitsAddAtConjugate E :=
  PI.OrbJet.AO.orbitsAddAtConjugate
