import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.OrbitsAddAtConjugate

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PI.OrbAddOne : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitsAddAtConjugate E :=
  PI.OrbJet.AO.orbitsAddAtConjugate
