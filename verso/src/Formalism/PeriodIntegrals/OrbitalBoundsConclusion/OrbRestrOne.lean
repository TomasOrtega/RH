import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitRestrictionDegreeOne.RestrictedSingleJetEquation

/- English proof (translation)
Introduce `D E p _ h5 hn u i Th hTh z`. Take `⟨ep0, hep0, be, hbe, ep, hep, sg, hsg, U, hU, hEq⟩` from `hTh`. Establish `hc : ∀ w, MvPowerSeries.constantCoeff (be w) = 0` using `fun w => PI.OrbJet.constantCoeff_zero_of_jet_bound p 2 (be w) (hbe w).2.2.1`. Establish `key` using `PI.OrbJet.restricted_single_jet_equation (D := D) p hn z Th U ep0 be hc ep sg hEq`. Simplify using `only [PI.OrbJet.oneLoc, PI.OrbJet.OJ.Loc1.AdmB, PI.OrbJet.OJ.Loc1.B0, PI.OrbJet.OJ.Loc1.Tht]`.

Use `⟨ep0, hep0, be z, ⟨ep z, hep z, sg z, hsg z, _, ?_, key⟩, (hbe z).1, (hbe z).2.1, (hbe z).2.2.1, (hbe z).2.2.2⟩` and prove the remaining obligations. Introduce `m`. Rewrite using `[MvPowerSeries.coeff_killCompl]`. Conclude with `hU _`.
-/
theorem PI.OrbRestrOne : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitRestrictionAtConjugate E := by
  intro D E p _ h5 hn u i Th hTh z
  obtain ⟨ep0, hep0, be, hbe, ep, hep, sg, hsg, U, hU, hEq⟩ := hTh
  have hc : ∀ w, MvPowerSeries.constantCoeff (be w) = 0 := fun w =>
    PI.OrbJet.constantCoeff_zero_of_jet_bound p 2 (be w) (hbe w).2.2.1
  have key := PI.OrbJet.restricted_single_jet_equation (D := D) p hn z Th U ep0 be hc ep sg hEq
  dsimp only [PI.OrbJet.oneLoc, PI.OrbJet.OJ.Loc1.AdmB, PI.OrbJet.OJ.Loc1.B0, PI.OrbJet.OJ.Loc1.Tht]
  refine ⟨ep0, hep0, be z, ⟨ep z, hep z, sg z, hsg z, _, ?_, key⟩,
    (hbe z).1, (hbe z).2.1, (hbe z).2.2.1, (hbe z).2.2.2⟩
  intro m
  rw [MvPowerSeries.coeff_killCompl]
  exact hU _
