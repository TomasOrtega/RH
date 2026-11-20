import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DerivativePreservation.EabPresMain

/- English proof (translation)
Introduce `E _ _ k r z i D a b f f₂ s hD hf hf₂`. Use `⟨Formalism.FourierDecayAlt.Q.EabLie.eab_smooth i D a b f hf, fun _ hL => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Conclude with `Formalism.FourierDecayAlt.Q.EabLie.eab_left i z D hD a b f hf hL`. Conclude with `Formalism.FourierDecayAlt.Q.EabLie.eab_lin i D a b f f₂ s hf hf₂ g hg`.
-/
theorem qnEabPres : Formalism.FourierDecayAlt.Q.EabPres := by
  intro E _ _ k r z i D a b f f₂ s hD hf hf₂
  refine ⟨Formalism.FourierDecayAlt.Q.EabLie.eab_smooth i D a b f hf, fun _ hL => ?_, fun g hg => ?_⟩
  · exact Formalism.FourierDecayAlt.Q.EabLie.eab_left i z D hD a b f hf hL
  · exact Formalism.FourierDecayAlt.Q.EabLie.eab_lin i D a b f f₂ s hf hf₂ g hg
