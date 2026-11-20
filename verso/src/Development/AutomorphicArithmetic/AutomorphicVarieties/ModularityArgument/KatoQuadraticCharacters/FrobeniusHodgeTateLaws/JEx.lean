import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA

open UpperTheory.V.Z.Kato.Joint

/- English proof (translation)
Introduce `l _ Ω _ _ _ A hA`. Take `⟨v, hv, hl⟩` from `hA`. Establish `hAl : A.valuation ((l : ℕ) : Ω) < 1`. Use `(hv ((l : ℕ) : NumberField.RingOfIntegers ℚ)).2 hl` as an intermediate fact. Simplify using `using this`.

Conclude with `⟨(ValuationSubring.mem_nonunits_iff _).2 hAl, Formalism.BasicNotions.Examples₂.LB.exists_emb A hAl⟩`.
-/
theorem UpperTheory.V.Z.Kato.Joint.jEx :
    UpperTheory.V.Z.Kato.Joint.JEx := by
  intro l _ Ω _ _ _ A hA
  obtain ⟨v, hv, hl⟩ := hA
  have hAl : A.valuation ((l : ℕ) : Ω) < 1 := by
    have := (hv ((l : ℕ) : NumberField.RingOfIntegers ℚ)).2 hl
    simpa using this
  exact ⟨(ValuationSubring.mem_nonunits_iff _).2 hAl, Formalism.BasicNotions.Examples₂.LB.exists_emb A hAl⟩
