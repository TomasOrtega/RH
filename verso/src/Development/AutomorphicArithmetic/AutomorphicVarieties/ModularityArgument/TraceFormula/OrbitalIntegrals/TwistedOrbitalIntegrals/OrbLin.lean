import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

/- English proof (translation)
Introduce `hT hU k _ _ _ _ _ n _ _ μk hμk γ hγ μ hμ`. Use `haveI : ValuativeExtension k k := ⟨fun _ _ => Iff.rfl⟩`. Take `⟨h0, h1, h2, h3⟩` from `hU k n μk γ`. Take `⟨μ', a, b, c⟩` from `h3 μ hμ`. Establish `t` using `hT k k 1 h0 n μk hμk γ (h2 hγ) μ' a`.

Simplify `t` using `only [c]`.
-/
theorem UpperTheory.V.Z.Tf.Orb.orbLin :
    UpperTheory.V.Z.Tf.Orb.TwOrbLin → UpperTheory.V.Z.Tf.Orb.Untwist → UpperTheory.V.Z.Tf.Orb.OrbLin := by
  intro hT hU k _ _ _ _ _ n _ _ μk hμk γ hγ μ hμ
  haveI : ValuativeExtension k k := ⟨fun _ _ => Iff.rfl⟩
  obtain ⟨h0, h1, h2, h3⟩ := hU k n μk γ
  obtain ⟨μ', a, b, c⟩ := h3 μ hμ
  have t := hT k k 1 h0 n μk hμk γ (h2 hγ) μ' a
  simpa only [c] using t
