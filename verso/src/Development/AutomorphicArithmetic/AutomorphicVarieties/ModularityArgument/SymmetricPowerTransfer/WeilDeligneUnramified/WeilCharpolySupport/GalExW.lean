import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.CompEx

/- English proof (translation)
Introduce `P L Ω _ _ _ _ _ _ l _ ι hl hE n hn σ hσ`. Take `⟨r, HT, hc, hs, -, -, hLG, hp, hi⟩` from `P.gal L Ω hE l hl ι n hn σ hσ`. Use `⟨r, ⟨hc, UpperTheory.V.Z.Sym.Al.compEx P.af.litN L hE n hn σ hσ, fun w hw τ hτ => (hLG w hw τ hτ).1, hp⟩, fun h => ?_⟩` and prove the remaining obligations. Take `⟨π, h1, h2, h3, -, h4, h5⟩` from `hi h`. Conclude with `⟨π, h1, h2, h3, h4, h5⟩`.
-/
theorem UpperTheory.V.Z.Sym.W.galExW :
    UpperTheory.V.Z.Sym.W.GalExW := by
  intro P L Ω _ _ _ _ _ _ l _ ι hl hE n hn σ hσ
  obtain ⟨r, HT, hc, hs, -, -, hLG, hp, hi⟩ := P.gal L Ω hE l hl ι n hn σ hσ
  refine ⟨r, ⟨hc, UpperTheory.V.Z.Sym.Al.compEx P.af.litN L hE n hn σ hσ,
    fun w hw τ hτ => (hLG w hw τ hτ).1, hp⟩, fun h => ?_⟩
  obtain ⟨π, h1, h2, h3, -, h4, h5⟩ := hi h
  exact ⟨π, h1, h2, h3, h4, h5⟩
