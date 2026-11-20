import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GreenbergWilesOfPoitouTate

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UpperTheory.Lit.greenbergWiles (hPT : GlobalTheory.Published.PoitouTateNormalised) (hGE : ReciprocityTheory.Gal.GlobalEulerChar)
    (hLT : ReciprocityTheory.Gal.LocalTateDuality) (hLE : ReciprocityTheory.Gal.LocalEulerChar) (hLF : ReciprocityTheory.Gal.LocalFiniteness) :
    ReciprocityTheory.Gal.GreenbergWiles :=
  GlobalTheory.CompanionTheory.GreenbergWiles.Assembly.greenbergWiles_of_poitouTate hPT hGE hLT hLE hLF
