import Mathlib
import Development.EtaleCohomology.EtaleSheaves.MayerVietorisSequence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExactStatement

/- English proof (translation)
Introduce `R _ U V E f g h`. Conclude with `GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact R f g h`.
-/
theorem UpperTheory.Cb.etale_mayer_vietoris_short_exact :
    LateralTheory.E.MayerVietorisSequence.SES := by
  intro R _ U V E f g h
  exact GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact R f g h
