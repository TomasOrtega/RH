import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h`. Take `⟨a, ha⟩` from `GlobalTheory.localArtinExists_holds E Ω A w h`. Use `⟨a, ha, fun b hb => ?_⟩` and prove the remaining obligations. Take `⟨art, hart⟩` from `GlobalTheory.globalArtinReciprocity_holds E Ω`. Establish `hinj` using `GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art hart w`.

Use `MonoidHom.ext fun σ => hinj ?_` and prove the remaining obligations. Conclude with `(hb.glob art hart σ).trans (ha.glob art hart σ).symm`.
-/
theorem UpperTheory.Zero.LLC.artEx :
    UpperTheory.Zero.LLC.ArtEx := by
  intro E Ω _ _ _ _ _ A w h
  obtain ⟨a, ha⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  refine ⟨a, ha, fun b hb => ?_⟩
  obtain ⟨art, hart⟩ := GlobalTheory.globalArtinReciprocity_holds E Ω
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art hart w
  refine MonoidHom.ext fun σ => hinj ?_
  exact (hb.glob art hart σ).trans (ha.glob art hart σ).symm
