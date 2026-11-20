import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Introduce `hZ hLC p _ D G L ha hm v hv t₀ ht gb hgb N N' h hok X X' c₁ c₂ hreg k α hα hE h₁ h₂`. Take `⟨hsm, Fx, At, hF, hT, hfin, htriv, hsum⟩` from `hZ p D G L ha hm v hv t₀ ht gb hgb N N' h hok X X' c₁ c₂ hreg k α hα hE h₁ h₂`. Take `⟨hN3, -, hN'3, -, hdvd, hconj⟩` from `hok`. Establish `hN : 0 < N` using `by omega`. Establish `hN' : 0 < N'` using `by omega`.

Establish `hle : L.KN N' ≤ GlobalTheory.HeckeCorr.heckeLevel (L.KN N) h⁻¹`. Take `⟨k', rfl⟩` from `hdvd`. Conclude with `fun u hu => GlobalTheory.W2.mem_heckeLevel_inv.2 ⟨GlobalTheory.W2.KN_mul_le L N k' hu, hconj u hu⟩`. Use `⟨hsm, Fx, At, hF, hT, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[hsum t]`.

Conclude with `hLC p G v (wtFix L v t₀ α t) (L.KN N) (L.KN N') h hle (GlobalTheory.W2.relIndex_KN_ne_zero L hN hN') htriv hfin`.
-/
theorem UpperTheory.Gal.W2.fixZ_of :
    UpperTheory.Gal.W2.HeckeFixedPointCMCycleClass → UpperTheory.Gal.W2.LevelChange → UpperTheory.Gal.W2.FixZ := by
  intro hZ hLC p _ D G L ha hm v hv t₀ ht gb hgb N N' h hok X X' c₁ c₂ hreg k α hα hE h₁ h₂
  obtain ⟨hsm, Fx, At, hF, hT, hfin, htriv, hsum⟩ :=
    hZ p D G L ha hm v hv t₀ ht gb hgb N N' h hok X X' c₁ c₂ hreg k α hα hE h₁ h₂
  obtain ⟨hN3, -, hN'3, -, hdvd, hconj⟩ := hok
  have hN : 0 < N := by omega
  have hN' : 0 < N' := by omega
  have hle : L.KN N' ≤ GlobalTheory.HeckeCorr.heckeLevel (L.KN N) h⁻¹ := by
    obtain ⟨k', rfl⟩ := hdvd
    exact fun u hu => GlobalTheory.W2.mem_heckeLevel_inv.2 ⟨GlobalTheory.W2.KN_mul_le L N k' hu, hconj u hu⟩
  refine ⟨hsm, Fx, At, hF, hT, fun t => ?_⟩
  rw [hsum t]
  exact hLC p G v (wtFix L v t₀ α t) (L.KN N) (L.KN N') h hle
    (GlobalTheory.W2.relIndex_KN_ne_zero L hN hN') htriv hfin
