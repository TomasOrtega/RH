import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Introduce `hEx hAd hLoc hPer p _ D G L ha hm v hv t₀ ht₀ ρ hρ PD RD N hN hNp D' t P hC hP`. Take `⟨q, j, hj⟩` from `hEx p D G L ha hm v hv t₀ ht₀ ρ hρ N D' t hC ⟨P, hP⟩`. Take `⟨⟨f, nu, rfl, h1, h2⟩, hH⟩` from `hC`. Establish `hW : IsWit D' f nu`. Use `⟨h1, fun n hn hnp => ?_⟩` and prove the remaining obligations.

Take `⟨a1, a2, a3, a4, a5⟩` from `h2 n hn hnp`. Use `⟨a1, a2, a3, a4, fun a a' => ?_⟩` and prove the remaining obligations. Establish `e : D.plat.EF a a' = 2 * D.EF a a'` using `by show ((2 : ℤ) • D.EF) a a' = _`. Simplify using `[LinearMap.smul_apply]`. Use `a5 a a'` as an intermediate fact.

Rewrite `this` using `[e]`. Conclude with `this`. Take `⟨h₁, hR⟩` from `hAd p D G L (Quot.out q) D' j hj f nu hW`. Take `⟨M, hM, hs, hML⟩` from `hLoc p D G L _ D' j hj hH`. Take `⟨hp, rfl⟩` from `(PD (Quot.out q)).onto M hM hs`.

Take `⟨Q, hQ, hQP⟩` from `(hPer p D G L _ ρ D' j hj).1 P hP`. Take `⟨z, hz⟩` from `(RD (Quot.out q)).line Q hQ`. Conclude with `⟨q, ((h₁, hp), z), j, hj, hR N hN hNp, hML, Q, hQ, hQP, hz⟩`.
-/
theorem UpperTheory.Gal.W2.coordEx_of :
    UpperTheory.Gal.W2.PlaceEx → UpperTheory.Gal.W2.AdOfWit → UpperTheory.Gal.W2.PlaceLoc → UpperTheory.Gal.W2.PlacePer → UpperTheory.Gal.W2.CoordEx := by
  intro hEx hAd hLoc hPer p _ D G L ha hm v hv t₀ ht₀ ρ hρ PD RD N hN hNp D' t P hC hP
  obtain ⟨q, j, hj⟩ := hEx p D G L ha hm v hv t₀ ht₀ ρ hρ N D' t hC ⟨P, hP⟩
  obtain ⟨⟨f, nu, rfl, h1, h2⟩, hH⟩ := hC
  have hW : IsWit D' f nu := by
    refine ⟨h1, fun n hn hnp => ?_⟩
    obtain ⟨a1, a2, a3, a4, a5⟩ := h2 n hn hnp
    refine ⟨a1, a2, a3, a4, fun a a' => ?_⟩
    have e : D.plat.EF a a' = 2 * D.EF a a' := by
      show ((2 : ℤ) • D.EF) a a' = _
      simp [LinearMap.smul_apply]
    have := a5 a a'
    rw [e] at this
    exact this
  obtain ⟨h₁, hR⟩ := hAd p D G L (Quot.out q) D' j hj f nu hW
  obtain ⟨M, hM, hs, hML⟩ := hLoc p D G L _ D' j hj hH
  obtain ⟨hp, rfl⟩ := (PD (Quot.out q)).onto M hM hs
  obtain ⟨Q, hQ, hQP⟩ := (hPer p D G L _ ρ D' j hj).1 P hP
  obtain ⟨z, hz⟩ := (RD (Quot.out q)).line Q hQ
  exact ⟨q, ((h₁, hp), z), j, hj, hR N hN hNp, hML, Q, hQ, hQP, hz⟩
