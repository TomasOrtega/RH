import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

/- English proof (translation)
Introduce `hHP hPF O _ bar g ρ D X s A _ S k m B P hB hP`. Establish `hBU : IsOpen (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)))` using `hB.prod isOpen_univ`. Establish `hS` using `S.hol m B P hB hP`. Use `hHP ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) X A k (B ×ˢ Set.univ) (fun bz => S.pt k (P bz.1) bz.2) hBU ?_ ?_` and prove the remaining obligations. Establish `hu : IsHolTo (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) (fun bz => S.u (P bz.1))` using `GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp hS.1 hBU differentiableOn_fst (fun bz hbz => hbz.1)`.

Use `GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr hu ?_` and prove the remaining obligations. Introduce `bz hbz`. Conclude with `(hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).1 bz.2`. Introduce `j`. Set `φ : (Fin m → ℂ) × (Fin k → Fin g → ℂ) → (Fin m → ℂ) × (Fin g → ℂ)` to `fun bz => (bz.1, bz.2 j)`.

Establish `hφ : Differentiable ℂ φ` using `by fun_prop`. Establish `hmaps : Set.MapsTo φ (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) (B ×ˢ (Set.univ : Set (Fin g → ℂ)))` using `fun bz hbz => ⟨hbz.1, Set.mem_univ _⟩`. Establish `he` using `GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp hS.2 hBU hφ.differentiableOn hmaps`. Use `GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr he ?_` and prove the remaining obligations. Introduce `bz hbz`.

Conclude with `(hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).2.1 bz.2 j`.
-/
theorem UpperTheory.Gal.W2.ptHol_of :
    UpperTheory.Gal.W2.HolPi → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.PtHol := by
  intro hHP hPF O _ bar g ρ D X s A _ S k m B P hB hP
  have hBU : IsOpen (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) := hB.prod isOpen_univ
  have hS := S.hol m B P hB hP
  refine hHP ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) X A k (B ×ˢ Set.univ)
    (fun bz => S.pt k (P bz.1) bz.2) hBU ?_ ?_
  · have hu : IsHolTo (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) (fun bz => S.u (P bz.1)) :=
      GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp hS.1 hBU differentiableOn_fst
        (fun bz hbz => hbz.1)
    refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr hu ?_
    intro bz hbz
    exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).1 bz.2
  · intro j
    let φ : (Fin m → ℂ) × (Fin k → Fin g → ℂ) → (Fin m → ℂ) × (Fin g → ℂ) :=
      fun bz => (bz.1, bz.2 j)
    have hφ : Differentiable ℂ φ := by
      fun_prop
    have hmaps : Set.MapsTo φ (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)))
        (B ×ˢ (Set.univ : Set (Fin g → ℂ))) :=
      fun bz hbz => ⟨hbz.1, Set.mem_univ _⟩
    have he := GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp hS.2 hBU hφ.differentiableOn hmaps
    refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr he ?_
    intro bz hbz
    exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).2.1 bz.2 j
