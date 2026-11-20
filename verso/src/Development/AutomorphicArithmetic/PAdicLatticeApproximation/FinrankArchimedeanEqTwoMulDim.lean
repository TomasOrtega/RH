import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Introduce `p _ D G L hm hA`. Establish `h1 : Module.finrank ℝ (Arch G) = Fintype.card (InfinitePlace G.F) * (G.n * 2)`. Establish `hc : Module.finrank ℝ (Fin G.n → ℂ) = G.n * 2`. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[Complex.finrank_real_complex]`.

Unfold `Arch`. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[hc]`. Establish `h2 : Module.finrank ℝ (Arch G) = G.n * Module.finrank ℚ G.F` using `(hA G.F G.n).2.1`. Establish `h3 : Module.finrank ℚ G.F = Module.finrank ℚ D.F` using `(AlgEquiv.ofRingEquiv (f := L.e) (fun r => by simp)).toLinearEquiv.finrank_eq.symm`.

Establish `h4 : Module.finrank ℚ (VQ D) = D.m * D.n * Module.finrank ℚ D.F` using `by haveI := D.freeLa`. Rewrite using `[← D.rankLa]`. Conclude with `Module.finrank_baseChange`. Establish `hg : D.g = D.m * D.n * Module.finrank ℚ D.F / 2` using `rfl`. Establish `h2' : Module.finrank ℝ (Arch G) = D.n * Module.finrank ℚ D.F`.

Rewrite using `[h2, h3, L.n_eq]`. Establish `h1' : Module.finrank ℝ (Arch G) = 2 * (Fintype.card (InfinitePlace G.F) * D.n)`. Rewrite using `[h1, L.n_eq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h4`, `hg` using `[hm, _root_.one_mul]`.

Use `⟨by rw [h2', h4], ?_⟩` and prove the remaining obligations. Rewrite using `[hg, ← h2', h1']`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.finrank_archimedean_eq_two_mul_dim :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → UpperTheory.Gal.W2.ArchSpan → Module.finrank ℝ (Arch G) = Module.finrank ℚ (VQ D) ∧ Module.finrank ℝ (Arch G) = 2 * D.g := by
  intro p _ D G L hm hA
  have h1 : Module.finrank ℝ (Arch G) = Fintype.card (InfinitePlace G.F) * (G.n * 2) := by
    have hc : Module.finrank ℝ (Fin G.n → ℂ) = G.n * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex]
    unfold Arch
    rw [Module.finrank_pi_fintype]
    simp [hc]
  have h2 : Module.finrank ℝ (Arch G) = G.n * Module.finrank ℚ G.F := (hA G.F G.n).2.1
  have h3 : Module.finrank ℚ G.F = Module.finrank ℚ D.F :=
    (AlgEquiv.ofRingEquiv (f := L.e) (fun r => by simp)).toLinearEquiv.finrank_eq.symm
  have h4 : Module.finrank ℚ (VQ D) = D.m * D.n * Module.finrank ℚ D.F := by
    haveI := D.freeLa
    rw [← D.rankLa]
    exact Module.finrank_baseChange
  have hg : D.g = D.m * D.n * Module.finrank ℚ D.F / 2 := rfl
  have h2' : Module.finrank ℝ (Arch G) = D.n * Module.finrank ℚ D.F := by
    rw [h2, h3, L.n_eq]
  have h1' : Module.finrank ℝ (Arch G) = 2 * (Fintype.card (InfinitePlace G.F) * D.n) := by
    rw [h1, L.n_eq]; ring
  rw [hm, _root_.one_mul] at h4 hg
  refine ⟨by rw [h2', h4], ?_⟩
  rw [hg, ← h2', h1']
  omega
