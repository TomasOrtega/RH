import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

open GlobalTheory.HolHom in
/- English proof (translation)
Introduce `V _ _ Y B s v₀ w hB hv₀ hs W hW hsW hder U f hU`. Establish `hhol` using `holAt_of_isHolTo hs hv₀`. Establish `hpU` using `(le_preimage_iff _ _).1 hU`. Establish `hpW` using `(le_preimage_iff _ _).1 hsW`. Take `⟨g, hgle, hpg⟩` from `hW.exists_basicOpen_le (V := U) ⟨_, hpU⟩ hpW`.

Establish `hDW : Y.basicOpen g ≤ W` using `Y.basicOpen_le g`. Use `letI := (Y.presheaf.map (homOfLE hDW).op).hom.toAlgebra`. Use `haveI := hW.isLocalization_basicOpen g`. Take `⟨⟨h, ⟨_, k, rfl⟩⟩, e⟩` from `IsLocalization.surj (Submonoid.powers g) ((Y.presheaf.map (homOfLE hgle).op).hom f)`. Simplify using `only [RingHom.algebraMap_toAlgebra] at e`.

Establish `hD0 : ⊤ ≤ s v₀ ⁻¹ᵁ Y.basicOpen g` using `(le_preimage_iff _ _).2 hpg`. Establish `hev : ∀ᶠ v in 𝓝 v₀, ⊤ ≤ s v ⁻¹ᵁ Y.basicOpen g` using `(hhol _ hD0).1`. Establish `heq : (fun v => valAt' (s v) W h) =ᶠ[𝓝 v₀] (fun v => valAt' (s v) U f * valAt' (s v) W g ^ k)` using `by filter_upwards [hev] with v hv`. Establish `e'` using `congrArg (HolHom.evalHom (s v) _ hv) e`. Simplify using `only [map_mul, map_pow, ← valR_eq] at e'`.

Rewrite `e'` using `[valR_res (s v) hgle f hv, valR_res (s v) hDW g hv, valR_res (s v) hDW h hv]`. Simplify using `only [valAt'_eq_valR]`. Conclude with `e'.symm`. Establish `hFd` using `(hhol U hU).2 f`. Establish `hGd` using `(hhol W hsW).2 g`.

Establish `hHd` using `(hhol W hsW).2 h`. Establish `hL` using `(hFd.hasFDerivAt.mul (hGd.hasFDerivAt.pow k)).congr_of_eventuallyEq heq`. Establish `huniq` using `hL.unique hHd.hasFDerivAt`. Establish `hw` using `congrArg (fun L => L w) huniq`. Establish `hG0 : valAt' (s v₀) W g ≠ 0` using `(le_basicOpen_iff _ hsW g).1 hD0`.

Simplify using `[hder g, hder h, hG0] at hw`. Conclude with `hw`.
-/
theorem UpperTheory.Gal.W2.flatAffine_of :
    UpperTheory.Gal.W2.FlatAffine := by
  intro V _ _ Y B s v₀ w hB hv₀ hs W hW hsW hder U f hU
  have hhol := holAt_of_isHolTo hs hv₀
  have hpU := (le_preimage_iff _ _).1 hU
  have hpW := (le_preimage_iff _ _).1 hsW
  obtain ⟨g, hgle, hpg⟩ := hW.exists_basicOpen_le (V := U) ⟨_, hpU⟩ hpW
  have hDW : Y.basicOpen g ≤ W := Y.basicOpen_le g
  letI := (Y.presheaf.map (homOfLE hDW).op).hom.toAlgebra
  haveI := hW.isLocalization_basicOpen g
  obtain ⟨⟨h, ⟨_, k, rfl⟩⟩, e⟩ :=
    IsLocalization.surj (Submonoid.powers g) ((Y.presheaf.map (homOfLE hgle).op).hom f)
  simp only [RingHom.algebraMap_toAlgebra] at e
  have hD0 : ⊤ ≤ s v₀ ⁻¹ᵁ Y.basicOpen g := (le_preimage_iff _ _).2 hpg
  have hev : ∀ᶠ v in 𝓝 v₀, ⊤ ≤ s v ⁻¹ᵁ Y.basicOpen g := (hhol _ hD0).1
  have heq : (fun v => valAt' (s v) W h) =ᶠ[𝓝 v₀]
      (fun v => valAt' (s v) U f * valAt' (s v) W g ^ k) := by
    filter_upwards [hev] with v hv
    have e' := congrArg (HolHom.evalHom (s v) _ hv) e
    simp only [map_mul, map_pow, ← valR_eq] at e'
    rw [valR_res (s v) hgle f hv, valR_res (s v) hDW g hv, valR_res (s v) hDW h hv] at e'
    simp only [valAt'_eq_valR]
    exact e'.symm
  have hFd := (hhol U hU).2 f
  have hGd := (hhol W hsW).2 g
  have hHd := (hhol W hsW).2 h
  have hL := (hFd.hasFDerivAt.mul (hGd.hasFDerivAt.pow k)).congr_of_eventuallyEq heq
  have huniq := hL.unique hHd.hasFDerivAt
  have hw := congrArg (fun L => L w) huniq
  have hG0 : valAt' (s v₀) W g ≠ 0 := (le_basicOpen_iff _ hsW g).1 hD0
  simp [hder g, hder h, hG0] at hw
  exact hw
