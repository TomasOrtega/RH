import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeOfBijective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory.CompanionTheory.Hodge.WedgeField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.WedgeFieldGeo

/- English proof (translation)
Introduce `hD hL hS hH1 hV hHopf hHF R _ A _ g hA hg hR`. Use `haveI : IsAbelianScheme A := hA`. Use `haveI : IsProper A.hom := IsAbelianScheme.proper`. Use `haveI : CompactSpace (Sp R) := by`. Unfold `Sp`.

Use `infer_instance`. Use `haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom`. Take `⟨P, iP, hfin, ⟨S⟩⟩` from `exists_finite_sys A.hom`. Use `letI := iP`. Use `haveI := hfin`.

Establish `hQ : AllQIso (resSys A.hom S)` using `hD R A.left A.hom inferInstance P S`. Take `⟨h1, h2, hSt⟩` from `hL R _ _ _ _ (resSys A.hom S) hQ`. Establish `hStein : Stein (OSys A.hom S)` using `hSt.mp (hS R A g hA hg)`. Establish `hvb : VB R (H1 (OSys A.hom S)) g` using `vb_of_bijective (resSys A.hom S) h1 (hH1 R A g hA hg hR)`. Establish `hvan : ∀ n : ℕ, g ≤ n → Function.Exact (dn (OSys A.hom S) n) (dn (OSys A.hom S) (n + 1))` using `fun n hn => hV R A g hA hg hR P S n hn`.

Establish `hh : Hopf (OSys A.hom S) (IsField R)` using `hHopf R A g hA hg P S`. Rewrite `hh` using `[eq_true hR]`. Conclude with `wedge_of_bijective (resSys A.hom S) h1 h2 (hHF R P (OSys A.hom S) g hR hStein hvb hvan hh)`.
-/
theorem wedgeField_of_field :
    DescentSt → LowSt → SteinSt → H1StructureFieldDim → VanSt → HopfSt → HopfFieldSt → WedgeFieldSt := by
  intro hD hL hS hH1 hV hHopf hHF R _ A _ g hA hg hR
  haveI : IsAbelianScheme A := hA
  haveI : IsProper A.hom := IsAbelianScheme.proper
  haveI : CompactSpace (Sp R) := by
    unfold Sp
    infer_instance
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨P, iP, hfin, ⟨S⟩⟩ := exists_finite_sys A.hom
  letI := iP
  haveI := hfin
  have hQ : AllQIso (resSys A.hom S) := hD R A.left A.hom inferInstance P S
  obtain ⟨h1, h2, hSt⟩ := hL R _ _ _ _ (resSys A.hom S) hQ
  have hStein : Stein (OSys A.hom S) := hSt.mp (hS R A g hA hg)
  have hvb : VB R (H1 (OSys A.hom S)) g := vb_of_bijective (resSys A.hom S) h1 (hH1 R A g hA hg hR)
  have hvan : ∀ n : ℕ, g ≤ n → Function.Exact (dn (OSys A.hom S) n) (dn (OSys A.hom S) (n + 1)) :=
    fun n hn => hV R A g hA hg hR P S n hn
  have hh : Hopf (OSys A.hom S) (IsField R) := hHopf R A g hA hg P S
  rw [eq_true hR] at hh
  exact wedge_of_bijective (resSys A.hom S) h1 h2 (hHF R P (OSys A.hom S) g hR hStein hvb hvan hh)

end GlobalTheory.CompanionTheory.Hodge.WedgeFieldGeo
