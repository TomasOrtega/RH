import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetDivZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PlkProper

/- English proof (translation)
Introduce `D A N j S κ s Φ k V hV`. Establish `: IsProper s.T.Z.s`. Take `⟨N, i, _, hi⟩` from `s.T.Z.proj`. Use `isProper_str (𝓞 ↥κ.c.F) N` as an intermediate fact. Rewrite using `[← hi]`.

Use `infer_instance`. Establish `: IsIso (spMap κ.e.toRingHom)`. Establish `: IsIso (CommRingCat.ofHom κ.e.toRingHom)` using `κ.e.toCommRingCatIso.isIso_hom`. Use `infer_instance`. Establish `: IsProper ((Φ.C k).π ≫ genStr s.T.Z ≫ spMap κ.e.toRingHom)`.

Rewrite using `[(Φ.C k).π_str]`. Use `infer_instance`. Establish `: IsProper (Φ.C k).π` using `IsProper.of_comp (Φ.C k).π (genStr s.T.Z ≫ spMap κ.e.toRingHom)`. Use `infer_instance`.
-/
theorem isProper_restrict_isoSpec : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V), IsProper (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) := by
  intro D A N j S κ s Φ k V hV
  have : IsProper s.T.Z.s := by
    obtain ⟨N, i, _, hi⟩ := s.T.Z.proj
    have := isProper_str (𝓞 ↥κ.c.F) N
    rw [← hi]; infer_instance
  have : IsIso (spMap κ.e.toRingHom) := by
    have : IsIso (CommRingCat.ofHom κ.e.toRingHom) := κ.e.toCommRingCatIso.isIso_hom
    infer_instance
  have : IsProper ((Φ.C k).π ≫ genStr s.T.Z ≫ spMap κ.e.toRingHom) := by
    rw [(Φ.C k).π_str]; infer_instance
  have : IsProper (Φ.C k).π := IsProper.of_comp (Φ.C k).π (genStr s.T.Z ≫ spMap κ.e.toRingHom)
  infer_instance

end GlobalTheory.PlkProper
