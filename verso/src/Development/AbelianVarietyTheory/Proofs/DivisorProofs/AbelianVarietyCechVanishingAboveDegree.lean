import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCovers
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

/- English proof (translation)
Introduce `K _ _ A _ hA`. Use `haveI : IsProper A.hom := hA.proper`. Use `haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom`. Establish `hsep : IsSeparated A.hom` using `inferInstance`. Take `⟨m, V, hV, hc⟩` from `GlobalTheory.exists_fin_affine_cover (X := A.left) (V := ⊤) (by simpa using isCompact_univ)`.

Use `⟨m, fun P hP j hj hNV => ?_⟩` and prove the remaining obligations. Take `⟨κ, _, _, W, hW, hWc, hne⟩` from `hNV`. Take `⟨e⟩` from `GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers K A.left A.hom P κ W (Fin m) V hP hsep hW hWc hV hc j`. Apply `hne` to reduce the goal to its premises. Establish `hz : IsZero ((GlobalTheory.AbLaw.cechLB A.hom P V).X j)` using `GlobalTheory.AbLaw.isZero_cechLB_X A.hom P V (by simpa using hj)`.

Establish `h0 : IsZero ((GlobalTheory.AbLaw.cechLB A.hom P V).homology j)` using `(HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (HomologicalComplex.ExactAt.of_isZero hz)`. Establish `: Subsingleton ((GlobalTheory.AbLaw.cechLB A.hom P V).homology j)` using `ModuleCat.isZero_iff_subsingleton.1 h0`. Conclude with `(HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (ModuleCat.isZero_iff_subsingleton.2 e.toEquiv.subsingleton)`.
-/
theorem not_NV_of_ge :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
      ∃ c : ℕ, ∀ P : LB A.left, P.IsLB → ∀ j : ℕ, c ≤ j → ¬ NV A P j := by
  intro K _ _ A _ hA
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hsep : IsSeparated A.hom := inferInstance
  obtain ⟨m, V, hV, hc⟩ :=
    GlobalTheory.exists_fin_affine_cover (X := A.left) (V := ⊤) (by simpa using isCompact_univ)
  refine ⟨m, fun P hP j hj hNV => ?_⟩
  obtain ⟨κ, _, _, W, hW, hWc, hne⟩ := hNV
  obtain ⟨e⟩ := GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers K A.left A.hom P κ W (Fin m) V
    hP hsep hW hWc hV hc j
  apply hne
  have hz : IsZero ((GlobalTheory.AbLaw.cechLB A.hom P V).X j) :=
    GlobalTheory.AbLaw.isZero_cechLB_X A.hom P V (by simpa using hj)
  have h0 : IsZero ((GlobalTheory.AbLaw.cechLB A.hom P V).homology j) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (HomologicalComplex.ExactAt.of_isZero hz)
  have : Subsingleton ((GlobalTheory.AbLaw.cechLB A.hom P V).homology j) :=
    ModuleCat.isZero_iff_subsingleton.1 h0
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (ModuleCat.isZero_iff_subsingleton.2 e.toEquiv.subsingleton)

end GlobalTheory.AmpleGen
