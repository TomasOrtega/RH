import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.LPdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

/- English proof (translation)
Introduce `hP l _ k _ _ hl d X p hSP hR G y`. Take `⟨hprop, hsm⟩` from `hSP`. Use `haveI := hprop`. Take `⟨hdiag, hpt⟩` from `hP k d p inferInstance hsm`. Take `⟨hy, hpb⟩` from `hpt y`.

Establish `hunitX : IsUnit ((l : Γ(X, ⊤)))`. Establish `h1 : IsUnit ((l : k))` using `isUnit_iff_ne_zero.mpr hl`. Establish `h2` using `(h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom`. Simplify `h2` using `[map_natCast]`. Establish `hunit : IsUnit ((l : Γ(S k, ⊤)))`.

Simplify `hunitX.map (y.1.appTop).hom` using `[map_natCast]`. Simplify using `only [GysQ.diag, GysQ.pt, GysQ.cls, dif_pos hdiag, dif_pos hy]`. Rewrite using `[G.nat hy hdiag (slice y) y.1 (by rw [slice, ← Category.assoc, pullback.lift_fst, Category.id_comp]) hpb]`. Use `congr 1`. Use `first`.

Consider the case `exact hR.one_nat y.1 hunitX`. Consider the case `exact hR.one_nat y.1 hunit`.
-/
theorem slice_holds : Slice := by
  intro hP l _ k _ _ hl d X p hSP hR G y
  obtain ⟨hprop, hsm⟩ := hSP
  haveI := hprop
  obtain ⟨hdiag, hpt⟩ := hP k d p inferInstance hsm
  obtain ⟨hy, hpb⟩ := hpt y
  have hunitX : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hunit : IsUnit ((l : Γ(S k, ⊤))) := by
    simpa [map_natCast] using hunitX.map (y.1.appTop).hom
  simp only [GysQ.diag, GysQ.pt, GysQ.cls, dif_pos hdiag, dif_pos hy]
  rw [G.nat hy hdiag (slice y) y.1
    (by rw [slice, ← Category.assoc, pullback.lift_fst, Category.id_comp]) hpb]
  congr 1
  first
  | exact hR.one_nat y.1 hunitX
  | exact hR.one_nat y.1 hunit

end UpperTheory.Gal.KunnethLefschetz
