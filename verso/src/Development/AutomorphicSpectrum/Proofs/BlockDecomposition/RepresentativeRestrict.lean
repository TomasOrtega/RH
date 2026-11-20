import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ZeroC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeRep

/- English proof (translation)
Introduce and unpack `⟨f, hf, hc, hz⟩`. Establish `hf' : CH.d (U.ι ⋙ sq a b) j f = 0` using `hf`. Establish `hb : CH.d (V.ι ⋙ sq a b) j ((resU (sq a b) h).pullC j f) = 0`. Rewrite using `[(resU (sq a b) h).d_pullC, hf', map_zero]`. Establish `hcl : (resU (sq a b) h).pull j c = (CH.cx (V.ι ⋙ sq a b)).cls ((resU (sq a b) h).pullC j f) hb`.

Establish `hc' : c = (CH.cx (U.ι ⋙ sq a b)).cls f hf'` using `hc`. Rewrite using `[hc']`. Both sides reduce to the same expression. Conclude with `⟨(resU (sq a b) h).pullC j f, hb, hcl, fun s => hz (s ⋙ ObjectProperty.ιOfLE h)⟩`.
-/
theorem rep_resB {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) (a b : IdF A)
    {U V : ObjectProperty C} (h : V ≤ U) {j : ℕ} (z : CH.Cn (CH.modF (U.ι ⋙ A)) j) (c : HU (sq a b) U j) :
    Rep (a.res U.ι) (b.res U.ι) z c → Rep (a.res V.ι) (b.res V.ι) (resB A h z) ((resU (sq a b) h).pull j c) := by
  rintro ⟨f, hf, hc, hz⟩
  have hf' : CH.d (U.ι ⋙ sq a b) j f = 0 := hf
  have hb : CH.d (V.ι ⋙ sq a b) j ((resU (sq a b) h).pullC j f) = 0 := by
    rw [(resU (sq a b) h).d_pullC, hf', map_zero]
  have hcl : (resU (sq a b) h).pull j c = (CH.cx (V.ι ⋙ sq a b)).cls ((resU (sq a b) h).pullC j f) hb := by
    have hc' : c = (CH.cx (U.ι ⋙ sq a b)).cls f hf' := hc
    rw [hc']
    rfl
  exact ⟨(resU (sq a b) h).pullC j f, hb, hcl, fun s => hz (s ⋙ ObjectProperty.ιOfLE h)⟩

end GlobalTheory.CompanionTheory.ConeRep
