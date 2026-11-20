import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod

open NumberField IsDedekindDomain ReciprocityTheory.Aut

namespace GlobalTheory.TypeTame

noncomputable abbrev conjSP {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) : SplitPlace L :=
  ⟨s.v, s.i.comp (IsCMField.complexConj L).toAlgHom⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjSP_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (x : L) :
    (conjSP s).i x = s.i (IsCMField.complexConj L x) := rfl

end GlobalTheory.TypeTame
