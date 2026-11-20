import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllFree
import Formalism.LocalToGlobal.ProjectiveLattices.UniqFree
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.RegularityR2Quotient
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.DatIndep
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof

noncomputable section

namespace Formalism.L2.PjFree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

open Formalism.L2.Pj (Rul)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩`.
-/
theorem isNormOn_iff {K : Type} [Field K] {R : Type} [CommRing R] [Algebra K R] (C : Submodule K R)
    (σ : K →+* ℂ) (N : R → ℝ) : PjFree.IsNormOn C σ N ↔ Formalism.L2.Pj.IsNormOn C σ N :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trivCls_eq : PjFree.trivCls Xo c = Formalism.L2.Pj.trivCls Xo c := rfl

variable {Xo c}

def QPt.toPj (q : PjFree.QPt Xo c) : Formalism.L2.Pj.QPt Xo c := ⟨q.T, q.ι, q.y, q.triv⟩

def QPt.ofPj (q : Formalism.L2.Pj.QPt Xo c) : PjFree.QPt Xo c := ⟨q.T, q.ι, q.y, q.triv⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem QPt.ofPj_toPj (q : PjFree.QPt Xo c) : QPt.ofPj q.toPj = q := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem QPt.toPj_ofPj (q : Formalism.L2.Pj.QPt Xo c) : (QPt.ofPj q).toPj = q := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ordQ_toPj (q : PjFree.QPt Xo c) (f : Rul Xo c) :
    Formalism.L2.Pj.ordQ Xo c q.toPj f = PjFree.ordQ Xo c q f := rfl

variable (Xo c)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem valSet_alg_eq (la : HeightOneSpectrum (𝓞 c.F)) :
    PjFree.valSet Xo c (PjFree.algCls Xo c) la = Formalism.L2.Pj.valSet Xo c (Formalism.L2.Pj.algCls Xo c) la := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h a n f hf hx q => h a n f hf hx (QPt.ofPj q), fun h a n f hf hx q => h a n f hf hx q.toPj⟩`.
-/
theorem regR1Q_iff_free (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) :
    PjFree.RegularityR1Quotient Xo c C ↔ Formalism.L2.Pj.RegularityR1Quotient Xo c C :=
  ⟨fun h a n f hf hx q => h a n f hf hx (QPt.ofPj q), fun h a n f hf hx q => h a n f hf hx q.toPj⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h aL nL aE nE k ws et c' hc hw he hx q => h aL nL aE nE k ws et c' hc hw he hx (QPt.ofPj q), fun h aL nL aE nE k ws et c' hc hw he hx q => h aL nL aE nE k ws et c' hc hw he hx q.toPj⟩`.
-/
theorem regR2Q_iff_free (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) :
    PjFree.RegularityR2Quotient Xo c C ↔ Formalism.L2.Pj.RegularityR2Quotient Xo c C :=
  ⟨fun h aL nL aE nE k ws et c' hc hw he hx q => h aL nL aE nE k ws et c' hc hw he hx (QPt.ofPj q),
   fun h aL nL aE nE k ws et c' hc hw he hx q => h aL nL aE nE k ws et c' hc hw he hx q.toPj⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem intAll_iff : PjFree.IntAll Xo c ↔ Formalism.L2.Pj.IntAll Xo c := Iff.rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem nabUniq_iff : PjFree.NabUniq Xo c ↔ Formalism.L2.Pj.NabUniq Xo c := Iff.rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frBaseChg_eq : @PjFree.FrBaseChg = @Formalism.L2.Pj.FrBaseChg := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem reFrame_eq : @PjFree.ReFrame = @Formalism.L2.Pj.ReFrame := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem xoNumPt_eq : @PjFree.XoNumPt = @Formalism.L2.Pj.XoNumPt := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem locFld_eq : @PjFree.LocFld = @Formalism.L2.Pj.LocFld := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tanLin_eq : @PjFree.TanLin = @Formalism.L2.Pj.TanLin := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sClause_eq : @PjFree.SClause = @Formalism.L2.Pj.SClause := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem intRebase_eq : @PjFree.IntRebase = @Formalism.L2.Pj.IntRebase := rfl

end Formalism.L2.PjFree
