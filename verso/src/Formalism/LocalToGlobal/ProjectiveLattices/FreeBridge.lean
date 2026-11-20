import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.PtFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree

noncomputable section

namespace Formalism.L2.PjFree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

section Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem FDSec_eq (X : Comp → Data E r) : FDSec X = Formalism.L2.Pj.FDSec X := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem isHolCusp_iff (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) :
    IsHolCusp X la P ↔ Formalism.L2.Pj.IsHolCusp X la P := by rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem supE_eq (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) :
    supE X la P = Formalism.L2.Pj.supE X la P := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem supN_eq (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) :
    supN X la P = Formalism.L2.Pj.supN X la P := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem holSub_eq (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) : holSub X la = Formalism.L2.Pj.holSub X la := rfl

end Sections

section Unif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def Unf.ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) : Unf Xo c σ r :=
  { Comp := U.Comp, fin := U.fin, X := U.X, un := U.un }

def Unf.toPj (U : Unf Xo c σ r) : Formalism.L2.Pj.Unf Xo c σ r :=
  { Comp := U.Comp, fin := U.fin, X := U.X, un := U.un }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Unf.toPj_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) : (Unf.ofPj U).toPj = U := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Unf.ofPj_toPj (U : Unf Xo c σ r) : Unf.ofPj U.toPj = U := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rdU_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) (f : Formalism.L2.Pj.Rul Xo c) : rdU (Unf.ofPj U) f = Formalism.L2.Pj.rdU U f := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem laU_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) :
    laU (Unf.ofPj U) a n k = Formalism.L2.Pj.laU U a n k := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem isUnf_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) : IsUnf (Unf.ofPj U) ↔ Formalism.L2.Pj.IsUnf U := by rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem goodEmb_iff (σ : c.F →+* ℂ) : GoodEmb c σ ↔ Formalism.L2.Pj.GoodEmb c σ := by rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem goodOf_eq (σ : c.F →+* ℂ) : goodOf c σ = Formalism.L2.Pj.goodOf c σ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lieFac_eq (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : lieFac Dw x a = Formalism.L2.Pj.lieFac Dw x a := rfl

variable (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cusp_ofPj (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    cusp Xo c (fun σ => Unf.ofPj (U σ)) a n = Formalism.L2.Pj.cusp Xo c U a n := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cuspMul_ofPj : CuspMul Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.CuspMul Xo c U := by rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cuspFD_ofPj : CuspFD Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.CuspFD Xo c U := by rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem supC_ofPj (x : ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Formalism.L2.Pj.Rul Xo c) :
    supC Xo c (fun σ => Unf.ofPj (U σ)) x σ a n f = Formalism.L2.Pj.supC Xo c U x σ a n f := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem supDef_ofPj : SupDef Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.SupDef Xo c U := by rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem regP_ofPj : regular₂ Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.regular₂ Xo c U := by rfl

end Unif

section Points

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Apply the first step, then apply the next step to every resulting obligation. Fix the arbitrary inputs or assume the hypotheses.

Split into cases according to the possible forms of the given data. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem isVal_iff {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    (la : HeightOneSpectrum (𝓞 K)) (v : R → EReal) : IsVal la v ↔ Formalism.L2.Pj.IsVal la v := by
  constructor
  · intro hv
    cases hv
    constructor <;> assumption
  · intro hv
    cases hv
    constructor <;> assumption

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l) (cls : ∀ (T : Formalism.L2.Pj.CDVR) (ι : c.F →+* T.Fr), Formalism.L2.Pj.IntFr Xo c T ι → Prop)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algCls_iff (T : Formalism.L2.Pj.CDVR) (ι : c.F →+* T.Fr) (y : Formalism.L2.Pj.IntFr Xo c T ι) :
    algCls Xo c T ι y ↔ Formalism.L2.Pj.algCls Xo c T ι y := by rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem valSet_eq (la : HeightOneSpectrum (𝓞 c.F)) : valSet Xo c cls la = Formalism.L2.Pj.valSet Xo c cls la := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem allCls_iff (T : Formalism.L2.Pj.CDVR) (ι : c.F →+* T.Fr) (y : Formalism.L2.Pj.IntFr Xo c T ι) :
    trivialClassCondition Xo c T ι y ↔ Formalism.L2.Pj.trivialClassCondition Xo c T ι y := by rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trivSet_eq : trivSet Xo c = Formalism.L2.Pj.trivSet Xo c := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem noCommonZero_iff {n : ℕ} (ws : Fin n → Formalism.L2.Pj.Rul Xo c) :
    NoCommonZero Xo c ws ↔ Formalism.L2.Pj.NoCommonZero Xo c ws := by rfl

end Points

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {r : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem perFr_eq (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x v τ i = Formalism.L2.Pj.perFr X x v τ i := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem relab_eq (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) : relab c σ τ = Formalism.L2.Pj.relab c σ τ := rfl

end Frames

end Formalism.L2.PjFree
