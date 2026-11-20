import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem GlobalTheory.Mem.Col2.TC.dtTied_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ T : Formalism.L2.Host.DtTied (I.rec7 l Z) (I.cf l Z), ∀ a, T.eDt a = (QuotientGroup.mk a : DtQ B.host I.SQ) := by
  intro B X I _ _ l Z
  refine ⟨GlobalTheory.Mem.Col2.dtIsoRational (I.rec7 l Z) (I.cf l Z) I.SQ (MulEquiv.refl _) (fun j => rfl) rfl ?_ (fun z => rfl), fun _ => rfl⟩
  show UOQ B.host I.SQ = _
  ext x
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy
