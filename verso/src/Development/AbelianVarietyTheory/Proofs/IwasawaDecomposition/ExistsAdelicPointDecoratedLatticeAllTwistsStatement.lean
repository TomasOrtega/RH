import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointDecoratedLatticeAllTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsAdelicPointDecoratedLatticeAllTwists.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_adelicPoint_decoratedLattice_allTwists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (n : ℕ) (p : DecoF B.fields.E n ((B.primes X).vT u) (B.primes X).vGs I.SQ), ∃ g : GA B n, PtOf g p := by
  first | exact @GlobalTheory.Mem.Col2.PtTwist.exists_ptOf_twists | exact GlobalTheory.Mem.Col2.PtTwist.exists_ptOf_twists | (intros; apply GlobalTheory.Mem.Col2.PtTwist.exists_ptOf_twists <;> assumption)
