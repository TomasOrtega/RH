import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfDecoratedLatticeUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FIsPointOfDecoratedLatticeUnique.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.isPointOfDecoratedLattice_unique : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (g : GL (Fin n) (Formalism.L2.DIV.AfE F E)) (p p' : Formalism.L2.Col.DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g p → GlobalTheory.Mem.Col2.IsPtOf hc g p' → p = p' := by
  first | exact @GlobalTheory.Mem.Col2.PtUniq.isPtOf_unique | exact GlobalTheory.Mem.Col2.PtUniq.isPtOf_unique | (intros; apply GlobalTheory.Mem.Col2.PtUniq.isPtOf_unique <;> assumption)
