import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicConjugateCharacterStandardForms
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAdelicConjugateCharacterStandardForms.lean&line=239#L239)
-/
theorem _root_.GlobalTheory.T.adelic_conjugate_character_standard_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), AdC (F u) i hi c c' γ ((F u).atT.eV v).1 → ∀ q : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E), q.under (𝓞 (I.rec7 l Z).host.F) ≠ ((F u).atT.eV v).1 → Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (Formalism.L2.Forms.mulLat γ.1 (clsCrd (I.rec7 l Z) u i hi c')) = Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (clsCrd (I.rec7 l Z) u i hi c) := by
  first | exact @GlobalTheory.Mem.Col2.SameOff.use₆ | exact GlobalTheory.Mem.Col2.SameOff.use₆ | (intros; apply GlobalTheory.Mem.Col2.SameOff.use₆ <;> assumption)
