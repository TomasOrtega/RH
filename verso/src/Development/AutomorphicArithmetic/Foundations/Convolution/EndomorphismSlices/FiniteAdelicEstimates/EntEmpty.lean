import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

private def lmOf (φ₁ φ₂ : ∀ w : Pl E, LF a b w) : LM (fun _ : Pl E => Unit) a b :=
  ⟨fun w _ _ => φ₁ w, φ₁, φ₂⟩

private def eU : Unit ≃ ∀ _ : (∅ : Finset (Pl E)), Unit := Equiv.ofUnique _ _

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `[LM.ent]`.
-/
private theorem ent_empty (L : LM (fun _ : Pl E => Unit) a b) (x y : ∀ _ : (∅ : Finset (Pl E)), Unit) :
    L.ent ∅ x y = L.s := by
  funext w; simp [LM.ent]

/- English proof (translation)
Use function extensionality and compare the values at `x y h`. Simplify using `only [Ar.ff, fm, ent_empty]`.
-/
private theorem ff_fm {l₁ : InfinitePlace E → DomWeight a} {l₂ : InfinitePlace E → DomWeight b} {D : Dom E a b}
    (A : Ar l₁ l₂ D) (S : Set (Pl E)) (L : LM (fun _ : Pl E => Unit) a b) :
    A.ff S L.s L.t = fm S ∅ A.blk eU L := by
  funext x y h
  simp only [Ar.ff, fm, ent_empty]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x y => by rw [ent_empty]; exact h₁, h₂⟩`.
-/
private theorem ok_lm {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) : (lmOf φ₁ φ₂).Ok ∅ :=
  ⟨fun x y => by rw [ent_empty]; exact h₁, h₂⟩

end

/- English proof (translation)
Introduce `E _ _ _ a b l₁ l₂ D A S hS`. Use `⟨(BlockFiniteConvolution.finConv' E A.blk S hS).1, fun φ₁ φ₂ h₁ h₂ => ?_⟩` and prove the remaining obligations. Establish `alg` using `fun (φ₁' φ₂' : ∀ w : Pl E, LF a b w) (h₁' : IsTestP φ₁') (h₂' : IsTestP φ₂') => BlockFiniteConvolution.fmAlg' E (fun _ => Unit) S ∅ A.blk eU hS (by simp) (lmOf φ₁ φ₂) (lmOf φ₁' φ₂') (ok_lm h₁ h₂) (ok_lm h₁' h₂')`. Take `⟨hf, -, -, -, hadj⟩` from `alg φ₁ φ₂ h₁ h₂`. Use `⟨?_, ?_, Fm.isTestFunction_star h₁, Fm.isTestFunction_star h₂, fun φ₁' φ₂' h₁' h₂' => ?_⟩` and prove the remaining obligations.

Use `ff_fm A S (lmOf φ₁ φ₂)` as an intermediate fact. Conclude with `this ▸ hf`. Conclude with `(congrArg adjF (ff_fm A S (lmOf φ₁ φ₂))).trans (hadj.trans (ff_fm A S (lmOf φ₁ φ₂).adj).symm)`. Take `⟨-, -, hmul, -, -⟩` from `alg φ₁' φ₂' h₁' h₂'`. Establish `e₁` using `ff_fm A S (lmOf φ₁ φ₂)`.

Establish `e₂` using `ff_fm A S (lmOf φ₁' φ₂')`. Establish `e₃` using `ff_fm A S ((lmOf φ₁ φ₂).mul (lmOf φ₁' φ₂'))`. Conclude with `(congrArg₂ (mulF A.ν) e₁ e₂).trans (hmul.trans e₃.symm)`.
-/
theorem ffAlg : FfAlg := by
  intro E _ _ _ a b l₁ l₂ D A S hS
  refine ⟨(BlockFiniteConvolution.finConv' E A.blk S hS).1, fun φ₁ φ₂ h₁ h₂ => ?_⟩
  have alg := fun (φ₁' φ₂' : ∀ w : Pl E, LF a b w) (h₁' : IsTestP φ₁') (h₂' : IsTestP φ₂') =>
    BlockFiniteConvolution.fmAlg' E (fun _ => Unit) S ∅ A.blk eU hS (by simp) (lmOf φ₁ φ₂) (lmOf φ₁' φ₂') (ok_lm h₁ h₂) (ok_lm h₁' h₂')
  obtain ⟨hf, -, -, -, hadj⟩ := alg φ₁ φ₂ h₁ h₂
  refine ⟨?_, ?_, Fm.isTestFunction_star h₁, Fm.isTestFunction_star h₂, fun φ₁' φ₂' h₁' h₂' => ?_⟩
  · have := ff_fm A S (lmOf φ₁ φ₂)
    exact this ▸ hf
  · exact (congrArg adjF (ff_fm A S (lmOf φ₁ φ₂))).trans (hadj.trans (ff_fm A S (lmOf φ₁ φ₂).adj).symm)
  · obtain ⟨-, -, hmul, -, -⟩ := alg φ₁' φ₂' h₁' h₂'
    have e₁ := ff_fm A S (lmOf φ₁ φ₂)
    have e₂ := ff_fm A S (lmOf φ₁' φ₂')
    have e₃ := ff_fm A S ((lmOf φ₁ φ₂).mul (lmOf φ₁' φ₂'))
    exact (congrArg₂ (mulF A.ν) e₁ e₂).trans (hmul.trans e₃.symm)

end UpperTheory.Zero.ConvolutionTheory.EB

end
