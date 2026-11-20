import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace

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

/- English proof (translation)
Introduce `E _ _ _ a b Z L w`. Establish `hK2 : K2 a b w = (KGL w a).prod (KGL w b)` using `rfl`. Establish `hop : IsOpen (((L.L₁ w).prod (L.L₂ w) : Subgroup _) : Set (GLw a w × GLw b w))`. Rewrite using `[Subgroup.coe_prod]`. Conclude with `(L.open₁ w).prod (L.open₂ w)`.

Establish `hle : (L.L₁ w).prod (L.L₂ w) ≤ K2 a b w` using `Subgroup.prod_mono (L.le₁ w) (L.le₂ w)`. Establish `hKop : IsOpen ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w))`. Rewrite using `[hK2, Subgroup.coe_prod]`. Conclude with `(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1`. Establish `hln : L.ln w = idem ((L.L₁ w).prod (L.L₂ w))` using `rfl`.

Establish `hKi : idem (K2 a b w) = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1`. Use function extensionality and compare the values at `y`. Simplify using `only [idem, Subgroup.relIndex_self, Nat.cast_one]`. Both sides reduce to the same expression. Take `⟨h1, h2, h3⟩` from `PositivityTheory.Rg.BcB.F.idemAlg E a b w _ hop hle`.

Take `⟨-, -, k3⟩` from `PositivityTheory.Rg.BcB.F.idemAlg E a b w _ hKop le_rfl`. Use `⟨hln ▸ h1, hln ▸ h2, fun hw => ?_, fun f hf => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨e₁, e₂⟩` from `L.off w hw`. Rewrite using `[hln, e₁, e₂, ← hK2, hKi]`. Rewrite using `[hln]`.

Conclude with `⟨(h3 f hf).2.1, (h3 f hf).1⟩`. Rewrite using `[← hKi]`. Conclude with `⟨(k3 f hf).2.1, (k3 f hf).1, (k3 f hf).2.2⟩`.
-/
theorem locAlg : LocAlg := by
  intro E _ _ _ a b Z L w
  have hK2 : K2 a b w = (KGL w a).prod (KGL w b) := rfl
  have hop : IsOpen (((L.L₁ w).prod (L.L₂ w) : Subgroup _) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (L.open₁ w).prod (L.open₂ w)
  have hle : (L.L₁ w).prod (L.L₂ w) ≤ K2 a b w := Subgroup.prod_mono (L.le₁ w) (L.le₂ w)
  have hKop : IsOpen ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
    rw [hK2, Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1
  have hln : L.ln w = idem ((L.L₁ w).prod (L.L₂ w)) := rfl
  have hKi : idem (K2 a b w) = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 := by
    funext y
    simp only [idem, Subgroup.relIndex_self, Nat.cast_one]
    rfl
  obtain ⟨h1, h2, h3⟩ := PositivityTheory.Rg.BcB.F.idemAlg E a b w _ hop hle
  obtain ⟨-, -, k3⟩ := PositivityTheory.Rg.BcB.F.idemAlg E a b w _ hKop le_rfl
  refine ⟨hln ▸ h1, hln ▸ h2, fun hw => ?_, fun f hf => ?_, fun f hf => ?_⟩
  · obtain ⟨e₁, e₂⟩ := L.off w hw
    rw [hln, e₁, e₂, ← hK2, hKi]
  · rw [hln]
    exact ⟨(h3 f hf).2.1, (h3 f hf).1⟩
  · rw [← hKi]
    exact ⟨(k3 f hf).2.1, (k3 f hf).1, (k3 f hf).2.2⟩

end UpperTheory.Zero.ConvolutionTheory.EB

end
