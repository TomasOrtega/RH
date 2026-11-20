import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

namespace GlobalTheory.IdemSumConj

/- English proof (translation)
Introduce `D P e h`. Use `⟨P.image Formalism.L2.DIV.conjPl, ?_⟩` and prove the remaining obligations. Take `⟨⟨es, hes, he⟩, hc⟩` from `h`. Use `⟨⟨fun Q => cA D (es (Formalism.L2.DIV.conjPl Q)), ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `Q hQ`.

Take `⟨PP, hPP, rfl⟩` from `Finset.mem_image.1 hQ`. Use `show Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.DIV.conjPl (Formalism.L2.DIV.conjPl PP)))) (Formalism.L2.DIV.conjPl PP)`. Rewrite using `[Formalism.L2.DIV.conjPl_conjPl]`. Conclude with `GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun x => Iff.rfl`. Rewrite using `[Finset.sum_image (fun a _ b _ (hab : Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b) => by`.

Rewrite using `[← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl b])]`. Simplify using `only [Formalism.L2.DIV.conjPl_conjPl]`. Rewrite using `[he, map_sum]`. Rewrite using `[GlobalTheory.MovedIdem.cA_cA, mul_comm]`. Conclude with `hc`.
-/
theorem exists_isIdemSum_cA :
    ∀ (D : D7) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q →
      ∃ Q' : Finset (Formalism.L2.DIV.Pl D.host.E), IsIdemSum (cA D E₂) Q' := by
  intro D P e h
  classical
  refine ⟨P.image Formalism.L2.DIV.conjPl, ?_⟩
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  refine ⟨⟨fun Q => cA D (es (Formalism.L2.DIV.conjPl Q)), ?_, ?_⟩, ?_⟩
  · intro Q hQ
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ
    show Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.DIV.conjPl (Formalism.L2.DIV.conjPl PP)))) (Formalism.L2.DIV.conjPl PP)
    rw [Formalism.L2.DIV.conjPl_conjPl]
    exact GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun x => Iff.rfl
  · rw [Finset.sum_image (fun a _ b _ (hab : Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b) => by
      rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl b])]
    simp only [Formalism.L2.DIV.conjPl_conjPl]
    rw [he, map_sum]
  · rw [GlobalTheory.MovedIdem.cA_cA, mul_comm]; exact hc

end GlobalTheory.IdemSumConj
