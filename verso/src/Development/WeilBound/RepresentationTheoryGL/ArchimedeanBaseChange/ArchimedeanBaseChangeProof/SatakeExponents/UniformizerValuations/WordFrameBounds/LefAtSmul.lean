import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.WaAtPlaceLs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.WbAdjOk
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.PtLVal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFrameOk
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HermitianConvolution.EllHomPf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace PositivityTheory.Rg.BcB.F.B3

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

namespace PWordId2

section Frame

variable {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T)
/- English proof (translation)
Use `⟨continuous_const.mul h.1, h.2.1.mul_left, fun d₁ d₂ h₁ h₂ => ?_⟩` and prove the remaining obligations. Rewrite using `[integral_const_mul, h.2.2 d₁ d₂ h₁ h₂]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lefAt_smul {a b : ℕ} {ν₁ : Measure (G a)} {ν₂ : Measure (G b)} {l₁ : DomWeight a} {l₂ : DomWeight b} {val : ℂ}
    {ψ : G a × G b → ℂ} (h : LefAt ν₁ ν₂ l₁ l₂ val ψ) (c : ℂ) : LefAt ν₁ ν₂ l₁ l₂ (c * val) fun y => c * ψ y := by
  refine ⟨continuous_const.mul h.1, h.2.1.mul_left, fun d₁ d₂ h₁ h₂ => ?_⟩
  rw [integral_const_mul, h.2.2 d₁ d₂ h₁ h₂]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [adel, Finset.prod_mul_distrib, Pi.smul_apply, smul_eq_mul, mul_assoc]`.
-/
theorem adel_scale {a b : ℕ} (S : Set (Pl E)) (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E) (ψ : InfinitePlace E → G a × G b → ℂ)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (c : InfinitePlace E → ℂ) :
    adel S u₁ u₂ (fun v y => c v * ψ v y) φ₁ φ₂ = (∏ v, c v) • adel S u₁ u₂ ψ φ₁ φ₂ := by
  funext x
  simp only [adel, Finset.prod_mul_distrib, Pi.smul_apply, smul_eq_mul, mul_assoc]

/- English proof (translation)
Use `choose c₀ hc₀ hT using fun i => BlockFiniteConvolution.pTTest₀ E (F.B i)`. Use `⟨fun i => F₀.C.c i * (F.B i).vol, c₀, hc₀, fun ws hws => ?_⟩` and prove the remaining obligations. Take `⟨-, -, hm⟩` from `lm F hE h' ws hws`. Establish `hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec` using `FrameOk.wirtinger_sub F`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations.

Take `⟨b1, b2, b3, -⟩` from `blk_eq F h hF i ws`. Conclude with `hT i F.d.kap F₀.Sec F.d.P (Equiv.refl _) F₀.hSec hP (fun w _ => (BlockFiniteConvolution.locOk₀ E n F.d F.ok _ (F₀.C.le i)).1 w) _ _ (F₀.hu _).1 (F₀.hu _).2 _ _ F.d.one _ _ ⟨(F₀.A i).vca, (F₀.A i).vcb⟩ b2 b1 b3 (hm _ (F₀.C.le i)).2`. Take `⟨t1, t2⟩` from `trace_eq F hE h' ws hws`. Take `⟨v₀⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `hμ : ∀ w, F.d.μ w = F₀.μ.loc w` using `fun w => by rw [← F₀.μloc w, F.same.2.2.1]`.

Set `sc : F₀.C.ι → InfinitePlace E → ℂ` to `fun i v => if v = v₀ then BGen.sc (ws.map (bw F i)).flatten else 1`. Establish `hsc : ∀ i, ∏ v, sc i v = BGen.sc (ws.map (bw F i)).flatten` using `fun i => by simp [sc]`. Establish `key` using `F₀.C.eq F₀.Sec F₀.hSec F.d.KU _ F.levOff.2.1 t1 F₀.u₁ F₀.u₂ F₀.hu (fun a => (prodL F.d (ls F ws) a).tr F.d.P F.d.one) (fun a => (prodL F.d (ls F ws) a).t) (fun a ha => ⟨(hm a ha).1.1, (hm a ha).1.2.1, (hm a ha).1.2.2.1, fun w hw => hμ w ▸ (hm a ha).1.2.2.2 w hw⟩) (fun i => by`. Take `⟨w, hw, hs, hr⟩` from `(hm _ (F₀.C.le i)).2`. Use `⟨w, hw, fun y hy => hr y ?_⟩` and prove the remaining obligations.

Simplify `hy)` using `[seen, hs]`. Use the proof step `(fun i v => sc i v * ((tw F i ws).va v ((F₀.A i).χa v) * (tw F i ws).vb v ((F₀.A i).χb v)))`. Use the proof step `(fun i v y => sc i v * (tw F i ws).arch (F₀.A i).Ta (F₀.A i).Tb v y)`. Use the proof step `(fun i v => lefAt_smul (lef_pt F i _ (blk_eq F h hF i ws).2.1 v) _) (U.UGen.sc (lU F ws))`. Use the proof step `(fun i => by`.

Rewrite using `[Finset.prod_mul_distrib, Finset.prod_mul_distrib, hsc, ← val_eq F hF i ws]`. Use the proof step `rfl)`. Use `t2.trans (key.trans (Finset.sum_congr rfl fun i _ => ?_))` and prove the remaining obligations. Establish `hv : (F.B i).vol ≠ 0` using `(BlockFiniteConvolution.finConv' E (F.B i) F₀.Sec F₀.hSec).1`. Rewrite using `[adel_scale, hsc, (blk_eq F h hF i ws).2.2.2, FBL.ellHom_holds, FBL.ellHom_holds]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem main (hE : GlobalTheory.BCT.Unr E) (h : LocWord) (h' : LocMatch) (hF : F.Struct) : WordIdAt F := by
  choose c₀ hc₀ hT using fun i => BlockFiniteConvolution.pTTest₀ E (F.B i)
  refine ⟨fun i => F₀.C.c i * (F.B i).vol, c₀, hc₀, fun ws hws => ?_⟩
  obtain ⟨-, -, hm⟩ := lm F hE h' ws hws
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := FrameOk.wirtinger_sub F
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨b1, b2, b3, -⟩ := blk_eq F h hF i ws
    exact hT i F.d.kap F₀.Sec F.d.P (Equiv.refl _) F₀.hSec hP
      (fun w _ => (BlockFiniteConvolution.locOk₀ E n F.d F.ok _ (F₀.C.le i)).1 w) _ _ (F₀.hu _).1 (F₀.hu _).2 _ _ F.d.one _ _
      ⟨(F₀.A i).vca, (F₀.A i).vcb⟩ b2 b1 b3 (hm _ (F₀.C.le i)).2
  obtain ⟨t1, t2⟩ := trace_eq F hE h' ws hws
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hμ : ∀ w, F.d.μ w = F₀.μ.loc w := fun w => by rw [← F₀.μloc w, F.same.2.2.1]
  let sc : F₀.C.ι → InfinitePlace E → ℂ := fun i v => if v = v₀ then BGen.sc (ws.map (bw F i)).flatten else 1
  have hsc : ∀ i, ∏ v, sc i v = BGen.sc (ws.map (bw F i)).flatten := fun i => by simp [sc]
  have key := F₀.C.eq F₀.Sec F₀.hSec F.d.KU _ F.levOff.2.1 t1 F₀.u₁ F₀.u₂ F₀.hu
    (fun a => (prodL F.d (ls F ws) a).tr F.d.P F.d.one) (fun a => (prodL F.d (ls F ws) a).t)
    (fun a ha => ⟨(hm a ha).1.1, (hm a ha).1.2.1, (hm a ha).1.2.2.1, fun w hw => hμ w ▸ (hm a ha).1.2.2.2 w hw⟩)
    (fun i => by
      obtain ⟨w, hw, hs, hr⟩ := (hm _ (F₀.C.le i)).2
      refine ⟨w, hw, fun y hy => hr y ?_⟩
      simpa [seen, hs] using hy)
    (fun i v => sc i v * ((tw F i ws).va v ((F₀.A i).χa v) * (tw F i ws).vb v ((F₀.A i).χb v)))
    (fun i v y => sc i v * (tw F i ws).arch (F₀.A i).Ta (F₀.A i).Tb v y)
    (fun i v => lefAt_smul (lef_pt F i _ (blk_eq F h hF i ws).2.1 v) _) (U.UGen.sc (lU F ws))
    (fun i => by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hsc, ← val_eq F hF i ws]
      rfl)
  refine t2.trans (key.trans (Finset.sum_congr rfl fun i _ => ?_))
  have hv : (F.B i).vol ≠ 0 := (BlockFiniteConvolution.finConv' E (F.B i) F₀.Sec F₀.hSec).1
  rw [adel_scale, hsc, (blk_eq F h hF i ws).2.2.2, FBL.ellHom_holds, FBL.ellHom_holds]
  field_simp

end Frame

end PWordId2

end PositivityTheory.Rg.BcB.F.B3

end
