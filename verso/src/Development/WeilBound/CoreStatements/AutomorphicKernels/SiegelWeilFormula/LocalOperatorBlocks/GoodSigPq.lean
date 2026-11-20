import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.POfAddQOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LocOpCont
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocOpMMLaw
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocNbar
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocalOperatorLongWeylIntegral

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Unfold `pOf qOf GoodSig`. Use `split_ifs`. Conclude with `Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))`. Conclude with `Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))`.
-/
theorem goodSig_pq {n m : ℕ} (sg : ℤˣ) (h : n ≤ m) : GoodSig n (pOf sg m) (qOf sg m) := by
  unfold pOf qOf GoodSig
  split_ifs
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))

/- English proof (translation)
Establish `hG : GoodAwayEx` using `KFock.goodAwayEx`. Use `{ sw := fun y f hf => (hL y f hf).1 one := R.locOp_one hT hG hL mul := R.locOp_mul hT hG hL lin := R.locOp_lin hT hG hL nU := R.locOp_nU hT hG hL mM := ?_ nbar := ?_ longWeylFunctional := R.localOperator_longWeyl_integral hT hA hG hL cont := locOp_cont hT R hL }` and prove the remaining obligations. Take `⟨k, hk⟩` from `R.locOp_mM_law w hT hG hL`. Conclude with `⟨k, fun y a ha hy f hf => hk y a ha hy f hf⟩`. Take `⟨C, s, κ, ε, hs, hκ, h4, hf, -, hs2, hη⟩` from `R.locOp_nbar hT hA hG hL`.

Conclude with `⟨C, s, κ, ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹, hs, hκ, hs2, hη, h4, fun y c hc hy f hf' => hf y c hc hy f hf'⟩`.
-/
theorem locHyp_of (hT : TAll) (hA : AuxiliaryPrimeFunction) {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ} (hL : R.IsLocOp w L) :
    LocHyp (R.sg w) L := by
  have hG : GoodAwayEx := KFock.goodAwayEx
  refine
    { sw := fun y f hf => (hL y f hf).1
      one := R.locOp_one hT hG hL
      mul := R.locOp_mul hT hG hL
      lin := R.locOp_lin hT hG hL
      nU := R.locOp_nU hT hG hL
      mM := ?_
      nbar := ?_
      longWeylFunctional := R.localOperator_longWeyl_integral hT hA hG hL
      cont := locOp_cont hT R hL }
  · obtain ⟨k, hk⟩ := R.locOp_mM_law w hT hG hL
    exact ⟨k, fun y a ha hy f hf => hk y a ha hy f hf⟩
  · obtain ⟨C, s, κ, ε, hs, hκ, h4, hf, -, hs2, hη⟩ := R.locOp_nbar hT hA hG hL
    exact ⟨C, s, κ, ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹, hs, hκ, hs2, hη, h4, fun y c hc hy f hf' => hf y c hc hy f hf'⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d R w L hL`. Take `⟨sL, ρ, e, hD, h1, h2⟩` from `locData_of (locHyp_of hT hA R hL)`. Conclude with `⟨sL, ρ, pOf (R.sg w) d.m, qOf (R.sg w) d.m, e, fun hnm => goodSig_pq _ hnm, hD, h1, h2⟩`.
-/
theorem locInst_of (hT : TAll) (hA : AuxiliaryPrimeFunction) (_hF : FockMem) (_hLi : LiftEx) : LocInst := by
  intro F E _ _ _ _ _ σ d R w L hL
  obtain ⟨sL, ρ, e, hD, h1, h2⟩ := locData_of (locHyp_of hT hA R hL)
  exact ⟨sL, ρ, pOf (R.sg w) d.m, qOf (R.sg w) d.m, e, fun hnm => goodSig_pq _ hnm, hD, h1, h2⟩

end PositivityTheory.SiegelWeilFormula.KLI

end
