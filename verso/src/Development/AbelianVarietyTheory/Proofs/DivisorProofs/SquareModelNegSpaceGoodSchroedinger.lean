import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdelesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVacuumFinitePlacesRationalDarbouxStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainConjugateUnitaryAdeliStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj

/- English proof (translation)
Introduce `D T L sc G μ₀ _hL t i j M hM B hB X Y hJ r s r' s' hX hY`. Take `⟨co, hco⟩` from `GlobalTheory.T.exists_rational_darboux_hermitian_tensor_adeles D.sp.cm.sig B X Y r s r' s' hB hX hY`. Establish `hR : Node.InRange D.R.m (.grid (i : ℕ) (j : ℕ))` using `⟨i.2.le, j.2.le⟩`. Establish `hH` using `(hM.vtx _ hR).haar_fund`. Take `⟨dom, hh, hd⟩` from `GlobalTheory.T.exists_haar_fundamentalDomain_conjugateUnitaryAdelicIso (spW₁ G i j) (-1) (neg_ne_zero.2 one_ne_zero) hJ _ _ hH.1 hH.2`.

Set `M0 : Model D.sp.cm.sig X Y` to `⟨co, fun _ => 0, (M.ν (.grid (i : ℕ) (j : ℕ))).map (conjU _ (-1) hJ), dom⟩`. Establish `hb` using `GlobalTheory.T.exists_latticeVacuum_finitePlaces_rationalDarboux D.sp.cm.sig B X Y r s r' s' hB hX hY M0 hco`. Establish `hc` using `GlobalTheory.T.eventually_integralPointsIndicator_isVacuum D.sp.cm.sig B X Y r s r' s' hB hX hY M0 hco`. Use `⟨co, fun v => if M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1) then Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1 else (hb v).choose, dom, ?_⟩` and prove the remaining obligations. Use `⟨hco, fun v => ?_, ?_, hh, hd⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `M0.IsVac B.ψ v (if M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1) then Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1 else (hb v).choose)`. Distinguish the cases in `h : M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1)`. Rewrite using `[if_pos h]`. Conclude with `h`. Rewrite using `[if_neg h]`.

Conclude with `(hb v).choose_spec`. Use `filter_upwards [hc] with v hv`. Conclude with `if_pos hv`.
-/
theorem squareModelW₁_good : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW₁ G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (hJ : X.J = (-1 : D.host.E) • (spW₁ G i j).gram) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∃ co vac dom, Model.IsGood (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co vac ((M.ν (.grid (i : ℕ) (j : ℕ))).map (conjU _ (-1) hJ)) dom) B.ψ := by
  intro D T L sc G μ₀ _hL t i j M hM B hB X Y hJ r s r' s' hX hY
  obtain ⟨co, hco⟩ := GlobalTheory.T.exists_rational_darboux_hermitian_tensor_adeles D.sp.cm.sig B X Y r s r' s' hB hX hY
  have hR : Node.InRange D.R.m (.grid (i : ℕ) (j : ℕ)) := ⟨i.2.le, j.2.le⟩
  have hH := (hM.vtx _ hR).haar_fund
  obtain ⟨dom, hh, hd⟩ := GlobalTheory.T.exists_haar_fundamentalDomain_conjugateUnitaryAdelicIso (spW₁ G i j) (-1) (neg_ne_zero.2 one_ne_zero) hJ _ _ hH.1 hH.2
  let M0 : Model D.sp.cm.sig X Y := ⟨co, fun _ => 0, (M.ν (.grid (i : ℕ) (j : ℕ))).map (conjU _ (-1) hJ), dom⟩
  have hb := GlobalTheory.T.exists_latticeVacuum_finitePlaces_rationalDarboux D.sp.cm.sig B X Y r s r' s' hB hX hY M0 hco
  have hc := GlobalTheory.T.eventually_integralPointsIndicator_isVacuum D.sp.cm.sig B X Y r s r' s' hB hX hY M0 hco
  refine ⟨co, fun v => if M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1)
    then Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1 else (hb v).choose, dom, ?_⟩
  refine ⟨hco, fun v => ?_, ?_, hh, hd⟩
  · change M0.IsVac B.ψ v (if M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1)
      then Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1 else (hb v).choose)
    by_cases h : M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1)
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact (hb v).choose_spec
  · filter_upwards [hc] with v hv
    exact if_pos hv

end GlobalTheory.FunObj
