import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFrameCol
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialFourierInversion

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KappaTheta

/- English proof (translation)
Introduce `D ψ L S L'' τ hτ f hf`. Establish `hτ' : τᴴ * (L.gram * τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram`. Rewrite using `[hτ]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `set κ : WO S L'' → WO L S := fun w => GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w) with hκdef`. Take `⟨hadd, hcont, hrat, -, hsym, hparts⟩` from `GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1) hτ' κ (fun _ => rfl)`. Establish `hH : ∀ w w', symplOH L S (κ w) (κ w') = symplOH S L'' w w'` using `fun w w' => by`. Unfold `symplOH`.

Rewrite using `[hsym]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Set `A : WO S L'' →+ WO L S` to `AddMonoidHom.mk' κ hadd`. Use `⟨fun γ w => ?_, ?_, hf.cont.comp hcont, fun k M h1 h2 w => ?_⟩` and prove the remaining obligations.

Take `⟨γ', hγ'⟩` from `hrat (ratW L'' S γ) ⟨γ, rfl⟩ show f (κ (ratW L'' S γ + w)) = ψ (-(symplOH S L'' (ratW L'' S γ) w)) * f (κ w)`. Establish `e : κ (ratW L'' S γ) = ratW S L γ'` using `hγ'.symm`. Rewrite using `[hadd, ← hH, e, hf.quasi]`. Take `⟨U, hU, h⟩` from `hf.level`. Use `⟨U.comap A, hU.preimage hcont, fun u hu h0 => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `w`. Establish `e` using `congrFun (h _ hu ((hparts u).1 h0)) (κ w)`. Unfold `heisO at e ⊢`. Use `show ψ (symplOH S L'' w u) * f (κ (w + u)) = f (κ w)`. Rewrite using `[← e, ← hH, hadd]`.

Both sides reduce to the same expression. Establish `h3 : ∀ t, (A (M t)).map (finPart D) = 0` using `fun t => (hparts (M t)).2 (h2 t)`. Use `hf.smooth k (A.comp M) (hcont.comp h1) h3 (κ w)` as an intermediate fact. Establish `heq : (fun t => f (κ (w + M t))) = fun t => f (κ w + A (M t))`. Use function extensionality and compare the values at `fun t => congrArg f (hadd w (M t))`.

Conclude with `(congrArg (ContDiff ℝ _) heq).mpr this`.
-/
theorem isThetaFunO_comp_kappa : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (L S L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ f, IsThetaFunO ψ L S f → IsThetaFunO ψ S L'' (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w))) := by
  intro D ψ L S L'' τ hτ f hf
  have hτ' : τᴴ * (L.gram * τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; congr 1; push_cast; ring
  set κ : WO S L'' → WO L S := fun w => GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w) with hκdef
  obtain ⟨hadd, hcont, hrat, -, hsym, hparts⟩ :=
    GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1) hτ' κ (fun _ => rfl)
  have hH : ∀ w w', symplOH L S (κ w) (κ w') = symplOH S L'' w w' := fun w w' => by
    unfold symplOH
    rw [hsym]
    push_cast
    ring
  let A : WO S L'' →+ WO L S := AddMonoidHom.mk' κ hadd
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp hcont, fun k M h1 h2 w => ?_⟩
  · obtain ⟨γ', hγ'⟩ := hrat (ratW L'' S γ) ⟨γ, rfl⟩
    show f (κ (ratW L'' S γ + w)) = ψ (-(symplOH S L'' (ratW L'' S γ) w)) * f (κ w)
    have e : κ (ratW L'' S γ) = ratW S L γ' := hγ'.symm
    rw [hadd, ← hH, e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hcont, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu ((hparts u).1 h0)) (κ w)
    unfold heisO at e ⊢
    show ψ (symplOH S L'' w u) * f (κ (w + u)) = f (κ w)
    rw [← e, ← hH, hadd]
    rfl
  · have h3 : ∀ t, (A (M t)).map (finPart D) = 0 := fun t => (hparts (M t)).2 (h2 t)
    have := hf.smooth k (A.comp M) (hcont.comp h1) h3 (κ w)
    have heq : (fun t => f (κ (w + M t))) = fun t => f (κ w + A (M t)) :=
      funext fun t => congrArg f (hadd w (M t))
    exact (congrArg (ContDiff ℝ _) heq).mpr this

end GlobalTheory.KappaTheta

end
