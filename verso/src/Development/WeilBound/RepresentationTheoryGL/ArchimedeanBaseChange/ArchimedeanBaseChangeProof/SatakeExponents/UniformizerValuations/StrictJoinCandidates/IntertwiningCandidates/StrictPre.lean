import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.LocIso
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.LocUniq

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

namespace StrictPreorder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Substitute `h` using the available equality. Use `hR.get (i := i.1) (by simp) (by simp)` as an intermediate fact. Simplify using `using this`.
-/
theorem forall₂_ofFn {α β : Type} {R : α → β → Prop} {c c' : ℕ} (h : c = c') (f : Fin c → α) (g : Fin c' → β)
    (hR : List.Forall₂ R (List.ofFn f) (List.ofFn g)) (i : Fin c) : R (f i) (g (Fin.cast h i)) := by
  subst h
  have := hR.get (i := i.1) (by simp) (by simp)
  simpa using this

/- English proof (translation)
Take `⟨x1, x2⟩` from `x`. Take `⟨y1, y2⟩` from `y`. Take `⟨h, hI⟩` from `hxy`. Simplify using `only at h`. Substitute `h` using the available equality.

Conclude with `F5.Bo.LocUniq_holds E x1 y2 hy w σ σ' (F5.Bo.LocIso_holds E x1 x2 y2 hI w σ hσ) hσ'`.
-/
theorem cls_eq (x y : Σ M : ℕ, Submodule ℂ (Sm E M)) (hxy : SIso x y) (hy : IsDiscrete y.2)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin x.1) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin y.1) (w.adicCompletion E))) (hσ : IsLocCompGL x.2 w σ) (hσ' : IsLocCompGL y.2 w σ') :
    GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred = GlobalTheory.LocGL.IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨h, hI⟩ := hxy
  simp only at h
  subst h
  exact F5.Bo.LocUniq_holds E x1 y2 hy w σ σ' (F5.Bo.LocIso_holds E x1 x2 y2 hI w σ hσ) hσ'

end StrictPreorder

/- English proof (translation)
Introduce `E _ _ _ n P P' hS`. Take `⟨hF, hc, hm⟩` from `hS`. Use `⟨finCongr hc, fun i w => ?_, fun i τ => congrFun (hm i) τ⟩` and prove the remaining obligations. Establish `hI : SIso ⟨P.N i, P.V i⟩ ⟨P'.N (Fin.cast hc i), P'.V (Fin.cast hc i)⟩` using `StrictPreorder.forall₂_ofFn hc (fun j => (⟨P.N j, P.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) (fun j => (⟨P'.N j, P'.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) hF i`. Conclude with `StrictPreorder.cls_eq _ _ hI (P'.discrete _) w (P.σ i w) (P'.σ _ w) (P.loc i w) (P'.loc _ w)`.
-/
theorem StrictPre_holds : StrictPre := by
  intro E _ _ _ n P P' hS
  obtain ⟨hF, hc, hm⟩ := hS
  refine ⟨finCongr hc, fun i w => ?_, fun i τ => congrFun (hm i) τ⟩
  have hI : SIso ⟨P.N i, P.V i⟩ ⟨P'.N (Fin.cast hc i), P'.V (Fin.cast hc i)⟩ :=
    StrictPreorder.forall₂_ofFn hc (fun j => (⟨P.N j, P.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)))
      (fun j => (⟨P'.N j, P'.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) hF i
  exact StrictPreorder.cls_eq _ _ hI (P'.discrete _) w (P.σ i w) (P'.σ _ w) (P.loc i w) (P'.loc _ w)

end PositivityTheory.Rg.BcB.F.FX.Bo

end
