import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : ThetaX D}

structure ThetaTiedDef (T : ThetaTied D X) : Prop where

  ev_def : ∀ V : HSp D, V.SigOK → V.IsDefinite → Set.range (T.ev V) = {φ | IsAutFunDef V φ}

  typ : ∀ V : HSp D, V.SigOK → V.IsDefinite → ∀ P : D.what₂.Tau → SPar,
    (∀ τ, GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 (P τ)) →
    X.typ V P = ⨅ τ, isoDef (gramAt D V τ) (X.actR V τ) (P τ)

def AutFunDefIffSm (D : D7) : Prop :=
  ∀ θ, IsInfFam (D := D) θ → ∀ V : HSp D, V.SigOK → V.IsDefinite → ∀ φ, IsAutFunDef V φ ↔ IsAutFunSm θ V φ

def IsoDefIffTypeAt (T : ThetaTied D X) : Prop :=
  ∀ θ, IsInfFam (D := D) θ → ∀ V : HSp D, V.SigOK → V.IsDefinite → ∀ P : D.what₂.Tau → SPar,
    (∀ τ, GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 (P τ)) → ∀ F : X.AF V,
      F ∈ (⨅ τ, isoDef (gramAt D V τ) (X.actR V τ) (P τ)) ↔ ∀ τ, IsTypeAt θ V τ (P τ) (T.ev V F)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Prove the second alternative. Prove the first alternative.
-/
theorem defOneIndef {V : HSp D} (hd : V.IsDefinite) : ∀ τ τ' : D.what₂.Tau, τ ≠ τ' →
    (V.sig (tauE D τ)).1 = 0 ∨ (V.sig (tauE D τ)).2 = 0 ∨ (V.sig (tauE D τ')).1 = 0 ∨ (V.sig (tauE D τ')).2 = 0 := by
  intro τ _ _
  rcases hd (tauE D τ) with h | h
  · exact Or.inr (Or.inl (by rw [h]))
  · exact Or.inl (by rw [h])

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Prove the second alternative. Prove the first alternative.
-/
theorem sParGap_of_isDefinite {V : HSp D} (hd : V.IsDefinite) (P : D.what₂.Tau → SPar) :
    ∀ τ, SParGap V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 (P τ) := by
  intro τ
  rcases hd (tauE D τ) with h | h
  · exact Or.inr (Or.inl (by rw [h]))
  · exact Or.inl (by rw [h])

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ThetaTiedDef.of_iff {T : ThetaTied D X} (sm : ThetaSmoothnessCondition T) (ty : TypTied T) (h1 : AutFunDefIffSm D)
    (h2 : IsoDefIffTypeAt T) : ThetaTiedDef T where
  ev_def := by
    intro V hs hd
    obtain ⟨θ, hθ⟩ := sm.1
    rw [sm.2 θ hθ V hs]
    ext φ
    exact (h1 θ hθ V hs hd φ).symm
  typ := by
    intro V hs hd P hP
    obtain ⟨θ, hθ⟩ := ty.1
    ext F
    rw [ty.2 θ hθ V hs P hP (sParGap_of_isDefinite hd P) F]
    exact (h2 θ hθ V hs hd P hP F).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem ThetaTiedDef.autFunDefIffSm {T : ThetaTied D X} (h : ThetaTiedDef T) (sm : ThetaSmoothnessCondition T) : AutFunDefIffSm D := by
  intro θ hθ V hs hd φ
  have e : {φ | IsAutFunDef V φ} = {φ | IsAutFunSm θ V φ} := by rw [← h.ev_def V hs hd, sm.2 θ hθ V hs]
  exact Set.ext_iff.1 e φ

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ThetaTiedDef.isoDefIffTypeAt {T : ThetaTied D X} (h : ThetaTiedDef T) (ty : TypTied T) : IsoDefIffTypeAt T := by
  intro θ hθ V hs hd P hP F
  rw [← h.typ V hs hd P hP]
  exact ty.2 θ hθ V hs P hP (sParGap_of_isDefinite hd P) F

end Formalism.L2.Theta

end
