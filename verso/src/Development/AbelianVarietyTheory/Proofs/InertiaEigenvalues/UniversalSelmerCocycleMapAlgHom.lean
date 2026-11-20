import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerCocyclesScalarChangeTransferStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

/- English proof (translation)
Introduce `D N X bkP i s B _ _ A _ _ π κ κ' hκ Q a Φ Z hU Y _ _ _ _`. Use `letI : Module B Y := Module.compHom Y π.toRingHom`. Establish `hsm : ∀ (b : B) (y : Y), b • y = π b • y` using `fun _ _ => rfl`. Take `⟨hrep, hsel⟩` from `GlobalTheory.T.selmerCocycles_scalarChange_transfer D N X bkP i s B A π κ κ' hκ Y hsm`. Take `⟨h1, h2, h3⟩` from `hU Y`.

Establish `hm : ∀ x : Fin a → Y, matAct (Φ.map π) x = matAct Φ x` using `fun _ => rfl`. Establish `hr : ∀ g (x : Fin a → Y), rect ((Z g).map π) x = rect (Z g) x` using `fun _ _ => rfl`. Establish `hc : ∀ f, Cob (repOn (Tgl i s) κ Y) f ↔ Cob (repOn (Tgl i s) κ' Y) f` using `fun f => by`. Simplify using `only [Cob, hrep]`. Simplify using `only [hm, hr]`.

Use `⟨fun x hx => (hsel _ _).1 (h1 x hx), fun x hx hb => h2 x hx ((hc _).2 hb), fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hb⟩` from `h3 f ((hsel _ _).2 hf)`. Conclude with `⟨x, hx, (hc _).1 hb⟩`.
-/
theorem univ_map : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (A : Type) [CommRing A] [Algebra (X.O0 i) A] (π : B →ₐ[X.O0 i] A) (κ : GE N →* Bˣ) (κ' : GE N →* Aˣ), (∀ g, ((κ' g : Aˣ) : A) = π (κ g : Bˣ)) → ∀ (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) B) Z, Univ bkP i s κ Q Φ Z → Univ bkP i s κ' Q (Φ.map π) (fun g => (Z g).map π) := by
  intro D N X bkP i s B _ _ A _ _ π κ κ' hκ Q a Φ Z hU Y _ _ _ _
  letI : Module B Y := Module.compHom Y π.toRingHom
  have hsm : ∀ (b : B) (y : Y), b • y = π b • y := fun _ _ => rfl
  obtain ⟨hrep, hsel⟩ := GlobalTheory.T.selmerCocycles_scalarChange_transfer D N X bkP i s B A π κ κ' hκ Y hsm
  obtain ⟨h1, h2, h3⟩ := hU Y
  have hm : ∀ x : Fin a → Y, matAct (Φ.map π) x = matAct Φ x := fun _ => rfl
  have hr : ∀ g (x : Fin a → Y), rect ((Z g).map π) x = rect (Z g) x := fun _ _ => rfl
  have hc : ∀ f, Cob (repOn (Tgl i s) κ Y) f ↔ Cob (repOn (Tgl i s) κ' Y) f := fun f => by
    simp only [Cob, hrep]
  simp only [hm, hr]
  refine ⟨fun x hx => (hsel _ _).1 (h1 x hx), fun x hx hb => h2 x hx ((hc _).2 hb), fun f hf => ?_⟩
  obtain ⟨x, hx, hb⟩ := h3 f ((hsel _ _).2 hf)
  exact ⟨x, hx, (hc _).1 hb⟩

end GlobalTheory.NewPrime
