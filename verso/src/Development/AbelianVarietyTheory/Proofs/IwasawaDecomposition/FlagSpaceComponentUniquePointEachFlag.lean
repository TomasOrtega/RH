import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentCarriesEveryFrameFlagStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointOverGeometricBasePointStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.CarryAll

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z F _ e C K _ χ p hp`. Set `y : C.Y.X` to `p (IsLocalRing.closedPoint K)`. Set `ψ : C.Y.X.presheaf.stalk y →+* K` to `(Scheme.stalkClosedPointTo p).hom`. Establish `hfac : p = spMap ψ ≫ stalkPt C.Y y` using `(Scheme.Spec_stalkClosedPointTo_fromSpecStalk p).symm`. Take `⟨φ, fr, t, hT, -⟩` from `C.gr_spec y`.

Take `⟨g, hg⟩` from `EigFrame.exists_baseChange E H Dw l Xo c O β Z _ K φ (stalkPt C.Y y ≫ C.π ≫ genι Z) fr ψ`. Establish `hs : stalkPt C.Y y ≫ C.π ≫ genStr Z = spMap φ`. Take `⟨s', hs'⟩ : ∃ s' : c.F →+* C.Y.X.presheaf.stalk y, spMap s' = stalkPt C.Y y ≫ C.π ≫ genStr Z` from `⟨(Spec.preimage (stalkPt C.Y y ≫ C.π ≫ genStr Z)).hom, Spec.map_preimage _⟩`. Rewrite using `[← hs']`. Use `congr 1`.

Establish `ha : Function.Injective (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField)` using `IsFractionRing.injective _ _`. Establish `h2 : (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField).comp s' = constF e C.Y`. Apply `GlobalTheory.ShFam.EigLoc.spMap_inj` to reduce the goal to its premises. Rewrite using `[GlobalTheory.ShFam.TieBase.spMap_trans, hs', ← GlobalTheory.ShFam.TieBase.genericPt_str e C.Y C.π C.π_str, GlobalTheory.ShFam.TieBase.genericPt_eq C.Y y]`. Simplify using `only [Category.assoc]`.

Use `RingHom.ext fun r => ha ?_` and prove the remaining obligations. Use `DFunLike.congr_fun (h2.trans hT.2.1) r` as an intermediate fact. Conclude with `this`. Establish `hφ : χ = ψ.comp φ`. Apply `GlobalTheory.ShFam.EigLoc.spMap_inj` to reduce the goal to its premises.

Rewrite using `[GlobalTheory.ShFam.TieBase.spMap_trans, ← hs, ← hp, hfac]`. Simplify using `only [Category.assoc]`. Substitute `hφ` using the available equality. Establish `key : ∀ q : Sp K ⟶ C.Y.X, q = spMap ψ ≫ stalkPt C.Y y → ∃ g : EigFrame Z (ψ.comp φ) (q ≫ C.π ≫ genι Z), C.Carries q g`. Introduce `q hq`.

Substitute `hq` using the available equality. Use `⟨g, y, ψ, φ, fr, t, 1, rfl, hT, rfl, rfl, fun τ i => ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩` and prove the remaining obligations. Establish `e' : (fun k => spMap (dualMap ψ) ≫ fr.v τ k) = g.v τ` using `funext fun k => (hg τ k).symm`. Rewrite using `[e']`. Conclude with `isCombAtG_single Z.t _ (g.tan τ) i`.

Conclude with `key p hfac`.
-/
theorem carry_some : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (K : Type) [Field K] (χ : c.F →+* K) (p : Sp K ⟶ C.Y.X), p ≫ C.π ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (p ≫ C.π ≫ genι Z), C.Carries p g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C K _ χ p hp
  let y : C.Y.X := p (IsLocalRing.closedPoint K)
  let ψ : C.Y.X.presheaf.stalk y →+* K := (Scheme.stalkClosedPointTo p).hom
  have hfac : p = spMap ψ ≫ stalkPt C.Y y := (Scheme.Spec_stalkClosedPointTo_fromSpecStalk p).symm
  obtain ⟨φ, fr, t, hT, -⟩ := C.gr_spec y
  obtain ⟨g, hg⟩ := EigFrame.exists_baseChange E H Dw l Xo c O β Z _ K φ (stalkPt C.Y y ≫ C.π ≫ genι Z) fr ψ
  have hs : stalkPt C.Y y ≫ C.π ≫ genStr Z = spMap φ := by
    obtain ⟨s', hs'⟩ : ∃ s' : c.F →+* C.Y.X.presheaf.stalk y, spMap s' = stalkPt C.Y y ≫ C.π ≫ genStr Z :=
      ⟨(Spec.preimage (stalkPt C.Y y ≫ C.π ≫ genStr Z)).hom, Spec.map_preimage _⟩
    rw [← hs']
    congr 1
    have ha : Function.Injective (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) :=
      IsFractionRing.injective _ _
    have h2 : (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField).comp s' = constF e C.Y := by
      apply GlobalTheory.ShFam.EigLoc.spMap_inj
      rw [GlobalTheory.ShFam.TieBase.spMap_trans, hs', ← GlobalTheory.ShFam.TieBase.genericPt_str e C.Y C.π C.π_str,
        GlobalTheory.ShFam.TieBase.genericPt_eq C.Y y]
      simp only [Category.assoc]
    refine RingHom.ext fun r => ha ?_
    have := DFunLike.congr_fun (h2.trans hT.2.1) r
    exact this
  have hφ : χ = ψ.comp φ := by
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    rw [GlobalTheory.ShFam.TieBase.spMap_trans, ← hs, ← hp, hfac]
    simp only [Category.assoc]
  subst hφ
  have key : ∀ q : Sp K ⟶ C.Y.X, q = spMap ψ ≫ stalkPt C.Y y →
      ∃ g : EigFrame Z (ψ.comp φ) (q ≫ C.π ≫ genι Z), C.Carries q g := by
    intro q hq
    subst hq
    refine ⟨g, y, ψ, φ, fr, t, 1, rfl, hT, rfl, rfl, fun τ i => ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩
    have e' : (fun k => spMap (dualMap ψ) ≫ fr.v τ k) = g.v τ := funext fun k => (hg τ k).symm
    rw [e']
    exact isCombAtG_single Z.t _ (g.tan τ) i
  exact key p hfac

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ k X j hj hstr f hf K _ _ χ x hx g`. Establish `hm : Mono j` using `by have := hj; infer_instance`. Establish `hx' : (x ≫ j) ≫ genStr Z = spMap χ` using `by rw [Category.assoc]; exact hx`. Establish `tr : ∀ (C : FlagCpt Z e) (p : Sp K ⟶ C.Y.X) (a b : Sp K ⟶ Z.X) (h : a = b) (g₀ : EigFrame Z χ a), C.Carries p g₀ → C.Carries p (h ▸ g₀)`. Introduce `C p a b h g₀ hg`.

Substitute `h` using the available equality. Conclude with `hg`. Take `⟨p, hp⟩` from `GlobalTheory.T.exists_flagComponent_point_over_geometricBasePoint E H Dw l Xo c O β Z F e σ N U Φ k X j hj hstr f hf (GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β Z F e σ N U Φ) (fun i K _ χ p h => carry_some E H Dw l Xo c O β Z F e (Φ.C i) K χ p h …`. Establish `hπ : p ≫ (Φ.C k).π = x ≫ j` using `by rw [← hf, ← Category.assoc, hp]`. Take `⟨g₀, hg₀⟩` from `carry_some E H Dw l Xo c O β Z F e (Φ.C k) K χ p (by rw [← Category.assoc, hπ, Category.assoc]; exact hx)`.

Establish `h1 : p ≫ (Φ.C k).π ≫ genι Z = (x ≫ j) ≫ genι Z` using `by rw [← Category.assoc, hπ]`. Take `⟨p', hp', hc⟩` from `GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β Z F e σ N U Φ k K χ (x ≫ j) hx' (h1 ▸ g₀) g p hπ (tr _ p _ _ h1 g₀ hg₀)`. Take `⟨q, -, hqu⟩` from `Φ.lifts K χ (x ≫ j) hx' g`. Establish `e'` using `hqu ⟨k, p'⟩ ⟨hp', hc⟩`. Use `⟨p', ⟨(cancel_mono j).1 (by rw [Category.assoc, hf, hp']), hc⟩, fun p₂ ⟨h₂, c₂⟩ => ?_⟩` and prove the remaining obligations.

Establish `e₂` using `hqu ⟨k, p₂⟩ ⟨by rw [← hf, ← Category.assoc, h₂], c₂⟩`. Conclude with `eq_of_heq (Sigma.mk.inj_iff.1 (e₂.trans e'.symm)).2`.
-/
theorem carries_everywhere : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (k : U.Comp) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : (Φ.C k).Y.X ⟶ X.X), f ≫ j = (Φ.C k).π → ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ (Φ.C k).Y.X, p ≫ f = x ∧ (Φ.C k).Carries p g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ k X j hj hstr f hf K _ _ χ x hx g
  have hm : Mono j := by have := hj; infer_instance
  have hx' : (x ≫ j) ≫ genStr Z = spMap χ := by rw [Category.assoc]; exact hx
  have tr : ∀ (C : FlagCpt Z e) (p : Sp K ⟶ C.Y.X) (a b : Sp K ⟶ Z.X) (h : a = b) (g₀ : EigFrame Z χ a),
      C.Carries p g₀ → C.Carries p (h ▸ g₀) := by
    intro C p a b h g₀ hg; subst h; exact hg
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_flagComponent_point_over_geometricBasePoint E H Dw l Xo c O β Z F e σ N U Φ k X j hj hstr f hf (GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β Z F e σ N U Φ)
    (fun i K _ χ p h => carry_some E H Dw l Xo c O β Z F e (Φ.C i) K χ p h) K χ x hx
  have hπ : p ≫ (Φ.C k).π = x ≫ j := by rw [← hf, ← Category.assoc, hp]
  obtain ⟨g₀, hg₀⟩ := carry_some E H Dw l Xo c O β Z F e (Φ.C k) K χ p (by rw [← Category.assoc, hπ, Category.assoc]; exact hx)
  have h1 : p ≫ (Φ.C k).π ≫ genι Z = (x ≫ j) ≫ genι Z := by rw [← Category.assoc, hπ]
  obtain ⟨p', hp', hc⟩ := GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β Z F e σ N U Φ k K χ (x ≫ j) hx' (h1 ▸ g₀) g p hπ (tr _ p _ _ h1 g₀ hg₀)
  obtain ⟨q, -, hqu⟩ := Φ.lifts K χ (x ≫ j) hx' g
  have e' := hqu ⟨k, p'⟩ ⟨hp', hc⟩
  refine ⟨p', ⟨(cancel_mono j).1 (by rw [Category.assoc, hf, hp']), hc⟩, fun p₂ ⟨h₂, c₂⟩ => ?_⟩
  have e₂ := hqu ⟨k, p₂⟩ ⟨by rw [← hf, ← Category.assoc, h₂], c₂⟩
  exact eq_of_heq (Sigma.mk.inj_iff.1 (e₂.trans e'.symm)).2

end GlobalTheory.CarryAll
