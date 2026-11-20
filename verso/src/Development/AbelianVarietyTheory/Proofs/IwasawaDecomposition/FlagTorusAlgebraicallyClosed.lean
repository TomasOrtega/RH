import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtFJQOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NoBase

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ShFam.Horiz

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hc`.
-/
theorem carries_of_frameCast (C : FlagCpt Z e) {k : Type} [Field k] {φ : c.F →+* k} {x x' : Sp k ⟶ Z.X} (h : x = x')
    {p : Sp k ⟶ C.Y.X} {g : EigFrame Z φ x} (hc : C.Carries p (frameCast h g)) : C.Carries p g := by
  subst h
  exact hc

/- English proof (translation)
Use `letI := (constF e C.Y).toAlgebra`. Use `Z.jQ_open` as an intermediate fact. Establish `h1 : Z.jQ (GlobalTheory.AllWt.ptF C.y0 s₀) = C.π (genericPt C.Y s₀)`. Establish `h2` using `congrArg (fun f => f s₀) C.y0_x`. Simplify `h2` using `only [Scheme.Hom.comp_apply]`.

Establish `h2 : genericPt C.Y s₀ ⤳ genericPoint C.Y.X`. Establish `h3 : genericPt C.Y s₀ ∈ Set.range (C.Y.X.fromSpecStalk (genericPoint C.Y.X))` using `⟨s₀, rfl⟩`. Rewrite `h3` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis. Establish `h3 : genericPoint C.Y.X ⤳ w` using `(genericPoint_spec C.Y.X).specializes trivial`. Establish `h4` using `(h2.trans h3).map C.π.continuous`.

Rewrite `h4` using `[← h1, h]`. Conclude with `Z.jQ.isOpenEmbedding.isInducing.specializes_iff.1 h4`.
-/
theorem y0_specializes (C : FlagCpt Z e) (s₀ : Sp C.Y.Fn) {w : C.Y.X} {ξ : Xo.XF c} (h : C.π w = Z.jQ ξ) :
    (letI := (constF e C.Y).toAlgebra; GlobalTheory.AllWt.ptF C.y0) s₀ ⤳ ξ := by
  letI := (constF e C.Y).toAlgebra
  have := Z.jQ_open
  have h1 : Z.jQ (GlobalTheory.AllWt.ptF C.y0 s₀) = C.π (genericPt C.Y s₀) := by
    have h2 := congrArg (fun f => f s₀) C.y0_x
    simpa only [Scheme.Hom.comp_apply] using h2
  have h2 : genericPt C.Y s₀ ⤳ genericPoint C.Y.X := by
    have h3 : genericPt C.Y s₀ ∈ Set.range (C.Y.X.fromSpecStalk (genericPoint C.Y.X)) := ⟨s₀, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at h3
  have h3 : genericPoint C.Y.X ⤳ w := (genericPoint_spec C.Y.X).specializes trivial
  have h4 := (h2.trans h3).map C.π.continuous
  rw [← h1, h] at h4
  exact Z.jQ.isOpenEmbedding.isInducing.specializes_iff.1 h4

/- English proof (translation)
Use `letI := (constF e C.Y).toAlgebra`. Set `s₀ : Sp C.Y.Fn` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C.Y.Fn)`. Set `w₀` to `GlobalTheory.AllWt.ptF C.y0 s₀`. Set `W₀ : Comp Xo c` to `⟨irreducibleComponent w₀, irreducibleComponent_mem_irreducibleComponents w₀⟩`. Establish `hc : IsClosed W₀.1` using `isClosed_of_mem_irreducibleComponents _ W₀.2`.

Establish `h0 : w₀ ∈ W₀.1` using `mem_irreducibleComponent`. Establish `h1 : ξ ∈ W₀.1` using `(y0_specializes C s₀ h).mem_closed hc h0`. Establish `h2 : ξ' ∈ W₀.1` using `(y0_specializes C s₀ h').mem_closed hc h0`. Distinguish the cases in `hne : W₀ = W`. Rewrite using `[← hne]`.

Conclude with `h2`. Conclude with `absurd hξ (Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c W₀ W hne) h1)`.
-/
theorem mem_comp_of_over (C : FlagCpt Z e) {w w' : C.Y.X} {ξ ξ' : Xo.XF c} (h : C.π w = Z.jQ ξ) (h' : C.π w' = Z.jQ ξ')
    (W : Comp Xo c) (hξ : ξ ∈ W.1) : ξ' ∈ W.1 := by
  letI := (constF e C.Y).toAlgebra
  let s₀ : Sp C.Y.Fn := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C.Y.Fn)
  let w₀ := GlobalTheory.AllWt.ptF C.y0 s₀
  let W₀ : Comp Xo c := ⟨irreducibleComponent w₀, irreducibleComponent_mem_irreducibleComponents w₀⟩
  have hc : IsClosed W₀.1 := isClosed_of_mem_irreducibleComponents _ W₀.2
  have h0 : w₀ ∈ W₀.1 := mem_irreducibleComponent
  have h1 : ξ ∈ W₀.1 := (y0_specializes C s₀ h).mem_closed hc h0
  have h2 : ξ' ∈ W₀.1 := (y0_specializes C s₀ h').mem_closed hc h0
  by_cases hne : W₀ = W
  · rw [← hne]; exact h2
  · exact absurd hξ (Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c W₀ W hne) h1)

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z F _ _ e σ N U Φ hσ hU hF k y`. Establish `hne : ∀ k, (U.X k).dom.Nonempty` using `fun k => ReciprocityTheory.ChartRestriction.G.PullbackSections.noBase_dom_nonempty (U.X k)`. Take `⟨q, hq⟩` from `GlobalTheory.UnifComp.exists_equiv_comp E H Dw l Xo c σ N U hσ hU hne hF`. Set `s : Sp (CAt σ)` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)`. Establish `claim : ∀ i (w : (Φ.C i).Y.X) (ξ : Xo.XF c), (Φ.C i).π w = Z.jQ ξ → ξ ∈ (q i).1`.

Introduce `i w ξ h`. Take `⟨x₀, hx₀⟩` from `hne i`. Take `⟨w₁, hw₁⟩` from `Φ.label i ⟨x₀, hx₀⟩ s`. Rewrite `hw₁` using `[Scheme.Hom.comp_apply]`. Conclude with `mem_comp_of_over (Φ.C i) hw₁ h (q i) (hq i ⟨x₀, hx₀⟩ s)`.

Set `P` to `U.un k y`. Set `a` to `cxOf Z P`. Take `⟨⟨i, p⟩, ⟨hp, hc⟩, -⟩` from `Φ.lifts ℂ σ a.1.1 a.1.2 a.2`. Establish `hs : GlobalTheory.AllWt.ptF (S` using `CAt σ) P s ∈ (q i).1 := by`. Establish `hp' : p ≫ (Φ.C i).π = GlobalTheory.AllWt.ptF (S` using `CAt σ) P ≫ Z.jQ := hp`.

Establish `h1 : (p ≫ (Φ.C i).π) s = (GlobalTheory.AllWt.ptF (S` using `CAt σ) P ≫ Z.jQ) s := congrArg (fun f => f s) hp'`. Conclude with `claim i (p s) _ (((Scheme.Hom.comp_apply _ _ _).symm.trans h1).trans (Scheme.Hom.comp_apply _ _ _))`. Choose the witnesses or unpack the hypotheses as in `rfl : i = k := by`. Assume the negation of the conclusion as `hik`. Conclude with `Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c (q i) (q k) (fun h => hik (q.injective h))) hs (hq k y s)`.

Use `letI := σ.toAlgebra`. Unfold `CarriedC Carried`. Conclude with `⟨p, hp, carries_of_frameCast (Φ.C i) (Category.assoc _ _ _).symm hc⟩`.
-/
theorem carriedC_flagTor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → FnAlgClosed Xo c → ∀ k (y : (U.X k).dom), CarriedC (Φ.C k) (U.un k y) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e σ N U Φ hσ hU hF k y
  have hne : ∀ k, (U.X k).dom.Nonempty := fun k => ReciprocityTheory.ChartRestriction.G.PullbackSections.noBase_dom_nonempty (U.X k)
  obtain ⟨q, hq⟩ := GlobalTheory.UnifComp.exists_equiv_comp E H Dw l Xo c σ N U hσ hU hne hF
  let s : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have claim : ∀ i (w : (Φ.C i).Y.X) (ξ : Xo.XF c), (Φ.C i).π w = Z.jQ ξ → ξ ∈ (q i).1 := by
    intro i w ξ h
    obtain ⟨x₀, hx₀⟩ := hne i
    obtain ⟨w₁, hw₁⟩ := Φ.label i ⟨x₀, hx₀⟩ s
    rw [Scheme.Hom.comp_apply] at hw₁
    exact mem_comp_of_over (Φ.C i) hw₁ h (q i) (hq i ⟨x₀, hx₀⟩ s)
  let P := U.un k y
  let a := cxOf Z P
  obtain ⟨⟨i, p⟩, ⟨hp, hc⟩, -⟩ := Φ.lifts ℂ σ a.1.1 a.1.2 a.2
  have hs : GlobalTheory.AllWt.ptF (S := CAt σ) P s ∈ (q i).1 := by
    have hp' : p ≫ (Φ.C i).π = GlobalTheory.AllWt.ptF (S := CAt σ) P ≫ Z.jQ := hp
    have h1 : (p ≫ (Φ.C i).π) s = (GlobalTheory.AllWt.ptF (S := CAt σ) P ≫ Z.jQ) s := congrArg (fun f => f s) hp'
    exact claim i (p s) _ (((Scheme.Hom.comp_apply _ _ _).symm.trans h1).trans (Scheme.Hom.comp_apply _ _ _))
  obtain rfl : i = k := by
    by_contra hik
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c (q i) (q k) (fun h => hik (q.injective h))) hs (hq k y s)
  letI := σ.toAlgebra
  unfold CarriedC Carried
  exact ⟨p, hp, carries_of_frameCast (Φ.C i) (Category.assoc _ _ _).symm hc⟩

end GlobalTheory.ShFam.Horiz
