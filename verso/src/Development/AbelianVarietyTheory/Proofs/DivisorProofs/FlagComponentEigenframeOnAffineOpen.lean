import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ShFam.Cell

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z F _ e C V hV φV f₀ U hU hUV hg φ fr t hx A hS hT hvec U' hU' hle hg' w a hc`. Set `r : Γ(C.Y.X, U) →+* Γ(C.Y.X, U')` to `(C.Y.X.presheaf.map (homOfLE hle).op).hom`. Establish `hsp : spMap r ≫ hU.fromSpec = hU'.fromSpec` using `IsAffineOpen.map_fromSpec hU hU' (homOfLE hle).op`. Establish `hx' : spMap r ≫ (hU.fromSpec ≫ C.π) ≫ genι Z = (hU'.fromSpec ≫ C.π) ≫ genι Z`. Simplify using `only [← Category.assoc, hsp]`.

Take `⟨fr', hfr'⟩` from `GlobalTheory.ShFam.Spread.exists_bc fr r rfl hx'`. Establish `hx2 : spMap (C.π.appLE V U' (hle.trans hUV)).hom ≫ hV.fromSpec ≫ genι Z = (hU'.fromSpec ≫ C.π) ≫ genι Z`. Rewrite using `[← Category.assoc]`. Conclude with `congrArg (· ≫ genι Z) (IsAffineOpen.SpecMap_appLE_fromSpec C.π hV hU' (hle.trans hUV))`. Establish `hfn : (fnOf U' hg').comp r = fnOf U hg` using `RingHom.ext fun z => fnOf_resG hle hg' z`.

Establish `hω : r.comp (C.π.appLE V U hUV).hom = (C.π.appLE V U' (hle.trans hUV)).hom`. Rewrite using `[← CommRingCat.hom_comp, Scheme.Hom.appLE_map]`. Use `⟨hU', hle.trans hUV, hg', r.comp φ, fr', t, hx2, fun τ => (A τ).map r, ?_, ?_, ?_, hc⟩` and prove the remaining obligations. Rewrite using `[← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hS, ← hsp]`. Simplify using `only [Category.assoc]`.

Use `⟨?_, ?_, fun τ i => ?_⟩` and prove the remaining obligations. Rewrite using `[hT.1, ← hfn, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, Category.assoc, hx']`. Rewrite using `[hT.2.1, ← hfn]`. Both sides reduce to the same expression. Take `⟨cf, h1, h2, h3⟩` from `hT.2.2 τ i`.

Use `⟨cf, h1, h2, ?_⟩` and prove the remaining obligations. Establish `ee : (fun j => spMap (dualMap (fnOf U' hg')) ≫ fr'.v τ j) = fun j => spMap (dualMap (fnOf U hg)) ≫ fr.v τ j`. Use function extensionality and compare the values at `fun j => by`. Establish `e₁ : fr'.v τ j = spMap (dualMap r) ≫ fr.v τ j` using `congrArg (fun v => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left) (hfr' τ j)`. Rewrite using `[e₁, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hfn]`.

Use `congr 2`. Apply the tactic sequence `exact RingHom.ext fun z => by ext <;> simp [dualMap]`. Rewrite using `[ee]`. Conclude with `h3`. Introduce `τ i`.

Rewrite using `[hfr', hvec, GlobalTheory.LieLocFrame.res_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.LieLocFrame.res_res _ hx r hx' hω hx2]`. Both sides reduce to the same expression.
-/
theorem cellAt_restrict : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) {U : C.Y.X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ C.π ⁻¹ᵁ V) (hg : genericPoint C.Y.X ∈ U) {φ : c.F →+* Γ(C.Y.X, U)} (fr : EigFrame Z φ ((hU.fromSpec ≫ C.π) ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (hx : spMap (C.π.appLE V U hUV).hom ≫ hV.fromSpec ≫ genι Z = (hU.fromSpec ≫ C.π) ≫ genι Z) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(C.Y.X, U)), (hU.fromSpec ≫ C.π) ≫ genStr Z = spMap φ → fr.Tri (fnOf U hg) C.f0 t → (∀ τ i, fr.vec τ i = ∑ k, A τ i k • GlobalTheory.LieLocFrame.res (C.π.appLE V U hUV).hom hx (f₀.vec τ k)) → ∀ {U' : C.Y.X.Opens} (hU' : IsAffineOpen U') (hle : U' ≤ U), genericPoint C.Y.X ∈ U' → ∀ (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (a : ∀ τ : E →+* ℂ, GlobalTheory.ShFam.Cell.Above (Dw.mult τ) → Γ(C.Y.X, U')), (∀ τ, GlobalTheory.ShFam.Cell.InCell ((A τ).map (C.Y.X.presheaf.map (homOfLE hle).op).hom) (w τ) (a τ)) → GlobalTheory.ShFam.Cell.CellAt C hV f₀ w U' a := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C V hV φV f₀ U hU hUV hg φ fr t hx A hS hT hvec U' hU' hle hg' w a hc
  let r : Γ(C.Y.X, U) →+* Γ(C.Y.X, U') := (C.Y.X.presheaf.map (homOfLE hle).op).hom
  have hsp : spMap r ≫ hU.fromSpec = hU'.fromSpec := IsAffineOpen.map_fromSpec hU hU' (homOfLE hle).op
  have hx' : spMap r ≫ (hU.fromSpec ≫ C.π) ≫ genι Z = (hU'.fromSpec ≫ C.π) ≫ genι Z := by
    simp only [← Category.assoc, hsp]
  obtain ⟨fr', hfr'⟩ := GlobalTheory.ShFam.Spread.exists_bc fr r rfl hx'
  have hx2 : spMap (C.π.appLE V U' (hle.trans hUV)).hom ≫ hV.fromSpec ≫ genι Z = (hU'.fromSpec ≫ C.π) ≫ genι Z := by
    rw [← Category.assoc]
    exact congrArg (· ≫ genι Z) (IsAffineOpen.SpecMap_appLE_fromSpec C.π hV hU' (hle.trans hUV))
  have hfn : (fnOf U' hg').comp r = fnOf U hg := RingHom.ext fun z => fnOf_resG hle hg' z
  have hω : r.comp (C.π.appLE V U hUV).hom = (C.π.appLE V U' (hle.trans hUV)).hom := by
    rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
  refine ⟨hU', hle.trans hUV, hg', r.comp φ, fr', t, hx2, fun τ => (A τ).map r, ?_, ?_, ?_, hc⟩
  · rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hS, ← hsp]
    simp only [Category.assoc]
  · refine ⟨?_, ?_, fun τ i => ?_⟩
    · rw [hT.1, ← hfn, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, Category.assoc, hx']
    · rw [hT.2.1, ← hfn]; rfl
    · obtain ⟨cf, h1, h2, h3⟩ := hT.2.2 τ i
      refine ⟨cf, h1, h2, ?_⟩
      have ee : (fun j => spMap (dualMap (fnOf U' hg')) ≫ fr'.v τ j) = fun j => spMap (dualMap (fnOf U hg)) ≫ fr.v τ j :=
        funext fun j => by
          have e₁ : fr'.v τ j = spMap (dualMap r) ≫ fr.v τ j :=
            congrArg (fun v => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left) (hfr' τ j)
          rw [e₁, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hfn]
          congr 2
          exact RingHom.ext fun z => by ext <;> simp [dualMap]
      rw [ee]
      exact h3
  · intro τ i
    rw [hfr', hvec, GlobalTheory.LieLocFrame.res_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [GlobalTheory.LieLocFrame.res_res _ hx r hx' hω hx2]
    rfl

end GlobalTheory.ShFam.Cell
