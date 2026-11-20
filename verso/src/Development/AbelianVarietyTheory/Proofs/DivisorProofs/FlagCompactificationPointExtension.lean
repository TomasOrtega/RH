import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFrameTriangularThroughStalkFrames
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls.CarryBC

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

/- English proof (translation)
Establish `hu : ∀ τ i, IsUnit (fK.co g τ i i)` using `fun τ => GlobalTheory.ShFam.CarriesAt.isUnit_diag_of_blockTriangular (h τ) (fK.isUnit_det_co g τ)`. Use `⟨fun τ i => (hu τ i).unit, hx, hχ, fun τ i => ⟨fun a => fK.co g τ a i, (hu τ i).unit_spec.symm, fun a ha => h τ ha, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← funext (hf τ)]`. Conclude with `fK.co_spec g τ i`.
-/
theorem tri_of_co {R K : Type} [CommRing R] [CommRing K] {φ : c.F →+* R} {x₀ : Sp R ⟶ Z.X} {χ : c.F →+* K}
    {x : Sp K ⟶ Z.X} {f : EigFrame Z φ x₀} {ρ : R →+* K} {fK g : EigFrame Z χ x} (hf : f.IsMap ρ fK)
    (hχ : χ = ρ.comp φ) (hx : x = spMap ρ ≫ x₀) (h : ∀ τ, (fK.co g τ).BlockTriangular id) :
    ∃ t, f.Tri ρ g t := by
  have hu : ∀ τ i, IsUnit (fK.co g τ i i) := fun τ =>
    GlobalTheory.ShFam.CarriesAt.isUnit_diag_of_blockTriangular (h τ) (fK.isUnit_det_co g τ)
  refine ⟨fun τ i => (hu τ i).unit, hx, hχ, fun τ i => ⟨fun a => fK.co g τ a i, (hu τ i).unit_spec.symm,
    fun a ha => h τ ha, ?_⟩⟩
  rw [← funext (hf τ)]
  exact fK.co_spec g τ i

/- English proof (translation)
Establish `hx' : x' = spMap (ψ.comp ρ) ≫ x₀`. Rewrite using `[hg.1, hx, ← Category.assoc]`. Use `congr 1`. Simplify using `[spMap, Spec.map_comp]`. Establish `key (hχ : χ = ρ.comp φ) : (∃ t', f.Tri (ψ.comp ρ) g' t') ↔ ∃ t', f.Tri ρ g t'`.

Take `⟨fK, hfK⟩` from `f.exists_isMap ρ hχ hx`. Take `⟨fK', hfK'⟩` from `fK.exists_isMap ψ hg.2.1 hg.1`. Take `⟨gK', hgK'⟩` from `g.exists_isMap ψ hg.2.1 hg.1`. Establish `hc : f.IsMap (ψ.comp ρ) fK'` using `fun τ i => by`. Rewrite using `[hfK' τ i, hfK τ i, ← Category.assoc, ← GlobalTheory.ShFam.CarriesAt.spMap_dualMap_comp]`.

Establish `hT : ∀ τ, (gK'.co g' τ).BlockTriangular id` using `fun τ a i h => (EigFrame.Tri.co (τ := τ) hg hgK').1 a i h`. Establish `hM : ∀ τ, fK'.co gK' τ = (fK.co g τ).map ψ` using `fun τ => EigFrame.IsMap.co τ hfK' hgK' hg.1`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t', h⟩`. Use `tri_of_co hfK hχ hx fun τ a i hi => hψ ?_` and prove the remaining obligations.

Establish `hd : IsUnit (gK'.co g' τ).det` using `gK'.isUnit_det_co g' τ`. Establish `hW : fK'.co gK' τ = fK'.co g' τ * (gK'.co g' τ)⁻¹`. Rewrite using `[← fK'.co_mul gK' g' τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]`. Establish `hWt : (fK'.co gK' τ).BlockTriangular id` using `by haveI := Matrix.invertibleOfIsUnitDet _ hd`. Rewrite using `[hW]`.

Conclude with `Matrix.BlockTriangular.mul (fun a i h' => (EigFrame.Tri.co (τ := τ) h hc).1 a i h') (Matrix.blockTriangular_inv_of_blockTriangular (hT τ))`. Use `hWt hi` as an intermediate fact. Rewrite `this` using `[hM, Matrix.map_apply]`. Rewrite using `[this, map_zero]`. Introduce and unpack `⟨t', h⟩`.

Use `tri_of_co hc (by rw [hg.2.1, hχ, RingHom.comp_assoc]) hx' fun τ => ?_` and prove the remaining obligations. Rewrite using `[← fK'.co_mul gK' g' τ]`. Use `Matrix.BlockTriangular.mul (fun a i hi => ?_) (hT τ)` and prove the remaining obligations. Rewrite using `[hM, Matrix.map_apply, (EigFrame.Tri.co (τ := τ) h hfK).1 a i hi, map_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨t', h⟩`. Conclude with `(key (RingHom.ext fun a => hψ ((RingHom.congr_fun hg.2.1 a).symm.trans (RingHom.congr_fun h.2.1 a)))).1 ⟨t', h⟩`. Introduce and unpack `⟨t', h⟩`. Conclude with `(key h.2.1).2 ⟨t', h⟩`.
-/
theorem exists_tri_comp_iff {R K K' : Type} [CommRing R] [CommRing K] [CommRing K'] {φ : c.F →+* R} {x₀ : Sp R ⟶ Z.X}
    {χ : c.F →+* K} {x : Sp K ⟶ Z.X} {χ' : c.F →+* K'} {x' : Sp K' ⟶ Z.X} (f : EigFrame Z φ x₀) (ρ : R →+* K)
    {ψ : K →+* K'} (hψ : Function.Injective ψ) {g : EigFrame Z χ x} {g' : EigFrame Z χ' x'}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K'ˣ} (hg : g.Tri ψ g' t) (hx : x = spMap ρ ≫ x₀) :
    (∃ t', f.Tri (ψ.comp ρ) g' t') ↔ ∃ t', f.Tri ρ g t' := by
  have hx' : x' = spMap (ψ.comp ρ) ≫ x₀ := by
    rw [hg.1, hx, ← Category.assoc]
    congr 1
    simp [spMap, Spec.map_comp]
  have key (hχ : χ = ρ.comp φ) : (∃ t', f.Tri (ψ.comp ρ) g' t') ↔ ∃ t', f.Tri ρ g t' := by
    obtain ⟨fK, hfK⟩ := f.exists_isMap ρ hχ hx
    obtain ⟨fK', hfK'⟩ := fK.exists_isMap ψ hg.2.1 hg.1
    obtain ⟨gK', hgK'⟩ := g.exists_isMap ψ hg.2.1 hg.1
    have hc : f.IsMap (ψ.comp ρ) fK' := fun τ i => by
      rw [hfK' τ i, hfK τ i, ← Category.assoc, ← GlobalTheory.ShFam.CarriesAt.spMap_dualMap_comp]
    have hT : ∀ τ, (gK'.co g' τ).BlockTriangular id := fun τ a i h => (EigFrame.Tri.co (τ := τ) hg hgK').1 a i h
    have hM : ∀ τ, fK'.co gK' τ = (fK.co g τ).map ψ := fun τ => EigFrame.IsMap.co τ hfK' hgK' hg.1
    constructor
    · rintro ⟨t', h⟩
      refine tri_of_co hfK hχ hx fun τ a i hi => hψ ?_
      have hd : IsUnit (gK'.co g' τ).det := gK'.isUnit_det_co g' τ
      have hW : fK'.co gK' τ = fK'.co g' τ * (gK'.co g' τ)⁻¹ := by
        rw [← fK'.co_mul gK' g' τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      have hWt : (fK'.co gK' τ).BlockTriangular id := by
        haveI := Matrix.invertibleOfIsUnitDet _ hd
        rw [hW]
        exact Matrix.BlockTriangular.mul (fun a i h' => (EigFrame.Tri.co (τ := τ) h hc).1 a i h')
          (Matrix.blockTriangular_inv_of_blockTriangular (hT τ))
      have := hWt hi
      rw [hM, Matrix.map_apply] at this
      rw [this, map_zero]
    · rintro ⟨t', h⟩
      refine tri_of_co hc (by rw [hg.2.1, hχ, RingHom.comp_assoc]) hx' fun τ => ?_
      rw [← fK'.co_mul gK' g' τ]
      refine Matrix.BlockTriangular.mul (fun a i hi => ?_) (hT τ)
      rw [hM, Matrix.map_apply, (EigFrame.Tri.co (τ := τ) h hfK).1 a i hi, map_zero]
  constructor
  · rintro ⟨t', h⟩
    exact (key (RingHom.ext fun a => hψ
      ((RingHom.congr_fun hg.2.1 a).symm.trans (RingHom.congr_fun h.2.1 a)))).1 ⟨t', h⟩
  · rintro ⟨t', h⟩
    exact (key h.2.1).2 ⟨t', h⟩

end Frames

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Oz _ β Z F _ e C K _ χ x g K' _ ψ χ' x' g' t p hx _ hg`. Take `⟨φ, f, t₀, hf, -⟩` from `C.gr_spec (p (IsLocalRing.closedPoint K))`. Use `set ρ := (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom with hρ`. Establish `hp : p = spMap ρ ≫ stalkPt C.Y (p (IsLocalRing.closedPoint K))` using `(GlobalTheory.FlagBundle.spMap_stalkClosedPointTo p).symm`. Establish `hp' : spMap ψ ≫ p = spMap (ψ.comp ρ) ≫ stalkPt C.Y (p (IsLocalRing.closedPoint K))`.

Establish `e3 : spMap (ψ.comp ρ) = spMap ψ ≫ spMap ρ` using `by simp [spMap, Spec.map_comp]`. Rewrite using `[e3, Category.assoc, ← hp]`. Establish `hx₀ : x = spMap ρ ≫ stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z`. Rewrite using `[← Category.assoc, ← hp, hx]`. Establish `key` using `exists_tri_comp_iff f ρ ψ.injective hg hx₀`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨t', h'⟩` from `key.1 (GlobalTheory.ShFam.CarriesAt.tri_of_carries E H Dw l Xo c Oz β Z F e C K' χ' x' g' _ h _ _ φ f t₀ hp' hf)`. Conclude with `⟨_, ρ, φ, f, t₀, t', hp, hf, h'⟩`. Introduce `h`.

Take `⟨t', h'⟩` from `key.2 (GlobalTheory.ShFam.CarriesAt.tri_of_carries E H Dw l Xo c Oz β Z F e C K χ x g _ h _ _ φ f t₀ hp hf)`. Conclude with `⟨_, ψ.comp ρ, φ, f, t₀, t', hp', hf, h'⟩`.
-/
theorem carries_baseChange_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z χ x) (K' : Type) [Field K'] (ψ : K →+* K') (χ' : c.F →+* K') (x' : Sp K' ⟶ Z.X) (g' : EigFrame Z χ' x') (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K'ˣ) (p : Sp K ⟶ C.Y.X), x = p ≫ C.π ≫ genι Z → p ≫ C.π ≫ genStr Z = spMap χ → g.Tri ψ g' t → (C.Carries (spMap ψ ≫ p) g' ↔ C.Carries p g) := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ e C K _ χ x g K' _ ψ χ' x' g' t p hx _ hg
  obtain ⟨φ, f, t₀, hf, -⟩ := C.gr_spec (p (IsLocalRing.closedPoint K))
  set ρ := (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom with hρ
  have hp : p = spMap ρ ≫ stalkPt C.Y (p (IsLocalRing.closedPoint K)) :=
    (GlobalTheory.FlagBundle.spMap_stalkClosedPointTo p).symm
  have hp' : spMap ψ ≫ p = spMap (ψ.comp ρ) ≫ stalkPt C.Y (p (IsLocalRing.closedPoint K)) := by
    have e3 : spMap (ψ.comp ρ) = spMap ψ ≫ spMap ρ := by simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, ← hp]
  have hx₀ : x = spMap ρ ≫ stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z := by
    rw [← Category.assoc, ← hp, hx]
  have key := exists_tri_comp_iff f ρ ψ.injective hg hx₀
  constructor
  · intro h
    obtain ⟨t', h'⟩ := key.1 (GlobalTheory.ShFam.CarriesAt.tri_of_carries E H Dw l Xo c Oz β Z F e C K' χ' x' g' _ h _ _ φ f t₀ hp' hf)
    exact ⟨_, ρ, φ, f, t₀, t', hp, hf, h'⟩
  · intro h
    obtain ⟨t', h'⟩ := key.2 (GlobalTheory.ShFam.CarriesAt.tri_of_carries E H Dw l Xo c Oz β Z F e C K χ x g _ h _ _ φ f t₀ hp hf)
    exact ⟨_, ψ.comp ρ, φ, f, t₀, t', hp', hf, h'⟩

end GlobalTheory.FlagCls.CarryBC

end
