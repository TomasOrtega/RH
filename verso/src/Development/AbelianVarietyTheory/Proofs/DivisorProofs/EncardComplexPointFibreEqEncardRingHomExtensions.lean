import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCover
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ X Y p q π hπ U hU hV σ y hy`. Establish `hmem : ∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z = y → z ∈ CxPts.ptsIn q σ (π ⁻¹ᵁ U)`. Introduce `z hz`. Establish `: PtsOver.map π hπ (spMap σ) z ∈ CxPts.ptsIn p σ U` using `hz ▸ hy`. Conclude with `this`.

Establish `hcomp : ∀ (z : CxPts q σ) (hz : PtsOver.map π hπ (spMap σ) z = y) (f : Γ(X, U)), CxPts.evHom (hmem z hz) ((π.app U).hom f) = CxPts.evHom hy f`. Introduce `z hz f`. Rewrite using `[← CxPts.ev_eq, ← CxPts.ev_eq, CxPts.ev_app π hπ U f z, hz]`. Apply `Set.encard_congr` to reduce the goal to its premises. Use `Equiv.ofBijective (fun z => ⟨CxPts.evHom (hmem z.1 z.2), RingHom.ext (hcomp z.1 z.2)⟩) ⟨?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨z, hz⟩ ⟨w, hw⟩ h`. Establish `h' : CxPts.evHom (hmem z hz) = CxPts.evHom (hmem w hw)` using `congrArg Subtype.val h`. Use `Subtype.ext (Subtype.ext (ext_of_valR hV (hmem z hz) (hmem w hw) fun f => ?_))` and prove the remaining obligations. Rewrite using `[valR_eq _ _ (hmem z hz), valR_eq _ _ (hmem w hw)]`. Conclude with `congrArg (fun φ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ => φ f) h'`.

Introduce and unpack `⟨ψ, hψ⟩`. Establish `hψ' : ∀ f, ψ ((π.app U).hom f) = CxPts.evHom hy f` using `fun f => by`. Rewrite using `[← RingHom.comp_apply, hψ]`. Establish `h₀ : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) ⁻¹ᵁ (π ⁻¹ᵁ U)` using `le_preimage_specMap_fromSpec hV (CommRingCat.ofHom ψ)`. Establish `hv : valMap (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) (π ⁻¹ᵁ U) h₀ = CommRingCat.ofHom ψ` using `valMap_specMap_fromSpec hV (CommRingCat.ofHom ψ) h₀`.

Establish `e : (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) ≫ π = y.1`. Use `ext_of_valR hU h₀ hy fun f => ?_` and prove the remaining obligations. Rewrite using `[valR_comp, valR_eq _ _ h₀, hv, valR_eq _ _ hy]`. Conclude with `hψ' f`. Set `z : CxPts q σ` to `⟨Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, by`.

Rewrite using `[← hπ, ← Category.assoc, e, y.2]⟩`. Establish `hz : PtsOver.map π hπ (spMap σ) z = y` using `Subtype.ext e`. Use `⟨⟨z, hz⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(valMap (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) (π ⁻¹ᵁ U) (hmem z hz)).hom = ψ`. Rewrite using `[hv]`.

Both sides reduce to the same expression.
-/
theorem encard_fibre_eq_encard_ringHom : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}
    {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (U : X.Opens), IsAffineOpen U →
    IsAffineOpen (π ⁻¹ᵁ U) → ∀ (σ : k →+* ℂ) (y : GlobalTheory.CxPts p σ) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ U),
    (GlobalTheory.Points.PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard =
      {ψ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ | ψ.comp (π.app U).hom = GlobalTheory.CxPts.evHom hy}.encard := by
  intro k _ X Y p q π hπ U hU hV σ y hy
  have hmem : ∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z = y →
      z ∈ CxPts.ptsIn q σ (π ⁻¹ᵁ U) := by
    intro z hz
    have : PtsOver.map π hπ (spMap σ) z ∈ CxPts.ptsIn p σ U := hz ▸ hy
    exact this
  have hcomp : ∀ (z : CxPts q σ) (hz : PtsOver.map π hπ (spMap σ) z = y) (f : Γ(X, U)),
      CxPts.evHom (hmem z hz) ((π.app U).hom f) = CxPts.evHom hy f := by
    intro z hz f
    rw [← CxPts.ev_eq, ← CxPts.ev_eq, CxPts.ev_app π hπ U f z, hz]
  apply Set.encard_congr
  refine Equiv.ofBijective (fun z => ⟨CxPts.evHom (hmem z.1 z.2), RingHom.ext (hcomp z.1 z.2)⟩)
    ⟨?_, ?_⟩
  · rintro ⟨z, hz⟩ ⟨w, hw⟩ h
    have h' : CxPts.evHom (hmem z hz) = CxPts.evHom (hmem w hw) := congrArg Subtype.val h
    refine Subtype.ext (Subtype.ext (ext_of_valR hV (hmem z hz) (hmem w hw) fun f => ?_))
    rw [valR_eq _ _ (hmem z hz), valR_eq _ _ (hmem w hw)]
    exact congrArg (fun φ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ => φ f) h'
  · rintro ⟨ψ, hψ⟩
    have hψ' : ∀ f, ψ ((π.app U).hom f) = CxPts.evHom hy f := fun f => by
      rw [← RingHom.comp_apply, hψ]
    have h₀ : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) ⁻¹ᵁ (π ⁻¹ᵁ U) :=
      le_preimage_specMap_fromSpec hV (CommRingCat.ofHom ψ)
    have hv : valMap (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) (π ⁻¹ᵁ U) h₀ =
        CommRingCat.ofHom ψ :=
      valMap_specMap_fromSpec hV (CommRingCat.ofHom ψ) h₀
    have e : (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) ≫ π = y.1 := by
      refine ext_of_valR hU h₀ hy fun f => ?_
      rw [valR_comp, valR_eq _ _ h₀, hv, valR_eq _ _ hy]
      exact hψ' f
    let z : CxPts q σ := ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, by
      rw [← hπ, ← Category.assoc, e, y.2]⟩
    have hz : PtsOver.map π hπ (spMap σ) z = y := Subtype.ext e
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    change (valMap (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) (π ⁻¹ᵁ U) (hmem z hz)).hom = ψ
    rw [hv]
    rfl

end GlobalTheory
