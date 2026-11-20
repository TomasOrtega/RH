import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
theorem spMap_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
The claim follows from `RingHom.ext fun x => by ext <;> simp [dualMap]`.
-/
theorem dualMap_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) := RingHom.ext fun x => by ext <;> simp [dualMap]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Apply the tactic sequence `have e : dualMap (AlgHom.id c.F S).toRingHom = RingHom.id _ := RingHom.ext fun x => by ext <;> simp [dualMap]`. Use `⟨?_, ?_, 𝟙 _, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[spMap_algHom_id, Category.id_comp]`. Introduce `τ i`. Rewrite using `[e]`.

Simplify using `[spMap]`. Conclude with `Category.id_comp _`. Rewrite using `[spMap_algHom_id]`. Simplify using the standard rewrite rules. Introduce `i h`.

Rewrite using `[show Scheme.Hom.appLE (𝟙 (Gx y.x)) _ _ h = Scheme.Hom.app (𝟙 (Gx y.x)) ((PPx y.x).U i) from (Scheme.Hom.app_eq_appLE _).symm, Scheme.Hom.id_app]`. Both sides reduce to the same expression.
-/
theorem frMap_refl {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y := by
  have e : dualMap (AlgHom.id c.F S).toRingHom = RingHom.id _ :=
    RingHom.ext fun x => by ext <;> simp [dualMap]
  refine ⟨?_, ?_, 𝟙 _, ?_, ?_, ?_⟩
  · rw [spMap_algHom_id, Category.id_comp]
  · intro τ i
    rw [e]
    simp [spMap]
  · exact Category.id_comp _
  · rw [spMap_algHom_id]
    simp
  · intro i h
    rw [show Scheme.Hom.appLE (𝟙 (Gx y.x)) _ _ h = Scheme.Hom.app (𝟙 (Gx y.x)) ((PPx y.x).U i) from
      (Scheme.Hom.app_eq_appLE _).symm, Scheme.Hom.id_app]
    rfl

/- English proof (translation)
Establish `hc : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom` using `rfl`. Take `⟨hx1, hu1, pm1, hs1, hf1, ha1⟩` from `h₁`. Take `⟨hx2, hu2, pm2, hs2, hf2, ha2⟩` from `h₂`. Use `⟨?_, ?_, pm2 ≫ pm1, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hx2, hx1, hc, spMap_comp, Category.assoc]`.

Introduce `τ i`. Rewrite using `[hu2, hu1, hc, dualMap_comp, spMap_comp, Category.assoc]`. Rewrite using `[Category.assoc, hs1, hs2]`. Rewrite using `[Category.assoc, hf1, ← Category.assoc, hf2, Category.assoc, ← spMap_comp, hc]`. Introduce `i h`.

Establish `hb1 : ∀ p, (snd (Over.mk y.x) Xo.univ.t.G).left.base (pm1.base p) = (snd (Over.mk z.x) Xo.univ.t.G).left.base p` using `fun p => by`. Rewrite using `[← hs1]`. Both sides reduce to the same expression. Establish `hb2 : ∀ p, (snd (Over.mk z.x) Xo.univ.t.G).left.base (pm2.base p) = (snd (Over.mk w.x) Xo.univ.t.G).left.base p` using `fun p => by`. Rewrite using `[← hs2]`.

Both sides reduce to the same expression. Establish `h1 : (PPx z.x).U i ≤ pm1 ⁻¹ᵁ (PPx y.x).U i`. Introduce `p hp`. Express the relevant statement in the definitionally equal form `p ∈ (⋂ k, (snd (Over.mk z.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _)) at hp`. Express the relevant statement in the definitionally equal form `pm1.base p ∈ (⋂ k, (snd (Over.mk y.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _))`.

Simplify using `only [Set.mem_iInter, Set.mem_preimage] at hp ⊢`. Introduce `k`. Rewrite using `[hb1]`. Conclude with `hp k`. Establish `h2 : (PPx w.x).U i ≤ pm2 ⁻¹ᵁ (PPx z.x).U i`.

Introduce `p hp`. Express the relevant statement in the definitionally equal form `p ∈ (⋂ k, (snd (Over.mk w.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _)) at hp`. Express the relevant statement in the definitionally equal form `pm2.base p ∈ (⋂ k, (snd (Over.mk z.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _))`. Simplify using `only [Set.mem_iInter, Set.mem_preimage] at hp ⊢`. Introduce `k`.

Rewrite using `[hb2]`. Conclude with `hp k`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE pm2 pm1 _ _ _ h1 h2]`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply]`. Rewrite using `[ha1 i h1, ha2 i h2]`.
-/
theorem frMap_trans {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U}
    (h₁ : FrMap φ y z) (h₂ : FrMap ψ z w) : FrMap (ψ.comp φ) y w := by
  have hc : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom := rfl
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  refine ⟨?_, ?_, pm2 ≫ pm1, ?_, ?_, ?_⟩
  · rw [hx2, hx1, hc, spMap_comp, Category.assoc]
  · intro τ i
    rw [hu2, hu1, hc, dualMap_comp, spMap_comp, Category.assoc]
  · rw [Category.assoc, hs1, hs2]
  · rw [Category.assoc, hf1, ← Category.assoc, hf2, Category.assoc, ← spMap_comp, hc]
  · intro i h
    have hb1 : ∀ p, (snd (Over.mk y.x) Xo.univ.t.G).left.base (pm1.base p) =
        (snd (Over.mk z.x) Xo.univ.t.G).left.base p := fun p => by
      rw [← hs1]; rfl
    have hb2 : ∀ p, (snd (Over.mk z.x) Xo.univ.t.G).left.base (pm2.base p) =
        (snd (Over.mk w.x) Xo.univ.t.G).left.base p := fun p => by
      rw [← hs2]; rfl
    have h1 : (PPx z.x).U i ≤ pm1 ⁻¹ᵁ (PPx y.x).U i := by
      intro p hp
      change p ∈ (⋂ k, (snd (Over.mk z.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _)) at hp
      change pm1.base p ∈ (⋂ k, (snd (Over.mk y.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _))
      simp only [Set.mem_iInter, Set.mem_preimage] at hp ⊢
      intro k
      rw [hb1]
      exact hp k
    have h2 : (PPx w.x).U i ≤ pm2 ⁻¹ᵁ (PPx z.x).U i := by
      intro p hp
      change p ∈ (⋂ k, (snd (Over.mk w.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _)) at hp
      change pm2.base p ∈ (⋂ k, (snd (Over.mk z.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _))
      simp only [Set.mem_iInter, Set.mem_preimage] at hp ⊢
      intro k
      rw [hb2]
      exact hp k
    rw [← Scheme.Hom.appLE_comp_appLE pm2 pm1 _ _ _ h1 h2]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [ha1 i h1, ha2 i h2]

/- English proof (translation)
Use `show Module.FaithfullyFlat S S`. Conclude with `Module.FaithfullyFlat.self S`.
-/
theorem faithfullyFlat_id (S : Type) [CommRing S] : (RingHom.id S).FaithfullyFlat := by
  show Module.FaithfullyFlat S S
  exact Module.FaithfullyFlat.self S

end ReciprocityTheory.ChartRestriction.G.PullbackSections
