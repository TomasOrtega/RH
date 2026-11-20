import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

/- English proof (translation)
Introduce `c'`. Take `⟨c', rfl⟩` from `Hyp1.mk_surjective _ c'`. Take `⟨h0, hh⟩` from `hO (toO _ (Hyp1.mk _ c'))`. Take `⟨f, rfl⟩` from `H1.mk_surjective F h0`. Rewrite `hh` using `[toO_mk, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]`.

Take `⟨g', hg'⟩` from `hh`. Set `g : ∀ t, F.obj (G.obj t)` to `g'`. Set `f' : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t')` to `c'.1.1`. Set `ω' : ∀ t, Ω[F.obj (G.obj t)⁄R]` to `c'.1.2`. Establish `hga : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g t' - mp F (G.map a) (g t) = f.1 _ _ (G.map a) - f' t t' a` using `fun t t' a ↦ congrFun (congrFun (congrFun hg' t) t') a`.

Establish `hκ : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), D R _ (f.1 T T'' (φ ≫ ψ)) = p1 F ψ (D R _ (f.1 T T' φ)) + D R _ (f.1 T' T'' ψ)`. Introduce `T T' T'' φ ψ`. Rewrite using `[Z1.comp f φ ψ, map_add, p1_D]`. Set `θ' : ∀ t, Ω[F.obj (G.obj t)⁄R]` to `fun t ↦ ω' t + D R _ (g t)`. Establish `hθ' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), D R _ (f.1 _ _ (G.map a)) = θ' t' - p1 F (G.map a) (θ' t)`.

Introduce `t t' a`. Establish `e1 : ω' t' = p1 F (G.map a) (ω' t) + D R _ (f' t t' a)` using `cechDeRhamTotalCocyclesOne.conn c' a`. Establish `e2 : f.1 _ _ (G.map a) = g t' - mp F (G.map a) (g t) + f' t t' a` using `(sub_eq_iff_eq_add.1 (hga a).symm)`. Simplify using `only [θ']`. Rewrite using `[e1, e2]`.

Simplify using `only [map_add, map_sub, p1_D]`. Normalize the expressions using the abelian group laws. Take `⟨θ, hθ⟩` from `hc (fun T T' φ ↦ D R _ (f.1 T T' φ)) hκ θ' hθ'`. Establish `hθ2 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), D R _ (f.1 T T' φ) = θ T' - p1 F φ (θ T)` using `hθ`. Set `ψ0 : Glob1 (G ⋙ F)` to `⟨fun t ↦ θ' t - θ (G.obj t), fun t t' a ↦ by`.

Express the relevant statement in the definitionally equal form `θ' t' - θ (G.obj t') = p1 F (G.map a) (θ' t - θ (G.obj t))`. Establish `e` using `(hθ2 (G.map a)).symm.trans (hθ' a)`. Rewrite using `[map_sub]`. Rewrite `e`, the goal using `[← sub_eq_zero]`. Rewrite using `[← neg_eq_zero, ← e]`.

Use the proof step `abel⟩`. Take `⟨ψ, hψ⟩` from `hf ψ0`. Establish `hψG : ∀ t, ψ.1 (G.obj t) = θ' t - θ (G.obj t)` using `fun t ↦ (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).symm.trans (congrArg (fun z : Glob1 (G ⋙ F) ↦ z.1 t) hψ)`. Set `ω : A0 F` to `fun T ↦ θ T + ψ.1 T`. Establish `hωG : ∀ t, ω (G.obj t) = θ' t` using `fun t ↦ by`.

Express the relevant statement in the definitionally equal form `θ (G.obj t) + ψ.1 (G.obj t) = _`. Rewrite using `[hψG]`. Normalize the expressions using the abelian group laws. Establish `hconn : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω T' = p1 F φ (ω T) + D R _ (f.1 T T' φ)`. Introduce `T T' φ`.

Express the relevant statement in the definitionally equal form `θ T' + ψ.1 T' = p1 F φ (θ T + ψ.1 T) + D R _ (f.1 T T' φ)`. Rewrite using `[map_add, ← ψ.2 φ, hθ2 φ]`. Normalize the expressions using the abelian group laws. Establish `hclosed : ∀ T, dOne R _ (ω T) = 0`. Introduce `T`.

Use `hs T _ fun t u ↦ ?_` and prove the remaining obligations. Establish `e : p1 F u (ω T) = ω' t + D R _ (g t) - D R _ (f.1 _ _ u)`. Rewrite using `[eq_sub_iff_add_eq, ← hconn u, hωG]`. Rewrite using `[pOm_dOne, e, map_sub, map_add, dOne_D, dOne_D]`. Establish `e3 : dOne R _ (ω' t) = 0` using `cechDeRhamTotalCocyclesOne.closed c' t`.

Rewrite using `[e3]`. Simplify using the standard rewrite rules. Set `c : cechDeRhamTotalCocyclesOne F` to `⟨(f.1, ω), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨f.2, hconn, hclosed⟩⟩`. Use `⟨Hyp1.mk F c, ?_⟩` and prove the remaining obligations. Rewrite using `[pullHyp1_mk, Hyp1.mk_eq_mk]`.

Use `⟨g', Tot1.ext (fun t t' a ↦ hga a) fun t ↦ ?_⟩` and prove the remaining obligations. Establish `e4 : q1 (CoefMap.restrict F G) t (ω (G.obj t)) = θ' t` using `(cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).trans (hωG t)`. Express the relevant statement in the definitionally equal form `D R _ (g t) = q1 (CoefMap.restrict F G) t (ω (G.obj t)) - c'.1.2 t`. Rewrite using `[e4]`. Express the relevant statement in the definitionally equal form `_ = ω' t + D R _ (g t) - ω' t`.

Normalize the expressions using the abelian group laws.
-/
theorem pullHyp1_restrict_surjective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (hO : Function.Surjective (CoefMap.restrict F G).pull1)
    (hc : ∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
        κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) →
      ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
        κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) →
      ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T))
    (hf : Function.Surjective (pullGlob1 (CoefMap.restrict F G)))
    (hs : ∀ (T : C) (η : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u η = 0) → η = 0) :
    Function.Surjective (pullHyp1 (CoefMap.restrict F G)) := by
  intro c'
  obtain ⟨c', rfl⟩ := Hyp1.mk_surjective _ c'
  obtain ⟨h0, hh⟩ := hO (toO _ (Hyp1.mk _ c'))
  obtain ⟨f, rfl⟩ := H1.mk_surjective F h0
  rw [toO_mk, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hh
  obtain ⟨g', hg'⟩ := hh
  let g : ∀ t, F.obj (G.obj t) := g'
  let f' : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t') := c'.1.1
  let ω' : ∀ t, Ω[F.obj (G.obj t)⁄R] := c'.1.2
  have hga : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
      g t' - mp F (G.map a) (g t) = f.1 _ _ (G.map a) - f' t t' a := fun t t' a ↦
    congrFun (congrFun (congrFun hg' t) t') a
  have hκ : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      D R _ (f.1 T T'' (φ ≫ ψ)) = p1 F ψ (D R _ (f.1 T T' φ)) + D R _ (f.1 T' T'' ψ) := by
    intro T T' T'' φ ψ
    rw [Z1.comp f φ ψ, map_add, p1_D]
  let θ' : ∀ t, Ω[F.obj (G.obj t)⁄R] := fun t ↦ ω' t + D R _ (g t)
  have hθ' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
      D R _ (f.1 _ _ (G.map a)) = θ' t' - p1 F (G.map a) (θ' t) := by
    intro t t' a
    have e1 : ω' t' = p1 F (G.map a) (ω' t) + D R _ (f' t t' a) := cechDeRhamTotalCocyclesOne.conn c' a
    have e2 : f.1 _ _ (G.map a) = g t' - mp F (G.map a) (g t) + f' t t' a :=
      (sub_eq_iff_eq_add.1 (hga a).symm)
    simp only [θ']
    rw [e1, e2]
    simp only [map_add, map_sub, p1_D]
    abel
  obtain ⟨θ, hθ⟩ := hc (fun T T' φ ↦ D R _ (f.1 T T' φ)) hκ θ' hθ'
  have hθ2 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), D R _ (f.1 T T' φ) = θ T' - p1 F φ (θ T) := hθ
  let ψ0 : Glob1 (G ⋙ F) := ⟨fun t ↦ θ' t - θ (G.obj t), fun t t' a ↦ by
    change θ' t' - θ (G.obj t') = p1 F (G.map a) (θ' t - θ (G.obj t))
    have e := (hθ2 (G.map a)).symm.trans (hθ' a)
    rw [map_sub]
    rw [← sub_eq_zero] at e ⊢
    rw [← neg_eq_zero, ← e]
    abel⟩
  obtain ⟨ψ, hψ⟩ := hf ψ0
  have hψG : ∀ t, ψ.1 (G.obj t) = θ' t - θ (G.obj t) := fun t ↦
    (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).symm.trans (congrArg (fun z : Glob1 (G ⋙ F) ↦ z.1 t) hψ)
  let ω : A0 F := fun T ↦ θ T + ψ.1 T
  have hωG : ∀ t, ω (G.obj t) = θ' t := fun t ↦ by
    change θ (G.obj t) + ψ.1 (G.obj t) = _
    rw [hψG]; abel
  have hconn : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω T' = p1 F φ (ω T) + D R _ (f.1 T T' φ) := by
    intro T T' φ
    change θ T' + ψ.1 T' = p1 F φ (θ T + ψ.1 T) + D R _ (f.1 T T' φ)
    rw [map_add, ← ψ.2 φ, hθ2 φ]; abel
  have hclosed : ∀ T, dOne R _ (ω T) = 0 := by
    intro T
    refine hs T _ fun t u ↦ ?_
    have e : p1 F u (ω T) = ω' t + D R _ (g t) - D R _ (f.1 _ _ u) := by
      rw [eq_sub_iff_add_eq, ← hconn u, hωG]
    rw [pOm_dOne, e, map_sub, map_add, dOne_D, dOne_D]
    have e3 : dOne R _ (ω' t) = 0 := cechDeRhamTotalCocyclesOne.closed c' t
    rw [e3]; simp
  let c : cechDeRhamTotalCocyclesOne F := ⟨(f.1, ω), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨f.2, hconn, hclosed⟩⟩
  refine ⟨Hyp1.mk F c, ?_⟩
  rw [pullHyp1_mk, Hyp1.mk_eq_mk]
  refine ⟨g', Tot1.ext (fun t t' a ↦ hga a) fun t ↦ ?_⟩
  have e4 : q1 (CoefMap.restrict F G) t (ω (G.obj t)) = θ' t := (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).trans (hωG t)
  change D R _ (g t) = q1 (CoefMap.restrict F G) t (ω (G.obj t)) - c'.1.2 t
  rw [e4]
  change _ = ω' t + D R _ (g t) - ω' t
  abel

end GlobalTheory.CechDR
