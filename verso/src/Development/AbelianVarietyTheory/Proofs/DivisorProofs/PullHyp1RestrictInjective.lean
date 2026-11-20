import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Take `⟨x, rfl⟩` from `Hyp1.mk_surjective F c`. Establish `ht : toO F (Hyp1.mk F x) = 0` using `h1 (by rw [← toO_pullHyp1, hc, map_zero, map_zero])`. Rewrite `hc` using `[pullHyp1_mk, Hyp1.mk_eq_zero]`.

Take `⟨g, hg'⟩` from `hc`. Take `⟨g', rfl⟩ : ∃ g' : ∀ t, F.obj (G.obj t), (g' : Tot0 (G ⋙ F)) = g` from `⟨g, rfl⟩`. Establish `hf' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' - mp F (G.map a) (g' t) = x.1.1 _ _ (G.map a)` using `fun t t' a ↦ congrArg (fun y : Tot1 (G ⋙ F) ↦ y.1 t t' a) hg'`. Establish `hω : ∀ t, D R _ (g' t) = x.1.2 (G.obj t)` using `fun t ↦ (congrArg (fun y : Tot1 (G ⋙ F) ↦ y.2 t) hg').trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _)`. Rewrite `ht` using `[toO_mk, H1.mk_eq_zero]`.

Take `⟨g₀, hg₀⟩` from `ht`. Establish `hg0 : ∀ (T T' : C) (φ : T ⟶ T'), g₀ T' - mp F φ (g₀ T) = x.1.1 T T' φ` using `fun T T' φ ↦ congrFun (congrFun (congrFun hg₀ T) T') φ`. Take `⟨h, hh, hhG⟩` from `h0 (fun t ↦ g' t - g₀ (G.obj t)) (fun t t' a ↦ by`. Establish `e1` using `hf' a`. Establish `e2` using `hg0 _ _ (G.map a)`.

Rewrite using `[map_sub]`. Take the linear combination `e1 - e2)`. Set `θ : Glob1 F` to `⟨fun T ↦ x.1.2 T - D R _ (g₀ T), fun T T' φ ↦ by show x.1.2 T' - D R _ (g₀ T') = p1 F φ (x.1.2 T - D R _ (g₀ T))`. Rewrite using `[map_sub, p1_D, cechDeRhamTotalCocyclesOne.conn x φ, ← hg0 T T' φ, map_sub]`. Use the proof step `abel⟩`.

Set `ψ : Glob1 F` to `⟨fun T ↦ D R _ (h T), fun T T' φ ↦ by show D R _ (h T') = p1 F φ (D R _ (h T))`. Rewrite using `[p1_D, ← hh φ]⟩`. Establish `hθψ : θ = ψ` using `hf (Subtype.ext (funext fun t ↦ by`. Express the relevant statement in the definitionally equal form `q1 (CoefMap.restrict F G) t (θ.1 (G.obj t)) = q1 (CoefMap.restrict F G) t (ψ.1 (G.obj t))`. Rewrite using `[cechDeRhamCoefMapOneForms_restrictAlongFunctor, cechDeRhamCoefMapOneForms_restrictAlongFunctor]`.

Use `show x.1.2 (G.obj t) - D R _ (g₀ (G.obj t)) = D R _ (h (G.obj t))`. Rewrite using `[hhG, map_sub, hω]))`. Use `Hyp1.mk_eq_zero.2 ⟨g₀ + h, Tot1.ext (fun T T' φ ↦ ?_) fun T ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[dTot0_f]`. Simplify using `only [Pi.add_apply, map_add]`.

Take the linear combination `hh φ + hg0 T T' φ`. Establish `e : x.1.2 T - D R _ (g₀ T) = D R _ (h T)` using `congrArg (fun ω : Glob1 F ↦ ω.1 T) hθψ`. Rewrite using `[dTot0_ω, Pi.add_apply, map_add, ← e]`. Normalize the expressions using the abelian group laws.
-/
theorem pullHyp1_restrict_injective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (h1 : Function.Injective (CoefMap.restrict F G).pull1)
    (h0 : ∀ g' : ∀ t, F.obj (G.obj t), (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' = mp F (G.map a) (g' t)) →
      ∃ g : C0 F, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) ∧ ∀ t, g (G.obj t) = g' t)
    (hf : Function.Injective (pullGlob1 (CoefMap.restrict F G))) :
    Function.Injective (pullHyp1 (CoefMap.restrict F G)) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, rfl⟩ := Hyp1.mk_surjective F c
  have ht : toO F (Hyp1.mk F x) = 0 := h1 (by rw [← toO_pullHyp1, hc, map_zero, map_zero])
  rw [pullHyp1_mk, Hyp1.mk_eq_zero] at hc
  obtain ⟨g, hg'⟩ := hc
  obtain ⟨g', rfl⟩ : ∃ g' : ∀ t, F.obj (G.obj t), (g' : Tot0 (G ⋙ F)) = g := ⟨g, rfl⟩
  have hf' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' - mp F (G.map a) (g' t) = x.1.1 _ _ (G.map a) :=
    fun t t' a ↦ congrArg (fun y : Tot1 (G ⋙ F) ↦ y.1 t t' a) hg'
  have hω : ∀ t, D R _ (g' t) = x.1.2 (G.obj t) := fun t ↦
    (congrArg (fun y : Tot1 (G ⋙ F) ↦ y.2 t) hg').trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _)
  rw [toO_mk, H1.mk_eq_zero] at ht
  obtain ⟨g₀, hg₀⟩ := ht
  have hg0 : ∀ (T T' : C) (φ : T ⟶ T'), g₀ T' - mp F φ (g₀ T) = x.1.1 T T' φ := fun T T' φ ↦
    congrFun (congrFun (congrFun hg₀ T) T') φ
  obtain ⟨h, hh, hhG⟩ := h0 (fun t ↦ g' t - g₀ (G.obj t)) (fun t t' a ↦ by
    have e1 := hf' a
    have e2 := hg0 _ _ (G.map a)
    rw [map_sub]
    linear_combination e1 - e2)
  let θ : Glob1 F := ⟨fun T ↦ x.1.2 T - D R _ (g₀ T), fun T T' φ ↦ by
    show x.1.2 T' - D R _ (g₀ T') = p1 F φ (x.1.2 T - D R _ (g₀ T))
    rw [map_sub, p1_D, cechDeRhamTotalCocyclesOne.conn x φ, ← hg0 T T' φ, map_sub]; abel⟩
  let ψ : Glob1 F := ⟨fun T ↦ D R _ (h T), fun T T' φ ↦ by
    show D R _ (h T') = p1 F φ (D R _ (h T))
    rw [p1_D, ← hh φ]⟩
  have hθψ : θ = ψ := hf (Subtype.ext (funext fun t ↦ by
    change q1 (CoefMap.restrict F G) t (θ.1 (G.obj t)) = q1 (CoefMap.restrict F G) t (ψ.1 (G.obj t))
    rw [cechDeRhamCoefMapOneForms_restrictAlongFunctor, cechDeRhamCoefMapOneForms_restrictAlongFunctor]
    show x.1.2 (G.obj t) - D R _ (g₀ (G.obj t)) = D R _ (h (G.obj t))
    rw [hhG, map_sub, hω]))
  refine Hyp1.mk_eq_zero.2 ⟨g₀ + h, Tot1.ext (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · rw [dTot0_f]
    simp only [Pi.add_apply, map_add]
    linear_combination hh φ + hg0 T T' φ
  · have e : x.1.2 T - D R _ (g₀ T) = D R _ (h T) := congrArg (fun ω : Glob1 F ↦ ω.1 T) hθψ
    rw [dTot0_ω, Pi.add_apply, map_add, ← e]
    abel

end GlobalTheory.CechDR
