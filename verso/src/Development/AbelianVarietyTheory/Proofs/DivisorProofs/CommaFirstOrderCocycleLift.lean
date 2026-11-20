import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationOfData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨c, rfl⟩` from `Hyp2.mk_surjective F x`. Rewrite `hx` using `[pullHyp2_mk, Hyp2.mk_eq_zero]`. Take `⟨⟨f₀, θ₀⟩, hfe⟩` from `hx`.

Take `⟨f', rfl⟩ : ∃ f' : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t'), (f' : C1 (G ⋙ F)) = f₀` from `⟨f₀, rfl⟩`. Take `⟨θ', rfl⟩ : ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (θ' : A0 (G ⋙ F)) = θ₀` from `⟨θ₀, rfl⟩`. Establish `hz : ∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), mp F (G.map b) (f' t t' a) - f' t t'' (a ≫ b) + f' t' t'' b = c.1.1 _ _ _ (G.map a) (G.map b)` using `fun t t' t'' a b ↦ congrArg (fun y : Tot2 (G ⋙ F) ↦ y.1 t t' t'' a b) hfe`. Establish `ha : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), θ' t' - p1 F (G.map a) (θ' t) - D R _ (f' t t' a) = c.1.2.1 _ _ (G.map a)` using `fun t t' a ↦ (congrArg (fun y : Tot2 (G ⋙ F) ↦ y.2.1 t t' a) hfe).trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t' _)`. Establish `hη : ∀ t, dOne R _ (θ' t) = c.1.2.2 (G.obj t)` using `fun t ↦ (congrArg (fun y : Tot2 (G ⋙ F) ↦ y.2.2 t) hfe).trans (qOm_restrict F G t _)`.

Establish `hz0 : H2.mk F ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩ = 0` using `h2 (by`. Rewrite using `[CoefMap.pullCohomologyTwo_class, map_zero]`. Conclude with `H2.mk_eq_zero.2 ⟨f', by funext t t' t'' a b; exact hz a b⟩)`. Take `⟨f, hfz⟩` from `H2.mk_eq_zero.1 hz0`. Establish `hf1 : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), mp F ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = c.1.1 T T' T'' φ ψ` using `fun T T' T'' φ ψ ↦ congrFun (congrFun (congrFun (congrFun (congrFun hfz T) T') T'') φ) ψ`.

Set `u : Z1 (G ⋙ F)` to `⟨fun t t' a ↦ f' t t' a - f _ _ (G.map a), fun t t' t'' a b ↦ by`. Establish `e1` using `hz a b`. Establish `e2` using `hf1 (G.map a) (G.map b)`. Rewrite `e2` using `[← G.map_comp]`. Use `show f' t t'' (a ≫ b) - f _ _ (G.map (a ≫ b)) = mp F (G.map b) (f' t t' a - f _ _ (G.map a)) + (f' t' t'' b - f _ _ (G.map b))`.

Rewrite using `[map_sub]`. Take the linear combination `e2 - e1⟩`. Take `⟨g₀, hg₀⟩` from `h1 (H1.mk _ u)`. Take `⟨g, rfl⟩` from `H1.mk_surjective F g₀`. Rewrite `hg₀` using `[CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]`.

Take `⟨h₀, hh'⟩` from `hg₀`. Take `⟨h', rfl⟩ : ∃ h' : ∀ t, F.obj (G.obj t), (h' : C0 (G ⋙ F)) = h₀` from `⟨h₀, rfl⟩`. Establish `hfu : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), f' t t' a = f _ _ (G.map a) + g.1 _ _ (G.map a) - (h' t' - mp F (G.map a) (h' t))` using `fun t t' a ↦ by`. Establish `e : h' t' - mp F (G.map a) (h' t) = g.1 _ _ (G.map a) - (f' t t' a - f _ _ (G.map a))` using `congrFun (congrFun (congrFun hh' t) t') a`. Take the linear combination `e`.

Take `⟨f₁, hf₁⟩ : ∃ f₁ : C1 F, ∀ T T' φ, f₁ T T' φ = f T T' φ + g.1 T T' φ` from `⟨_, fun _ _ _ ↦ rfl⟩`. Establish `hf1' : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), mp F ψ (f₁ T T' φ) - f₁ T T'' (φ ≫ ψ) + f₁ T' T'' ψ = c.1.1 T T' T'' φ ψ` using `fun T T' T'' φ ψ ↦ by`. Rewrite using `[hf₁, hf₁, hf₁, map_add]`. Take the linear combination `hf1 φ ψ - Z1.comp g φ ψ`. Take `⟨a₁, ha₁⟩ : ∃ a₁ : A1 F, ∀ T T' φ, a₁ T T' φ = c.1.2.1 T T' φ + D R _ (f₁ T T' φ)` from `⟨_, fun _ _ _ ↦ rfl⟩`.

Establish `hac : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), a₁ T T'' (φ ≫ ψ) = p1 F ψ (a₁ T T' φ) + a₁ T' T'' ψ` using `fun T T' T'' φ ψ ↦ by`. Establish `e` using `cechDeRhamTotalCocyclesTwo.one c φ ψ`. Rewrite `e` using `[← hf1' φ ψ, map_add, map_sub]`. Rewrite using `[ha₁, ha₁, ha₁, map_add, p1_D, e]`. Normalize the expressions using the abelian group laws.

Take `⟨θ'', hθ''⟩ : ∃ θ'' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ t, θ'' t = θ' t + D R _ (h' t)` from `⟨_, fun _ ↦ rfl⟩`. Establish `hres : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), a₁ _ _ (G.map a) = θ'' t' - p1 F (G.map a) (θ'' t)` using `fun t t' a ↦ by`. Establish `e` using `ha a`. Rewrite `e` using `[hfu a]`. Simplify using `only [map_add, map_sub] at e`.

Rewrite using `[ha₁, hθ'', hθ'', hf₁]`. Simplify using `only [map_add, p1_D]`. Take the linear combination `(norm := abel1) -e`. Take `⟨θ, hθ⟩` from `hc a₁ hac θ'' hres`. Set `ω' : Glob1 (G ⋙ F)` to `⟨fun t ↦ θ (G.obj t) - θ'' t, fun t t' a ↦ by`.

Establish `e1` using `hθ (G.map a)`. Establish `e2` using `hres a`. Use `show θ (G.obj t') - θ'' t' = p1 F (G.map a) (θ (G.obj t) - θ'' t)`. Rewrite using `[map_sub]`. Take the linear combination `(norm := abel1) e2 - e1⟩`.

Take `⟨ω, hω⟩` from `hf ω'`. Establish `hωG : ∀ t, ω.1 (G.obj t) = θ (G.obj t) - θ'' t` using `fun t ↦ (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).symm.trans (congrArg (fun y : Glob1 (G ⋙ F) ↦ y.1 t) hω)`. Take `⟨θ₁, hθ₁⟩ : ∃ θ₁ : A0 F, ∀ T, θ₁ T = θ T - ω.1 T` from `⟨_, fun _ ↦ rfl⟩`. Establish `hθ1 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), a₁ T T' φ = θ₁ T' - p1 F φ (θ₁ T)` using `fun T T' φ ↦ by`. Rewrite using `[hθ₁, hθ₁, map_sub, ← ω.2 φ, hθ φ]`.

Normalize the expressions using the abelian group laws. Establish `hθ1G : ∀ t, θ₁ (G.obj t) = θ'' t` using `fun t ↦ by rw [hθ₁, hωG]; abel`. Take `⟨η₂, hη₂⟩ : ∃ η₂ : W0 F 2, ∀ T, η₂ T = c.1.2.2 T - dOne R _ (θ₁ T)` from `⟨_, fun _ ↦ rfl⟩`. Establish `hη2 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η₂ T' = pOm F 2 φ (η₂ T)` using `fun T T' φ ↦ by`. Establish `e1` using `cechDeRhamTotalCocyclesTwo.two c φ`.

Establish `e2` using `congrArg (dOne R _) (hθ1 φ)`. Rewrite `e2` using `[ha₁]`. Simplify using `only [map_add, map_sub, dOne_D, add_zero] at e2`. Rewrite using `[hη₂, hη₂, map_sub, pOm_dOne]`. Take the linear combination `(norm := abel1) e1 + e2`.

Establish `hη2G : ∀ t, η₂ (G.obj t) = 0` using `fun t ↦ by`. Rewrite using `[hη₂, hθ1G, hθ'', map_add, dOne_D, add_zero, ← hη t, sub_self]`. Establish `hη0 : ∀ T, η₂ T = 0` using `fun T ↦ hs T _ fun t u ↦ by rw [← hη2 u, hη2G]`. Use `Hyp2.mk_eq_zero.2 ⟨(f₁, θ₁), Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_⟩` and prove the remaining obligations. Conclude with `hf1' φ ψ`.

Establish `e` using `hθ1 φ`. Rewrite `e` using `[ha₁]`. Use `show θ₁ T' - p1 F φ (θ₁ T) - D R _ (f₁ T T' φ) = c.1.2.1 T T' φ`. Take the linear combination `(norm := abel1) -e`. Establish `e` using `hη0 T`.

Rewrite `e` using `[hη₂]`. Conclude with `(sub_eq_zero.1 e).symm`.
-/
theorem pullHyp2_restrict_injective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (h2 : Function.Injective (CoefMap.restrict F G).pull2)
    (h1 : Function.Surjective (CoefMap.restrict F G).pull1)
    (hc : ∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
        κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) →
      ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R],
        (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) →
        ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T))
    (hf : Function.Surjective (pullGlob1 (CoefMap.restrict F G)))
    (hs : ∀ (T : C) (x : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u x = 0) → x = 0) :
    Function.Injective (pullHyp2 (CoefMap.restrict F G)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := Hyp2.mk_surjective F x
  rw [pullHyp2_mk, Hyp2.mk_eq_zero] at hx
  obtain ⟨⟨f₀, θ₀⟩, hfe⟩ := hx
  obtain ⟨f', rfl⟩ : ∃ f' : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t'), (f' : C1 (G ⋙ F)) = f₀ :=
    ⟨f₀, rfl⟩
  obtain ⟨θ', rfl⟩ : ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (θ' : A0 (G ⋙ F)) = θ₀ := ⟨θ₀, rfl⟩
  have hz : ∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''),
      mp F (G.map b) (f' t t' a) - f' t t'' (a ≫ b) + f' t' t'' b =
        c.1.1 _ _ _ (G.map a) (G.map b) :=
    fun t t' t'' a b ↦ congrArg (fun y : Tot2 (G ⋙ F) ↦ y.1 t t' t'' a b) hfe
  have ha : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
      θ' t' - p1 F (G.map a) (θ' t) - D R _ (f' t t' a) = c.1.2.1 _ _ (G.map a) :=
    fun t t' a ↦ (congrArg (fun y : Tot2 (G ⋙ F) ↦ y.2.1 t t' a) hfe).trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t' _)
  have hη : ∀ t, dOne R _ (θ' t) = c.1.2.2 (G.obj t) :=
    fun t ↦ (congrArg (fun y : Tot2 (G ⋙ F) ↦ y.2.2 t) hfe).trans (qOm_restrict F G t _)

  have hz0 : H2.mk F ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩ = 0 := h2 (by
    rw [CoefMap.pullCohomologyTwo_class, map_zero]
    exact H2.mk_eq_zero.2 ⟨f', by funext t t' t'' a b; exact hz a b⟩)
  obtain ⟨f, hfz⟩ := H2.mk_eq_zero.1 hz0
  have hf1 : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      mp F ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = c.1.1 T T' T'' φ ψ :=
    fun T T' T'' φ ψ ↦ congrFun (congrFun (congrFun (congrFun (congrFun hfz T) T') T'') φ) ψ

  let u : Z1 (G ⋙ F) := ⟨fun t t' a ↦ f' t t' a - f _ _ (G.map a), fun t t' t'' a b ↦ by
    have e1 := hz a b
    have e2 := hf1 (G.map a) (G.map b)
    rw [← G.map_comp] at e2
    show f' t t'' (a ≫ b) - f _ _ (G.map (a ≫ b)) =
      mp F (G.map b) (f' t t' a - f _ _ (G.map a)) + (f' t' t'' b - f _ _ (G.map b))
    rw [map_sub]
    linear_combination e2 - e1⟩
  obtain ⟨g₀, hg₀⟩ := h1 (H1.mk _ u)
  obtain ⟨g, rfl⟩ := H1.mk_surjective F g₀
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hg₀
  obtain ⟨h₀, hh'⟩ := hg₀
  obtain ⟨h', rfl⟩ : ∃ h' : ∀ t, F.obj (G.obj t), (h' : C0 (G ⋙ F)) = h₀ := ⟨h₀, rfl⟩
  have hfu : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), f' t t' a =
      f _ _ (G.map a) + g.1 _ _ (G.map a) - (h' t' - mp F (G.map a) (h' t)) := fun t t' a ↦ by
    have e : h' t' - mp F (G.map a) (h' t) = g.1 _ _ (G.map a) - (f' t t' a - f _ _ (G.map a)) :=
      congrFun (congrFun (congrFun hh' t) t') a
    linear_combination e
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : C1 F, ∀ T T' φ, f₁ T T' φ = f T T' φ + g.1 T T' φ := ⟨_, fun _ _ _ ↦ rfl⟩
  have hf1' : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      mp F ψ (f₁ T T' φ) - f₁ T T'' (φ ≫ ψ) + f₁ T' T'' ψ = c.1.1 T T' T'' φ ψ := fun T T' T'' φ ψ ↦ by
    rw [hf₁, hf₁, hf₁, map_add]
    linear_combination hf1 φ ψ - Z1.comp g φ ψ

  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : A1 F, ∀ T T' φ, a₁ T T' φ = c.1.2.1 T T' φ + D R _ (f₁ T T' φ) :=
    ⟨_, fun _ _ _ ↦ rfl⟩
  have hac : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a₁ T T'' (φ ≫ ψ) = p1 F ψ (a₁ T T' φ) + a₁ T' T'' ψ := fun T T' T'' φ ψ ↦ by
    have e := cechDeRhamTotalCocyclesTwo.one c φ ψ
    rw [← hf1' φ ψ, map_add, map_sub] at e
    rw [ha₁, ha₁, ha₁, map_add, p1_D, e]
    abel
  obtain ⟨θ'', hθ''⟩ : ∃ θ'' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ t, θ'' t = θ' t + D R _ (h' t) :=
    ⟨_, fun _ ↦ rfl⟩
  have hres : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), a₁ _ _ (G.map a) = θ'' t' - p1 F (G.map a) (θ'' t) :=
    fun t t' a ↦ by
      have e := ha a
      rw [hfu a] at e
      simp only [map_add, map_sub] at e
      rw [ha₁, hθ'', hθ'', hf₁]
      simp only [map_add, p1_D]
      linear_combination (norm := abel1) -e
  obtain ⟨θ, hθ⟩ := hc a₁ hac θ'' hres

  let ω' : Glob1 (G ⋙ F) := ⟨fun t ↦ θ (G.obj t) - θ'' t, fun t t' a ↦ by
    have e1 := hθ (G.map a)
    have e2 := hres a
    show θ (G.obj t') - θ'' t' = p1 F (G.map a) (θ (G.obj t) - θ'' t)
    rw [map_sub]
    linear_combination (norm := abel1) e2 - e1⟩
  obtain ⟨ω, hω⟩ := hf ω'
  have hωG : ∀ t, ω.1 (G.obj t) = θ (G.obj t) - θ'' t := fun t ↦
    (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).symm.trans (congrArg (fun y : Glob1 (G ⋙ F) ↦ y.1 t) hω)
  obtain ⟨θ₁, hθ₁⟩ : ∃ θ₁ : A0 F, ∀ T, θ₁ T = θ T - ω.1 T := ⟨_, fun _ ↦ rfl⟩
  have hθ1 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), a₁ T T' φ = θ₁ T' - p1 F φ (θ₁ T) := fun T T' φ ↦ by
    rw [hθ₁, hθ₁, map_sub, ← ω.2 φ, hθ φ]; abel
  have hθ1G : ∀ t, θ₁ (G.obj t) = θ'' t := fun t ↦ by rw [hθ₁, hωG]; abel

  obtain ⟨η₂, hη₂⟩ : ∃ η₂ : W0 F 2, ∀ T, η₂ T = c.1.2.2 T - dOne R _ (θ₁ T) := ⟨_, fun _ ↦ rfl⟩
  have hη2 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η₂ T' = pOm F 2 φ (η₂ T) := fun T T' φ ↦ by
    have e1 := cechDeRhamTotalCocyclesTwo.two c φ
    have e2 := congrArg (dOne R _) (hθ1 φ)
    rw [ha₁] at e2
    simp only [map_add, map_sub, dOne_D, add_zero] at e2
    rw [hη₂, hη₂, map_sub, pOm_dOne]
    linear_combination (norm := abel1) e1 + e2
  have hη2G : ∀ t, η₂ (G.obj t) = 0 := fun t ↦ by
    rw [hη₂, hθ1G, hθ'', map_add, dOne_D, add_zero, ← hη t, sub_self]
  have hη0 : ∀ T, η₂ T = 0 := fun T ↦ hs T _ fun t u ↦ by rw [← hη2 u, hη2G]
  refine Hyp2.mk_eq_zero.2 ⟨(f₁, θ₁), Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · exact hf1' φ ψ
  · have e := hθ1 φ
    rw [ha₁] at e
    show θ₁ T' - p1 F φ (θ₁ T) - D R _ (f₁ T T' φ) = c.1.2.1 T T' φ
    linear_combination (norm := abel1) -e
  · have e := hη0 T
    rw [hη₂] at e
    exact (sub_eq_zero.1 e).symm

end GlobalTheory.CechDR
