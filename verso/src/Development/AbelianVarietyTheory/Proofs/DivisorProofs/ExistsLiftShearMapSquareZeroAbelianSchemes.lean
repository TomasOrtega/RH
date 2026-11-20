import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationCompIsoLiftIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationTensorLiftsIffProjectionsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShearLift

variable {S : Scheme.{0}}

/- English proof (translation)
The claim follows from `inferInstanceAs (IsMonHom (lift f g ≫ μ[G]))`.
-/
theorem isMonHom_mul {H G : Over S} [GrpObj H] [GrpObj G] [IsCommMonObj G] (f g : H ⟶ G) [IsMonHom f]
    [IsMonHom g] : IsMonHom (f * g) :=
  inferInstanceAs (IsMonHom (lift f g ≫ μ[G]))

/- English proof (translation)
Establish `key : ∀ {T : Over S'} (x y : T ⟶ G'), x * y = y * x`. Introduce `T x y`. Set `x₀ : Over.mk (T.hom ≫ b) ⟶ G` to `Over.homMk (x.left ≫ φ) (by`. Simplify using `only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])`. Set `y₀ : Over.mk (T.hom ≫ b) ⟶ G` to `Over.homMk (y.left ≫ φ) (by`.

Simplify using `only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])`. Establish `e₁` using `h.2 T x y x₀ y₀ rfl rfl`. Establish `e₂` using `h.2 T y x y₀ x₀ rfl rfl`. Establish `c : x₀ * y₀ = y₀ * x₀` using `mul_comm _ _`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Apply `h.1.hom_ext` to reduce the goal to its premises. Rewrite using `[← e₁, ← e₂, c]`. Rewrite using `[Over.w, Over.w]`. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[mul_eq_mul, comp_mul, key]`.

Simplify using the standard rewrite rules.
-/
theorem isCommMonObj_of_isGrpPullback {S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    [IsCommMonObj G] {b : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G b φ) : IsCommMonObj G' := by
  have key : ∀ {T : Over S'} (x y : T ⟶ G'), x * y = y * x := by
    intro T x y
    let x₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    let y₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (y.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    have e₁ := h.2 T x y x₀ y₀ rfl rfl
    have e₂ := h.2 T y x y₀ x₀ rfl rfl
    have c : x₀ * y₀ = y₀ * x₀ := mul_comm _ _
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← e₁, ← e₂, c]
    · rw [Over.w, Over.w]
  refine ⟨?_⟩
  rw [mul_eq_mul, comp_mul, key]
  simp

/- English proof (translation)
Use `⟨GlobalTheory.AbDual.isPullback_prod m.1 n.1 h₁ h₂, ?_⟩` and prove the remaining obligations. Introduce `T x y x₀ y₀ hx hy`. Establish `e₁ : ((x₀ * y₀) ≫ fst A B).left = ((x * y) ≫ fst A' B').left ≫ f`. Rewrite using `[mul_comp, mul_comp]`. Use `m.2 T _ _ _ _ ?_ ?_` and prove the remaining obligations.

Simplify using `only [Over.comp_left, hx, Category.assoc, h₁]`. Simplify using `only [Over.comp_left, hy, Category.assoc, h₁]`. Establish `e₂ : ((x₀ * y₀) ≫ snd A B).left = ((x * y) ≫ snd A' B').left ≫ g`. Rewrite using `[mul_comp, mul_comp]`. Use `n.2 T _ _ _ _ ?_ ?_` and prove the remaining obligations.

Simplify using `only [Over.comp_left, hx, Category.assoc, h₂]`. Simplify using `only [Over.comp_left, hy, Category.assoc, h₂]`. Establish `p : IsPullback (fst A B).left (snd A B).left A.hom B.hom` using `IsPullback.of_hasPullback _ _`. Apply `p.hom_ext` to reduce the goal to its premises. Rewrite using `[← Over.comp_left, e₁]`.

Simplify using `only [Over.comp_left, Category.assoc, h₁]`. Rewrite using `[← Over.comp_left, e₂]`. Simplify using `only [Over.comp_left, Category.assoc, h₂]`.
-/
theorem isGrpPullback_tensor {S' : Scheme.{0}} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B]
    [GrpObj A'] [GrpObj B'] {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsGrpPullback A' A b f) (n : IsGrpPullback B' B b g) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsGrpPullback (A' ⊗ B') (A ⊗ B) b h := by
  refine ⟨GlobalTheory.AbDual.isPullback_prod m.1 n.1 h₁ h₂, ?_⟩
  intro T x y x₀ y₀ hx hy
  have e₁ : ((x₀ * y₀) ≫ fst A B).left = ((x * y) ≫ fst A' B').left ≫ f := by
    rw [mul_comp, mul_comp]
    refine m.2 T _ _ _ _ ?_ ?_
    · simp only [Over.comp_left, hx, Category.assoc, h₁]
    · simp only [Over.comp_left, hy, Category.assoc, h₁]
  have e₂ : ((x₀ * y₀) ≫ snd A B).left = ((x * y) ≫ snd A' B').left ≫ g := by
    rw [mul_comp, mul_comp]
    refine n.2 T _ _ _ _ ?_ ?_
    · simp only [Over.comp_left, hx, Category.assoc, h₂]
    · simp only [Over.comp_left, hy, Category.assoc, h₂]
  have p : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback _ _
  apply p.hom_ext
  · rw [← Over.comp_left, e₁]
    simp only [Over.comp_left, Category.assoc, h₁]
  · rw [← Over.comp_left, e₂]
    simp only [Over.comp_left, Category.assoc, h₂]

/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hker hL g g' A₀ B₀ _ _ A' B' _ _ i' j' hA hB hAab hBab hAg hBg X Y i j h k hX hY e e' he he' hie hje l hl₁ hl₂ f₀ _ hf`. Use `haveI : IsCommMonObj B' := hBab.comm`. Use `haveI : IsCommMonObj B₀ := isCommMonObj_of_isGrpPullback hB`. Use `haveI hm : IsMonHom ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀) := isMonHom_mul _ _`. Take `⟨σ, hσ⟩ : ∃ σ : A₀ ⊗ B₀ ⟶ A₀ ⊗ B₀, σ = lift (fst A₀ B₀) ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀)` from `⟨_, rfl⟩`.

Take `⟨τ, hτ⟩ : ∃ τ : A₀ ⊗ B₀ ⟶ A₀ ⊗ B₀, τ = lift (fst A₀ B₀) ((fst A₀ B₀ ≫ f₀)⁻¹ * snd A₀ B₀)` from `⟨_, rfl⟩`. Use `haveI : IsMonHom σ := by rw [hσ]; infer_instance`. Establish `σ₁ : σ ≫ fst A₀ B₀ = fst A₀ B₀` using `by rw [hσ, lift_fst]`. Establish `σ₂ : σ ≫ snd A₀ B₀ = (fst A₀ B₀ ≫ f₀) * snd A₀ B₀` using `by rw [hσ, lift_snd]`. Establish `τ₁ : τ ≫ fst A₀ B₀ = fst A₀ B₀` using `by rw [hτ, lift_fst]`.

Establish `τ₂ : τ ≫ snd A₀ B₀ = (fst A₀ B₀ ≫ f₀)⁻¹ * snd A₀ B₀` using `by rw [hτ, lift_snd]`. Establish `hστ : σ ≫ τ = 𝟙 _`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, τ₁, σ₁, Category.id_comp]`. Rewrite using `[Category.assoc, τ₂, comp_mul, GrpObj.comp_inv, ← Category.assoc, σ₁, σ₂, inv_mul_cancel_left, Category.id_comp]`.

Establish `hτσ : τ ≫ σ = 𝟙 _`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, σ₁, τ₁, Category.id_comp]`. Rewrite using `[Category.assoc, σ₂, comp_mul, ← Category.assoc, τ₁, τ₂, mul_inv_cancel_left, Category.id_comp]`. Use `haveI : IsIso σ := ⟨τ, hστ, hτσ⟩`.

Use `haveI : IsIso σ.left := ⟨τ.left, by rw [← Over.comp_left, hστ, Over.id_left], by rw [← Over.comp_left, hτσ, Over.id_left]⟩`. Take `⟨h₀, h₀₁, h₀₂⟩` from `GlobalTheory.AbDual.exists_prod_pullback hA hB`. Establish `hAB : IsGrpPullback (A₀ ⊗ B₀) (A' ⊗ B') (spMap π) h₀` using `isGrpPullback_tensor hA hB h₀₁ h₀₂`. Establish `hABab` using `ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A' B' hAab hBab`. Establish `hABg` using `GlobalTheory.AbDual.smooth_prod hAg hBg`.

Establish `hl : IsPullback l (A₀ ⊗ B₀).hom (X ⊗ Y).hom (spMap π)` using `GlobalTheory.AbDual.isPullback_prod h k hl₁ hl₂`. Establish `hσl : IsPullback (σ.left ≫ l) (A₀ ⊗ B₀).hom (X ⊗ Y).hom (spMap π)`. Establish `q` using `(IsPullback.of_horiz_isIso (fst := σ.left) (snd := (A₀ ⊗ B₀).hom) (f := (A₀ ⊗ B₀).hom) (g := 𝟙 _) ⟨by rw [Over.w, Category.comp_id]⟩).paste_horiz hl`. Rewrite `q` using `[Category.id_comp]`. Then use the resulting hypothesis. Establish `hsm : Smooth (X ⊗ Y).hom` using `by haveI := hX haveI := hY`.

Rewrite using `[Over.tensorObj_hom, Limits.pullback.condition]`. Use `infer_instance`. Establish `hfil : schemeFil (divided₂ hI) (A₀ ⊗ B₀) (X ⊗ Y) l hl.w = schemeFil (divided₂ hI) (A₀ ⊗ B₀) (X ⊗ Y) (σ.left ≫ l) hσl.w`. Use extensionality with `d`. Rewrite using `[GlobalTheory.T.hodgeFiltration_comp_iso_lift_iff R R₀ I (divided₂ hI) π (A₀ ⊗ B₀) (A₀ ⊗ B₀) σ (X ⊗ Y) l hl.w hσl.w d]`.

Establish `P` using `fun d' ↦ GlobalTheory.T.hodgeFiltration_tensor_lifts_iff_projections R R₀ I (divided₂ hI) π A₀ B₀ X Y i j h.w k.w e e' he he' hie hje l hl₁ hl₂ hl.w d'`. Rewrite using `[P d, P (push (divided₂ hI) (spMap π) σ d)]`. Establish `c₁ : push (divided₂ hI) (spMap π) (fst A₀ B₀) (push (divided₂ hI) (spMap π) σ d) = push (divided₂ hI) (spMap π) (fst A₀ B₀) d`. Rewrite using `[← LinearMap.comp_apply, ← push_comp, push_congr _ _ σ₁]`. Establish `c₂ : push (divided₂ hI) (spMap π) (snd A₀ B₀) (push (divided₂ hI) (spMap π) σ d) = push (divided₂ hI) (spMap π) f₀ (push (divided₂ hI) (spMap π) (fst A₀ B₀) d) + push (divided₂ hI) (spMap π) (snd A₀ B₀) d`.

Rewrite using `[← LinearMap.comp_apply, ← push_comp, push_congr _ _ σ₂, push_mul, LinearMap.add_apply, push_comp, LinearMap.comp_apply]`. Rewrite using `[c₁, c₂]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ha, hb⟩`. Conclude with `⟨ha, add_mem (hf _ ha) hb⟩`.

Introduce and unpack `⟨ha, hb⟩`. Use `⟨ha, ?_⟩` and prove the remaining obligations. Use `sub_mem hb (hf _ ha)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_left]`. Then use the resulting hypothesis. Take `⟨E, hE⟩` from `hL.exists_iso hAB hABab hABg hl hσl hsm hsm hfil`.

Use `⟨E.hom ≫ snd X Y, ?_⟩` and prove the remaining obligations. Rewrite using `[Over.comp_left, ← Category.assoc, hE, Category.assoc, hl₂, ← Category.assoc, ← Over.comp_left, σ₂]`.
-/
theorem exists_lift_shear : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π →
    ∀ (g g' : ℕ) (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (i' : A₀.left ⟶ A'.left) (j' : B₀.left ⟶ B'.left),
    IsGrpPullback A₀ A' (spMap π) i' → IsGrpPullback B₀ B' (spMap π) j' → IsAbelianScheme A' → IsAbelianScheme B' →
    SmoothOfRelativeDimension g A'.hom → SmoothOfRelativeDimension g' B'.hom →
    ∀ (X Y : Over (Sp R)) (i : A₀.left ⟶ X.left) (j : B₀.left ⟶ Y.left) (h : IsPullback i A₀.hom X.hom (spMap π))
      (k : IsPullback j B₀.hom Y.hom (spMap π)), Smooth X.hom → Smooth Y.hom →
    ∀ (e : Sp R ⟶ X.left) (e' : Sp R ⟶ Y.left), e ≫ X.hom = 𝟙 _ → e' ≫ Y.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ B₀).left ≫ j = spMap π ≫ e' →
    ∀ (l : (A₀ ⊗ B₀).left ⟶ (X ⊗ Y).left), l ≫ (fst X Y).left = (fst A₀ B₀).left ≫ i → l ≫ (snd X Y).left = (snd A₀ B₀).left ≫ j →
    ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀],
    (∀ d ∈ schemeFil (divided₂ hI) A₀ X i h.w, push (divided₂ hI) (spMap π) f₀ d ∈ schemeFil (divided₂ hI) B₀ Y j k.w) →
    ∃ φ : X ⊗ Y ⟶ Y, l ≫ φ.left = ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀).left ≫ j := by
  intro R R₀ _ _ I hI π hπ hker hL g g' A₀ B₀ _ _ A' B' _ _ i' j' hA hB hAab hBab hAg hBg X Y i j h k hX hY
    e e' he he' hie hje l hl₁ hl₂ f₀ _ hf
  haveI : IsCommMonObj B' := hBab.comm
  haveI : IsCommMonObj B₀ := isCommMonObj_of_isGrpPullback hB
  haveI hm : IsMonHom ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀) := isMonHom_mul _ _
  obtain ⟨σ, hσ⟩ : ∃ σ : A₀ ⊗ B₀ ⟶ A₀ ⊗ B₀, σ = lift (fst A₀ B₀) ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀) := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : A₀ ⊗ B₀ ⟶ A₀ ⊗ B₀, τ = lift (fst A₀ B₀) ((fst A₀ B₀ ≫ f₀)⁻¹ * snd A₀ B₀) := ⟨_, rfl⟩
  haveI : IsMonHom σ := by rw [hσ]; infer_instance
  have σ₁ : σ ≫ fst A₀ B₀ = fst A₀ B₀ := by rw [hσ, lift_fst]
  have σ₂ : σ ≫ snd A₀ B₀ = (fst A₀ B₀ ≫ f₀) * snd A₀ B₀ := by rw [hσ, lift_snd]
  have τ₁ : τ ≫ fst A₀ B₀ = fst A₀ B₀ := by rw [hτ, lift_fst]
  have τ₂ : τ ≫ snd A₀ B₀ = (fst A₀ B₀ ≫ f₀)⁻¹ * snd A₀ B₀ := by rw [hτ, lift_snd]
  have hστ : σ ≫ τ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, τ₁, σ₁, Category.id_comp]
    · rw [Category.assoc, τ₂, comp_mul, GrpObj.comp_inv, ← Category.assoc, σ₁, σ₂, inv_mul_cancel_left,
        Category.id_comp]
  have hτσ : τ ≫ σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, σ₁, τ₁, Category.id_comp]
    · rw [Category.assoc, σ₂, comp_mul, ← Category.assoc, τ₁, τ₂, mul_inv_cancel_left, Category.id_comp]
  haveI : IsIso σ := ⟨τ, hστ, hτσ⟩
  haveI : IsIso σ.left :=
    ⟨τ.left, by rw [← Over.comp_left, hστ, Over.id_left], by rw [← Over.comp_left, hτσ, Over.id_left]⟩
  obtain ⟨h₀, h₀₁, h₀₂⟩ := GlobalTheory.AbDual.exists_prod_pullback hA hB
  have hAB : IsGrpPullback (A₀ ⊗ B₀) (A' ⊗ B') (spMap π) h₀ := isGrpPullback_tensor hA hB h₀₁ h₀₂
  have hABab := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A' B' hAab hBab
  have hABg := GlobalTheory.AbDual.smooth_prod hAg hBg
  have hl : IsPullback l (A₀ ⊗ B₀).hom (X ⊗ Y).hom (spMap π) := GlobalTheory.AbDual.isPullback_prod h k hl₁ hl₂
  have hσl : IsPullback (σ.left ≫ l) (A₀ ⊗ B₀).hom (X ⊗ Y).hom (spMap π) := by
    have q := (IsPullback.of_horiz_isIso (fst := σ.left) (snd := (A₀ ⊗ B₀).hom) (f := (A₀ ⊗ B₀).hom)
      (g := 𝟙 _) ⟨by rw [Over.w, Category.comp_id]⟩).paste_horiz hl
    rwa [Category.id_comp] at q
  have hsm : Smooth (X ⊗ Y).hom := by
    haveI := hX
    haveI := hY
    rw [Over.tensorObj_hom, Limits.pullback.condition]
    infer_instance
  have hfil : schemeFil (divided₂ hI) (A₀ ⊗ B₀) (X ⊗ Y) l hl.w =
      schemeFil (divided₂ hI) (A₀ ⊗ B₀) (X ⊗ Y) (σ.left ≫ l) hσl.w := by
    ext d
    rw [GlobalTheory.T.hodgeFiltration_comp_iso_lift_iff R R₀ I (divided₂ hI) π (A₀ ⊗ B₀) (A₀ ⊗ B₀) σ (X ⊗ Y) l hl.w hσl.w d]
    have P := fun d' ↦ GlobalTheory.T.hodgeFiltration_tensor_lifts_iff_projections R R₀ I (divided₂ hI) π A₀ B₀ X Y i j h.w k.w e e' he he' hie hje l hl₁ hl₂ hl.w d'
    rw [P d, P (push (divided₂ hI) (spMap π) σ d)]
    have c₁ : push (divided₂ hI) (spMap π) (fst A₀ B₀) (push (divided₂ hI) (spMap π) σ d) =
        push (divided₂ hI) (spMap π) (fst A₀ B₀) d := by
      rw [← LinearMap.comp_apply, ← push_comp, push_congr _ _ σ₁]
    have c₂ : push (divided₂ hI) (spMap π) (snd A₀ B₀) (push (divided₂ hI) (spMap π) σ d) =
        push (divided₂ hI) (spMap π) f₀ (push (divided₂ hI) (spMap π) (fst A₀ B₀) d) +
          push (divided₂ hI) (spMap π) (snd A₀ B₀) d := by
      rw [← LinearMap.comp_apply, ← push_comp, push_congr _ _ σ₂, push_mul, LinearMap.add_apply, push_comp,
        LinearMap.comp_apply]
    rw [c₁, c₂]
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨ha, add_mem (hf _ ha) hb⟩
    · rintro ⟨ha, hb⟩
      refine ⟨ha, ?_⟩
      have := sub_mem hb (hf _ ha)
      rwa [add_sub_cancel_left] at this
  obtain ⟨E, hE⟩ := hL.exists_iso hAB hABab hABg hl hσl hsm hsm hfil
  refine ⟨E.hom ≫ snd X Y, ?_⟩
  rw [Over.comp_left, ← Category.assoc, hE, Category.assoc, hl₂, ← Category.assoc, ← Over.comp_left, σ₂]

end GlobalTheory.ShearLift
