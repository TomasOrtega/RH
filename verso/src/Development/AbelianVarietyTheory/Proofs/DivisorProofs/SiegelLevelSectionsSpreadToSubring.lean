import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismsEqSpreadToSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Introduce `g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j hψ hj hjψ`. Use `haveI : Smooth u.A.hom := u.ab.smooth`. Establish `hsec₀ : ∀ a, (d₀.lev a).left ≫ d₀.A.hom = 𝟙 (Sp R₀)` using `fun a => Over.w (d₀.lev a)`. Establish `hsecu : ∀ a, (u.lev a).left ≫ u.A.hom = 𝟙 Y` using `fun a => Over.w (u.lev a)`. Establish `key : ∀ i : Fin g ⊕ Fin g, ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → spMap (Subring.inclusion hle) ≫ (d₀.lev (Pi.single i 1)).left ≫ ψ = spMap (Subring.inclusion hle) ≫ h₀ ≫ (u.lev (Pi.single i 1)).left`.

Introduce `i`. Set `x : Sp R₀ ⟶ pullback u.A.hom h₀` to `pullback.lift ((d₀.lev (Pi.single i 1)).left ≫ ψ) (𝟙 _) (by`. Rewrite using `[Category.assoc, hψ.w, ← Category.assoc, hsec₀, Category.id_comp])`. Set `y : Sp R₀ ⟶ pullback u.A.hom h₀` to `pullback.lift (h₀ ≫ (u.lev (Pi.single i 1)).left) (𝟙 _) (by`. Rewrite using `[Category.assoc, hsecu, Category.comp_id, Category.id_comp])`.

Establish `hx : x ≫ pullback.snd _ _ = 𝟙 _` using `pullback.lift_snd _ _ _`. Establish `hy : y ≫ pullback.snd _ _ = 𝟙 _` using `pullback.lift_snd _ _ _`. Establish `hxy : spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [x, y, Category.assoc, pullback.lift_fst]`.

Rewrite using `[← Category.assoc, ← hj, Category.assoc, hjψ, Category.assoc]`. Simplify using `only [x, y, Category.assoc, pullback.lift_snd]`. Take `⟨F, hF⟩` from `morphisms_eq_spread_to_subring S R₀ (Sp S) (Sp R₀) (pullback u.A.hom h₀) (𝟙 _) (𝟙 _) (pullback.snd _ _) (spMap R₀.subtype) x y (IsPullback.id_vert _) hx hy hxy`. Use `⟨F, fun R₁ hle hF₁ => ?_⟩` and prove the remaining obligations. Use `congrArg (· ≫ pullback.fst u.A.hom h₀) (hF R₁ hle hF₁ (Sp R₁) (𝟙 _) (spMap (Subring.inclusion hle)) (IsPullback.id_vert _))` as an intermediate fact.

Simplify `this` using `only [x, y, Category.assoc, pullback.lift_fst]`. Use `choose F hF using key`. Use `⟨Finset.univ.biUnion F, fun R₁ hle hsub s₁ d₁ φ₁ hgp hlev₁ a => ?_⟩` and prove the remaining obligations. Establish `hbasis : ∀ i : Fin g ⊕ Fin g, (d₁.lev (Pi.single i 1)).left ≫ (φ₁ ≫ ψ) = (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev (Pi.single i 1)).left`. Introduce `i`.

Establish `hFi : (F i : Set S) ⊆ R₁` using `fun x hx => hsub (by`. Simplify using `only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]`. Conclude with `⟨i, hx⟩)`. Rewrite using `[← Category.assoc, hlev₁, Category.assoc, hF i R₁ hle hFi, Category.assoc]`. Set `f : Sp R₁ ⟶ Y` to `spMap (Subring.inclusion hle) ≫ h₀`.

Set `M : Over Y` to `Over.mk ((𝟙_ (Over (Sp R₁))).hom ≫ f)`. Establish `hunit : (toUnit M).left = f`. Use `Over.w (toUnit M)` as an intermediate fact. Conclude with `(Category.comp_id _).symm.trans (this.trans (Category.id_comp _))`. Establish `w : ∀ a, ((d₁.lev a).left ≫ (φ₁ ≫ ψ)) ≫ u.A.hom = M.hom`.

Introduce `a`. Rewrite using `[Category.assoc, hgp.1.w, ← Category.assoc, Over.w (d₁.lev a)]`. Both sides reduce to the same expression. Set `Ψ₁ : (Fin g ⊕ Fin g → ℤ) →+ Additive (M ⟶ u.A)` to `AddMonoidHom.mk' (fun a => Additive.ofMul (toUnit M ≫ u.lev a)) (by`. Introduce `a b`.

Rewrite using `[u.lev_add, comp_mul]`. Use the proof step `rfl)`. Set `Ψ₂ : (Fin g ⊕ Fin g → ℤ) →+ Additive (M ⟶ u.A)` to `AddMonoidHom.mk' (fun a => Additive.ofMul (Over.homMk ((d₁.lev a).left ≫ (φ₁ ≫ ψ)) (w a) : M ⟶ u.A)) (by`. Introduce `a b`. Use `show Additive.ofMul _ = Additive.ofMul (_ * _)`.

Use `congr 1`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hgp.2 (𝟙_ _) (d₁.lev a) (d₁.lev b) _ _ rfl rfl, ← d₁.lev_add]`. Use the proof step `rfl)`. Establish `hΨ : Ψ₁ = Ψ₂`.

Use `AddMonoidHom.functions_ext' _ _ _ (fun i => AddMonoidHom.ext_int ?_)` and prove the remaining obligations. Use `show Additive.ofMul (toUnit M ≫ u.lev (Pi.single i 1)) = Additive.ofMul (Over.homMk ((d₁.lev (Pi.single i 1)).left ≫ (φ₁ ≫ ψ)) (w (Pi.single i 1)) : M ⟶ u.A)`. Use `congrArg Additive.ofMul (Over.OverMorphism.ext ?_)` and prove the remaining obligations. Rewrite using `[Over.comp_left, hunit]`. Conclude with `(hbasis i).symm`.

Use `congrArg (fun φ => (Additive.toMul (φ a)).left) hΨ` as an intermediate fact. Simplify using `only [Ψ₁, Ψ₂, AddMonoidHom.mk'_apply, toMul_ofMul, Over.comp_left, Over.homMk_left] at this`. Rewrite using `[← this, hunit]`.
-/
theorem siegel_levels_spread_to_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → (∀ a, (e.lev a).left ≫ j = spMap R₀.subtype ≫ (d₀.lev a).left) → (∀ a, (e.lev a).left ≫ (j ≫ ψ) = (spMap R₀.subtype ≫ h₀) ≫ (u.lev a).left) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left), IsGrpPullback d₁.A u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) → (∀ a, (d₁.lev a).left ≫ φ₁ = spMap (Subring.inclusion hle) ≫ (d₀.lev a).left) → ∀ a, (d₁.lev a).left ≫ (φ₁ ≫ ψ) = (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev a).left := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j hψ hj hjψ
  classical
  haveI : Smooth u.A.hom := u.ab.smooth
  have hsec₀ : ∀ a, (d₀.lev a).left ≫ d₀.A.hom = 𝟙 (Sp R₀) := fun a => Over.w (d₀.lev a)
  have hsecu : ∀ a, (u.lev a).left ≫ u.A.hom = 𝟙 Y := fun a => Over.w (u.lev a)
  have key : ∀ i : Fin g ⊕ Fin g, ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      spMap (Subring.inclusion hle) ≫ (d₀.lev (Pi.single i 1)).left ≫ ψ =
        spMap (Subring.inclusion hle) ≫ h₀ ≫ (u.lev (Pi.single i 1)).left := by
    intro i
    let x : Sp R₀ ⟶ pullback u.A.hom h₀ := pullback.lift ((d₀.lev (Pi.single i 1)).left ≫ ψ) (𝟙 _) (by
      rw [Category.assoc, hψ.w, ← Category.assoc, hsec₀, Category.id_comp])
    let y : Sp R₀ ⟶ pullback u.A.hom h₀ := pullback.lift (h₀ ≫ (u.lev (Pi.single i 1)).left) (𝟙 _) (by
      rw [Category.assoc, hsecu, Category.comp_id, Category.id_comp])
    have hx : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hy : y ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hxy : spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y := by
      apply pullback.hom_ext
      · simp only [x, y, Category.assoc, pullback.lift_fst]
        rw [← Category.assoc, ← hj, Category.assoc, hjψ, Category.assoc]
      · simp only [x, y, Category.assoc, pullback.lift_snd]
    obtain ⟨F, hF⟩ := morphisms_eq_spread_to_subring S R₀ (Sp S) (Sp R₀) (pullback u.A.hom h₀) (𝟙 _) (𝟙 _)
      (pullback.snd _ _) (spMap R₀.subtype) x y (IsPullback.id_vert _) hx hy hxy
    refine ⟨F, fun R₁ hle hF₁ => ?_⟩
    have := congrArg (· ≫ pullback.fst u.A.hom h₀)
      (hF R₁ hle hF₁ (Sp R₁) (𝟙 _) (spMap (Subring.inclusion hle)) (IsPullback.id_vert _))
    simpa only [x, y, Category.assoc, pullback.lift_fst] using this
  choose F hF using key
  refine ⟨Finset.univ.biUnion F, fun R₁ hle hsub s₁ d₁ φ₁ hgp hlev₁ a => ?_⟩
  have hbasis : ∀ i : Fin g ⊕ Fin g, (d₁.lev (Pi.single i 1)).left ≫ (φ₁ ≫ ψ) =
      (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev (Pi.single i 1)).left := by
    intro i
    have hFi : (F i : Set S) ⊆ R₁ := fun x hx => hsub (by
      simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      exact ⟨i, hx⟩)
    rw [← Category.assoc, hlev₁, Category.assoc, hF i R₁ hle hFi, Category.assoc]
  let f : Sp R₁ ⟶ Y := spMap (Subring.inclusion hle) ≫ h₀
  let M : Over Y := Over.mk ((𝟙_ (Over (Sp R₁))).hom ≫ f)
  have hunit : (toUnit M).left = f := by
    have := Over.w (toUnit M)
    exact (Category.comp_id _).symm.trans (this.trans (Category.id_comp _))
  have w : ∀ a, ((d₁.lev a).left ≫ (φ₁ ≫ ψ)) ≫ u.A.hom = M.hom := by
    intro a
    rw [Category.assoc, hgp.1.w, ← Category.assoc, Over.w (d₁.lev a)]
    rfl
  let Ψ₁ : (Fin g ⊕ Fin g → ℤ) →+ Additive (M ⟶ u.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (toUnit M ≫ u.lev a)) (by
      intro a b
      rw [u.lev_add, comp_mul]
      rfl)
  let Ψ₂ : (Fin g ⊕ Fin g → ℤ) →+ Additive (M ⟶ u.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (Over.homMk ((d₁.lev a).left ≫ (φ₁ ≫ ψ)) (w a) : M ⟶ u.A)) (by
      intro a b
      show Additive.ofMul _ = Additive.ofMul (_ * _)
      congr 1
      apply Over.OverMorphism.ext
      rw [hgp.2 (𝟙_ _) (d₁.lev a) (d₁.lev b) _ _ rfl rfl, ← d₁.lev_add]
      rfl)
  have hΨ : Ψ₁ = Ψ₂ := by
    refine AddMonoidHom.functions_ext' _ _ _ (fun i => AddMonoidHom.ext_int ?_)
    show Additive.ofMul (toUnit M ≫ u.lev (Pi.single i 1)) =
      Additive.ofMul (Over.homMk ((d₁.lev (Pi.single i 1)).left ≫ (φ₁ ≫ ψ)) (w (Pi.single i 1)) : M ⟶ u.A)
    refine congrArg Additive.ofMul (Over.OverMorphism.ext ?_)
    rw [Over.comp_left, hunit]
    exact (hbasis i).symm
  have := congrArg (fun φ => (Additive.toMul (φ a)).left) hΨ
  simp only [Ψ₁, Ψ₂, AddMonoidHom.mk'_apply, toMul_ofMul, Over.comp_left, Over.homMk_left] at this
  rw [← this, hunit]

end GlobalTheory
