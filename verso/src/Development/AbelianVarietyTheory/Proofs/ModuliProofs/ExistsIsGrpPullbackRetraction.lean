import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

def translInvIso {S : Scheme.{0}} (B : Over S) [GrpObj B] (c : 𝟙_ (Over S) ⟶ B) : B ≅ B where
  hom := 𝟙 B * (toUnit B ≫ c)⁻¹
  inv := 𝟙 B * (toUnit B ≫ c)
  hom_inv_id := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, inv_mul_cancel_right]
  inv_hom_id := by
    rw [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, ← Category.assoc, comp_toUnit, mul_inv_cancel_right]

/- English proof (translation)
Simplify using `[translInvIso, MonObj.comp_mul, GrpObj.comp_inv]`.
-/
theorem comp_translInvIso_hom {S : Scheme.{0}} {B T : Over S} [GrpObj B] (c : 𝟙_ (Over S) ⟶ B) (x : T ⟶ B) :
    x ≫ (translInvIso B c).hom = x * (toUnit T ≫ c)⁻¹ := by
  simp [translInvIso, MonObj.comp_mul, GrpObj.comp_inv]

/- English proof (translation)
Establish `hw : (η[G'].left ≫ φ) ≫ G.hom = (Over.mk ((𝟙_ (Over S')).hom ≫ f)).hom`. Rewrite using `[Category.assoc, h.1.w, ← Category.assoc, Over.w]`. Both sides reduce to the same expression. Set `u : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G` to `Over.homMk (η[G'].left ≫ φ) hw`. Establish `hη : (η[G'] : 𝟙_ (Over S') ⟶ G') * η[G'] = η[G']`.

Rewrite using `[MonObj.one_eq_one]`. Conclude with `_root_.one_mul _`. Establish `huu : u * u = u` using `by ext1`. Rewrite using `[h.2 _ η[G'] η[G'] u u rfl rfl, hη]`. Both sides reduce to the same expression.

Establish `hu1 : u = 1` using `mul_eq_left.mp huu`. Use `congrArg (fun v => CommaMorphism.left v) hu1` as an intermediate fact. Simplify `this` using `[u, Hom.one_def]`.
-/
theorem unit_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  have hw : (η[G'].left ≫ φ) ≫ G.hom = (Over.mk ((𝟙_ (Over S')).hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let u : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk (η[G'].left ≫ φ) hw
  have hη : (η[G'] : 𝟙_ (Over S') ⟶ G') * η[G'] = η[G'] := by
    rw [MonObj.one_eq_one]
    exact _root_.one_mul _
  have huu : u * u = u := by
    ext1
    rw [h.2 _ η[G'] η[G'] u u rfl rfl, hη]
    rfl
  have hu1 : u = 1 := mul_eq_left.mp huu
  have := congrArg (fun v => CommaMorphism.left v) hu1
  simpa [u, Hom.one_def] using this

/- English proof (translation)
Set `adj` to `Over.mapPullbackAdj f`. Set `B : Over S'` to `Over.mk (pullback.snd A₀.hom f)`. Set `F : (Over S')ᵒᵖ ⥤ GrpCat` to `(Over.map f).op ⋙ yonedaGrpObj A₀`. Set `α : (F ⋙ forget _).RepresentableBy B` to `{ homEquiv := (adj.homEquiv _ _).symm homEquiv_comp := fun g h => (adj.representableBy A₀).homEquiv_comp g h }`. Set `_ : GrpObj B` to `GrpObj.ofRepresentableBy B F α`.

Set `E : ∀ T : Over S', (T ⟶ B) ≃ ((Over.map f).obj T ⟶ A₀)` to `fun T => (adj.homEquiv T A₀).symm`. Establish `hmul : ∀ {T : Over S'} (x y : T ⟶ B), E T (x * y) = E T x * E T y`. Introduce `T x y`. Conclude with `((yonedaGrpObjIsoOfRepresentableBy B F α).hom.app (Opposite.op T)).hom.map_mul x y`. Establish `hinv : ∀ {T : Over S'} (x : T ⟶ B), E T x⁻¹ = (E T x)⁻¹`.

Introduce `T x`. Conclude with `((yonedaGrpObjIsoOfRepresentableBy B F α).hom.app (Opposite.op T)).hom.map_inv x`. Establish `hleft : ∀ {T : Over S'} (x : T ⟶ B), (E T x).left = x.left ≫ pullback.fst A₀.hom f` using `fun x => rfl`. Establish `hB : IsGrpPullback B A₀ f (pullback.fst A₀.hom f)`. Use `⟨IsPullback.of_hasPullback A₀.hom f, ?_⟩` and prove the remaining obligations.

Introduce `T x y x₁ y₁ hx hy`. Establish `ex : x₁ = E T x` using `by ext1; rw [hx, hleft]`. Establish `ey : y₁ = E T y` using `by ext1; rw [hy, hleft]`. Rewrite using `[ex, ey, ← hmul, hleft]`. Establish `hBab : IsAbelianScheme B` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback h₀ hB`.

Set `x₀ : (Over.map f).obj A' ⟶ A₀` to `Over.homMk ρ₀ (by rw [hρ.w]; rfl)`. Set `m₀ : A' ⟶ B` to `(E A').symm x₀`. Establish `hm₀ : m₀.left ≫ pullback.fst A₀.hom f = ρ₀`. Rewrite using `[← hleft]`. Express the relevant statement in the definitionally equal form `(E A' ((E A').symm x₀)).left = ρ₀`.

Rewrite using `[Equiv.apply_symm_apply]`. Both sides reduce to the same expression. Set `c : 𝟙_ (Over S') ⟶ B` to `η[A'] ≫ m₀`. Set `m : A' ⟶ B` to `m₀ ≫ (translInvIso B c).hom`. Establish `hm : m = m₀ * (toUnit A' ≫ c)⁻¹` using `comp_translInvIso_hom c m₀`.

Establish `hm1 : η[A'] ≫ m = η[B]`. Rewrite using `[← Category.assoc, comp_translInvIso_hom, MonObj.one_eq_one, toUnit_unit, Category.id_comp]`. Conclude with `_root_.mul_inv_cancel c`. Establish `: IsMonHom m` using `rig S' A' B h' hBab m hm1`. Use `⟨m.left ≫ pullback.fst A₀.hom f, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Establish `h1 : IsIso m₀.left`. Establish `e : m₀.left = hρ.isoPullback.hom`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[IsPullback.isoPullback_hom_fst]`. Conclude with `hm₀`.

Rewrite using `[IsPullback.isoPullback_hom_snd]`. Conclude with `Over.w m₀`. Rewrite using `[e]`. Use `infer_instance`. Establish `h2 : IsIso (translInvIso B c).hom.left` using `inferInstanceAs (IsIso ((Over.forget S').map (translInvIso B c).hom))`.

Establish `h3 : IsIso m.left`. Express the relevant statement in the definitionally equal form `IsIso (m₀.left ≫ (translInvIso B c).hom.left)`. Use `infer_instance`. Establish `sq : IsPullback m.left A'.hom B.hom (𝟙 S')` using `IsPullback.of_horiz_isIso ⟨by rw [Over.w m, Category.comp_id]⟩`. Use `sq.paste_horiz (IsPullback.of_hasPullback A₀.hom f)` as an intermediate fact.

Rewrite `this` using `[Category.id_comp]`. Then use the resulting hypothesis. Introduce `T x y x₁ y₁ hx hy`. Rewrite using `[hB.2 T (x ≫ m) (y ≫ m) x₁ y₁ (by rw [hx, ← Category.assoc]; rfl) (by rw [hy, ← Category.assoc]; rfl), ← MonObj.mul_comp, ← Category.assoc]`. Both sides reduce to the same expression. Establish `hJ : j ≫ ((Over.map f).obj A').hom = A₀.hom`.

Express the relevant statement in the definitionally equal form `j ≫ A'.hom ≫ f = A₀.hom`. Rewrite using `[← hρ.w, ← Category.assoc, hjρ, Category.id_comp]`. Set `J : A₀ ⟶ (Over.map f).obj A'` to `Over.homMk j hJ`. Establish `hρm : m.left ≫ pullback.fst A₀.hom f = (x₀ * (E A' (toUnit A' ≫ c))⁻¹).left`. Rewrite using `[← hleft, hm, hmul, hinv, Equiv.apply_symm_apply]`.

Establish `hc : c.left ≫ pullback.fst A₀.hom f = η[A'].left ≫ ρ₀`. Express the relevant statement in the definitionally equal form `(η[A'].left ≫ m₀.left) ≫ _ = _`. Rewrite using `[Category.assoc, hm₀]`. Establish `hz : J ≫ E A' (toUnit A' ≫ c) = 1` using `by ext1`. Express the relevant statement in the definitionally equal form `j ≫ (A'.hom ≫ c.left) ≫ pullback.fst A₀.hom f = A₀.hom ≫ η[A₀].left`.

Rewrite using `[Category.assoc, hc, ← Category.assoc j, hj.1.w]`. Simplify using `only [Category.assoc]`. Rewrite using `[← Category.assoc i, ← unit_left_comp hj, Category.assoc, hjρ, Category.comp_id]`. Establish `hJx : J ≫ x₀ = 𝟙 A₀` using `by ext1`. Conclude with `hjρ`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hρm]`. Both sides reduce to the same expression. Use `_ = 𝟙 A₀.left := by`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, hJx, hz, _root_.inv_one, _root_.mul_one]`.

Both sides reduce to the same expression.
-/
theorem exists_isGrpPullback_retraction (rig : Out.RigiditySt) {S S' : Scheme.{0}} (A₀ : Over S) [GrpObj A₀]
    (A' : Over S') [GrpObj A'] (f : S' ⟶ S) (i : S ⟶ S') (ρ₀ : A'.left ⟶ A₀.left) (j : A₀.left ⟶ A'.left)
    (h₀ : IsAbelianScheme A₀) (h' : IsAbelianScheme A') (hj : IsGrpPullback A₀ A' i j)
    (hρ : IsPullback ρ₀ A'.hom A₀.hom f) (hjρ : j ≫ ρ₀ = 𝟙 _) :
    ∃ ρ, IsGrpPullback A' A₀ f ρ ∧ j ≫ ρ = 𝟙 _ := by
  let adj := Over.mapPullbackAdj f
  let B : Over S' := Over.mk (pullback.snd A₀.hom f)
  let F : (Over S')ᵒᵖ ⥤ GrpCat := (Over.map f).op ⋙ yonedaGrpObj A₀
  let α : (F ⋙ forget _).RepresentableBy B :=
    { homEquiv := (adj.homEquiv _ _).symm
      homEquiv_comp := fun g h => (adj.representableBy A₀).homEquiv_comp g h }
  let _ : GrpObj B := GrpObj.ofRepresentableBy B F α
  let E : ∀ T : Over S', (T ⟶ B) ≃ ((Over.map f).obj T ⟶ A₀) := fun T => (adj.homEquiv T A₀).symm
  have hmul : ∀ {T : Over S'} (x y : T ⟶ B), E T (x * y) = E T x * E T y := by
    intro T x y
    exact ((yonedaGrpObjIsoOfRepresentableBy B F α).hom.app (Opposite.op T)).hom.map_mul x y
  have hinv : ∀ {T : Over S'} (x : T ⟶ B), E T x⁻¹ = (E T x)⁻¹ := by
    intro T x
    exact ((yonedaGrpObjIsoOfRepresentableBy B F α).hom.app (Opposite.op T)).hom.map_inv x
  have hleft : ∀ {T : Over S'} (x : T ⟶ B), (E T x).left = x.left ≫ pullback.fst A₀.hom f :=
    fun x => rfl
  have hB : IsGrpPullback B A₀ f (pullback.fst A₀.hom f) := by
    refine ⟨IsPullback.of_hasPullback A₀.hom f, ?_⟩
    intro T x y x₁ y₁ hx hy
    have ex : x₁ = E T x := by ext1; rw [hx, hleft]
    have ey : y₁ = E T y := by ext1; rw [hy, hleft]
    rw [ex, ey, ← hmul, hleft]
  have hBab : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback h₀ hB
  let x₀ : (Over.map f).obj A' ⟶ A₀ := Over.homMk ρ₀ (by rw [hρ.w]; rfl)
  let m₀ : A' ⟶ B := (E A').symm x₀
  have hm₀ : m₀.left ≫ pullback.fst A₀.hom f = ρ₀ := by
    rw [← hleft]
    change (E A' ((E A').symm x₀)).left = ρ₀
    rw [Equiv.apply_symm_apply]
    rfl
  let c : 𝟙_ (Over S') ⟶ B := η[A'] ≫ m₀
  let m : A' ⟶ B := m₀ ≫ (translInvIso B c).hom
  have hm : m = m₀ * (toUnit A' ≫ c)⁻¹ := comp_translInvIso_hom c m₀
  have hm1 : η[A'] ≫ m = η[B] := by
    rw [← Category.assoc, comp_translInvIso_hom, MonObj.one_eq_one, toUnit_unit, Category.id_comp]
    exact _root_.mul_inv_cancel c
  have : IsMonHom m := rig S' A' B h' hBab m hm1
  refine ⟨m.left ≫ pullback.fst A₀.hom f, ⟨?_, ?_⟩, ?_⟩
  · have h1 : IsIso m₀.left := by
      have e : m₀.left = hρ.isoPullback.hom := by
        apply pullback.hom_ext
        · rw [IsPullback.isoPullback_hom_fst]; exact hm₀
        · rw [IsPullback.isoPullback_hom_snd]; exact Over.w m₀
      rw [e]; infer_instance
    have h2 : IsIso (translInvIso B c).hom.left :=
      inferInstanceAs (IsIso ((Over.forget S').map (translInvIso B c).hom))
    have h3 : IsIso m.left := by
      change IsIso (m₀.left ≫ (translInvIso B c).hom.left)
      infer_instance
    have sq : IsPullback m.left A'.hom B.hom (𝟙 S') :=
      IsPullback.of_horiz_isIso ⟨by rw [Over.w m, Category.comp_id]⟩
    have := sq.paste_horiz (IsPullback.of_hasPullback A₀.hom f)
    rwa [Category.id_comp] at this
  · intro T x y x₁ y₁ hx hy
    rw [hB.2 T (x ≫ m) (y ≫ m) x₁ y₁ (by rw [hx, ← Category.assoc]; rfl)
      (by rw [hy, ← Category.assoc]; rfl), ← MonObj.mul_comp, ← Category.assoc]
    rfl
  · have hJ : j ≫ ((Over.map f).obj A').hom = A₀.hom := by
      change j ≫ A'.hom ≫ f = A₀.hom
      rw [← hρ.w, ← Category.assoc, hjρ, Category.id_comp]
    let J : A₀ ⟶ (Over.map f).obj A' := Over.homMk j hJ
    have hρm : m.left ≫ pullback.fst A₀.hom f = (x₀ * (E A' (toUnit A' ≫ c))⁻¹).left := by
      rw [← hleft, hm, hmul, hinv, Equiv.apply_symm_apply]
    have hc : c.left ≫ pullback.fst A₀.hom f = η[A'].left ≫ ρ₀ := by
      change (η[A'].left ≫ m₀.left) ≫ _ = _
      rw [Category.assoc, hm₀]
    have hz : J ≫ E A' (toUnit A' ≫ c) = 1 := by
      ext1
      change j ≫ (A'.hom ≫ c.left) ≫ pullback.fst A₀.hom f = A₀.hom ≫ η[A₀].left
      rw [Category.assoc, hc, ← Category.assoc j, hj.1.w]
      simp only [Category.assoc]
      rw [← Category.assoc i, ← unit_left_comp hj, Category.assoc, hjρ, Category.comp_id]
    have hJx : J ≫ x₀ = 𝟙 A₀ := by
      ext1
      exact hjρ
    calc j ≫ m.left ≫ pullback.fst A₀.hom f = (J ≫ (x₀ * (E A' (toUnit A' ≫ c))⁻¹)).left := by
          rw [hρm]; rfl
      _ = 𝟙 A₀.left := by
          rw [MonObj.comp_mul, GrpObj.comp_inv, hJx, hz, _root_.inv_one, _root_.mul_one]; rfl

/- English proof (translation)
Introduce `hL A₀ _ A' _ ρ₀ j h₀ h' hj hρ hjρ`. Take `⟨ρ, hρ', hjρ'⟩` from `exists_isGrpPullback_retraction hL.rigidity A₀ A' _ _ ρ₀ j h₀ h' hj hρ hjρ`. Conclude with `⟨ρ, by unfold IsConst; exact ⟨hρ', hj, hjρ'⟩⟩`.
-/
theorem exists_isConst_of_isPullback :
    Out.Laws → ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ₀ : A'.left ⟶ A₀.left) (j : A₀.left ⟶ A'.left), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j → IsPullback ρ₀ A'.hom A₀.hom (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ₀ = 𝟙 _ → ∃ ρ, IsConst A' A₀ ρ j := by
  intro hL A₀ _ A' _ ρ₀ j h₀ h' hj hρ hjρ
  obtain ⟨ρ, hρ', hjρ'⟩ := exists_isGrpPullback_retraction hL.rigidity A₀ A' _ _ ρ₀ j h₀ h' hj hρ hjρ
  exact ⟨ρ, by unfold IsConst; exact ⟨hρ', hj, hjρ'⟩⟩

end GlobalTheory.KS
