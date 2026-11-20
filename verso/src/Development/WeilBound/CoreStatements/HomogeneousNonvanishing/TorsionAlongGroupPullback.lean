import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Substitute `hb` using the available equality. Establish `hw : ∀ x : Over.mk a ⟶ G', (x.left ≫ φ) ≫ G.hom = a ≫ f`. Introduce `x`. Establish `hx : x.left ≫ G'.hom = a` using `Over.w x`. Rewrite using `[Category.assoc, h.1.w, ← Category.assoc, hx]`.

Set `F : (Over.mk a ⟶ G') → (Over.mk (a ≫ f) ⟶ G)` to `fun x => Over.homMk (x.left ≫ φ) (hw x)`. Establish `hF : ∀ x, (F x).left = x.left ≫ φ` using `fun x => rfl`. Establish `hmul : ∀ x y, F (x * y) = F x * F y`. Introduce `x y`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[hF]`. Conclude with `(h.2 (Over.mk a) x y (F x) (F y) (hF x) (hF y)).symm`. Use `⟨MonoidHom.mk' F hmul, ⟨?_, ?_⟩, hF⟩` and prove the remaining obligations. Introduce `x y hxy`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Establish `e1 : (F x).left = (F y).left` using `congrArg (fun g => Over.Hom.left g) hxy`. Rewrite `e1` using `[hF, hF]`. Apply `h.1.hom_ext e1` to reduce the goal to its premises. Rewrite using `[Over.w x, Over.w y]`. Introduce `g`.

Establish `hg : g.left ≫ G.hom = a ≫ f` using `Over.w g`. Use `⟨Over.homMk (h.1.lift g.left a hg) (h.1.lift_snd _ _ _), ?_⟩` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show (h.1.lift g.left a hg) ≫ φ = g.left`. Conclude with `h.1.lift_fst _ _ _`.
-/
theorem tors_push {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : U ⟶ S') (b : U ⟶ S) (hb : a ≫ f = b) :
    ∃ π : (Over.mk a ⟶ G') →* (Over.mk b ⟶ G), Function.Bijective π ∧ ∀ x, (π x).left = x.left ≫ φ := by
  subst hb
  have hw : ∀ x : Over.mk a ⟶ G', (x.left ≫ φ) ≫ G.hom = a ≫ f := by
    intro x
    have hx : x.left ≫ G'.hom = a := Over.w x
    rw [Category.assoc, h.1.w, ← Category.assoc, hx]
  let F : (Over.mk a ⟶ G') → (Over.mk (a ≫ f) ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (hw x)
  have hF : ∀ x, (F x).left = x.left ≫ φ := fun x => rfl
  have hmul : ∀ x y, F (x * y) = F x * F y := by
    intro x y
    apply Over.OverMorphism.ext
    rw [hF]
    exact (h.2 (Over.mk a) x y (F x) (F y) (hF x) (hF y)).symm
  refine ⟨MonoidHom.mk' F hmul, ⟨?_, ?_⟩, hF⟩
  · intro x y hxy
    apply Over.OverMorphism.ext
    have e1 : (F x).left = (F y).left := congrArg (fun g => Over.Hom.left g) hxy
    rw [hF, hF] at e1
    apply h.1.hom_ext e1
    rw [Over.w x, Over.w y]
  · intro g
    have hg : g.left ≫ G.hom = a ≫ f := Over.w g
    refine ⟨Over.homMk (h.1.lift g.left a hg) (h.1.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    show (h.1.lift g.left a hg) ≫ φ = g.left
    exact h.1.lift_fst _ _ _

/- English proof (translation)
Establish `cancel : ∀ {W : Scheme.{0}} (u v : W ⟶ G₀.left), u ≫ ψ = v ≫ ψ → u ≫ G₀.hom = v ≫ G₀.hom → u = v` using `fun u v e1 e2 => h.1.hom_ext e1 e2`. Establish `base : ∀ (Y : Over (Sp R)) (y : Y ⟶ Γ.G), (y.left ≫ i₀) ≫ G₀.hom = Y.hom`. Introduce `Y y`. Rewrite using `[Category.assoc, hi]`. Conclude with `Over.w y`.

Establish `pushY : ∀ (Y : Over (Sp R)), ∃ π : (Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀) →* (Over.mk (Y.hom ≫ x) ⟶ G), Function.Bijective π ∧ ∀ g, (π g).left = g.left ≫ ψ`. Introduce `Y`. Conclude with `tors_push h (Y.hom ≫ 𝟙 _) (Y.hom ≫ x) (by simp)`. Establish `w1 : ∀ (Y : Over (Sp R)) (g : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀), g.left ≫ G₀.hom = Y.hom`. Introduce `Y g`.

Use `Over.w g` as an intermediate fact. Simplify using `using this`. Prove the components needed by the constructor for the conclusion. Introduce `t`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, h.1.w, ← Category.assoc, hi]`. Introduce `Y y z y₀ z₀ hy hz`. Take `⟨π, -, hπ⟩` from `pushY Y`. Set `y₁ : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀` to `Over.homMk (y.left ≫ i₀) (by simpa using base Y y)`. Set `z₁ : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀` to `Over.homMk (z.left ≫ i₀) (by simpa using base Y z)`.

Establish `ey : π y₁ = y₀`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hπ, hy]`. Use `show (y.left ≫ i₀) ≫ ψ = _`. Rewrite using `[Category.assoc]`.

Establish `ez : π z₁ = z₀`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hπ, hz]`. Use `show (z.left ≫ i₀) ≫ ψ = _`. Rewrite using `[Category.assoc]`.

Rewrite using `[← ey, ← ez, ← map_mul, hπ, t.mul Y y z y₁ z₁ rfl rfl, Category.assoc]`. Introduce `Y y z e`. Apply `t.inj Y y z` to reduce the goal to its premises. Apply `cancel` to reduce the goal to its premises. Simplify `e` using `only [Category.assoc]`.

Rewrite using `[base Y y, base Y z]`. Introduce `Y g`. Take `⟨π, ⟨hinj, hsurj⟩, hπ⟩` from `pushY Y`. Take `⟨g₁, rfl⟩` from `hsurj g`. Rewrite using `[← map_pow, ← map_one π, hinj.eq_iff, t.kernel Y g₁, hπ]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Conclude with `⟨y, by rw [← hy, Category.assoc]⟩`. Introduce and unpack `⟨y, hy⟩`. Use `⟨y, cancel _ _ (by rw [Category.assoc, hy]) ?_⟩` and prove the remaining obligations.

Rewrite using `[base Y y, w1 Y g₁]`. Introduce `t`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hi, Category.comp_id]`. Introduce `Y y z y₀ z₀ hy hz`.

Take `⟨π, -, hπ⟩` from `pushY Y`. Establish `m` using `t.mul Y y z (π y₀) (π z₀) (by rw [hπ, hy, Category.assoc]) (by rw [hπ, hz, Category.assoc])`. Rewrite `m` using `[← map_mul, hπ]`. Apply `cancel` to reduce the goal to its premises. Rewrite using `[m, Category.assoc]`.

Rewrite using `[w1 Y, base Y]`. Introduce `Y y z e`. Apply `t.inj Y y z` to reduce the goal to its premises. Simplify using `only [← Category.assoc, e]`. Introduce `Y g₁`.

Take `⟨π, ⟨hinj, -⟩, hπ⟩` from `pushY Y`. Rewrite using `[← hinj.eq_iff, map_pow, map_one, t.kernel Y (π g₁), hπ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Use `⟨y, cancel _ _ (by rw [Category.assoc, hy]) ?_⟩` and prove the remaining obligations.

Rewrite using `[base Y y, w1 Y g₁]`. Introduce and unpack `⟨y, hy⟩`. Conclude with `⟨y, by rw [← hy, Category.assoc]⟩`.
-/
theorem tors_iff {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T) {X : Scheme.{0}}
    {x : Sp R ⟶ X} {G : Over X} [GrpObj G] {G₀ : Over (Sp R)} [GrpObj G₀] {ψ : G₀.left ⟶ G.left} (N : ℕ)
    (h : IsGrpPullback G₀ G x ψ) (i₀ : Γ.G.left ⟶ G₀.left) (hi : i₀ ≫ G₀.hom = Γ.G.hom) :
    Γ.IsTorsionAlong G₀ (𝟙 _) N i₀ ↔ Γ.IsTorsionAlong G x N (i₀ ≫ ψ) := by
  have cancel : ∀ {W : Scheme.{0}} (u v : W ⟶ G₀.left), u ≫ ψ = v ≫ ψ → u ≫ G₀.hom = v ≫ G₀.hom → u = v :=
    fun u v e1 e2 => h.1.hom_ext e1 e2
  have base : ∀ (Y : Over (Sp R)) (y : Y ⟶ Γ.G), (y.left ≫ i₀) ≫ G₀.hom = Y.hom := by
    intro Y y
    rw [Category.assoc, hi]
    exact Over.w y
  have pushY : ∀ (Y : Over (Sp R)), ∃ π : (Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀) →* (Over.mk (Y.hom ≫ x) ⟶ G),
      Function.Bijective π ∧ ∀ g, (π g).left = g.left ≫ ψ := by
    intro Y
    exact tors_push h (Y.hom ≫ 𝟙 _) (Y.hom ≫ x) (by simp)
  have w1 : ∀ (Y : Over (Sp R)) (g : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀), g.left ≫ G₀.hom = Y.hom := by
    intro Y g
    have := Over.w g
    simpa using this
  constructor
  · intro t
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, h.1.w, ← Category.assoc, hi]
    · intro Y y z y₀ z₀ hy hz
      obtain ⟨π, -, hπ⟩ := pushY Y
      let y₁ : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀ := Over.homMk (y.left ≫ i₀) (by simpa using base Y y)
      let z₁ : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀ := Over.homMk (z.left ≫ i₀) (by simpa using base Y z)
      have ey : π y₁ = y₀ := by
        apply Over.OverMorphism.ext
        rw [hπ, hy]
        show (y.left ≫ i₀) ≫ ψ = _
        rw [Category.assoc]
      have ez : π z₁ = z₀ := by
        apply Over.OverMorphism.ext
        rw [hπ, hz]
        show (z.left ≫ i₀) ≫ ψ = _
        rw [Category.assoc]
      rw [← ey, ← ez, ← map_mul, hπ, t.mul Y y z y₁ z₁ rfl rfl, Category.assoc]
    · intro Y y z e
      apply t.inj Y y z
      apply cancel
      · simpa only [Category.assoc] using e
      · rw [base Y y, base Y z]
    · intro Y g
      obtain ⟨π, ⟨hinj, hsurj⟩, hπ⟩ := pushY Y
      obtain ⟨g₁, rfl⟩ := hsurj g
      rw [← map_pow, ← map_one π, hinj.eq_iff, t.kernel Y g₁, hπ]
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨y, by rw [← hy, Category.assoc]⟩
      · rintro ⟨y, hy⟩
        refine ⟨y, cancel _ _ (by rw [Category.assoc, hy]) ?_⟩
        rw [base Y y, w1 Y g₁]
  · intro t
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hi, Category.comp_id]
    · intro Y y z y₀ z₀ hy hz
      obtain ⟨π, -, hπ⟩ := pushY Y
      have m := t.mul Y y z (π y₀) (π z₀) (by rw [hπ, hy, Category.assoc]) (by rw [hπ, hz, Category.assoc])
      rw [← map_mul, hπ] at m
      apply cancel
      · rw [m, Category.assoc]
      · rw [w1 Y, base Y]
    · intro Y y z e
      apply t.inj Y y z
      simp only [← Category.assoc, e]
    · intro Y g₁
      obtain ⟨π, ⟨hinj, -⟩, hπ⟩ := pushY Y
      rw [← hinj.eq_iff, map_pow, map_one, t.kernel Y (π g₁), hπ]
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨y, cancel _ _ (by rw [Category.assoc, hy]) ?_⟩
        rw [base Y y, w1 Y g₁]
      · rintro ⟨y, hy⟩
        exact ⟨y, by rw [← hy, Category.assoc]⟩

/- English proof (translation)
Introduce `R _ _ T _ Γ X x G _ G₀ _ ψ N h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `i t`. Establish `w : i ≫ G.hom = Γ.G.hom ≫ x` using `t.isOver`. Use `⟨h.1.lift i Γ.G.hom w, h.1.lift_fst _ _ _, ?_⟩` and prove the remaining obligations.

Establish `e` using `(tors_iff Γ N h (h.1.lift i Γ.G.hom w) (h.1.lift_snd _ _ _)).2`. Rewrite `e` using `[h.1.lift_fst]`. Conclude with `e t`. Introduce `i₀ t`. Establish `hi : i₀ ≫ G₀.hom = Γ.G.hom`.

Use `t.isOver` as an intermediate fact. Simplify using `using this`. Conclude with `(tors_iff Γ N h i₀ hi).1 t`.
-/
theorem isTorsionAlong_iff_of_isGrpPullback : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G] (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (N : ℕ), IsGrpPullback G₀ G x ψ → (∀ i : Γ.G.left ⟶ G.left, Γ.IsTorsionAlong G x N i → ∃ i₀ : Γ.G.left ⟶ G₀.left, i₀ ≫ ψ = i ∧ Γ.IsTorsionAlong G₀ (𝟙 _) N i₀) ∧ ∀ i₀ : Γ.G.left ⟶ G₀.left, Γ.IsTorsionAlong G₀ (𝟙 _) N i₀ → Γ.IsTorsionAlong G x N (i₀ ≫ ψ) := by
  intro R _ _ T _ Γ X x G _ G₀ _ ψ N h
  refine ⟨?_, ?_⟩
  · intro i t
    have w : i ≫ G.hom = Γ.G.hom ≫ x := t.isOver
    refine ⟨h.1.lift i Γ.G.hom w, h.1.lift_fst _ _ _, ?_⟩
    have e := (tors_iff Γ N h (h.1.lift i Γ.G.hom w) (h.1.lift_snd _ _ _)).2
    rw [h.1.lift_fst] at e
    exact e t
  · intro i₀ t
    have hi : i₀ ≫ G₀.hom = Γ.G.hom := by
      have := t.isOver
      simpa using this
    exact (tors_iff Γ N h i₀ hi).1 t

end PositivityTheory.UnitarySelfGeneration
