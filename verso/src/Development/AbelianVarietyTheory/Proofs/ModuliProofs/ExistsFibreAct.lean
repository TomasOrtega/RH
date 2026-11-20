import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

namespace GlobalTheory.FibreAct

/- English proof (translation)
Use `haveI : IsIso ψ.left := inferInstanceAs (IsIso ((Over.forget S).map ψ))`. Use `⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩` and prove the remaining obligations. Set `U : Over.mk (T.hom ≫ 𝟙 S) ⟶ T` to `Over.homMk (𝟙 T.left) (by simp)`. Establish `ex : x₀ = U ≫ x ≫ ψ` using `Over.OverMorphism.ext (hx.trans (Category.id_comp _).symm)`. Establish `ey : y₀ = U ≫ y ≫ ψ` using `Over.OverMorphism.ext (hy.trans (Category.id_comp _).symm)`.

Rewrite using `[ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]`. Conclude with `Category.id_comp _`.
-/
theorem isGrpPullback_of_iso {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (ψ : G' ⟶ G) [IsIso ψ]
    [IsMonHom ψ] : IsGrpPullback G' G (𝟙 S) ψ.left := by
  haveI : IsIso ψ.left := inferInstanceAs (IsIso ((Over.forget S).map ψ))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let U : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = U ≫ x ≫ ψ := Over.OverMorphism.ext (hx.trans (Category.id_comp _).symm)
  have ey : y₀ = U ≫ y ≫ ψ := Over.OverMorphism.ext (hy.trans (Category.id_comp _).symm)
  rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
  exact Category.id_comp _

/- English proof (translation)
Establish `w : ∀ c, (φ ≫ (a.act c).left) ≫ G.hom = G'.hom ≫ f` using `fun c => by`. Rewrite using `[Category.assoc, Over.w, h.1.w]`. Set `r : O → (G' ⟶ G')` to `fun c => Over.homMk (h.1.lift (φ ≫ (a.act c).left) G'.hom (w c)) (h.1.lift_snd _ _ _)`. Establish `hr : ∀ c, (r c).left ≫ φ = φ ≫ (a.act c).left` using `fun c => h.1.lift_fst _ _ _`. Establish `key : ∀ T : Over S', ∃ e : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G), ∀ x c, e (x ≫ r c) = e x ≫ a.act c` using `fun T => by`.

Take `⟨e, he⟩` from `GlobalTheory.LiePull.exists_pushEquiv h T _ rfl`. Conclude with `⟨e, fun x c => Over.OverMorphism.ext (by`. Rewrite using `[he, Over.comp_left, Over.comp_left, he, Category.assoc, hr, Category.assoc])⟩`. Take `⟨e, he⟩` from `key G'`. Establish `he' : ∀ c, e (r c) = e (𝟙 G') ≫ a.act c` using `fun c => by rw [← he, Category.id_comp]`.

Use `⟨⟨r, fun c => ?_, e.injective ?_, fun c d => e.injective ?_, fun c d => e.injective ?_⟩, hr⟩` and prove the remaining obligations. Use `haveI := a.hom c`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨e₁, he₁⟩` from `key (𝟙_ (Over S'))`. Establish `o : η[G'] = (1 : 𝟙_ (Over S') ⟶ G')` using `by rw [Hom.one_def]; simp`.

Apply `e₁.injective` to reduce the goal to its premises. Rewrite using `[he₁, o, map_one, MonObj.one_comp]`. Take `⟨e₂, he₂⟩` from `key (G' ⊗ G')`. Establish `m₁ : μ[G'] = fst G' G' * snd G' G'` using `by rw [Hom.mul_def]; simp`. Establish `m₂ : (r c ⊗ₘ r c) ≫ μ[G'] = (fst G' G' ≫ r c) * (snd G' G' ≫ r c)`.

Rewrite using `[Hom.mul_def]`. Use `congr 1`. Apply `e₂.injective` to reduce the goal to its premises. Rewrite using `[m₂, he₂, m₁, map_mul, map_mul, he₂, he₂, MonObj.mul_comp]`. Rewrite using `[he', a.one, Category.comp_id]`.

Rewrite using `[he, he', he', a.mul, Category.assoc]`. Rewrite using `[map_mul, he', he', he', a.add, MonObj.comp_mul]`.
-/
theorem exists_lift_act {O : Type} [CommRing O] {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : OAct O G) :
    ∃ a' : OAct O G', ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left := by
  have w : ∀ c, (φ ≫ (a.act c).left) ≫ G.hom = G'.hom ≫ f := fun c => by
    rw [Category.assoc, Over.w, h.1.w]
  let r : O → (G' ⟶ G') := fun c => Over.homMk (h.1.lift (φ ≫ (a.act c).left) G'.hom (w c)) (h.1.lift_snd _ _ _)
  have hr : ∀ c, (r c).left ≫ φ = φ ≫ (a.act c).left := fun c => h.1.lift_fst _ _ _
  have key : ∀ T : Over S', ∃ e : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G),
      ∀ x c, e (x ≫ r c) = e x ≫ a.act c := fun T => by
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h T _ rfl
    exact ⟨e, fun x c => Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hr, Category.assoc])⟩
  obtain ⟨e, he⟩ := key G'
  have he' : ∀ c, e (r c) = e (𝟙 G') ≫ a.act c := fun c => by rw [← he, Category.id_comp]
  refine ⟨⟨r, fun c => ?_, e.injective ?_, fun c d => e.injective ?_, fun c d => e.injective ?_⟩, hr⟩
  · haveI := a.hom c
    refine ⟨?_, ?_⟩
    · obtain ⟨e₁, he₁⟩ := key (𝟙_ (Over S'))
      have o : η[G'] = (1 : 𝟙_ (Over S') ⟶ G') := by rw [Hom.one_def]; simp
      apply e₁.injective
      rw [he₁, o, map_one, MonObj.one_comp]
    · obtain ⟨e₂, he₂⟩ := key (G' ⊗ G')
      have m₁ : μ[G'] = fst G' G' * snd G' G' := by rw [Hom.mul_def]; simp
      have m₂ : (r c ⊗ₘ r c) ≫ μ[G'] = (fst G' G' ≫ r c) * (snd G' G' ≫ r c) := by
        rw [Hom.mul_def]; congr 1
      apply e₂.injective
      rw [m₂, he₂, m₁, map_mul, map_mul, he₂, he₂, MonObj.mul_comp]
  · rw [he', a.one, Category.comp_id]
  · rw [he, he', he', a.mul, Category.assoc]
  · rw [map_mul, he', he', he', a.add, MonObj.comp_mul]

/- English proof (translation)
Introduce `E _ _ _ H D g k J a bas o _ b ρ S s t τ x β A₀ _ m hP hx hm`. Take `⟨φ, hφ, -, -, hd⟩` from `hP`. Use `haveI := hφ`. Establish `hi : IsGrpPullback t.A τ.G (𝟙 S) φ.inv.left` using `isGrpPullback_of_iso φ.inv`. Take `⟨act, hact⟩` from `exists_lift_act hi τ.act`.

Take `⟨act₀, hact₀⟩` from `exists_lift_act hm act`. Use `⟨act, act₀, hact₀, fun σ => ?_⟩` and prove the remaining obligations. Establish `L : ∀ n, LieMult act₀ (𝟙 _) σ n ↔ LieMult τ.act x σ n` using `fun n => by`. Rewrite using `[GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hm hact₀ ℂ (𝟙 _) σ n, GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hi hact ℂ _ σ n, Category.id_comp, Category.comp_id]`. Rewrite using `[L, L]`.

Conclude with `(hd ℂ x β hx).1 σ`.
-/
theorem exists_fibre_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H S) (x : Sp ℂ ⟶ S) (β : o →+* ℂ) (A₀ : Over (Sp ℂ)) [GrpObj A₀] (m : A₀.left ⟶ t.A.left), IsPEL D a bas ρ t τ → x ≫ s = spMap β → IsGrpPullback A₀ t.A x m → ∃ (act : OAct (𝓞 E) t.A) (act₀ : OAct (𝓞 E) A₀), (∀ c, (act₀.act c).left ≫ m = m ≫ (act.act c).left) ∧ DetCond D act₀ (𝟙 _) (β ρ) := by
  intro E _ _ _ H D g k J a bas o _ b ρ S s t τ x β A₀ _ m hP hx hm
  obtain ⟨φ, hφ, -, -, hd⟩ := hP
  haveI := hφ
  have hi : IsGrpPullback t.A τ.G (𝟙 S) φ.inv.left := isGrpPullback_of_iso φ.inv
  obtain ⟨act, hact⟩ := exists_lift_act hi τ.act
  obtain ⟨act₀, hact₀⟩ := exists_lift_act hm act
  refine ⟨act, act₀, hact₀, fun σ => ?_⟩
  have L : ∀ n, LieMult act₀ (𝟙 _) σ n ↔ LieMult τ.act x σ n := fun n => by
    rw [GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hm hact₀ ℂ (𝟙 _) σ n,
      GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hi hact ℂ _ σ n, Category.id_comp, Category.comp_id]
  rw [L, L]
  exact (hd ℂ x β hx).1 σ

end GlobalTheory.FibreAct
