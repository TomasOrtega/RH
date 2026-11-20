import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.ArcInf

section General
variable {k : Type} [CommRing k] {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C] [Algebra k C]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algOverHom_left (ψ : A →ₐ[k] B) : (algOverHom ψ).left = spMap (ψ : A →+* B) := rfl

/- English proof (translation)
Use `ext1`. Rewrite using `[Over.comp_left, algOverHom_left, algOverHom_left, algOverHom_left]`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Both sides reduce to the same expression.
-/
theorem algOverHom_comp (ψ : A →ₐ[k] B) (χ : B →ₐ[k] C) :
    algOverHom (χ.comp ψ) = algOverHom χ ≫ algOverHom ψ := by
  ext1
  rw [Over.comp_left, algOverHom_left, algOverHom_left, algOverHom_left]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/- English proof (translation)
Use `ext1`. Rewrite using `[algOverHom_left]`. Conclude with `Spec.map_id _`.
-/
theorem algOverHom_id : algOverHom (AlgHom.id k A) = 𝟙 _ := by
  ext1
  rw [algOverHom_left]
  exact Spec.map_id _

/- English proof (translation)
Introduce `a b h`. Establish `h1 : spMap (a : A →+* B) = spMap (b : A →+* B)` using `congrArg (fun x => x.left) h`. Establish `h2` using `Spec.map_injective h1`. Conclude with `AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h2)`.
-/
theorem algOverHom_injective : Function.Injective (algOverHom : (A →ₐ[k] B) → _) := by
  intro a b h
  have h1 : spMap (a : A →+* B) = spMap (b : A →+* B) := congrArg (fun x => x.left) h
  have h2 := Spec.map_injective h1
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h2)

/- English proof (translation)
Introduce `φ`. Take `⟨g, hg⟩` from `Spec.map_surjective φ.left`. Establish `hw : φ.left ≫ spMap (algebraMap k A) = spMap (algebraMap k B)` using `Over.w φ`. Rewrite `hw` using `[← hg, ← Spec.map_comp]`. Establish `h2` using `congrArg CommRingCat.Hom.hom (Spec.map_injective hw)`.

Use `⟨⟨g.hom, fun c => congrArg (fun f : k →+* B => f c) h2⟩, ?_⟩` and prove the remaining obligations. Use `ext1`. Conclude with `hg`.
-/
theorem algOverHom_surjective : Function.Surjective (algOverHom : (A →ₐ[k] B) → _) := by
  intro φ
  obtain ⟨g, hg⟩ := Spec.map_surjective φ.left
  have hw : φ.left ≫ spMap (algebraMap k A) = spMap (algebraMap k B) := Over.w φ
  rw [← hg, ← Spec.map_comp] at hw
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective hw)
  refine ⟨⟨g.hom, fun c => congrArg (fun f : k →+* B => f c) h2⟩, ?_⟩
  ext1
  exact hg

/- English proof (translation)
Apply `algOverHom_injective` to reduce the goal to its premises. Use `ext1`. Use `congrArg (fun x => x.left) h` as an intermediate fact. Simplify using `only [Over.comp_left] at this`. Conclude with `(cancel_mono j.left).1 this`.
-/
theorem eq_of_comp_eq {G : Over (Sp k)} {j : algOver k A ⟶ G} (hj : IsOpenImmersion j.left) {a b : A →ₐ[k] B}
    (h : algOverHom a ≫ j = algOverHom b ≫ j) : a = b := by
  apply algOverHom_injective
  ext1
  have := congrArg (fun x => x.left) h
  simp only [Over.comp_left] at this
  exact (cancel_mono j.left).1 this

end General

variable {k : Type} [Field k]

/- English proof (translation)
Establish `hu : ∀ y : nonZeroDivisors (PowerSeries k), IsUnit (ρ y)`. Introduce and unpack `⟨y, hy⟩`. Establish `h0 : y ≠ 0` using `nonZeroDivisors.ne_zero hy`. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.associated_pow_irreducible h0 (PowerSeries.X_irreducible (R := k))`. Take `⟨u, hu⟩` from `hn.symm`.

Use `show IsUnit (ρ y)`. Rewrite using `[← hu, map_mul, map_pow]`. Conclude with `(h.pow n).mul (u.isUnit.map ρ)`. Conclude with `⟨IsLocalization.liftAlgHom (S := FractionRing (PowerSeries k)) hu, fun x => by simp⟩`.
-/
theorem exists_lift {F : Type} [CommRing F] [Algebra k F] (ρ : PowerSeries k →ₐ[k] F)
    (h : IsUnit (ρ PowerSeries.X)) :
    ∃ σ : FractionRing (PowerSeries k) →ₐ[k] F, ∀ x, σ (algebraMap (PowerSeries k) _ x) = ρ x := by
  have hu : ∀ y : nonZeroDivisors (PowerSeries k), IsUnit (ρ y) := by
    rintro ⟨y, hy⟩
    have h0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 (PowerSeries.X_irreducible (R := k))
    obtain ⟨u, hu⟩ := hn.symm
    show IsUnit (ρ y)
    rw [← hu, map_mul, map_pow]
    exact (h.pow n).mul (u.isUnit.map ρ)
  exact ⟨IsLocalization.liftAlgHom (S := FractionRing (PowerSeries k)) hu, fun x => by simp⟩

def IsChart (G : Over (Sp k)) [GrpObj G] {A : Type} [CommRing A] [Algebra k A] (j : algOver k A ⟶ G)
    (ε : A →ₐ[k] k) {r : ℕ} (f : Fin r → A) : Prop :=
  IsOpenImmersion j.left ∧ algOverHom ε ≫ j = 1 ∧ Algebra.adjoin k (Set.range f) = ⊤ ∧ ∀ i, ε (f i) = 0

def TwoVar {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] (j : algOver k A ⟶ G)
    {r : ℕ} (f : Fin r → A) (a : algOver k (FractionRing (PowerSeries k)) ⟶ G)
    (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k) : Prop :=
  ∀ (F : Type) [Field F] [Algebra k F] (τ : MvPowerSeries (Fin 2) k →ₐ[k] F)
    (σ₀ σ₁ : FractionRing (PowerSeries k) →ₐ[k] F), τ d ≠ 0 →
    (∀ x : PowerSeries k, σ₀ (algebraMap _ _ x) = τ (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k))) →
    (∀ x : PowerSeries k, σ₁ (algebraMap _ _ x) = τ (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))) →
    ∃ χ : A →ₐ[k] F, (∀ i, χ (f i) * τ d = τ (h i)) ∧
      algOverHom σ₁ ≫ a = (algOverHom χ ≫ j) * (algOverHom σ₀ ≫ a)

/- English proof (translation)
The claim follows from `AlgHom.ext_of_adjoin_eq_top hc.2.2.1 (by rintro _ ⟨i, rfl⟩; exact h i)`.
-/
theorem IsChart.hom_ext {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] {j : algOver k A ⟶ G}
    {ε : A →ₐ[k] k} {r : ℕ} {f : Fin r → A} (hc : IsChart G j ε f) {B : Type} [CommRing B] [Algebra k B]
    {a b : A →ₐ[k] B} (h : ∀ i, a (f i) = b (f i)) : a = b :=
  AlgHom.ext_of_adjoin_eq_top hc.2.2.1 (by rintro _ ⟨i, rfl⟩; exact h i)

end GlobalTheory.SS.ArcInf
end
