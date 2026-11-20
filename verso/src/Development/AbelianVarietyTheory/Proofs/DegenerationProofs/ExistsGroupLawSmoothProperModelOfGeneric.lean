import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

open SpreadAb (grpObj_of_dominant isPullback_square)

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ X f A _ _ φ h _ _`. Take `⟨a₁, ha₁, H₁⟩` from `exists_hom (pullback.fst f f ≫ f) f (isPullback_square h) ((μ[A]).left ≫ φ) (by`. Rewrite using `[(isPullback_square h).w, Category.assoc, h.w, Over.w_assoc]`. Use the proof step `rfl)`. Take `⟨a₂, ha₂, H₂⟩` from `exists_hom f f h ((ι[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc])`.

Take `⟨a₃, ha₃, H₃⟩` from `exists_hom (𝟙 _) f (IsPullback.id_vert (spMap (algebraMap R K))) ((η[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc]; simp)`. Use `⟨a₁ * a₂ * a₃, mul_ne_zero (mul_ne_zero ha₁ ha₂) ha₃, fun R' _ g hg ψ hψ hψg G π φ' hG hφ₁ hφ₂ => ?_⟩` and prove the remaining obligations. Rewrite `hg` using `[map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff]`. Take `⟨⟨u₁, u₂⟩, u₃⟩` from `hg`. Establish `hc : spMap ψ ≫ spMap g = spMap (algebraMap R K)`.

Rewrite using `[← hψg, ← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hφ : IsPullback φ' A.hom G.hom (spMap ψ)` using `IsPullback.of_right (by rwa [hφ₁, hc]) hφ₂ hG`. Use `ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom ψ) hψ` as an intermediate fact. Establish `: Flat G.hom` using `MorphismProperty.of_isPullback (P := @Flat) hG inferInstance`.

Establish `: IsSeparated G.hom` using `MorphismProperty.of_isPullback (P := @IsSeparated) hG inferInstance`. Take `⟨m, hm₁, hm₂⟩` from `H₁ R' g u₁ _ _ _ (isPullback_square hG).w`. Take `⟨i, hi₁, hi₂⟩` from `H₂ R' g u₂ _ _ _ hG.w`. Take `⟨e, he₁, he₂⟩` from `H₃ R' g u₃ _ (spMap g) (𝟙 _) (by simp)`. Establish `L : ∀ (Y : Over (Sp R')) (u : Y.left ⟶ X), u ≫ f = Y.hom ≫ spMap g → ∃ v : Y ⟶ G, v.left ≫ π = u` using `fun Y u w => ⟨Over.homMk (hG.lift u Y.hom w) (hG.lift_snd _ _ _), hG.lift_fst _ _ _⟩`.

Take `⟨m', hm'⟩` from `L (G ⊗ G) m (hm₁.trans (isPullback_square hG).w)`. Take `⟨i', hi'⟩` from `L G i (hi₁.trans hG.w)`. Take `⟨e', he'⟩` from `L (𝟙_ _) e (he₁.trans ((Category.comp_id _).trans (Category.id_comp _).symm))`. Conclude with `grpObj_of_dominant (spMap ψ) G A φ' hφ m' i' e' (fun φ₂ ⟨k₁, k₂⟩ => by`. Apply `hG.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, Category.assoc, hφ₁, hm']`. Use `hm₂ φ₂ (pullback.hom_ext ?_ ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.lift_fst, pullback.lift_fst, ← hφ₁]`. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) k₁).trans (Category.assoc _ _ _))`. Rewrite using `[Category.assoc, pullback.lift_snd, pullback.lift_snd, ← hφ₁]`.

Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) k₂).trans (Category.assoc _ _ _))`. Rewrite using `[Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc, ← Over.w (fst G G), reassoc_of% k₁, hφ₂, Over.w_assoc])`. Use the proof step `(by`. Apply `hG.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, hφ₁, hi']`.

Conclude with `hi₂ φ' hφ₁`. Rewrite using `[Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc])`. Use the proof step `(by`. Apply `hG.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, hφ₁, he']`.

Conclude with `he₂ _ hc`. Rewrite using `[Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc]`. Conclude with `(Category.comp_id _).trans (Category.id_comp _).symm)`.
-/
theorem exists_grpObj : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{0}) (f : X ⟶ Sp R) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ X), IsPullback φ A.hom f (spMap (algebraMap R K)) → Smooth f → IsProper f → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (ψ : R' →+* K), Function.Injective ψ → ψ.comp g = algebraMap R K → ∀ (G' : Over (Sp R')) (π : G'.left ⟶ X) (φ' : A.left ⟶ G'.left), IsPullback π G'.hom f (spMap g) → φ' ≫ π = φ → φ' ≫ G'.hom = A.hom ≫ spMap ψ → ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback A G' (spMap ψ) φ' := by
  intro R K _ _ _ _ _ _ X f A _ _ φ h _ _
  obtain ⟨a₁, ha₁, H₁⟩ := exists_hom (pullback.fst f f ≫ f) f (isPullback_square h) ((μ[A]).left ≫ φ) (by
    rw [(isPullback_square h).w, Category.assoc, h.w, Over.w_assoc]
    rfl)
  obtain ⟨a₂, ha₂, H₂⟩ := exists_hom f f h ((ι[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc])
  obtain ⟨a₃, ha₃, H₃⟩ := exists_hom (𝟙 _) f (IsPullback.id_vert (spMap (algebraMap R K)))
    ((η[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc]; simp)
  refine ⟨a₁ * a₂ * a₃, mul_ne_zero (mul_ne_zero ha₁ ha₂) ha₃,
    fun R' _ g hg ψ hψ hψg G π φ' hG hφ₁ hφ₂ => ?_⟩
  rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at hg
  obtain ⟨⟨u₁, u₂⟩, u₃⟩ := hg
  have hc : spMap ψ ≫ spMap g = spMap (algebraMap R K) := by
    rw [← hψg, ← Spec.map_comp]; rfl
  have hφ : IsPullback φ' A.hom G.hom (spMap ψ) := IsPullback.of_right (by rwa [hφ₁, hc]) hφ₂ hG
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom ψ) hψ
  have : Flat G.hom := MorphismProperty.of_isPullback (P := @Flat) hG inferInstance
  have : IsSeparated G.hom := MorphismProperty.of_isPullback (P := @IsSeparated) hG inferInstance
  obtain ⟨m, hm₁, hm₂⟩ := H₁ R' g u₁ _ _ _ (isPullback_square hG).w
  obtain ⟨i, hi₁, hi₂⟩ := H₂ R' g u₂ _ _ _ hG.w
  obtain ⟨e, he₁, he₂⟩ := H₃ R' g u₃ _ (spMap g) (𝟙 _) (by simp)
  have L : ∀ (Y : Over (Sp R')) (u : Y.left ⟶ X), u ≫ f = Y.hom ≫ spMap g → ∃ v : Y ⟶ G, v.left ≫ π = u :=
    fun Y u w => ⟨Over.homMk (hG.lift u Y.hom w) (hG.lift_snd _ _ _), hG.lift_fst _ _ _⟩
  obtain ⟨m', hm'⟩ := L (G ⊗ G) m (hm₁.trans (isPullback_square hG).w)
  obtain ⟨i', hi'⟩ := L G i (hi₁.trans hG.w)
  obtain ⟨e', he'⟩ := L (𝟙_ _) e (he₁.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  exact grpObj_of_dominant (spMap ψ) G A φ' hφ m' i' e'
    (fun φ₂ ⟨k₁, k₂⟩ => by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, hm']
        refine hm₂ φ₂ (pullback.hom_ext ?_ ?_)
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← hφ₁]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) k₁).trans (Category.assoc _ _ _))
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← hφ₁]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) k₂).trans (Category.assoc _ _ _))
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc, ← Over.w (fst G G), reassoc_of% k₁, hφ₂,
          Over.w_assoc])
    (by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, hi']
        exact hi₂ φ' hφ₁
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc])
    (by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, he']
        exact he₂ _ hc
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc]
        exact (Category.comp_id _).trans (Category.id_comp _).symm)

end GlobalTheory.GenSpread
