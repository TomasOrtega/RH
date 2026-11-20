import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfProper
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChart
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FibreAbDim

/- English proof (translation)
Take `⟨ρ, hρ⟩` from `GlobalTheory.HeckePoint.exists_ptsEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl`. Take `⟨σ, hσ⟩` from `GlobalTheory.HeckePoint.exists_ptsEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _)`. Establish `h1 : η[G'].left ≫ φ = (1 : Over.mk x ⟶ t.G).left`. Use `hσ 1` as an intermediate fact. Rewrite `this` using `[map_one]`.

Rewrite using `[this]`. Use `congr 2`. Establish `tan : ∀ w : epsR R ⟶ G', IsTangent w ↔ IsTanAtG t x (ρ w).left`. Introduce `w`. Prove the components needed by the constructor for the conclusion.

Introduce `hw`. Use `⟨Over.w (ρ w), ?_⟩` and prove the remaining obligations. Rewrite using `[hρ, ← Category.assoc, hw, h1]`. Introduce `hw`. Apply `h.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, ← hρ, hw.2, h1]`. Rewrite using `[Category.assoc, Over.w w, Over.w η[G']] show spMap _ ≫ spMap _ = 𝟙 _`. Unfold `spMap`. Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`.

Set `v' : Fin n → (epsR R ⟶ G')` to `fun a => ρ.symm (Over.homMk (v a) (hv a).1)`. Establish `hv' : ∀ a, (v' a).left ≫ φ = v a` using `fun a => by`. Rewrite using `[← hρ]`. Simplify using `[v']`. Establish `comb : ∀ (c : Fin n → R) (w : epsR R ⟶ G'), IsLieComb c v' w ↔ IsCombAtG t x v c (ρ w).left`.

Introduce `c w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Use `⟨fun i => ρ (u i), fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hρ, hu, Category.assoc, hv']`.

Both sides reduce to the same expression. Rewrite using `[map_list_prod, List.map_ofFn]`. Both sides reduce to the same expression. Introduce and unpack `⟨u, hu, e⟩`. Use `⟨fun i => ρ.symm (u i), fun i => ?_, ?_⟩` and prove the remaining obligations.

Apply `h.1.hom_ext` to reduce the goal to its premises. Rewrite using `[← hρ, MulEquiv.apply_symm_apply, hu, Category.assoc, hv']`. Both sides reduce to the same expression. Rewrite using `[Category.assoc, Over.w, Over.w] show spMap _ = spMap _ ≫ spMap _`. Unfold `spMap`.

Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Apply the tactic sequence `ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]`. Apply `ρ.injective` to reduce the goal to its premises. Rewrite using `[map_list_prod, List.map_ofFn]`.

Use `(Over.OverMorphism.ext ?_)` and prove the remaining obligations. Rewrite using `[← e]`. Use `congr 3`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Use `⟨v', fun a => (tan _).2 ?_, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[hρ, hv']`. Conclude with `hv a`. Simplify `hb _ ((tan w).1 hw)` using `only [comb]`.
-/
theorem exists_isLieBasis_of_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X) {G' : Over (Sp R)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G x φ) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left))
    (hv : ∀ a, IsTanAtG t x (v a))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf : Fin n → R, IsCombAtG t x v cf w) :
    ∃ v' : Fin n → (epsR R ⟶ G'), IsLieBasis v' := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.HeckePoint.exists_ptsEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  obtain ⟨σ, hσ⟩ := GlobalTheory.HeckePoint.exists_ptsEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _)
  have h1 : η[G'].left ≫ φ = (1 : Over.mk x ⟶ t.G).left := by
    have := hσ 1
    rw [map_one] at this
    rw [this]
    congr 2
  have tan : ∀ w : epsR R ⟶ G', IsTangent w ↔ IsTanAtG t x (ρ w).left := by
    intro w
    constructor
    · intro hw
      refine ⟨Over.w (ρ w), ?_⟩
      rw [hρ, ← Category.assoc, hw, h1]
    · intro hw
      apply h.1.hom_ext
      · rw [Category.assoc, ← hρ, hw.2, h1]
      · rw [Category.assoc, Over.w w, Over.w η[G']]
        show spMap _ ≫ spMap _ = 𝟙 _
        unfold spMap
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
  let v' : Fin n → (epsR R ⟶ G') := fun a => ρ.symm (Over.homMk (v a) (hv a).1)
  have hv' : ∀ a, (v' a).left ≫ φ = v a := fun a => by
    rw [← hρ]
    simp [v']
  have comb : ∀ (c : Fin n → R) (w : epsR R ⟶ G'), IsLieComb c v' w ↔ IsCombAtG t x v c (ρ w).left := by
    intro c w
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun i => ρ (u i), fun i => ?_, ?_⟩
      · rw [hρ, hu, Category.assoc, hv']
        rfl
      · rw [map_list_prod, List.map_ofFn]
        rfl
    · rintro ⟨u, hu, e⟩
      refine ⟨fun i => ρ.symm (u i), fun i => ?_, ?_⟩
      · apply h.1.hom_ext
        · rw [← hρ, MulEquiv.apply_symm_apply, hu, Category.assoc, hv']
          rfl
        · rw [Category.assoc, Over.w, Over.w]
          show spMap _ = spMap _ ≫ spMap _
          unfold spMap
          rw [← Spec.map_comp]
          congr 1
          ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
      · apply ρ.injective
        rw [map_list_prod, List.map_ofFn]
        refine (Over.OverMorphism.ext ?_)
        rw [← e]
        congr 3
        funext i
        simp
  refine ⟨v', fun a => (tan _).2 ?_, fun w hw => ?_⟩
  · rw [hρ, hv']
    exact hv a
  · simpa only [comb] using hb _ ((tan w).1 hw)

/- English proof (translation)
Introduce `E _ _ _ H X t hp U n v hv hb m hm A _ j hj`. Establish `hG` using `GlobalTheory.HeckePoint.isAbelianScheme_of_proper t hp`. Establish `hA` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hj`. Use `⟨hA, ?_⟩` and prove the remaining obligations. Establish `h₀` using `isGrpPullback_pullback t.G (chart U)`.

Establish `hG'` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG h₀`. Take `⟨v', hv'⟩` from `exists_isLieBasis_of_frame t (chart U) h₀ v hv hb`. Establish `w : j ≫ t.G.hom = (A.hom ≫ spMap (Ideal.Quotient.mk m)) ≫ chart U`. Rewrite using `[hj.1.w, Category.assoc]`. Establish `h₁` using `IsGrpPullback.cancel h₀ (hj.congr rfl (h₀.1.lift_fst _ _ w).symm) (h₀.1.lift_snd _ _ w)`.

Use `hG'.comm` as an intermediate fact. Use `hA.comm` as an intermediate fact. Use `hG.comm` as an intermediate fact. Take `⟨v₁, hv₁, -⟩` from `GlobalTheory.exists_isLieBasis_baseChange _ _ _ _ A _ h₁ hG'.smooth n v' hv'`. Establish `: IsLocalRing (Γ(X, U.1) ⧸ m)`.

Use `letI := Ideal.Quotient.field m`. Use `infer_instance`. Take `⟨g, hg⟩` from `GlobalTheory.AbelianDim.exists_relDim _ A hA`. Take `⟨v₂, hv₂⟩` from `GlobalTheory.KeyPow.exists_isLieBasis A hg`. Rewrite using `[GlobalTheory.KeyFramePoint.card_eq_of_isLieBasis hj hv₁ hv₂]`.

Conclude with `hg`.
-/
theorem isAbelianScheme_and_relDim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (j : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) j → IsAbelianScheme A ∧ SmoothOfRelativeDimension n A.hom := by
  intro E _ _ _ H X t hp U n v hv hb m hm A _ j hj
  have hG := GlobalTheory.HeckePoint.isAbelianScheme_of_proper t hp
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hj
  refine ⟨hA, ?_⟩
  have h₀ := isGrpPullback_pullback t.G (chart U)
  have hG' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG h₀
  obtain ⟨v', hv'⟩ := exists_isLieBasis_of_frame t (chart U) h₀ v hv hb
  have w : j ≫ t.G.hom = (A.hom ≫ spMap (Ideal.Quotient.mk m)) ≫ chart U := by
    rw [hj.1.w, Category.assoc]
  have h₁ := IsGrpPullback.cancel h₀ (hj.congr rfl (h₀.1.lift_fst _ _ w).symm) (h₀.1.lift_snd _ _ w)
  have := hG'.comm
  have := hA.comm
  have := hG.comm
  obtain ⟨v₁, hv₁, -⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ _ _ A _ h₁ hG'.smooth n v' hv'
  have : IsLocalRing (Γ(X, U.1) ⧸ m) := by
    letI := Ideal.Quotient.field m
    infer_instance
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim _ A hA
  obtain ⟨v₂, hv₂⟩ := GlobalTheory.KeyPow.exists_isLieBasis A hg
  rw [GlobalTheory.KeyFramePoint.card_eq_of_isLieBasis hj hv₁ hv₂]
  exact hg

end GlobalTheory.FibreAbDim
