import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivPull

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isPullback_fst_snd {S : Scheme.{0}} (A T : Over S) :
    IsPullback (fst A T).left (snd A T).left A.hom T.hom := by
  rw [Over.fst_left, Over.snd_left]
  exact IsPullback.of_hasPullback A.hom T.hom

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem isPullback_whisker {S : Scheme.{0}} (A T : Over S) {B : Scheme.{0}} (b : B ⟶ T.left) :
    IsPullback (A ◁ (Over.homMk b rfl : Over.mk (b ≫ T.hom) ⟶ T)).left
      (snd A (Over.mk (b ≫ T.hom))).left (snd A T).left b := by
  have h1 := isPullback_fst_snd A T
  have h2 := isPullback_fst_snd A (Over.mk (b ≫ T.hom))
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, CartesianMonoidalCategory.whiskerLeft_fst]
    exact h2
  · rw [← Over.comp_left, CartesianMonoidalCategory.whiskerLeft_snd, Over.comp_left]
    rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities.
-/
theorem pull_iso_eq_zero_iff {X Y : Scheme.{0}} (θ : Y ≅ X) (c : Pic X) :
    CechPic.pull θ.hom c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have h' := congrArg (CechPic.pull θ.inv) h
    rwa [← pull_comp, θ.inv_hom_id, pull_id, map_zero] at h'
  · intro h
    rw [h, map_zero]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Chain the equalities or inequalities of the calculation. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem triv_pull_iff {S : Scheme.{0}} (A Y Z : Over S) (N : LB (A ⊗ Y).left) (hN : N.IsLB) (i : Z ⟶ Y)
    (h : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A N i) (T : Over S) (y : T ⟶ Y) {B : Scheme.{0}} (b : B ⟶ T.left) :
    Triv ((ev N (fst A T) (snd A T ≫ y)).pull (pullback.fst (snd A T).left b)) ↔
      ∃ z : B ⟶ Z.left, z ≫ i.left = b ≫ y.left := by
  obtain ⟨-, h2⟩ := h
  obtain ⟨g, hg⟩ : ∃ g : Over.mk (b ≫ T.hom) ⟶ T, g = Over.homMk b rfl := ⟨_, rfl⟩
  have hW := isPullback_whisker A T b
  rw [← hg] at hW
  have hθ : hW.isoPullback.hom ≫ pullback.fst (snd A T).left b = (A ◁ g).left :=
    hW.isoPullback_hom_fst
  have hlift : lift (fst A (Over.mk (b ≫ T.hom))) (snd A (Over.mk (b ≫ T.hom)) ≫ g ≫ y) =
      (A ◁ g) ≫ lift (fst A T) (snd A T ≫ y) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hF := pull_isLB hN (lift (fst A T) (snd A T ≫ y)).left
  have hP := pull_isLB hF (pullback.fst (snd A T).left b)
  have hE := pull_isLB hN (lift (fst A (Over.mk (b ≫ T.hom))) (snd A (Over.mk (b ≫ T.hom)) ≫ g ≫ y)).left
  have e3 : cls _ hE = CechPic.pull hW.isoPullback.hom (cls _ hP) := by
    rw [cls_pull hN _ hE, cls_pull hF _ hP, cls_pull hN _ hF, ← pull_comp, ← pull_comp,
      hlift, Over.comp_left, hθ]
  have hg' : g.left = b := by
    rw [hg]
    rfl
  calc Triv ((ev N (fst A T) (snd A T ≫ y)).pull (pullback.fst (snd A T).left b))
      ↔ cls _ hP = 0 := (cls_eq_zero_iff hP).symm
    _ ↔ CechPic.pull hW.isoPullback.hom (cls _ hP) = 0 := (pull_iso_eq_zero_iff _ _).symm
    _ ↔ cls _ hE = 0 := by rw [e3]
    _ ↔ Triv (ev N (fst A (Over.mk (b ≫ T.hom))) (snd A (Over.mk (b ≫ T.hom)) ≫ g ≫ y)) :=
      cls_eq_zero_iff hE
    _ ↔ ∃ z, z ≫ i = g ≫ y := h2 _ _
    _ ↔ ∃ z : B ⟶ Z.left, z ≫ i.left = b ≫ y.left := by
      constructor
      · rintro ⟨z, hz⟩
        refine ⟨z.left, ?_⟩
        have hz' : (z ≫ i).left = (g ≫ y).left := by rw [hz]
        rw [Over.comp_left, Over.comp_left, hg'] at hz'
        exact hz'
      · rintro ⟨z, hz⟩
        have hzw : z ≫ Z.hom = (Over.mk (b ≫ T.hom)).hom := by
          show z ≫ Z.hom = b ≫ T.hom
          rw [← Over.w i, ← Category.assoc, hz, Category.assoc, Over.w y]
        refine ⟨Over.homMk z hzw, ?_⟩
        apply Over.OverMorphism.ext
        rw [Over.comp_left, Over.comp_left, hg']
        exact hz

end GlobalTheory.CompanionTheory.TrivPull
