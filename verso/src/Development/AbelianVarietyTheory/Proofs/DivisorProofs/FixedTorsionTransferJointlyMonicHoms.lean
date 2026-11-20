import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TorsionTransfer

/- English proof (translation)
Substitute using the available equality. Rewrite the conclusion using the stated equalities.
-/
theorem pow_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (x' : Over.mk b ⟶ G) (hx : x.left = x'.left) (m : ℕ) :
    (x ^ m).left = (x' ^ m).left := by
  subst h
  rw [Over.OverMorphism.ext hx]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Establish an intermediate fact.

Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fixed_of_jointlyMonic : ∀ (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (io : V →+* W) (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∀ (G : Over (Sp V)) [GrpObj G] (H : Over (Sp W)) [GrpObj H] (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), (∀ k, IsMonHom (r k)) → (∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y) → ∀ σ : F ≃+* F, (∀ w : W, σ (algebraMap (FractionRing W) F (algebraMap W _ w)) = algebraMap (FractionRing W) F (algebraMap W _ w)) → ∀ m : ℕ, (∀ y : TF (R := V) F ⟶ G, y ^ m = 1 → spMap σ.toRingHom ≫ y.left = y.left) → ∀ x : TF (R := W) F ⟶ H, x ^ m = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro V W _ _ _ _ io F _ _ _ hF G _ H _ r hr hmono σ hσ m hfix x hx
  have hT : spMap σ.toRingHom ≫ (TF (R := W) F).hom = (TF (R := W) F).hom := by
    show Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    congr 1
    ext w
    exact hσ w
  have hV : (TF (R := W) F).hom ≫ spMap io = (TF (R := V) F).hom := by
    show (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    congr 1
    ext v
    exact hF v
  have hpb := isGrpPullback_pullback G (spMap io)
  let x' : TF (R := W) F ⟶ H := Over.homMk (spMap σ.toRingHom ≫ x.left) (by
    rw [Category.assoc, Over.w x]; exact hT)
  have key : ∀ k, x' ≫ r k = x ≫ r k := by
    intro k
    have hk := hr k
    let z := x ≫ r k
    have hs : z.left ≫ pullback.snd G.hom (spMap io) = (TF (R := W) F).hom := Over.w z
    let y : TF (R := V) F ⟶ G := Over.homMk (z.left ≫ pullback.fst G.hom (spMap io)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hs]; exact hV)
    let ρ : (TF (R := W) F ⟶ H) →* (TF (R := W) F ⟶ (Over.pullback (spMap io)).obj G) :=
      MonoidHom.mk' (fun u => u ≫ r k) fun u v => MonObj.mul_comp u v (r k)
    have hzm : z ^ m = 1 := by
      have e := map_pow ρ x m
      rw [hx, map_one] at e
      exact e.symm
    have hym : y ^ m = 1 := by
      apply Over.OverMorphism.ext
      have e1 := pow_left_congr hV.symm y (pushHom hpb _ z) rfl m
      rw [← map_pow, hzm, map_one] at e1
      have e0 := pow_left_congr hV.symm y (pushHom hpb _ z) rfl 0
      simp only [pow_zero] at e0
      rw [e1, e0]
    have hfy := hfix y hym
    apply Over.OverMorphism.ext
    show (spMap σ.toRingHom ≫ x.left) ≫ (r k).left = x.left ≫ (r k).left
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      exact hfy
    · rw [Category.assoc, Category.assoc]
      change spMap σ.toRingHom ≫ z.left ≫ _ = z.left ≫ _
      rw [hs, hT]
  exact congrArg (fun u => u.left) (hmono _ x' x key)

end GlobalTheory.TorsionTransfer
