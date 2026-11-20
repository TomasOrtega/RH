import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in

/- English proof (translation)
Introduce `S X e m n hl hinv hcomm hassoc`. Establish `hr : ∀ (T : Over S) (x : T ⟶ X), lift x (toUnit T ≫ e) ≫ m = x` using `fun T x => by`. Rewrite using `[hcomm, hl]`. Set `M : MonObj X` to `{ one := e mul := m one_mul := by`. Establish `: e ▷ X = lift (toUnit _ ≫ e) (snd _ _)`.

Apply `hom_ext` to reduce the goal to its premises. Simplify using `only [whiskerRight_fst, lift_fst]`. Rewrite using `[toUnit_unique (fst _ _) (toUnit _)]`. Simplify using `only [whiskerRight_snd, lift_snd]`. Rewrite using `[this, hl, leftUnitor_hom]`.

Use `mul_one := by`. Establish `: X ◁ e = lift (fst _ _) (toUnit _ ≫ e)`. Apply `hom_ext` to reduce the goal to its premises. Simplify using `only [whiskerLeft_fst, lift_fst]`. Simplify using `only [whiskerLeft_snd, lift_snd]`.

Rewrite using `[toUnit_unique (snd _ _) (toUnit _)]`. Rewrite using `[this, hr, rightUnitor_hom]`. Use `mul_assoc := by`. Establish `h1 : m ▷ X = lift (lift (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _) ≫ m) (snd _ _)`. Apply `hom_ext` to reduce the goal to its premises.

Simplify using `only [whiskerRight_fst, lift_fst]`. Rewrite using `[← comp_lift, lift_fst_snd, Category.comp_id]`. Simplify using `only [whiskerRight_snd, lift_snd]`. Establish `h2 : (α_ X X X).hom ≫ X ◁ m = lift (fst _ _ ≫ fst _ _) (lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ m)`. Apply `hom_ext` to reduce the goal to its premises.

Simplify using `only [Category.assoc, whiskerLeft_fst, associator_hom_fst, lift_fst]`. Simplify using `only [Category.assoc, whiskerLeft_snd, lift_snd]`. Establish `h3 : (α_ X X X).hom ≫ snd _ _ = lift (fst _ _ ≫ snd _ _) (snd _ _)`. Apply the tactic sequence `apply hom_ext <;>`. Simplify using `only [lift_fst, lift_snd, Category.assoc, associator_hom_snd_fst, associator_hom_snd_snd]`.

Rewrite using `[reassoc_of% h3]`. Rewrite using `[h1, reassoc_of% h2, hassoc] }`. Set `G : GrpObj X` to `{ inv := n left_inv := by show lift n (𝟙 X) ≫ m = toUnit X ≫ e`. Simplify using `using hinv X (𝟙 X)`. Use `right_inv := by show lift (𝟙 X) n ≫ m = toUnit X ≫ e`.

Rewrite using `[hcomm]`. Simplify using `using hinv X (𝟙 X) }`. Use `⟨G, rfl, rfl, rfl, ⟨?_⟩⟩` and prove the remaining obligations. Establish `: (β_ X X).hom = lift (snd _ _) (fst _ _)`. Apply the tactic sequence `apply hom_ext <;> simp only [braiding_hom_fst, braiding_hom_snd, lift_fst, lift_snd]`.

Rewrite using `[this]`. Use `show lift (snd X X) (fst X X) ≫ m = m`. Rewrite using `[hcomm, lift_fst_snd, Category.id_comp]`.
-/
theorem _root_.GlobalTheory.exists_grpObj_over_of_points : ∀ (S : Scheme.{0}) (X : Over S) (e : 𝟙_ _ ⟶ X) (m : X ⊗ X ⟶ X) (n : X ⟶ X), (∀ (T : Over S) (x : T ⟶ X), lift (toUnit T ≫ e) x ≫ m = x) → (∀ (T : Over S) (x : T ⟶ X), lift (x ≫ n) x ≫ m = toUnit T ≫ e) → (∀ (T : Over S) (x y : T ⟶ X), lift x y ≫ m = lift y x ≫ m) → (∀ (T : Over S) (x y z : T ⟶ X), lift (lift x y ≫ m) z ≫ m = lift x (lift y z ≫ m) ≫ m) → ∃ G : GrpObj X, η[X] = e ∧ μ[X] = m ∧ (GrpObj.inv : X ⟶ X) = n ∧ IsCommMonObj X := by
  intro S X e m n hl hinv hcomm hassoc
  have hr : ∀ (T : Over S) (x : T ⟶ X), lift x (toUnit T ≫ e) ≫ m = x := fun T x => by
    rw [hcomm, hl]
  let M : MonObj X :=
    { one := e
      mul := m
      one_mul := by
        have : e ▷ X = lift (toUnit _ ≫ e) (snd _ _) := by
          apply hom_ext
          · simp only [whiskerRight_fst, lift_fst]
            rw [toUnit_unique (fst _ _) (toUnit _)]
          · simp only [whiskerRight_snd, lift_snd]
        rw [this, hl, leftUnitor_hom]
      mul_one := by
        have : X ◁ e = lift (fst _ _) (toUnit _ ≫ e) := by
          apply hom_ext
          · simp only [whiskerLeft_fst, lift_fst]
          · simp only [whiskerLeft_snd, lift_snd]
            rw [toUnit_unique (snd _ _) (toUnit _)]
        rw [this, hr, rightUnitor_hom]
      mul_assoc := by
        have h1 : m ▷ X = lift (lift (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _) ≫ m) (snd _ _) := by
          apply hom_ext
          · simp only [whiskerRight_fst, lift_fst]
            rw [← comp_lift, lift_fst_snd, Category.comp_id]
          · simp only [whiskerRight_snd, lift_snd]
        have h2 : (α_ X X X).hom ≫ X ◁ m =
            lift (fst _ _ ≫ fst _ _) (lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ m) := by
          apply hom_ext
          · simp only [Category.assoc, whiskerLeft_fst, associator_hom_fst, lift_fst]
          · simp only [Category.assoc, whiskerLeft_snd, lift_snd]
            have h3 : (α_ X X X).hom ≫ snd _ _ = lift (fst _ _ ≫ snd _ _) (snd _ _) := by
              apply hom_ext <;>
                simp only [lift_fst, lift_snd, Category.assoc, associator_hom_snd_fst,
                  associator_hom_snd_snd]
            rw [reassoc_of% h3]
        rw [h1, reassoc_of% h2, hassoc] }
  let G : GrpObj X :=
    { inv := n
      left_inv := by
        show lift n (𝟙 X) ≫ m = toUnit X ≫ e
        simpa using hinv X (𝟙 X)
      right_inv := by
        show lift (𝟙 X) n ≫ m = toUnit X ≫ e
        rw [hcomm]
        simpa using hinv X (𝟙 X) }
  refine ⟨G, rfl, rfl, rfl, ⟨?_⟩⟩
  have : (β_ X X).hom = lift (snd _ _) (fst _ _) := by
    apply hom_ext <;> simp only [braiding_hom_fst, braiding_hom_snd, lift_fst, lift_snd]
  rw [this]
  show lift (snd X X) (fst X X) ≫ m = m
  rw [hcomm, lift_fst_snd, Category.id_comp]

end GlobalTheory
