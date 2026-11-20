import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

/- English proof (translation)
Introduce `S I U A G ψ o hU hpb hcomp`. Set `p : (A ⊗ A).left ⟶ S` to `(A ⊗ A).hom`. Set `V : I → (A ⊗ A).left.Opens` to `fun i => p ⁻¹ᵁ U i`. Set `q : ∀ i, (V i).toScheme ⟶ (U i).toScheme` to `fun i => p ∣_ U i`. Establish `hP : ∀ i, IsPullback (V i).ι (q i) p (U i).ι` using `fun i => (isPullback_morphismRestrict p (U i)).flip`.

Set `T₀ : ∀ i, Over (U i).toScheme` to `fun i => Over.mk (q i)`. Set `r : ∀ i, Over.mk ((T₀ i).hom ≫ (U i).ι) ⟶ A ⊗ A` to `fun i => Over.homMk (V i).ι (hP i).w`. Establish `hx : ∀ i, ∃ x : T₀ i ⟶ G i, (r i ≫ fst A A).left = x.left ≫ ψ i` using `fun i => exists_lift (hpb i) _`. Establish `hy : ∀ i, ∃ y : T₀ i ⟶ G i, (r i ≫ snd A A).left = y.left ≫ ψ i` using `fun i => exists_lift (hpb i) _`. Use `choose x hx using hx`.

Use `choose y hy using hy`. Set `f : ∀ i, (V i).toScheme ⟶ A.left` to `fun i => (lift (x i) (y i) ≫ o i).left ≫ ψ i`. Establish `hf : ∀ i j (T : Scheme.{0}) (a : T ⟶ (V i).toScheme) (b : T ⟶ (V j).toScheme), a ≫ (V i).ι = b ≫ (V j).ι → a ≫ f i = b ≫ f j`. Introduce `i j T a b hab`. Set `ea : Over.mk (a ≫ q i) ⟶ T₀ i` to `Over.homMk a rfl`.

Set `eb : Over.mk (b ≫ q j) ⟶ T₀ j` to `Over.homMk b rfl`. Establish `key` using `hcomp i j T (a ≫ q i) (b ≫ q j) (ea ≫ x i) (ea ≫ y i) (eb ≫ x j) (eb ≫ y j) (by`. Simplify using `only [Over.comp_left, Category.assoc, ← hx, ea, eb, Over.homMk_left, r]`. Rewrite using `[← Category.assoc, hab, Category.assoc])`. Use the proof step `(by`.

Simplify using `only [Over.comp_left, Category.assoc, ← hy, ea, eb, Over.homMk_left, r]`. Rewrite using `[← Category.assoc, hab, Category.assoc])`. Rewrite `key` using `[← comp_lift, ← comp_lift]`. Simplify `key` using `only [f, ea, eb, Over.homMk_left, Over.comp_left, Category.assoc]`. Take `⟨F, hF, -⟩` from `existsUnique_hom (fun i => (V i).ι) (fun i => inferInstance) (covers hU hP) f hf`.

Establish `hFw : F ≫ A.hom = (A ⊗ A).hom`. Use `hom_ext (fun i => (V i).ι) (fun i => inferInstance) (covers hU hP) (fun i => ?_)` and prove the remaining obligations. Rewrite using `[reassoc_of% (hF i)]`. Simplify using `only [f, Category.assoc, (hpb i).w]`. Rewrite using `[← Category.assoc (lift (x i) (y i) ≫ o i).left, Over.w]`.

Conclude with `(hP i).w.symm`. Use `⟨Over.homMk F hFw, ?_⟩` and prove the remaining obligations. Introduce `i T x' y' x₀ y₀ hx₀ hy₀`. Establish `hg : (lift x₀ y₀).left ≫ p = T.hom ≫ (U i).ι` using `Over.w (lift x₀ y₀)`. Set `k : T.left ⟶ (V i).toScheme` to `(hP i).lift (lift x₀ y₀).left T.hom hg`.

Establish `hk₁ : k ≫ (V i).ι = (lift x₀ y₀).left` using `(hP i).lift_fst _ _ _`. Establish `hk₂ : k ≫ q i = T.hom` using `(hP i).lift_snd _ _ _`. Set `e : T ⟶ T₀ i` to `Over.homMk k hk₂`. Establish `ex : e ≫ x i = x'`. Apply `lift_ext (hpb i)` to reduce the goal to its premises.

Rewrite using `[Over.comp_left, Category.assoc, ← hx i, ← hx₀, Over.comp_left]`. Express the relevant statement in the definitionally equal form `k ≫ (V i).ι ≫ (fst A A).left = _`. Rewrite using `[reassoc_of% hk₁, ← Over.comp_left, lift_fst]`. Establish `ey : e ≫ y i = y'`. Apply `lift_ext (hpb i)` to reduce the goal to its premises.

Rewrite using `[Over.comp_left, Category.assoc, ← hy i, ← hy₀, Over.comp_left]`. Express the relevant statement in the definitionally equal form `k ≫ (V i).ι ≫ (snd A A).left = _`. Rewrite using `[reassoc_of% hk₁, ← Over.comp_left, lift_snd]`. Rewrite using `[← ex, ← ey, ← comp_lift, Category.assoc]`. Express the relevant statement in the definitionally equal form `(lift x₀ y₀).left ≫ F = (k ≫ (lift (x i) (y i) ≫ o i).left) ≫ ψ i`.

Rewrite using `[← hk₁, Category.assoc, hF i, Category.assoc]`.
-/
theorem exists_binary_op : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) (ψ : ∀ i, (G i).left ⟶ A.left) (o : ∀ i, G i ⊗ G i ⟶ G i), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (lift x y ≫ o i).left ≫ ψ i = (lift x' y' ≫ o j).left ≫ ψ j) → ∃ m : A ⊗ A ⟶ A, ∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (lift x y ≫ o i).left ≫ ψ i := by
  intro S I U A G ψ o hU hpb hcomp

  let p : (A ⊗ A).left ⟶ S := (A ⊗ A).hom
  let V : I → (A ⊗ A).left.Opens := fun i => p ⁻¹ᵁ U i
  let q : ∀ i, (V i).toScheme ⟶ (U i).toScheme := fun i => p ∣_ U i
  have hP : ∀ i, IsPullback (V i).ι (q i) p (U i).ι := fun i => (isPullback_morphismRestrict p (U i)).flip

  let T₀ : ∀ i, Over (U i).toScheme := fun i => Over.mk (q i)
  let r : ∀ i, Over.mk ((T₀ i).hom ≫ (U i).ι) ⟶ A ⊗ A := fun i =>
    Over.homMk (V i).ι (hP i).w

  have hx : ∀ i, ∃ x : T₀ i ⟶ G i, (r i ≫ fst A A).left = x.left ≫ ψ i := fun i =>
    exists_lift (hpb i) _
  have hy : ∀ i, ∃ y : T₀ i ⟶ G i, (r i ≫ snd A A).left = y.left ≫ ψ i := fun i =>
    exists_lift (hpb i) _
  choose x hx using hx
  choose y hy using hy

  let f : ∀ i, (V i).toScheme ⟶ A.left := fun i => (lift (x i) (y i) ≫ o i).left ≫ ψ i
  have hf : ∀ i j (T : Scheme.{0}) (a : T ⟶ (V i).toScheme) (b : T ⟶ (V j).toScheme),
      a ≫ (V i).ι = b ≫ (V j).ι → a ≫ f i = b ≫ f j := by
    intro i j T a b hab
    let ea : Over.mk (a ≫ q i) ⟶ T₀ i := Over.homMk a rfl
    let eb : Over.mk (b ≫ q j) ⟶ T₀ j := Over.homMk b rfl
    have key := hcomp i j T (a ≫ q i) (b ≫ q j) (ea ≫ x i) (ea ≫ y i) (eb ≫ x j) (eb ≫ y j)
      (by
        simp only [Over.comp_left, Category.assoc, ← hx, ea, eb, Over.homMk_left, r]
        rw [← Category.assoc, hab, Category.assoc])
      (by
        simp only [Over.comp_left, Category.assoc, ← hy, ea, eb, Over.homMk_left, r]
        rw [← Category.assoc, hab, Category.assoc])
    rw [← comp_lift, ← comp_lift] at key
    simpa only [f, ea, eb, Over.homMk_left, Over.comp_left, Category.assoc] using key
  obtain ⟨F, hF, -⟩ := existsUnique_hom (fun i => (V i).ι) (fun i => inferInstance)
    (covers hU hP) f hf

  have hFw : F ≫ A.hom = (A ⊗ A).hom := by
    refine hom_ext (fun i => (V i).ι) (fun i => inferInstance) (covers hU hP) (fun i => ?_)
    rw [reassoc_of% (hF i)]
    simp only [f, Category.assoc, (hpb i).w]
    rw [← Category.assoc (lift (x i) (y i) ≫ o i).left, Over.w]
    exact (hP i).w.symm
  refine ⟨Over.homMk F hFw, ?_⟩
  intro i T x' y' x₀ y₀ hx₀ hy₀
  have hg : (lift x₀ y₀).left ≫ p = T.hom ≫ (U i).ι := Over.w (lift x₀ y₀)
  let k : T.left ⟶ (V i).toScheme := (hP i).lift (lift x₀ y₀).left T.hom hg
  have hk₁ : k ≫ (V i).ι = (lift x₀ y₀).left := (hP i).lift_fst _ _ _
  have hk₂ : k ≫ q i = T.hom := (hP i).lift_snd _ _ _
  let e : T ⟶ T₀ i := Over.homMk k hk₂
  have ex : e ≫ x i = x' := by
    apply lift_ext (hpb i)
    rw [Over.comp_left, Category.assoc, ← hx i, ← hx₀, Over.comp_left]
    change k ≫ (V i).ι ≫ (fst A A).left = _
    rw [reassoc_of% hk₁, ← Over.comp_left, lift_fst]
  have ey : e ≫ y i = y' := by
    apply lift_ext (hpb i)
    rw [Over.comp_left, Category.assoc, ← hy i, ← hy₀, Over.comp_left]
    change k ≫ (V i).ι ≫ (snd A A).left = _
    rw [reassoc_of% hk₁, ← Over.comp_left, lift_snd]
  rw [← ex, ← ey, ← comp_lift, Category.assoc]
  change (lift x₀ y₀).left ≫ F = (k ≫ (lift (x i) (y i) ≫ o i).left) ≫ ψ i
  rw [← hk₁, Category.assoc, hF i, Category.assoc]

end GlobalTheory.CoverGlue
