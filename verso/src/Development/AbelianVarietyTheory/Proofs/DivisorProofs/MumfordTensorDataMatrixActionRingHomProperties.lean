import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TensAct

section General

variable {S : Scheme.{0}} {X Y Z G : Over S}

def preHom [GrpObj G] [IsCommMonObj G] (f : X ⟶ Y) : (Y ⟶ G) →* (X ⟶ G) where
  toFun g := f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' := fun g h => MonObj.comp_mul f g h

/- English proof (translation)
Use `show preHom f (∏ j, g j ^ n j) = ∏ j, (preHom f (g j)) ^ n j`. Rewrite using `[map_prod]`. Simplify using `only [map_zpow]`.
-/
theorem comp_prod_zpow [GrpObj G] [IsCommMonObj G] (f : X ⟶ Y) {K : Type} [Fintype K] (g : K → (Y ⟶ G)) (n : K → ℤ) :
    f ≫ (∏ j, g j ^ n j) = ∏ j, (f ≫ g j) ^ n j := by
  show preHom f (∏ j, g j ^ n j) = ∏ j, (preHom f (g j)) ^ n j
  rw [map_prod]
  simp only [map_zpow]

end General

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

/- English proof (translation)
The claim follows from `T.lim.hom_ext fun ⟨i⟩ => h i`.
-/
theorem hom_ext (T : Tens D D' W) {X} {f g : X ⟶ D'.P.A} (h : ∀ i, f ≫ T.pr i = g ≫ T.pr i) : f = g :=
  T.lim.hom_ext fun ⟨i⟩ => h i

/- English proof (translation)
Rewrite using `[Tens.act_pr, comp_prod_zpow]`.
-/
theorem comp_act_pr (T : Tens D D' W) {X} (f : X ⟶ D'.P.A) (a : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    f ≫ T.act a ≫ T.pr i = ∏ j, (f ≫ T.pr j) ^ a i j := by
  rw [Tens.act_pr, comp_prod_zpow]

/- English proof (translation)
Use `haveI := T.pr_hom`. Establish `h1 : ∀ {X} , (1 : X ⟶ D'.P.A) ≫ T.act a = 1`. Introduce `X`. Use `hom_ext T fun i => ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, comp_act_pr]`.

Simplify using `[MonObj.one_comp]`. Establish `h2 : ∀ {X} (f g : X ⟶ D'.P.A), (f * g) ≫ T.act a = (f ≫ T.act a) * (g ≫ T.act a)`. Introduce `X f g`. Use `hom_ext T fun i => ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, comp_act_pr, MonObj.mul_comp, Category.assoc, Category.assoc, comp_act_pr, comp_act_pr, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[MonObj.mul_comp, mul_zpow]`. Prove the components needed by the constructor for the conclusion. Use `h1 (X := 𝟙_ _)` as an intermediate fact. Simplify `this` using `[Hom.one_def]`.

Use `h2 (fst _ _) (snd _ _)` as an intermediate fact. Rewrite `this` using `[Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp]`. Rewrite using `[this]`. Use `congr 1`.
-/
theorem act_isMonHom (T : Tens D D' W) (a : Matrix (Fin r) (Fin r) ℤ) : IsMonHom (T.act a) := by
  haveI := T.pr_hom
  have h1 : ∀ {X} , (1 : X ⟶ D'.P.A) ≫ T.act a = 1 := by
    intro X
    refine hom_ext T fun i => ?_
    rw [Category.assoc, comp_act_pr]
    simp [MonObj.one_comp]
  have h2 : ∀ {X} (f g : X ⟶ D'.P.A), (f * g) ≫ T.act a = (f ≫ T.act a) * (g ≫ T.act a) := by
    intro X f g
    refine hom_ext T fun i => ?_
    rw [Category.assoc, comp_act_pr, MonObj.mul_comp, Category.assoc, Category.assoc, comp_act_pr, comp_act_pr,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [MonObj.mul_comp, mul_zpow]
  constructor
  · have := h1 (X := 𝟙_ _)
    simpa [Hom.one_def] using this
  · have := h2 (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this]
    congr 1

/- English proof (translation)
Use `hom_ext T fun i => ?_` and prove the remaining obligations. Rewrite using `[Tens.act_pr, Category.id_comp, Finset.prod_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Rewrite using `[Matrix.one_apply_ne hj.symm, zpow_zero]`.

Simplify using the standard rewrite rules.
-/
theorem act_one (T : Tens D D' W) : T.act 1 = 𝟙 _ := by
  refine hom_ext T fun i => ?_
  rw [Tens.act_pr, Category.id_comp, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    rw [Matrix.one_apply_ne hj.symm, zpow_zero]
  · simp

/- English proof (translation)
Use `hom_ext T fun i => ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, comp_act_pr, Tens.act_pr]`. Simplify using `only [Tens.act_pr, ← Finset.prod_zpow, ← zpow_mul, Matrix.mul_apply]`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Establish `: ∀ (s : Finset (Fin r)) (n : Fin r → ℤ), T.pr k ^ (∑ j ∈ s, n j) = ∏ j ∈ s, T.pr k ^ n j`. Introduce `s n`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]`.

Rewrite using `[this]`. Simplify using `only [mul_comm]`.
-/
theorem act_mul (T : Tens D D' W) (a b : Matrix (Fin r) (Fin r) ℤ) : T.act (a * b) = T.act b ≫ T.act a := by
  refine hom_ext T fun i => ?_
  rw [Category.assoc, comp_act_pr, Tens.act_pr]
  simp only [Tens.act_pr, ← Finset.prod_zpow, ← zpow_mul, Matrix.mul_apply]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  have : ∀ (s : Finset (Fin r)) (n : Fin r → ℤ), T.pr k ^ (∑ j ∈ s, n j) = ∏ j ∈ s, T.pr k ^ n j := by
    intro s n
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]
  rw [this]
  simp only [mul_comm]

/- English proof (translation)
Use `haveI := T.pr_hom`. Use `show _ = T.act a * T.act b`. Use `hom_ext T fun i => ?_` and prove the remaining obligations. Rewrite using `[MonObj.mul_comp]`. Simplify using `only [Tens.act_pr, Matrix.add_apply, zpow_add, Finset.prod_mul_distrib]`.
-/
theorem act_add (T : Tens D D' W) (a b : Matrix (Fin r) (Fin r) ℤ) :
    T.act (a + b) = padd D'.P.A (T.act a) (T.act b) := by
  haveI := T.pr_hom
  show _ = T.act a * T.act b
  refine hom_ext T fun i => ?_
  rw [MonObj.mul_comp]
  simp only [Tens.act_pr, Matrix.add_apply, zpow_add, Finset.prod_mul_distrib]

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ T` and use `⟨act_isMonHom T, act_one T, act_mul T, act_add T⟩`.
-/
theorem act_ring : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), (∀ a, IsMonHom (T.act a)) ∧ T.act 1 = 𝟙 _ ∧ (∀ a b, T.act (a * b) = T.act b ≫ T.act a) ∧
      ∀ a b, T.act (a + b) = padd D'.P.A (T.act a) (T.act b) :=
  fun _ _ _ _ _ _ _ T => ⟨act_isMonHom T, act_one T, act_mul T, act_add T⟩

end GlobalTheory.Mum.TensAct
