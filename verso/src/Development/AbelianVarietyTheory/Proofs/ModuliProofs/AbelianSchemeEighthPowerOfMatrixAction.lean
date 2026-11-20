import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentation
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.MatrixPower

section General

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

@[reducible] def retractGrpObj {G A : C} [GrpObj G] (i : A ⟶ G) (r : G ⟶ A) (hir : i ≫ r = 𝟙 A)
    [he : IsMonHom (r ≫ i)] : GrpObj A :=
  haveI : Mono i := (SplitMono.mk r hir).mono
  have h1 : ∀ {T : C}, ((1 : T ⟶ G) ≫ r) ≫ i = 1 := fun {T} => by
    rw [Category.assoc, MonObj.one_comp]
  have h2 : ∀ {T : C} (a b : T ⟶ A), ((a ≫ i * b ≫ i) ≫ r) ≫ i = a ≫ i * b ≫ i := fun a b => by
    rw [Category.assoc, MonObj.mul_comp]; simp [reassoc_of% hir]
  have h3 : (i⁻¹ ≫ r) ≫ i = i⁻¹ := by
    rw [Category.assoc, GrpObj.inv_comp]; simp [reassoc_of% hir]
  { one := (1 : 𝟙_ C ⟶ G) ≫ r
    mul := (fst A A ≫ i * snd A A ≫ i) ≫ r
    inv := i⁻¹ ≫ r
    one_mul := by
      rw [← cancel_mono i, Category.assoc, h2, MonObj.comp_mul, whiskerRight_fst_assoc,
        whiskerRight_snd_assoc, h1]
      simp [leftUnitor_hom]
    mul_one := by
      rw [← cancel_mono i, Category.assoc, h2, MonObj.comp_mul, whiskerLeft_fst_assoc,
        whiskerLeft_snd_assoc, h1]
      simp [rightUnitor_hom]
    mul_assoc := by
      rw [← cancel_mono i, Category.assoc, h2, Category.assoc, Category.assoc, h2,
        MonObj.comp_mul, whiskerRight_fst_assoc, whiskerRight_snd_assoc, h2,
        MonObj.comp_mul (A ◁ _), whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, h2]
      simp [MonObj.comp_mul, _root_.mul_assoc]
    left_inv := by
      rw [← cancel_mono i, Category.assoc, h2, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
        h3, Category.assoc, h1]
      simp
    right_inv := by
      rw [← cancel_mono i, Category.assoc, h2, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
        h3, Category.assoc, h1]
      simp }

/- English proof (translation)
The claim follows from `{ one_hom := by rw [MonObj.one_eq_one M, MonObj.one_eq_one N, h1] mul_hom := by rw [MonObj.mul_eq_mul M, MonObj.mul_eq_mul N, h2, MonObj.comp_mul, tensorHom_fst, tensorHom_snd] }`.
-/
private theorem isMonHom_of_one_comp_of_mul_comp {M N : C} [MonObj M] [MonObj N] (f : M ⟶ N)
    (h1 : (1 : 𝟙_ C ⟶ M) ≫ f = 1)
    (h2 : (fst M M * snd M M) ≫ f = fst M M ≫ f * snd M M ≫ f) : IsMonHom f :=
  { one_hom := by rw [MonObj.one_eq_one M, MonObj.one_eq_one N, h1]
    mul_hom := by
      rw [MonObj.mul_eq_mul M, MonObj.mul_eq_mul N, h2, MonObj.comp_mul, tensorHom_fst,
        tensorHom_snd] }

/- English proof (translation)
Set `gA : GrpObj A` to `retractGrpObj i r hir`. Establish `hm : ∀ {T : C} (a b : T ⟶ A), a * b = (a ≫ i * b ≫ i) ≫ r`. Introduce `T a b`. Rewrite using `[Hom.mul_def]`. Express the relevant statement in the definitionally equal form `lift a b ≫ (fst A A ≫ i * snd A A ≫ i) ≫ r = _`.

Rewrite using `[← Category.assoc, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]`. Establish `ho : ∀ {T : C}, (1 : T ⟶ A) = (1 : T ⟶ G) ≫ r`. Introduce `T`. Rewrite using `[Hom.one_def]`. Express the relevant statement in the definitionally equal form `toUnit T ≫ (1 : 𝟙_ C ⟶ G) ≫ r = _`.

Rewrite using `[← Category.assoc, MonObj.comp_one]`. Use `⟨gA, ?_, ?_⟩` and prove the remaining obligations. Use `isMonHom_of_one_comp_of_mul_comp i ?_ ?_` and prove the remaining obligations. Rewrite using `[ho, Category.assoc, MonObj.one_comp]`. Rewrite using `[hm, Category.assoc, MonObj.mul_comp]`.

Simplify using `only [Category.assoc, reassoc_of% hir]`. Use `isMonHom_of_one_comp_of_mul_comp r ho.symm ?_` and prove the remaining obligations. Rewrite using `[hm]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Category.assoc, hir, Category.comp_id]`.

Use `_ = _ := by rw [MonObj.mul_comp]; simp only [Category.assoc]`.
-/
theorem exists_grpObj_retract {G A : C} [GrpObj G] (i : A ⟶ G) (r : G ⟶ A) (hir : i ≫ r = 𝟙 A)
    [he : IsMonHom (r ≫ i)] : ∃ _ : GrpObj A, IsMonHom i ∧ IsMonHom r := by
  let gA : GrpObj A := retractGrpObj i r hir
  have hm : ∀ {T : C} (a b : T ⟶ A), a * b = (a ≫ i * b ≫ i) ≫ r := by
    intro T a b
    rw [Hom.mul_def]
    change lift a b ≫ (fst A A ≫ i * snd A A ≫ i) ≫ r = _
    rw [← Category.assoc, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  have ho : ∀ {T : C}, (1 : T ⟶ A) = (1 : T ⟶ G) ≫ r := by
    intro T
    rw [Hom.one_def]
    change toUnit T ≫ (1 : 𝟙_ C ⟶ G) ≫ r = _
    rw [← Category.assoc, MonObj.comp_one]
  refine ⟨gA, ?_, ?_⟩
  · refine isMonHom_of_one_comp_of_mul_comp i ?_ ?_
    · rw [ho, Category.assoc, MonObj.one_comp]
    · rw [hm, Category.assoc, MonObj.mul_comp]
      simp only [Category.assoc, reassoc_of% hir]
  · refine isMonHom_of_one_comp_of_mul_comp r ho.symm ?_
    rw [hm]
    calc (fst G G * snd G G) ≫ r = ((fst G G * snd G G) ≫ (r ≫ i)) ≫ r := by
          simp only [Category.assoc, hir, Category.comp_id]
      _ = _ := by rw [MonObj.mul_comp]; simp only [Category.assoc]

variable [BraidedCategory C]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp only [Finset.prod_empty, MonObj.comp_one]`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]`.
-/
theorem comp_prod {n : Type*} (s : Finset n) {T X G : C} [GrpObj G] [IsCommMonObj G]
    (f : T ⟶ X) (g : n → (X ⟶ G)) : f ≫ ∏ u ∈ s, g u = ∏ u ∈ s, f ≫ g u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, MonObj.comp_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp only [Finset.prod_empty, MonObj.one_comp]`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]`.
-/
theorem prod_comp {n : Type*} (s : Finset n) {T G H : C} [GrpObj G] [IsCommMonObj G]
    [GrpObj H] [IsCommMonObj H] (g : n → (T ⟶ G)) (f : G ⟶ H) [IsMonHom f] :
    (∏ u ∈ s, g u) ≫ f = ∏ u ∈ s, g u ≫ f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, MonObj.one_comp]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

/- English proof (translation)
Establish `: ∀ m, IsMonHom (ρ m)` using `hρ`. Establish `hc : ∀ a b : Matrix n n ℤ, ρ a ≫ ρ b = ρ (b * a)` using `fun a b => (hmul b a).symm`. Establish `h0 : ρ 0 = 1`. Establish `h` using `hadd 0 0`. Rewrite `h` using `[add_zero]`.

Conclude with `mul_eq_left.mp h.symm`. Establish `hneg : ∀ a, ρ (-a) = (ρ a)⁻¹` using `fun a => eq_inv_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])`. Establish `hsum : ∀ (s : Finset n) (f : n → Matrix n n ℤ), ρ (∑ v ∈ s, f v) = ∏ v ∈ s, ρ (f v)`. Introduce `s f`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => rw [Finset.sum_empty, Finset.prod_empty, h0]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]`. Establish `hzs : ∀ (k : ℤ) (a : Matrix n n ℤ), ρ (k • a) = ρ a ^ k`. Introduce `k a`. Use `Int.induction_on k ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[zero_smul, h0, zpow_zero]`. Introduce `j ih`. Rewrite using `[add_smul, one_smul, hadd, ih, zpow_add_one]`. Introduce `j ih`. Rewrite using `[sub_smul, one_smul, sub_eq_add_neg, hadd, ih, hneg, zpow_sub_one]`.

Establish `hidem : ρ (Matrix.single o o 1) ≫ ρ (Matrix.single o o 1) = ρ (Matrix.single o o 1) ≫ 𝟙 G`. Rewrite using `[Category.comp_id, hc, Matrix.single_mul_single_same, _root_.mul_one]`. Choose the witnesses or unpack the hypotheses as in `⟨A, i, r, hir, hri⟩ : ∃ (A : C) (i : A ⟶ G) (r : G ⟶ A), i ≫ r = 𝟙 A ∧ r ≫ i = ρ (Matrix.single o o 1) := by`. Use `⟨equalizer (ρ (Matrix.single o o 1)) (𝟙 G), equalizer.ι _ _, equalizer.lift _ hidem, ?_, equalizer.lift_ι _ _⟩` and prove the remaining obligations. Apply `equalizer.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, equalizer.lift_ι, Category.id_comp]`. Conclude with `(equalizer.condition _ _).trans (Category.comp_id _)`. Establish `hmono : Mono i` using `(SplitMono.mk r hir).mono`. Establish `: IsMonHom (r ≫ i)` using `by rw [hri]; infer_instance`. Take `⟨gA, hi, hr⟩` from `exists_grpObj_retract i r hir`.

Establish `hcA : IsCommMonObj A` using `(isCommMonObj_iff_isMulCommutative _).2 fun X => ⟨⟨fun a b => by show a * b = b * a`. Rewrite using `[← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]⟩⟩`. Use `⟨A, gA, hcA, ⟨i, r, hir⟩, fun u => ρ (Matrix.single o u 1) ≫ r, fun u => inferInstance, ?_, ?_⟩` and prove the remaining obligations. Introduce `T y`. Use `⟨∏ v, y v ≫ i ≫ ρ (Matrix.single v o 1), fun u => ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[prod_comp, Finset.prod_eq_single u]`. Establish `h3 : ρ (Matrix.single u o 1) ≫ ρ (Matrix.single o u 1) ≫ r = r ≫ i ≫ r`. Rewrite using `[← Category.assoc, hc, Matrix.single_mul_single_same, _root_.mul_one, ← hri, Category.assoc]`. Simplify using `only [Category.assoc]`.

Rewrite using `[h3, reassoc_of% hir, hir, Category.comp_id]`. Introduce `v _ hv`. Establish `h3 : ρ (Matrix.single v o 1) ≫ ρ (Matrix.single o u 1) ≫ r = 1`. Establish `h5 : Matrix.single o u (1 : ℤ) * Matrix.single v o 1 = 0`. Simplify using `[Ne.symm hv]`.

Rewrite using `[← Category.assoc, hc, h5, h0, MonObj.one_comp]`. Simplify using `only [Category.assoc]`. Rewrite using `[h3, MonObj.comp_one, MonObj.comp_one]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ u) h`.

Simplify using `only at hx`. Establish `h1 : (1 : Matrix n n ℤ) = ∑ v, Matrix.single v v 1`. Use extensionality with `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[Matrix.sum_apply, Matrix.single_apply]`. Rewrite using `[Matrix.sum_apply, Finset.sum_eq_zero]`. Conclude with `Matrix.one_apply_ne hab`. Introduce `v _`. Rewrite using `[Matrix.single_apply]`.

Use `split_ifs with h`. Conclude with `absurd (h.1.symm.trans h.2) hab`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[← hx v]`. Establish `h4 : ρ (Matrix.single o v 1) ≫ r ≫ i ≫ ρ (Matrix.single v o 1) = ρ (Matrix.single v v 1)`. Rewrite using `[reassoc_of% hri, hc, Matrix.single_mul_single_same, hc, Matrix.single_mul_single_same]`. Simplify using `only [_root_.mul_one]`. Simplify using `only [Category.assoc, h4]`.

Introduce `m u dsimp only`. Establish `hrow : Matrix.single o u (1 : ℤ) * m = ∑ v, m u v • Matrix.single o v 1`. Use extensionality with `a b`. Distinguish the cases in `ha : a = o`. Substitute `ha` using the available equality.

Simplify using `[Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply]`. Simplify using `[Matrix.mul_apply, Matrix.sum_apply, Ne.symm ha]`. Use `hcA` as an intermediate fact. Rewrite using `[← Category.assoc, hc, hrow, hsum, prod_comp]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[hzs, GrpObj.zpow_comp]`.
-/
theorem exists_power [HasEqualizers C] {n : Type*} [Fintype n] [DecidableEq n] (o : n)
    (G : C) [GrpObj G] [IsCommMonObj G] (ρ : Matrix n n ℤ → (G ⟶ G))
    (hρ : ∀ m, IsMonHom (ρ m)) (hmul : ∀ m m', ρ (m * m') = ρ m' ≫ ρ m)
    (hadd : ∀ m m', ρ (m + m') = ρ m * ρ m') (hone : ρ 1 = 𝟙 G) :
    ∃ (A : C) (_ : GrpObj A) (_ : IsCommMonObj A) (_ : Retract A G) (pr : n → (G ⟶ A)),
      (∀ u, IsMonHom (pr u)) ∧
      (∀ (T : C) (y : n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) ∧
      ∀ m u, ρ m ≫ pr u = ∏ v, pr v ^ m u v := by
  have : ∀ m, IsMonHom (ρ m) := hρ
  have hc : ∀ a b : Matrix n n ℤ, ρ a ≫ ρ b = ρ (b * a) := fun a b => (hmul b a).symm
  have h0 : ρ 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hneg : ∀ a, ρ (-a) = (ρ a)⁻¹ := fun a =>
    eq_inv_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
  have hsum : ∀ (s : Finset n) (f : n → Matrix n n ℤ), ρ (∑ v ∈ s, f v) = ∏ v ∈ s, ρ (f v) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty, h0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]
  have hzs : ∀ (k : ℤ) (a : Matrix n n ℤ), ρ (k • a) = ρ a ^ k := by
    intro k a
    refine Int.induction_on k ?_ ?_ ?_
    · rw [zero_smul, h0, zpow_zero]
    · intro j ih
      rw [add_smul, one_smul, hadd, ih, zpow_add_one]
    · intro j ih
      rw [sub_smul, one_smul, sub_eq_add_neg, hadd, ih, hneg, zpow_sub_one]
  have hidem : ρ (Matrix.single o o 1) ≫ ρ (Matrix.single o o 1) =
      ρ (Matrix.single o o 1) ≫ 𝟙 G := by
    rw [Category.comp_id, hc, Matrix.single_mul_single_same, _root_.mul_one]
  obtain ⟨A, i, r, hir, hri⟩ : ∃ (A : C) (i : A ⟶ G) (r : G ⟶ A),
      i ≫ r = 𝟙 A ∧ r ≫ i = ρ (Matrix.single o o 1) := by
    refine ⟨equalizer (ρ (Matrix.single o o 1)) (𝟙 G), equalizer.ι _ _, equalizer.lift _ hidem,
      ?_, equalizer.lift_ι _ _⟩
    apply equalizer.hom_ext
    rw [Category.assoc, equalizer.lift_ι, Category.id_comp]
    exact (equalizer.condition _ _).trans (Category.comp_id _)
  have hmono : Mono i := (SplitMono.mk r hir).mono
  have : IsMonHom (r ≫ i) := by rw [hri]; infer_instance
  obtain ⟨gA, hi, hr⟩ := exists_grpObj_retract i r hir
  have hcA : IsCommMonObj A :=
    (isCommMonObj_iff_isMulCommutative _).2 fun X => ⟨⟨fun a b => by
      show a * b = b * a
      rw [← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]⟩⟩
  refine ⟨A, gA, hcA, ⟨i, r, hir⟩,
    fun u => ρ (Matrix.single o u 1) ≫ r, fun u => inferInstance, ?_, ?_⟩
  · intro T y
    refine ⟨∏ v, y v ≫ i ≫ ρ (Matrix.single v o 1), fun u => ?_, fun x hx => ?_⟩
    · dsimp only
      rw [prod_comp, Finset.prod_eq_single u]
      · have h3 : ρ (Matrix.single u o 1) ≫ ρ (Matrix.single o u 1) ≫ r = r ≫ i ≫ r := by
          rw [← Category.assoc, hc, Matrix.single_mul_single_same, _root_.mul_one, ← hri,
            Category.assoc]
        simp only [Category.assoc]
        rw [h3, reassoc_of% hir, hir, Category.comp_id]
      · intro v _ hv
        have h3 : ρ (Matrix.single v o 1) ≫ ρ (Matrix.single o u 1) ≫ r = 1 := by
          have h5 : Matrix.single o u (1 : ℤ) * Matrix.single v o 1 = 0 := by
            simp [Ne.symm hv]
          rw [← Category.assoc, hc, h5, h0, MonObj.one_comp]
        simp only [Category.assoc]
        rw [h3, MonObj.comp_one, MonObj.comp_one]
      · intro h
        exact absurd (Finset.mem_univ u) h
    · dsimp only at hx
      have h1 : (1 : Matrix n n ℤ) = ∑ v, Matrix.single v v 1 := by
        ext a b
        by_cases hab : a = b
        · subst hab
          simp [Matrix.sum_apply, Matrix.single_apply]
        · rw [Matrix.sum_apply, Finset.sum_eq_zero]
          · exact Matrix.one_apply_ne hab
          · intro v _
            rw [Matrix.single_apply]
            split_ifs with h
            · exact absurd (h.1.symm.trans h.2) hab
            · rfl
      calc x = x ≫ ρ 1 := by rw [hone, Category.comp_id]
        _ = ∏ v, x ≫ ρ (Matrix.single v v 1) := by rw [h1, hsum, comp_prod]
        _ = _ := by
          refine Finset.prod_congr rfl fun v _ => ?_
          rw [← hx v]
          have h4 : ρ (Matrix.single o v 1) ≫ r ≫ i ≫ ρ (Matrix.single v o 1) =
              ρ (Matrix.single v v 1) := by
            rw [reassoc_of% hri, hc, Matrix.single_mul_single_same, hc,
              Matrix.single_mul_single_same]
            simp only [_root_.mul_one]
          simp only [Category.assoc, h4]
  · intro m u
    dsimp only
    have hrow : Matrix.single o u (1 : ℤ) * m = ∑ v, m u v • Matrix.single o v 1 := by
      ext a b
      by_cases ha : a = o
      · subst ha
        simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply]
      · simp [Matrix.mul_apply, Matrix.sum_apply, Ne.symm ha]
    have := hcA
    rw [← Category.assoc, hc, hrow, hsum, prod_comp]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hzs, GrpObj.zpow_comp]

end General

/- English proof (translation)
Introduce `S G _ ρ hab hρ hmul hadd hone`. Take `⟨hcomm, hsmooth, hproper, hgeo⟩` from `hab`. Take `⟨A, gA, hcA, R, pr, hpr, huniv, hact⟩` from `exists_power (0 : Fin 8) G ρ hρ hmul hadd hone`. Take `⟨-, -, -, hsm, -, -, -, -, hpro, -, hgc, -, -⟩` from `GlobalTheory.Retract.over_properties R`. Use `⟨A, gA, pr, ⟨hcA, hsm hsmooth, hpro hproper, hgc hgeo⟩, hpr, huniv, fun m u => ?_⟩` and prove the remaining obligations.

Rewrite using `[hact, List.prod_ofFn]`.
-/
theorem abelianScheme_matrix_power : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsAbelianScheme G → (∀ m, IsMonHom (ρ m)) → (∀ m m', ρ (m * m') = ρ m' ≫ ρ m) → (∀ m m', ρ (m + m') = ρ m * ρ m') → ρ 1 = 𝟙 G → ∃ (A : Over S) (_ : GrpObj A) (pr : Fin 8 → (G ⟶ A)), IsAbelianScheme A ∧ (∀ u, IsMonHom (pr u)) ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) ∧ ∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod := by
  intro S G _ ρ hab hρ hmul hadd hone
  obtain ⟨hcomm, hsmooth, hproper, hgeo⟩ := hab
  obtain ⟨A, gA, hcA, R, pr, hpr, huniv, hact⟩ := exists_power (0 : Fin 8) G ρ hρ hmul hadd hone
  obtain ⟨-, -, -, hsm, -, -, -, -, hpro, -, hgc, -, -⟩ := GlobalTheory.Retract.over_properties R
  refine ⟨A, gA, pr, ⟨hcA, hsm hsmooth, hpro hproper, hgc hgeo⟩, hpr, huniv, fun m u => ?_⟩
  rw [hact, List.prod_ofFn]

end GlobalTheory.MatrixPower
