import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2.TopPow

variable {R : Type} [CommRing R] [Algebra ℂ R]

/- English proof (translation)
Establish `h2 : (2 : ℂ) • x = 0`. Rewrite using `[two_smul]`. Use `nth_rewrite 2 [h]`. Conclude with `add_neg_cancel x`. Establish `h3` using `congrArg (fun y : R => (1 / 2 : ℂ) • y) h2`.

Simplify using `only [smul_smul, smul_zero] at h3`. Evaluate the numerical expressions using `at h3`. Conclude with `h3`.
-/
theorem eq_zero_of_eq_neg_self {x : R} (h : x = -x) : x = 0 := by
  have h2 : (2 : ℂ) • x = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel x
  have h3 := congrArg (fun y : R => (1 / 2 : ℂ) • y) h2
  simp only [smul_smul, smul_zero] at h3
  norm_num at h3
  exact h3

/- English proof (translation)
Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩), ← mul_assoc, h, zero_mul]`.
-/
theorem prod_eq_zero_of_pair {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → R) {i j : ι} (hij : i ≠ j)
    (h : f i * f j = 0) : ∏ k, f k = 0 := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩), ← mul_assoc, h, zero_mul]

/- English proof (translation)
Rewrite using `[← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]`. Establish `key : ∀ g : Fin (Fintype.card B) → B, ∏ i, w (g i) = if Function.Injective g then ∏ a, w a else 0`. Introduce `g`. Use `split_ifs with hg`. Conclude with `Fintype.prod_bijective g ((Fintype.bijective_iff_injective_and_card g).2 ⟨hg, by simp⟩) _ _ (fun _ => rfl)`.

Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij, hne⟩ : ∃ i j, g i = g j ∧ i ≠ j := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hg h`. Conclude with `prod_eq_zero_of_pair (fun k => w (g k)) hne (by simp only [hij]; exact hw _)`.

Simplify using `only [key, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]`. Use `congr 1`. Rewrite using `[← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _), Fintype.card_embedding_eq, Fintype.card_fin, Nat.descFactorial_self]`.
-/
theorem pow_card_sum_of_sq {B : Type} [Fintype B] [DecidableEq B] (w : B → R) (hw : ∀ a, w a * w a = 0) :
    (∑ a, w a) ^ Fintype.card B = (Fintype.card B).factorial • ∏ a, w a := by
  rw [← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
  have key : ∀ g : Fin (Fintype.card B) → B,
      ∏ i, w (g i) = if Function.Injective g then ∏ a, w a else 0 := by
    intro g
    split_ifs with hg
    · exact Fintype.prod_bijective g ((Fintype.bijective_iff_injective_and_card g).2 ⟨hg, by simp⟩) _ _
        (fun _ => rfl)
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, g i = g j ∧ i ≠ j := by
        by_contra h
        push_neg at h
        exact hg h
      exact prod_eq_zero_of_pair (fun k => w (g k)) hne (by simp only [hij]; exact hw _)
  simp only [key, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  congr 1
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq, Fintype.card_fin, Nat.descFactorial_self]

/- English proof (translation)
Proceed by induction on `σ using Equiv.Perm.swap_induction_on' with`. Consider the case `one => simp`. Consider the case `mul_swap f x y hxy ih`. Rewrite using `[Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy, mul_neg_one, Units.neg_smul, ← ih]`. Establish `split : ∀ F : B → R, ∏ a, F a = F x * F y * ∏ a ∈ (Finset.univ.erase x).erase y, F a` using `fun F => by`.

Rewrite using `[mul_assoc, Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hxy.symm, Finset.mem_univ y⟩), Finset.mul_prod_erase _ _ (Finset.mem_univ x)]`. Rewrite using `[split (fun a => s a ((f * Equiv.swap x y) a)), split (fun a => s a (f a))]`. Establish `hrest : ∏ a ∈ (Finset.univ.erase x).erase y, s a ((f * Equiv.swap x y) a) = ∏ a ∈ (Finset.univ.erase x).erase y, s a (f a)` using `Finset.prod_congr rfl fun a ha => by`. Establish `hay : a ≠ y` using `(Finset.mem_erase.1 ha).1`. Establish `hax : a ≠ x` using `(Finset.mem_erase.1 (Finset.mem_erase.1 ha).2).1`.

Rewrite using `[Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hax hay]`. Rewrite using `[hrest]`. Simplify using `only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]`. Rewrite using `[hs, neg_mul]`.
-/
theorem prod_perm {B : Type} [Fintype B] [DecidableEq B] (s : B → B → R)
    (hs : ∀ a b c d, s a b * s c d = -(s a d * s c b)) (σ : Equiv.Perm B) :
    ∏ a, s a (σ a) = Equiv.Perm.sign σ • ∏ a, s a a := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap f x y hxy ih =>
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy, mul_neg_one, Units.neg_smul, ← ih]
    have split : ∀ F : B → R, ∏ a, F a = F x * F y * ∏ a ∈ (Finset.univ.erase x).erase y, F a := fun F => by
      rw [mul_assoc, Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hxy.symm, Finset.mem_univ y⟩),
        Finset.mul_prod_erase _ _ (Finset.mem_univ x)]
    rw [split (fun a => s a ((f * Equiv.swap x y) a)), split (fun a => s a (f a))]
    have hrest : ∏ a ∈ (Finset.univ.erase x).erase y, s a ((f * Equiv.swap x y) a) =
        ∏ a ∈ (Finset.univ.erase x).erase y, s a (f a) := Finset.prod_congr rfl fun a ha => by
      have hay : a ≠ y := (Finset.mem_erase.1 ha).1
      have hax : a ≠ x := (Finset.mem_erase.1 (Finset.mem_erase.1 ha).2).1
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hax hay]
    rw [hrest]
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [hs, neg_mul]

/- English proof (translation)
Establish `h : ∀ p q : W, ExteriorAlgebra.ι ℂ p * ExteriorAlgebra.ι ℂ q = -(ExteriorAlgebra.ι ℂ q * ExteriorAlgebra.ι ℂ p)` using `fun p q => eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap p q)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h v w, neg_mul, mul_assoc]`. Use `_ = (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x) * ExteriorAlgebra.ι ℂ v := by`. Rewrite using `[h v x, mul_neg, neg_neg, mul_assoc]`.

Use `_ = _ := by rw [h w x, neg_mul, mul_assoc]`.
-/
theorem ι_three_swap {W : Type} [AddCommGroup W] [Module ℂ W] (v w x : W) :
    ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x) =
      -(ExteriorAlgebra.ι ℂ x * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ v)) := by
  have h : ∀ p q : W, ExteriorAlgebra.ι ℂ p * ExteriorAlgebra.ι ℂ q =
      -(ExteriorAlgebra.ι ℂ q * ExteriorAlgebra.ι ℂ p) :=
    fun p q => eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap p q)
  calc ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x)
      = (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ w) * ExteriorAlgebra.ι ℂ x := (mul_assoc _ _ _).symm
    _ = -(ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ x)) := by
      rw [h v w, neg_mul, mul_assoc]
    _ = (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x) * ExteriorAlgebra.ι ℂ v := by
      rw [h v x, mul_neg, neg_neg, mul_assoc]
    _ = _ := by rw [h w x, neg_mul, mul_assoc]

/- English proof (translation)
Simplify using `only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]`.
-/
theorem prod_smul_eq {ι : Type} [Fintype ι] (c : ι → ℂ) (x : ι → R) :
    ∏ a, c a • x a = (∏ a, c a) • ∏ a, x a := by
  simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]

/- English proof (translation)
Establish `hzero : ∀ a b c, s a b * s c b = 0` using `fun a b c => eq_zero_of_eq_neg_self (hs a b c b)`. Establish `hzero' : ∀ a b d, s a b * s a d = 0` using `fun a b d => eq_zero_of_eq_neg_self ((hs a b a d).trans (by rw [mul_comm]))`. Establish `hw : ∀ a, (∑ b, K a b • s a b) * (∑ b, K a b • s a b) = 0` using `fun a => by`. Rewrite using `[Finset.sum_mul_sum]`. Use `Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_mul_smul_comm, hzero', smul_zero]`. Rewrite using `[pow_card_sum_of_sq _ hw, Finset.prod_univ_sum, Fintype.piFinset_univ]`. Simplify using `only [prod_smul_eq]`. Establish `hnon : ∀ g : B → B, ¬ Function.Injective g → (∏ a, K a (g a)) • ∏ a, s a (g a) = 0`. Introduce `g hg`.

Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij, hne⟩ : ∃ i j, g i = g j ∧ i ≠ j := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hg h`. Rewrite using `[prod_eq_zero_of_pair (fun k => s k (g k)) hne (by simp only [hij]; exact hzero _ _ _), smul_zero]`.

Establish `hsum : ∑ g : B → B, (∏ a, K a (g a)) • ∏ a, s a (g a) = ∑ σ : Equiv.Perm B, (∏ a, K a (σ a)) • ∏ a, s a (σ a)`. Establish `hm` using `Finset.sum_map (Finset.univ : Finset (Equiv.Perm B)) ⟨fun σ : Equiv.Perm B => (σ : B → B), DFunLike.coe_injective⟩ (fun g : B → B => (∏ a, K a (g a)) • ∏ a, s a (g a))`. Simplify using `only [Function.Embedding.coeFn_mk] at hm`. Rewrite using `[← hm]`. Use `(Finset.sum_subset (Finset.subset_univ _) fun g _ hg => hnon g fun hi => hg ?_).symm` and prove the remaining obligations.

Conclude with `Finset.mem_map.2 ⟨Equiv.ofBijective g hi.bijective_of_finite, Finset.mem_univ _, rfl⟩`. Rewrite using `[hsum]`. Simplify using `only [prod_perm s hs, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]`. Rewrite using `[← Finset.sum_smul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Matrix.det_transpose, Matrix.det_apply]`. Use `congr 2`.

Simplify using `only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, Matrix.transpose_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
theorem sum_pow_card {B : Type} [Fintype B] [DecidableEq B] (s : B → B → R)
    (hs : ∀ a b c d, s a b * s c d = -(s a d * s c b)) (K : Matrix B B ℂ) :
    (∑ a, ∑ b, K a b • s a b) ^ Fintype.card B = ((Fintype.card B).factorial * K.det : ℂ) • ∏ a, s a a := by
  have hzero : ∀ a b c, s a b * s c b = 0 := fun a b c => eq_zero_of_eq_neg_self (hs a b c b)
  have hzero' : ∀ a b d, s a b * s a d = 0 := fun a b d =>
    eq_zero_of_eq_neg_self ((hs a b a d).trans (by rw [mul_comm]))
  have hw : ∀ a, (∑ b, K a b • s a b) * (∑ b, K a b • s a b) = 0 := fun a => by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun d _ => ?_
    rw [smul_mul_smul_comm, hzero', smul_zero]
  rw [pow_card_sum_of_sq _ hw, Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp only [prod_smul_eq]
  have hnon : ∀ g : B → B, ¬ Function.Injective g → (∏ a, K a (g a)) • ∏ a, s a (g a) = 0 := by
    intro g hg
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, g i = g j ∧ i ≠ j := by
      by_contra h
      push_neg at h
      exact hg h
    rw [prod_eq_zero_of_pair (fun k => s k (g k)) hne (by simp only [hij]; exact hzero _ _ _), smul_zero]
  have hsum : ∑ g : B → B, (∏ a, K a (g a)) • ∏ a, s a (g a) =
      ∑ σ : Equiv.Perm B, (∏ a, K a (σ a)) • ∏ a, s a (σ a) := by
    have hm := Finset.sum_map (Finset.univ : Finset (Equiv.Perm B))
      ⟨fun σ : Equiv.Perm B => (σ : B → B), DFunLike.coe_injective⟩
      (fun g : B → B => (∏ a, K a (g a)) • ∏ a, s a (g a))
    simp only [Function.Embedding.coeFn_mk] at hm
    rw [← hm]
    refine (Finset.sum_subset (Finset.subset_univ _) fun g _ hg => hnon g fun hi => hg ?_).symm
    exact Finset.mem_map.2 ⟨Equiv.ofBijective g hi.bijective_of_finite, Finset.mem_univ _, rfl⟩
  rw [hsum]
  simp only [prod_perm s hs, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  rw [← Finset.sum_smul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Matrix.det_transpose, Matrix.det_apply]
  congr 2
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_comm]

end GlobalTheory.FlagCell2.TopPow

namespace GlobalTheory.FlagCell2

/- English proof (translation)
Introduce `n B _ _ e _ K`. Use `TopPow.sum_pow_card (fun a b => sym (e a, e b)) (fun a b c d => ?_) K` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `dz (e a) * dzb (e b) * (dz (e c) * dzb (e d)) = -(dz (e a) * dzb (e d) * (dz (e c) * dzb (e b)))`. Simplify using `only [dz, dzb, mul_assoc]`.

Rewrite using `[← mul_neg]`. Use `congr 1`. Conclude with `TopPow.ι_three_swap _ _ _`.
-/
theorem pow_card_sum_sym : ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (e : B → Fin n), Function.Injective e →
    ∀ K : Matrix B B ℂ, (∑ a, ∑ b, K a b • sym (e a, e b) : Ev n) ^ Fintype.card B =
      ((Fintype.card B).factorial * K.det : ℂ) • ∏ a, sym (e a, e a) := by
  intro n B _ _ e _ K
  refine TopPow.sum_pow_card (fun a b => sym (e a, e b)) (fun a b c d => ?_) K
  apply Subtype.ext
  change dz (e a) * dzb (e b) * (dz (e c) * dzb (e d)) = -(dz (e a) * dzb (e d) * (dz (e c) * dzb (e b)))
  simp only [dz, dzb, mul_assoc]
  rw [← mul_neg]
  congr 1
  exact TopPow.ι_three_swap _ _ _

end GlobalTheory.FlagCell2
