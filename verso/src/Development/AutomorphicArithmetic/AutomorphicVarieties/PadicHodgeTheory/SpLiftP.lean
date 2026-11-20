import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CommOfIntegral
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

namespace UpperTheory.V.Loc.RankFourLocalLifting

open IsNilpotent

section Exp

variable {B B' H : Type} [CommRing B] [Algebra ℚ B] [CommRing B'] [Algebra ℚ B']

/- English proof (translation)
Take `⟨k, hk⟩` from `ha`. Establish `h2 : a ^ (k + 2) = 0` using `pow_eq_zero_of_le (by omega) hk`. Use `⟨∑ i ∈ Finset.range k, (((i + 2).factorial : ℚ)⁻¹ • a ^ i), ?_⟩` and prove the remaining obligations. Rewrite using `[exp_eq_sum h2, Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]`. Establish `: ∀ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ)⁻¹ • a ^ (i + 1 + 1)) = a ^ 2 * (((i + 2).factorial : ℚ)⁻¹ • a ^ i)` using `fun i _ => by`.

Rewrite using `[mul_smul_comm, ← pow_add, add_comm 2 i]`. Rewrite using `[Finset.sum_congr rfl this]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exp_two {a : B} (ha : IsNilpotent a) : ∃ c, exp a = 1 + a + a ^ 2 * c := by
  obtain ⟨k, hk⟩ := ha
  have h2 : a ^ (k + 2) = 0 := pow_eq_zero_of_le (by omega) hk
  refine ⟨∑ i ∈ Finset.range k, (((i + 2).factorial : ℚ)⁻¹ • a ^ i), ?_⟩
  rw [exp_eq_sum h2, Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
  have : ∀ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ)⁻¹ • a ^ (i + 1 + 1)) =
      a ^ 2 * (((i + 2).factorial : ℚ)⁻¹ • a ^ i) := fun i _ => by
    rw [mul_smul_comm, ← pow_add, add_comm 2 i]
  rw [Finset.sum_congr rfl this]
  simp
  ring

/- English proof (translation)
Establish `hn : IsNilpotent (a + -b)` using `(Commute.all _ _).isNilpotent_add ha hb.neg`. Establish `h1 : exp (a + -b) = 1`. Rewrite using `[exp_add_of_commute (Commute.all _ _) ha hb.neg, h, exp_mul_exp_neg_self hb]`. Take `⟨c, hc⟩` from `exp_two hn`. Establish `hu : IsUnit (1 + (a + -b) * c)` using `((Commute.all _ _).isNilpotent_mul_right hn).isUnit_one_add`.

Establish `h2 : (1 + (a + -b) * c) * (a + -b) = 0` using `by linear_combination h1 - hc`. Use `(hu.mul_right_eq_zero).1 h2` as an intermediate fact. Take the linear combination `this`.
-/
private theorem exp_inj {a b : B} (ha : IsNilpotent a) (hb : IsNilpotent b) (h : exp a = exp b) : a = b := by
  have hn : IsNilpotent (a + -b) := (Commute.all _ _).isNilpotent_add ha hb.neg
  have h1 : exp (a + -b) = 1 := by
    rw [exp_add_of_commute (Commute.all _ _) ha hb.neg, h, exp_mul_exp_neg_self hb]
  obtain ⟨c, hc⟩ := exp_two hn
  have hu : IsUnit (1 + (a + -b) * c) := ((Commute.all _ _).isNilpotent_mul_right hn).isUnit_one_add
  have h2 : (1 + (a + -b) * c) * (a + -b) = 0 := by linear_combination h1 - hc
  have := (hu.mul_right_eq_zero).1 h2
  linear_combination this

/- English proof (translation)
Use `Ideal.pow_mem_pow ha n` as an intermediate fact. Rewrite `this` using `[hm]`. Then use the resulting hypothesis.
-/
private theorem nil_of {m : Ideal B} {n : ℕ} (hm : m ^ n = ⊥) {a : B} (ha : a ∈ m) : a ^ n = 0 := by
  have := Ideal.pow_mem_pow ha n
  rwa [hm] at this

variable [TopologicalSpace H] [TopologicalSpace B] [IsTopologicalRing B] [TopologicalSpace B'] [IsTopologicalRing B']

/- English proof (translation)
Simplify using `only [fun g => exp_eq_sum (nil_of hm (h g)), Algebra.smul_def]`. Use `fun_prop`.
-/
private theorem exp_cont {m : Ideal B} {n : ℕ} (hm : m ^ n = ⊥) {y : H → B} (hy : Continuous y)
    (h : ∀ g, y g ∈ m) : Continuous fun g => exp (y g) := by
  simp only [fun g => exp_eq_sum (nil_of hm (h g)), Algebra.smul_def]
  fun_prop

/- English proof (translation)
Establish `key : ∀ k : ℕ, ∃ y : H → B, Continuous y ∧ (∀ g, y g ∈ m) ∧ ∀ g, u g * exp (-y g) - 1 ∈ m ^ (k + 1)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨fun _ => 0, continuous_const, fun _ => m.zero_mem, fun g => by simpa using h g⟩`. Consider the case `succ k ih`.

Take `⟨y, hy, h1, h2⟩` from `ih`. Establish `h3 : ∀ g, u g * exp (-y g) - 1 ∈ m` using `fun g => Ideal.pow_le_self (Nat.succ_ne_zero k) (h2 g)`. Use `⟨fun g => y g + (u g * exp (-y g) - 1), hy.add ((hu.mul (exp_cont hm hy.neg fun g => m.neg_mem (h1 g))).sub continuous_const), fun g => m.add_mem (h1 g) (h3 g), fun g => ?_⟩` and prove the remaining obligations. Establish `hw : IsNilpotent (-(u g * exp (-y g) - 1))` using `⟨n, nil_of hm (m.neg_mem (h3 g))⟩`. Take `⟨c, hc⟩` from `exp_two hw`.

Rewrite using `[neg_add, exp_add_of_commute (Commute.all _ _) ⟨n, nil_of hm (m.neg_mem (h1 g))⟩ hw, hc, ← mul_assoc]`. Establish `h4` using `Ideal.mul_mem_mul (h2 g) (h3 g)`. Rewrite `h4` using `[← _root_.pow_succ]`. Use `Ideal.mul_mem_right (c * (u g * exp (-y g)) - 1) _ h4 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Take `⟨y, hy, h1, h2⟩` from `key n`. Use `⟨y, hy, h1, fun g => ?_⟩` and prove the remaining obligations. Establish `h3` using `h2 g`. Rewrite `h3` using `[_root_.pow_succ, hm, Ideal.bot_mul, Ideal.mem_bot]`. Establish `h4` using `exp_neg_mul_exp_self (⟨n, nil_of hm (h1 g)⟩ : IsNilpotent (y g))`.

Take the linear combination `u g * h4 - exp (y g) * h3`.
-/
private theorem log_ex {m : Ideal B} {n : ℕ} (hm : m ^ n = ⊥) {u : H → B} (hu : Continuous u)
    (h : ∀ g, u g - 1 ∈ m) : ∃ y : H → B, Continuous y ∧ (∀ g, y g ∈ m) ∧ ∀ g, exp (y g) = u g := by
  have key : ∀ k : ℕ, ∃ y : H → B, Continuous y ∧ (∀ g, y g ∈ m) ∧ ∀ g, u g * exp (-y g) - 1 ∈ m ^ (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨fun _ => 0, continuous_const, fun _ => m.zero_mem, fun g => by simpa using h g⟩
    | succ k ih =>
      obtain ⟨y, hy, h1, h2⟩ := ih
      have h3 : ∀ g, u g * exp (-y g) - 1 ∈ m := fun g => Ideal.pow_le_self (Nat.succ_ne_zero k) (h2 g)
      refine ⟨fun g => y g + (u g * exp (-y g) - 1), hy.add ((hu.mul (exp_cont hm hy.neg fun g => m.neg_mem (h1 g))).sub
        continuous_const), fun g => m.add_mem (h1 g) (h3 g), fun g => ?_⟩
      have hw : IsNilpotent (-(u g * exp (-y g) - 1)) := ⟨n, nil_of hm (m.neg_mem (h3 g))⟩
      obtain ⟨c, hc⟩ := exp_two hw
      rw [neg_add, exp_add_of_commute (Commute.all _ _) ⟨n, nil_of hm (m.neg_mem (h1 g))⟩ hw, hc, ← mul_assoc]
      have h4 := Ideal.mul_mem_mul (h2 g) (h3 g)
      rw [← _root_.pow_succ] at h4
      convert Ideal.mul_mem_right (c * (u g * exp (-y g)) - 1) _ h4 using 1
      ring
  obtain ⟨y, hy, h1, h2⟩ := key n
  refine ⟨y, hy, h1, fun g => ?_⟩
  have h3 := h2 g
  rw [_root_.pow_succ, hm, Ideal.bot_mul, Ideal.mem_bot] at h3
  have h4 := exp_neg_mul_exp_self (⟨n, nil_of hm (h1 g)⟩ : IsNilpotent (y g))
  linear_combination u g * h4 - exp (y g) * h3

/- English proof (translation)
Take `⟨y, hy, h1, h2⟩` from `log_ex hm' hu h`. Establish `n1 : ∀ g, IsNilpotent (y g)` using `fun g => ⟨n', nil_of hm' (h1 g)⟩`. Establish `n2 : ∀ g, IsNilpotent (s (y g))` using `fun g => ⟨n, nil_of hm (hsm _ (h1 g))⟩`. Establish `h0 : ∀ g, u g = 1 → exp (s (y g)) = 1` using `fun g hg => by`. Rewrite using `[exp_inj (n1 g) IsNilpotent.zero (by rw [h2, hg, exp_zero]), map_zero, exp_zero]`.

Use `⟨⟨⟨fun g => exp (s (y g)), h0 1 (map_one u)⟩, fun a b => ?_⟩, exp_cont hm (hs.comp hy) fun g => hsm _ (h1 g), fun g => ?_, h0⟩` and prove the remaining obligations. Use `show exp (s (y (a * b))) = exp (s (y a)) * exp (s (y b))`. Rewrite using `[exp_inj (n1 (a * b)) ((Commute.all _ _).isNilpotent_add (n1 a) (n1 b)) (by rw [exp_add_of_commute (Commute.all _ _) (n1 a) (n1 b), h2, h2, h2, map_mul]), map_add, exp_add_of_commute (Commute.all _ _) (n2 a) (n2 b)]`. Use `show p (exp (s (y g))) = u g`. Rewrite using `[map_exp (n2 g), hps, h2]`.
-/
private theorem liftChar [Group H] {m : Ideal B} {n : ℕ} (hm : m ^ n = ⊥) {m' : Ideal B'} {n' : ℕ}
    (hm' : m' ^ n' = ⊥) (p : B →+* B') (s : B' →+ B) (hs : Continuous s) (hps : ∀ x, p (s x) = x)
    (hsm : ∀ x ∈ m', s x ∈ m) (u : H →* B') (hu : Continuous u) (h : ∀ g, u g - 1 ∈ m') :
    ∃ f : H →* B, Continuous f ∧ (∀ g, p (f g) = u g) ∧ ∀ g, u g = 1 → f g = 1 := by
  obtain ⟨y, hy, h1, h2⟩ := log_ex hm' hu h
  have n1 : ∀ g, IsNilpotent (y g) := fun g => ⟨n', nil_of hm' (h1 g)⟩
  have n2 : ∀ g, IsNilpotent (s (y g)) := fun g => ⟨n, nil_of hm (hsm _ (h1 g))⟩
  have h0 : ∀ g, u g = 1 → exp (s (y g)) = 1 := fun g hg => by
    rw [exp_inj (n1 g) IsNilpotent.zero (by rw [h2, hg, exp_zero]), map_zero, exp_zero]
  refine ⟨⟨⟨fun g => exp (s (y g)), h0 1 (map_one u)⟩, fun a b => ?_⟩, exp_cont hm (hs.comp hy) fun g => hsm _ (h1 g),
    fun g => ?_, h0⟩
  · show exp (s (y (a * b))) = exp (s (y a)) * exp (s (y b))
    rw [exp_inj (n1 (a * b)) ((Commute.all _ _).isNilpotent_add (n1 a) (n1 b))
      (by rw [exp_add_of_commute (Commute.all _ _) (n1 a) (n1 b), h2, h2, h2, map_mul]), map_add,
      exp_add_of_commute (Commute.all _ _) (n2 a) (n2 b)]
  · show p (exp (s (y g))) = u g
    rw [map_exp (n2 g), hps, h2]

end Exp

section Mat

variable {R R' E : Type} [CommRing R] [CommRing R'] [Field E]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring`.
-/
private theorem adj_mul (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]`.
-/
private theorem adj_adj (X : M4 R) : adj (adj X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[adj_apply, mul_add]`.
-/
private theorem adj_add (X Y : M4 R) : adj (X + Y) = adj X + adj Y := by
  ext i j
  simp [adj_apply, mul_add]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[adj_apply, mul_sub]`.
-/
private theorem adj_sub (X Y : M4 R) : adj (X - Y) = adj X - adj Y := by
  ext i j
  simp [adj_apply, mul_sub]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [adj_apply, Matrix.smul_apply]`. Rewrite using `[smul_comm]`.
-/
private theorem adj_smul (a : R) (X : M4 R) : adj (a • X) = a • adj X := by
  ext i j
  simp only [adj_apply, Matrix.smul_apply]
  rw [smul_comm]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.diagonal_apply]`.
-/
private theorem adj_diag (d : Fin 4 → R) : adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.diagonal_apply]

/- English proof (translation)
The claim follows from `adj_diag _`.
-/
private theorem adj_one : adj (1 : M4 R) = 1 := adj_diag _

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[adj_apply]`.
-/
private theorem adj_map (f : R →+* R') (X : M4 R) : adj (X.map f) = (adj X).map f := by
  ext i j
  simp [adj_apply]

variable [Algebra E R] (π : R →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a)

include hπ in
/- English proof (translation)
Establish `h1` using `hπ (a - algebraMap E R (π a)) (by simp)`. Establish `h2` using `h1.isUnit_add_right_of_commute ((IsUnit.mk0 _ ha).map (algebraMap E R)) (Commute.all _ _)`. Simplify using `using h2`.
-/
private theorem unit_of {a : R} (ha : π a ≠ 0) : IsUnit a := by
  have h1 := hπ (a - algebraMap E R (π a)) (by simp)
  have h2 := h1.isUnit_add_right_of_commute ((IsUnit.mk0 _ ha).map (algebraMap E R)) (Commute.all _ _)
  simpa using h2

include hπ in
/- English proof (translation)
Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Use `unit_of π hπ ?_` and prove the remaining obligations. Rewrite `h` using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Then use the resulting hypothesis.
-/
private theorem unit_mat {M : M4 R} (h : (M.map (π : R →+* E)).det ≠ 0) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  refine unit_of π hπ ?_
  rwa [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h

include hπ in
/- English proof (translation)
Establish `hP : X.charpoly.map (π : R →+* E) = ∏ j, (Polynomial.X - Polynomial.C (c j))`. Rewrite using `[← Matrix.charpoly_map, hX, Matrix.charpoly_diagonal]`. Establish `hne : ∀ i, ∏ j ∈ Finset.univ.erase i, (c i - c j) ≠ 0` using `fun i => Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 fun h => (Finset.mem_erase.1 hj).1 (hc h).symm`. Establish `hev : ∀ (P : Polynomial R) (x : E), π (Polynomial.aeval (algebraMap E R x) P) = (P.map (π : R →+* E)).eval x` using `fun P x => by`. Rewrite using `[Polynomial.coe_aeval_eq_eval, Polynomial.eval_map]`.

Use `Polynomial.eval₂_at_apply (p := P) (π : R →+* E) (algebraMap E R x)` as an intermediate fact. Simplify using `using this.symm`. Establish `hr : ∀ i, ∃ t : R, π t = c i ∧ X.charpoly.eval t = 0` using `fun i => by`. Take `⟨t, ⟨h1, h2⟩, -⟩` from `Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero (x := algebraMap E R (c i)) (P := X.charpoly) (hπ _ (by`. Rewrite using `[hev, hP, Polynomial.eval_prod]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp))) (unit_of π hπ (by`. Rewrite using `[hev, ← Polynomial.derivative_map, hP, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]`. Simplify `hne i))` using `[Polynomial.eval_prod]`. Use `⟨t, ?_, by simpa using h2⟩` and prove the remaining obligations. Use `(h1.map π).eq_zero` as an intermediate fact.

Rewrite `this` using `[map_sub, AlgHom.commutes, sub_eq_zero]`. Conclude with `this.symm`. Use `choose t ht1 ht2 using hr`. Use `⟨Matrix.of fun a i => algebraMap E R (∏ j ∈ Finset.univ.erase i, (c i - c j))⁻¹ * (Matrix.scalar (Fin 4) (t i) - X).adjugate a i, t, ?_, ?_, ht1⟩` and prove the remaining obligations. Use extensionality with `a i`.

Establish `h1 : ((Matrix.scalar (Fin 4) (t i) - X).adjugate).map (π : R →+* E) = (Matrix.diagonal fun j => c i - c j).adjugate`. Rewrite using `[← RingHom.mapMatrix_apply, RingHom.map_adjugate, map_sub, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hX, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), Matrix.diagonal_sub]`. Simplify using `[ht1]`. Establish `h2` using `congrFun (congrFun h1 a) i`. Rewrite `h2` using `[Matrix.adjugate_diagonal]`.

Simplify using `only [Matrix.map_apply, Matrix.of_apply, map_mul, RingHom.coe_coe, AlgHom.commutes] at h2 ⊢`. Rewrite using `[h2]`. Distinguish the cases in `h : a = i`. Substitute `h` using the available equality. Simplify using `using inv_mul_cancel₀ (hne a)`.

Simplify using `[h]`. Use extensionality with `a i`. Establish `h1` using `Matrix.mul_adjugate (Matrix.scalar (Fin 4) (t i) - X)`. Rewrite `h1` using `[← Matrix.eval_charpoly, ht2, zero_smul, sub_mul, sub_eq_zero]`. Establish `h2` using `congrFun (congrFun h1 a) i`.

Rewrite `h2` using `[Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_apply]`. Rewrite using `[Matrix.mul_diagonal, Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply, mul_left_comm (X a _), ← Finset.mul_sum]`. Rewrite `h2` using `[← Matrix.scalar_apply]`. Rewrite using `[← h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem diagX (X : M4 R) (c : Fin 4 → E) (hc : Function.Injective c)
    (hX : X.map (π : R →+* E) = Matrix.diagonal c) :
    ∃ (u : M4 R) (t : Fin 4 → R), u.map (π : R →+* E) = 1 ∧ X * u = u * Matrix.diagonal t ∧ ∀ i, π (t i) = c i := by
  have hP : X.charpoly.map (π : R →+* E) = ∏ j, (Polynomial.X - Polynomial.C (c j)) := by
    rw [← Matrix.charpoly_map, hX, Matrix.charpoly_diagonal]
  have hne : ∀ i, ∏ j ∈ Finset.univ.erase i, (c i - c j) ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 fun h => (Finset.mem_erase.1 hj).1 (hc h).symm
  have hev : ∀ (P : Polynomial R) (x : E), π (Polynomial.aeval (algebraMap E R x) P) =
      (P.map (π : R →+* E)).eval x := fun P x => by
    rw [Polynomial.coe_aeval_eq_eval, Polynomial.eval_map]
    have := Polynomial.eval₂_at_apply (p := P) (π : R →+* E) (algebraMap E R x)
    simpa using this.symm
  have hr : ∀ i, ∃ t : R, π t = c i ∧ X.charpoly.eval t = 0 := fun i => by
    obtain ⟨t, ⟨h1, h2⟩, -⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero (x := algebraMap E R (c i))
      (P := X.charpoly) (hπ _ (by
        rw [hev, hP, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp))) (unit_of π hπ (by
        rw [hev, ← Polynomial.derivative_map, hP, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        simpa [Polynomial.eval_prod] using hne i))
    refine ⟨t, ?_, by simpa using h2⟩
    have := (h1.map π).eq_zero
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at this
    exact this.symm
  choose t ht1 ht2 using hr
  refine ⟨Matrix.of fun a i => algebraMap E R (∏ j ∈ Finset.univ.erase i, (c i - c j))⁻¹ *
    (Matrix.scalar (Fin 4) (t i) - X).adjugate a i, t, ?_, ?_, ht1⟩
  · ext a i
    have h1 : ((Matrix.scalar (Fin 4) (t i) - X).adjugate).map (π : R →+* E) =
        (Matrix.diagonal fun j => c i - c j).adjugate := by
      rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, map_sub, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hX,
        Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), Matrix.diagonal_sub]
      simp [ht1]
    have h2 := congrFun (congrFun h1 a) i
    rw [Matrix.adjugate_diagonal] at h2
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, RingHom.coe_coe, AlgHom.commutes] at h2 ⊢
    rw [h2]
    by_cases h : a = i
    · subst h
      simpa using inv_mul_cancel₀ (hne a)
    · simp [h]
  · ext a i
    have h1 := Matrix.mul_adjugate (Matrix.scalar (Fin 4) (t i) - X)
    rw [← Matrix.eval_charpoly, ht2, zero_smul, sub_mul, sub_eq_zero] at h1
    have h2 := congrFun (congrFun h1 a) i
    rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_apply] at h2
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.of_apply, mul_left_comm (X a _), ← Finset.mul_sum]
    rw [← Matrix.scalar_apply] at h2
    rw [← h2]
    ring

include hπ in
/- English proof (translation)
Take `⟨x, hx⟩` from `Module.Dual.exists_forall_ne_zero_of_forall_exists (K := E) (M := H →₀ E) (fun ij : {ij : Fin 4 × Fin 4 // ij.1 ≠ ij.2} => Finsupp.linearCombination E (fun g => χ ij.1.1 g) - Finsupp.linearCombination E (fun g => χ ij.1.2 g)) (fun ij => by`. Take `⟨g, hg⟩` from `hχ _ _ ij.2`. Conclude with `⟨Finsupp.single g 1, by simpa [sub_ne_zero] using hg⟩)`. Take `⟨u, t, hu, hX, ht⟩` from `diagX π hπ (Finsupp.linearCombination E (fun g => r g) x) (fun i => Finsupp.linearCombination E (fun g => χ i g) x) (fun i j h => by`. Assume the negation of the conclusion as `hij`.

Conclude with `hx ⟨(i, j), hij⟩ (sub_eq_zero.2 h))`. Use the proof step `(by clear hx`. Use extensionality with `i j`. Proceed by induction on `x using Finsupp.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb`. Simplify using `only [map_add, ← Matrix.diagonal_add, Matrix.add_apply, Matrix.map_apply] at ha hb ⊢`. Rewrite using `[ha, hb]`. Consider the case `single g a`. Use `congrFun (congrFun (hr g) i) j` as an intermediate fact.

Simplify using `only [Matrix.map_apply, RingHom.coe_coe, Finsupp.linearCombination_single, Matrix.smul_apply, map_smul] at this ⊢`. Rewrite using `[this]`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.diagonal_apply, h])`. Establish `hXc : ∀ (y : H →₀ E) g, r g * Finsupp.linearCombination E (fun g => r g) y = Finsupp.linearCombination E (fun g => r g) y * r g` using `fun y g => by`. Proceed by induction on `y using Finsupp.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add, mul_add, add_mul, ha, hb]`. Consider the case `single g a => simp [hc]`. Take `⟨U, rfl⟩ : IsUnit u` from `unit_mat π hπ (by rw [hu]; simp)`. Establish `hd : ∀ g, ∃ d, r g * (U : M4 R) = (U : M4 R) * Matrix.diagonal d` using `fun g => by`.

Establish `h1 : ((U⁻¹ : (M4 R)ˣ) * r g * U : M4 R) * Matrix.diagonal t = Matrix.diagonal t * ((U⁻¹ : (M4 R)ˣ) * r g * U : M4 R)`. Establish `h2 : Matrix.diagonal t * (U⁻¹ : (M4 R)ˣ) = (U⁻¹ : (M4 R)ˣ) * Finsupp.linearCombination E (fun g => r g) x`. Rewrite using `[Units.mul_inv_eq_iff_eq_mul, mul_assoc, hX, Units.inv_mul_cancel_left]`. Rewrite using `[mul_assoc, ← hX, ← mul_assoc, ← mul_assoc, ← mul_assoc, h2, mul_assoc (U⁻¹ : (M4 R)ˣ).1, hXc, ← mul_assoc]`. Establish `h3 : ((U⁻¹ : (M4 R)ˣ) * r g * U : M4 R).IsDiag` using `fun i j hij => by`.

Establish `h4` using `congrFun (congrFun h1 i) j`. Rewrite `h4` using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Establish `h5 : IsUnit (t i - t j)` using `unit_of π hπ (by`. Rewrite using `[map_sub, ht, ht]`. Conclude with `hx ⟨(i, j), hij⟩)`.

Conclude with `h5.mul_right_eq_zero.1 (by linear_combination -h4)`. Conclude with `⟨_, by rw [h3.diagonal_diag, mul_assoc, Units.mul_inv_cancel_left]⟩`. Establish `hS : (adj (U : M4 R) * U).IsDiag` using `fun i j hij => by`. Take `⟨g, hg⟩` from `hχ i j hij`. Take `⟨d, hd⟩` from `hd g`.

Establish `h1 : ∀ a, π (d a) = χ a g` using `fun a => by`. Use `congrArg (fun M : M4 R => M.map (π : R →+* E)) hd` as an intermediate fact. Simplify using `only [Matrix.map_mul, hu, hr, Matrix.diagonal_map (map_zero _), mul_one, one_mul] at this`. Conclude with `(congrFun (Matrix.diagonal_injective this) a).symm`. Establish `h2 : adj (Matrix.diagonal d) * (adj (U : M4 R) * U) * Matrix.diagonal d = algebraMap E R (θ g) • (adj (U : M4 R) * U)`.

Establish `h3 : adj (r g) * r g = _` using `hG g`. Rewrite using `[← mul_assoc, ← adj_mul, ← hd, mul_assoc, ← hd, adj_mul, mul_assoc, ← mul_assoc (adj (r g)), h3]`. Simplify using the standard rewrite rules. Establish `h4` using `congrFun (congrFun h2 i) j`. Rewrite `h4` using `[adj_diag, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]`.

Establish `h5 : IsUnit (d i.rev * d j - algebraMap E R (θ g))` using `unit_of π hπ (by`. Rewrite using `[map_sub, map_mul, h1, h1, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, ← hθ g i, ← mul_sub]`. Use `mul_ne_zero (fun h => ?_) (sub_ne_zero.2 hg.symm)` and prove the remaining obligations. Use `map_mul (χ i.rev) g g⁻¹` as an intermediate fact. Simplify using `[h] at this)`.

Conclude with `h5.mul_right_eq_zero.1 (by linear_combination h4)`. Take `⟨s, hs⟩ : ∃ s, adj (U : M4 R) * (U : M4 R) = Matrix.diagonal s` from `⟨_, hS.diagonal_diag.symm⟩`. Establish `hs1 : ∀ i, π (s i) = 1` using `fun i => by`. Use `congrArg (fun M : M4 R => M.map (π : R →+* E)) hs` as an intermediate fact. Simplify using `only [Matrix.map_mul, ← adj_map, hu, adj_one, Matrix.diagonal_map (map_zero _), mul_one] at this`.

Simplify using `using (congrFun (congrFun this i) i).symm`. Establish `hs2 : ∀ i, s i.rev = s i` using `fun i => by`. Use `congrArg adj hs` as an intermediate fact. Rewrite `this` using `[adj_mul, adj_adj, hs, adj_diag]`. Conclude with `(congrFun (Matrix.diagonal_injective this) i).symm`.

Take `⟨a, ha⟩` from `(unit_of π hπ (a := s 0) (by simp [hs1])).exists_right_inv`. Take `⟨b, hb⟩` from `(unit_of π hπ (a := s 1) (by simp [hs1])).exists_right_inv`. Establish `ha1 : π a = 1` using `by simpa [hs1] using congrArg π ha`. Establish `hb1 : π b = 1` using `by simpa [hs1] using congrArg π hb`. Use `⟨(U : M4 R) * Matrix.diagonal ![1, 1, b, a], ?_, ?_, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.map_mul, hu, one_mul, Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_one]`. Use `congr 1`. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp [ha1, hb1]`. Use `show _ = _`.

Rewrite using `[adj_mul, mul_assoc, ← mul_assoc (adj _) _ (Matrix.diagonal _), hs, adj_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, one_smul, ← Matrix.diagonal_one]`. Use `congr 1`. Use extensionality with `i`. Establish `e3 : s 3 = s 0` using `hs2 0`. Establish `e2 : s 2 = s 1` using `hs2 1`.

Apply the tactic sequence `fin_cases i <;> simp [Fin.rev, e2, e3, ha, hb, mul_comm a, mul_comm b]`. Take `⟨d, hd⟩` from `hd g`. Use `⟨d, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, hd, mul_assoc, mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Simplify using `only [mul_comm]`.
-/
private theorem diagAll [Infinite E] {H : Type} [Group H] (χ : Fin 4 → H →* E) (θ : H → E)
    (hθ : ∀ g i, χ i.rev g * χ i g = θ g) (hχ : ∀ i j, i ≠ j → ∃ g, χ i g ≠ χ j g) (r : H →* M4 R)
    (hc : ∀ g h, r g * r h = r h * r g) (hr : ∀ g, (r g).map (π : R →+* E) = Matrix.diagonal fun i => χ i g)
    (hG : ∀ g, IsGSp (algebraMap E R (θ g)) (r g)) :
    ∃ u : M4 R, u.map (π : R →+* E) = 1 ∧ IsGSp 1 u ∧ ∀ g, ∃ d, r g * u = u * Matrix.diagonal d := by
  obtain ⟨x, hx⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists (K := E) (M := H →₀ E)
    (fun ij : {ij : Fin 4 × Fin 4 // ij.1 ≠ ij.2} =>
      Finsupp.linearCombination E (fun g => χ ij.1.1 g) - Finsupp.linearCombination E (fun g => χ ij.1.2 g))
    (fun ij => by
      obtain ⟨g, hg⟩ := hχ _ _ ij.2
      exact ⟨Finsupp.single g 1, by simpa [sub_ne_zero] using hg⟩)
  obtain ⟨u, t, hu, hX, ht⟩ := diagX π hπ (Finsupp.linearCombination E (fun g => r g) x)
    (fun i => Finsupp.linearCombination E (fun g => χ i g) x)
    (fun i j h => by
      by_contra hij
      exact hx ⟨(i, j), hij⟩ (sub_eq_zero.2 h))
    (by
      clear hx
      ext i j
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
        simp only [map_add, ← Matrix.diagonal_add, Matrix.add_apply, Matrix.map_apply] at ha hb ⊢
        rw [ha, hb]
      | single g a =>
        have := congrFun (congrFun (hr g) i) j
        simp only [Matrix.map_apply, RingHom.coe_coe, Finsupp.linearCombination_single, Matrix.smul_apply,
          map_smul] at this ⊢
        rw [this]
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, h])
  have hXc : ∀ (y : H →₀ E) g, r g * Finsupp.linearCombination E (fun g => r g) y =
      Finsupp.linearCombination E (fun g => r g) y * r g := fun y g => by
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, mul_add, add_mul, ha, hb]
    | single g a => simp [hc]
  obtain ⟨U, rfl⟩ : IsUnit u := unit_mat π hπ (by rw [hu]; simp)
  have hd : ∀ g, ∃ d, r g * (U : M4 R) = (U : M4 R) * Matrix.diagonal d := fun g => by
    have h1 : ((U⁻¹ : (M4 R)ˣ) * r g * U : M4 R) * Matrix.diagonal t =
        Matrix.diagonal t * ((U⁻¹ : (M4 R)ˣ) * r g * U : M4 R) := by
      have h2 : Matrix.diagonal t * (U⁻¹ : (M4 R)ˣ) = (U⁻¹ : (M4 R)ˣ) * Finsupp.linearCombination E (fun g => r g) x := by
        rw [Units.mul_inv_eq_iff_eq_mul, mul_assoc, hX, Units.inv_mul_cancel_left]
      rw [mul_assoc, ← hX, ← mul_assoc, ← mul_assoc, ← mul_assoc, h2, mul_assoc (U⁻¹ : (M4 R)ˣ).1, hXc, ← mul_assoc]
    have h3 : ((U⁻¹ : (M4 R)ˣ) * r g * U : M4 R).IsDiag := fun i j hij => by
      have h4 := congrFun (congrFun h1 i) j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h4
      have h5 : IsUnit (t i - t j) := unit_of π hπ (by
        rw [map_sub, ht, ht]
        exact hx ⟨(i, j), hij⟩)
      exact h5.mul_right_eq_zero.1 (by linear_combination -h4)
    exact ⟨_, by rw [h3.diagonal_diag, mul_assoc, Units.mul_inv_cancel_left]⟩
  have hS : (adj (U : M4 R) * U).IsDiag := fun i j hij => by
    obtain ⟨g, hg⟩ := hχ i j hij
    obtain ⟨d, hd⟩ := hd g
    have h1 : ∀ a, π (d a) = χ a g := fun a => by
      have := congrArg (fun M : M4 R => M.map (π : R →+* E)) hd
      simp only [Matrix.map_mul, hu, hr, Matrix.diagonal_map (map_zero _), mul_one, one_mul] at this
      exact (congrFun (Matrix.diagonal_injective this) a).symm
    have h2 : adj (Matrix.diagonal d) * (adj (U : M4 R) * U) * Matrix.diagonal d =
        algebraMap E R (θ g) • (adj (U : M4 R) * U) := by
      have h3 : adj (r g) * r g = _ := hG g
      rw [← mul_assoc, ← adj_mul, ← hd, mul_assoc, ← hd, adj_mul, mul_assoc, ← mul_assoc (adj (r g)), h3]
      simp
    have h4 := congrFun (congrFun h2 i) j
    rw [adj_diag, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul] at h4
    have h5 : IsUnit (d i.rev * d j - algebraMap E R (θ g)) := unit_of π hπ (by
      rw [map_sub, map_mul, h1, h1, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, ← hθ g i, ← mul_sub]
      refine mul_ne_zero (fun h => ?_) (sub_ne_zero.2 hg.symm)
      have := map_mul (χ i.rev) g g⁻¹
      simp [h] at this)
    exact h5.mul_right_eq_zero.1 (by linear_combination h4)
  obtain ⟨s, hs⟩ : ∃ s, adj (U : M4 R) * (U : M4 R) = Matrix.diagonal s := ⟨_, hS.diagonal_diag.symm⟩
  have hs1 : ∀ i, π (s i) = 1 := fun i => by
    have := congrArg (fun M : M4 R => M.map (π : R →+* E)) hs
    simp only [Matrix.map_mul, ← adj_map, hu, adj_one, Matrix.diagonal_map (map_zero _), mul_one] at this
    simpa using (congrFun (congrFun this i) i).symm
  have hs2 : ∀ i, s i.rev = s i := fun i => by
    have := congrArg adj hs
    rw [adj_mul, adj_adj, hs, adj_diag] at this
    exact (congrFun (Matrix.diagonal_injective this) i).symm
  obtain ⟨a, ha⟩ := (unit_of π hπ (a := s 0) (by simp [hs1])).exists_right_inv
  obtain ⟨b, hb⟩ := (unit_of π hπ (a := s 1) (by simp [hs1])).exists_right_inv
  have ha1 : π a = 1 := by simpa [hs1] using congrArg π ha
  have hb1 : π b = 1 := by simpa [hs1] using congrArg π hb
  refine ⟨(U : M4 R) * Matrix.diagonal ![1, 1, b, a], ?_, ?_, fun g => ?_⟩
  · rw [Matrix.map_mul, hu, one_mul, Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [ha1, hb1]
  · show _ = _
    rw [adj_mul, mul_assoc, ← mul_assoc (adj _) _ (Matrix.diagonal _), hs, adj_diag, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, one_smul, ← Matrix.diagonal_one]
    congr 1
    ext i
    have e3 : s 3 = s 0 := hs2 0
    have e2 : s 2 = s 1 := hs2 1
    fin_cases i <;> simp [Fin.rev, e2, e3, ha, hb, mul_comm a, mul_comm b]
  · obtain ⟨d, hd⟩ := hd g
    refine ⟨d, ?_⟩
    rw [← mul_assoc, hd, mul_assoc, mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp only [mul_comm]

include hπ in
/- English proof (translation)
Establish `h2' : adj u' * u' = 1` using `by simpa [IsGSp] using h2`. Establish `hm : (u' + 1).map (π' : R' →+* E) = (2 : E) • (1 : M4 E)`. Rewrite using `[← RingHom.mapMatrix_apply, map_add, map_one, RingHom.mapMatrix_apply, h1, two_smul]`. Take `⟨W, hW⟩` from `(unit_mat π' hπ' (M := u' + 1) (by rw [hm]; simp)).exists_left_inv`. Establish `hW' : (u' + 1) * W = 1` using `mul_eq_one_comm.1 hW`.

Establish `hY : adj ((u' - 1) * W) = -((u' - 1) * W)`. Establish `e : (adj u' - 1) * (u' + 1) = -((adj u' + 1) * (u' - 1))`. Simplify using `only [sub_mul, mul_add, add_mul, mul_sub, h2', mul_one, one_mul]`. Normalize the expressions using the abelian group laws. Establish `e2 : adj W * (adj u' + 1) = 1` using `by rw [← adj_one, ← adj_add, ← adj_mul, hW', adj_one]`.

Establish `e3 : adj u' - 1 = (adj u' - 1) * (u' + 1) * W` using `by rw [mul_assoc, hW', mul_one]`. Rewrite using `[adj_mul, adj_sub, adj_one, e3, e, neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, e2, one_mul]`. Establish `hY2 : 1 + (u' - 1) * W = u' * (1 - (u' - 1) * W)` using `by nth_rw 1 [← hW'] nth_rw 3 [← hW'] noncomm_ring`. Establish `hY3 : ((u' - 1) * W).map (π' : R' →+* E) = 0`. Rewrite using `[← RingHom.mapMatrix_apply, map_mul, map_sub, map_one, RingHom.mapMatrix_apply, h1, sub_self, zero_mul]`.

Generalize the expression as in `(u' - 1) * W = Y' at hY hY2 hY3`. Take `⟨Y, hY4, hY5⟩ : ∃ Y : M4 R, Y.map (p : R →+* R') = Y' ∧ adj Y = -Y` from `by choose s hs using hp`. Establish `e : (Y'.map s).map (p : R →+* R') = Y'`. Use extensionality with `i j`. Conclude with `hs _`.

Use `⟨algebraMap E R 2⁻¹ • (Y'.map s - adj (Y'.map s)), ?_, by rw [adj_smul, adj_sub, adj_adj, ← smul_neg, neg_sub]⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_smul' _ _ _ (map_mul _), ← RingHom.mapMatrix_apply, map_sub, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← adj_map, e, hY, sub_neg_eq_add, ← two_smul E, RingHom.coe_coe, AlgHom.commutes, algebraMap_smul, smul_smul]`. Simplify using the standard rewrite rules. Establish `hY6 : Y.map (π : R →+* E) = 0`. Rewrite using `[← hY3, ← hY4, ← hc]`.

Both sides reduce to the same expression. Take `⟨Z, hZ⟩` from `(unit_mat π hπ (M := 1 - Y) (by`. Rewrite using `[← RingHom.mapMatrix_apply, map_sub, map_one, RingHom.mapMatrix_apply, hY6]`. Use the proof step `simp)).exists_right_inv`. Use `⟨(1 + Y) * Z, ?_, ?_⟩` and prove the remaining obligations.

Establish `e` using `congrArg (p : R →+* R').mapMatrix hZ`. Rewrite `e` using `[map_mul, map_sub, map_one, RingHom.mapMatrix_apply, hY4]`. Rewrite using `[← RingHom.mapMatrix_apply, map_mul, map_add, map_one, RingHom.mapMatrix_apply _ Y, hY4, hY2, mul_assoc, e, mul_one]`. Use `show _ = _`. Establish `e : (1 + -Y) * (1 + Y) = (1 + Y) * (1 - Y)` using `by noncomm_ring`.

Establish `e2 : adj Z * (1 + Y) = 1`. Use `congrArg adj hZ` as an intermediate fact. Rewrite `this` using `[adj_mul, adj_sub, adj_one, hY5, sub_neg_eq_add]`. Then use the resulting hypothesis. Rewrite using `[adj_mul, adj_add, adj_one, hY5, one_smul, mul_assoc, ← mul_assoc (1 + -Y), e, mul_assoc, hZ, mul_one, e2]`.
-/
private theorem liftSp [CharZero E] [Algebra E R'] (π' : R' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a)
    (p : R →ₐ[E] R') (hp : Function.Surjective p) (hc : π'.comp p = π) (u' : M4 R')
    (h1 : u'.map (π' : R' →+* E) = 1) (h2 : IsGSp 1 u') : ∃ u : M4 R, u.map (p : R →+* R') = u' ∧ IsGSp 1 u := by
  have h2' : adj u' * u' = 1 := by simpa [IsGSp] using h2
  have hm : (u' + 1).map (π' : R' →+* E) = (2 : E) • (1 : M4 E) := by
    rw [← RingHom.mapMatrix_apply, map_add, map_one, RingHom.mapMatrix_apply, h1, two_smul]
  obtain ⟨W, hW⟩ := (unit_mat π' hπ' (M := u' + 1) (by rw [hm]; simp)).exists_left_inv
  have hW' : (u' + 1) * W = 1 := mul_eq_one_comm.1 hW
  have hY : adj ((u' - 1) * W) = -((u' - 1) * W) := by
    have e : (adj u' - 1) * (u' + 1) = -((adj u' + 1) * (u' - 1)) := by
      simp only [sub_mul, mul_add, add_mul, mul_sub, h2', mul_one, one_mul]
      abel
    have e2 : adj W * (adj u' + 1) = 1 := by rw [← adj_one, ← adj_add, ← adj_mul, hW', adj_one]
    have e3 : adj u' - 1 = (adj u' - 1) * (u' + 1) * W := by rw [mul_assoc, hW', mul_one]
    rw [adj_mul, adj_sub, adj_one, e3, e, neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, e2, one_mul]
  have hY2 : 1 + (u' - 1) * W = u' * (1 - (u' - 1) * W) := by
    nth_rw 1 [← hW']
    nth_rw 3 [← hW']
    noncomm_ring
  have hY3 : ((u' - 1) * W).map (π' : R' →+* E) = 0 := by
    rw [← RingHom.mapMatrix_apply, map_mul, map_sub, map_one, RingHom.mapMatrix_apply, h1, sub_self, zero_mul]
  generalize (u' - 1) * W = Y' at hY hY2 hY3
  obtain ⟨Y, hY4, hY5⟩ : ∃ Y : M4 R, Y.map (p : R →+* R') = Y' ∧ adj Y = -Y := by
    choose s hs using hp
    have e : (Y'.map s).map (p : R →+* R') = Y' := by
      ext i j
      exact hs _
    refine ⟨algebraMap E R 2⁻¹ • (Y'.map s - adj (Y'.map s)), ?_, by rw [adj_smul, adj_sub, adj_adj, ← smul_neg, neg_sub]⟩
    rw [Matrix.map_smul' _ _ _ (map_mul _), ← RingHom.mapMatrix_apply, map_sub, RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, ← adj_map, e, hY, sub_neg_eq_add, ← two_smul E, RingHom.coe_coe, AlgHom.commutes,
      algebraMap_smul, smul_smul]
    simp
  have hY6 : Y.map (π : R →+* E) = 0 := by
    rw [← hY3, ← hY4, ← hc]
    rfl
  obtain ⟨Z, hZ⟩ := (unit_mat π hπ (M := 1 - Y) (by
    rw [← RingHom.mapMatrix_apply, map_sub, map_one, RingHom.mapMatrix_apply, hY6]; simp)).exists_right_inv
  refine ⟨(1 + Y) * Z, ?_, ?_⟩
  · have e := congrArg (p : R →+* R').mapMatrix hZ
    rw [map_mul, map_sub, map_one, RingHom.mapMatrix_apply, hY4] at e
    rw [← RingHom.mapMatrix_apply, map_mul, map_add, map_one, RingHom.mapMatrix_apply _ Y, hY4, hY2, mul_assoc, e, mul_one]
  · show _ = _
    have e : (1 + -Y) * (1 + Y) = (1 + Y) * (1 - Y) := by noncomm_ring
    have e2 : adj Z * (1 + Y) = 1 := by
      have := congrArg adj hZ
      rwa [adj_mul, adj_sub, adj_one, hY5, sub_neg_eq_add] at this
    rw [adj_mul, adj_add, adj_one, hY5, one_smul, mul_assoc, ← mul_assoc (1 + -Y), e, mul_assoc, hZ, mul_one, e2]

end Mat

/- English proof (translation)
Use `haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective`. Use `letI : Algebra ℚ B := ((algebraMap ℚ_[l] B).comp (algebraMap ℚ ℚ_[l])).toAlgebra`. Use `letI : Algebra ℚ B' := ((algebraMap ℚ_[l] B').comp (algebraMap ℚ ℚ_[l])).toAlgebra`. Use `letI := moduleTopology ℚ_[l] B`. Use `letI := moduleTopology ℚ_[l] B'`.

Use `haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩`. Use `haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩`. Use `haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B`. Use `haveI : IsTopologicalRing B' := IsModuleTopology.isTopologicalRing ℚ_[l] B'`. Use `haveI : IsNoetherianRing B := isNoetherian_of_tower ℚ_[l] inferInstance`.

Use `haveI : IsNoetherianRing B' := isNoetherian_of_tower ℚ_[l] inferInstance`. Take `⟨n, hn⟩ : IsNilpotent (RingHom.ker π)` from `(Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).2 hπ`. Take `⟨n', hn'⟩ : IsNilpotent (RingHom.ker π')` from `(Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).2 hπ'`. Take `⟨s, hs⟩` from `p.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)`. Establish `hs1 : ∀ x, p (s x) = x` using `LinearMap.congr_fun hs`.

Establish `hs2 : Continuous s` using `IsModuleTopology.continuous_of_linearMap (s.restrictScalars ℚ_[l])`. Establish `hpπ : ∀ x, π' (p x) = π x` using `fun x => by rw [← hpc]; rfl`. Establish `hr'c : Continuous r'` using `continuous_matrix hcont`. Establish `hχc : ∀ i, (Continuous fun g => algebraMap E B (χ i g)) ∧ Continuous fun g => algebraMap E B' (χ i g)` using `fun i => by`. Establish `e : ∀ g, χ i g = π' (r' g i i)` using `fun g => by simpa using (congrFun (congrFun (hr g) i) i).symm`.

Simplify using `only [e]`. Conclude with `⟨(IsModuleTopology.continuous_of_linearMap ((Algebra.linearMap E B ∘ₗ π'.toLinearMap).restrictScalars ℚ_[l])).comp (hcont i i), (IsModuleTopology.continuous_of_linearMap ((Algebra.linearMap E B' ∘ₗ π'.toLinearMap).restrictScalars ℚ_[l])).comp (hcont i i)⟩`. Take `⟨u', hu1, hu2, hu3⟩` from `diagAll π' hπ' χ θ hθ hχ r' hc hr hG`. Take `⟨u, hu4, hu5⟩` from `liftSp π hπ π' hπ' p hp hpc u' hu1 hu2`. Establish `a1 : adj u' * u' = 1` using `by simpa [IsGSp] using hu2`.

Establish `a2 : u' * adj u' = 1` using `mul_eq_one_comm.1 a1`. Establish `b1 : adj u * u = 1` using `by simpa [IsGSp] using hu5`. Establish `b2 : u * adj u = 1` using `mul_eq_one_comm.1 b1`. Use `choose d hd using hu3`. Establish `hd1 : ∀ g, Matrix.diagonal (d g) = adj u' * r' g * u'` using `fun g => by`.

Rewrite using `[mul_assoc, hd, ← mul_assoc, a1, one_mul]`. Establish `hd2 : ∀ g i, d g i = (adj u' * r' g * u') i i` using `fun g i => by rw [← hd1, Matrix.diagonal_apply_eq]`. Establish `hd3 : ∀ g, r' g = 1 → ∀ i, d g i = 1` using `fun g hg i => by rw [hd2, hg, mul_one, a1, Matrix.one_apply_eq]`. Establish `hd4 : ∀ g h i, d (g * h) i = d g i * d h i` using `fun g h i => by`. Establish `: Matrix.diagonal (d (g * h)) = Matrix.diagonal (d g) * Matrix.diagonal (d h)`.

Rewrite using `[hd1, hd1, hd1, map_mul, mul_assoc _ u', ← mul_assoc u', ← mul_assoc u', a2, one_mul]`. Simplify using `only [mul_assoc]`. Rewrite `this` using `[Matrix.diagonal_mul_diagonal]`. Conclude with `congrFun (Matrix.diagonal_injective this) i`. Establish `hd5 : ∀ g i, π' (d g i) = χ i g` using `fun g i => by`.

Use `congrArg (fun M : M4 B' => M.map (π' : B' →+* E)) (hd g)` as an intermediate fact. Simplify using `only [Matrix.map_mul, hu1, hr, Matrix.diagonal_map (map_zero _), mul_one, one_mul] at this`. Conclude with `(congrFun (Matrix.diagonal_injective this) i).symm`. Establish `hd6 : ∀ g i, d g i.rev * d g i = algebraMap E B' (θ g)` using `fun g i => by`. Establish `h3 : adj (r' g) * r' g = _` using `hG g`.

Establish `: adj (Matrix.diagonal (d g)) * Matrix.diagonal (d g) = algebraMap E B' (θ g) • (1 : M4 B')`. Rewrite using `[hd1, adj_mul, adj_mul, adj_adj, mul_assoc, mul_assoc, ← mul_assoc u', ← mul_assoc u', a2, one_mul, ← mul_assoc (adj (r' g)), h3, smul_mul_assoc, one_mul, mul_smul_comm, a1]`. Rewrite `this` using `[adj_diag, Matrix.diagonal_mul_diagonal]`. Simplify using `using congrFun (congrFun this i) i`. Establish `hχ1 : ∀ i g, χ i g * χ i g⁻¹ = 1` using `fun i g => by rw [← map_mul, mul_inv_cancel, map_one]`.

Establish `hχ2 : ∀ g, r' g = 1 → ∀ i, χ i g = 1` using `fun g hg i => by rw [← hd5, hd3 g hg, map_one]`. Establish `hf : ∀ i, ∃ f : H →* B, Continuous f ∧ (∀ g, p (f g) = d g i * algebraMap E B' (χ i g⁻¹)) ∧ ∀ g, r' g = 1 → f g = 1` using `fun i => by`. Take `⟨f, h1, h2, h3⟩` from `liftChar hn hn' (p : B →+* B') s.toAddMonoidHom hs2 hs1 (fun x hx => by show π (s x) = 0`. Rewrite using `[← hpπ, hs1]`. Conclude with `hx)`.

Use the proof step `⟨⟨fun g => d g i * algebraMap E B' (χ i g⁻¹), by simp [hd3 1 (map_one r')]⟩, fun a b => by`. Simplify using `only [hd4, mul_inv_rev, map_mul]`. Use the proof step `ring⟩`. Use the proof step `(by show Continuous fun g => d g i * algebraMap E B' (χ i g⁻¹)`. Simplify using `only [hd2]`.

Conclude with `(((continuous_const.mul hr'c).mul continuous_const).matrix_elem i i).mul ((hχc i).2.comp continuous_inv))`. Use the proof step `(fun g => by show π' (d g i * algebraMap E B' (χ i g⁻¹) - 1) = 0`. Rewrite using `[map_sub, map_mul, hd5, AlgHom.commutes, map_one]`. Conclude with `sub_eq_zero.2 (hχ1 i g))`. Use `⟨f, h1, h2, fun g hg => h3 g ?_⟩` and prove the remaining obligations.

Use `show d g i * algebraMap E B' (χ i g⁻¹) = 1`. Use `hχ1 i g` as an intermediate fact. Rewrite `this` using `[hχ2 g hg, one_mul]`. Rewrite using `[hd3 g hg, this, map_one, one_mul]`. Use `choose f hf1 hf2 hf3 using hf`.

Establish `hf4 : ∀ i g, f i g * f i g⁻¹ = 1` using `fun i g => by rw [← map_mul, mul_inv_cancel, map_one]`. Choose the witnesses or unpack the hypotheses as in `⟨F, hF1, hF2, hF3, hF4, hF5⟩ : ∃ F : H → Fin 4 → B, Continuous F ∧ (∀ g h, F (g * h) = F g * F h) ∧ (∀ g i, F g i.rev * F g i = 1) ∧ (∀ g, r' g = 1 → F g = 1) ∧ ∀ g i, algebraMap E B' (χ i g) * p (F g i) = d g i := by`. Use `⟨fun g => ![f 0 g, f 1 g, f 1 g⁻¹, f 0 g⁻¹], ?_, fun g h => ?_, fun g i => ?_, fun g hg => ?_, fun g i => ?_⟩` and prove the remaining obligations. Use `fun_prop`. Apply the tactic sequence `ext i fin_cases i <;> simp [mul_comm]`.

Use `fin_cases i exacts [(mul_comm _ _).trans (hf4 0 g), (mul_comm _ _).trans (hf4 1 g), hf4 1 g, hf4 0 g]`. Establish `: r' g⁻¹ = 1`. Use `map_mul r' g g⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, map_one, hg, one_mul]`. Conclude with `this.symm`.

Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp [hf3 _ _ hg, hf3 _ _ this]`. Establish `e1 : ∀ i, algebraMap E B' (χ i g) * p (f i g) = d g i` using `fun i => by`. Rewrite using `[hf2, mul_left_comm, ← map_mul, hχ1, map_one, mul_one]`. Establish `e2 : ∀ i : Fin 4, algebraMap E B' (χ i.rev g) * p (f i g⁻¹) = d g i.rev` using `fun i => by`.

Rewrite using `[hf2, inv_inv, mul_left_comm, ← map_mul, hθ, ← hd6 g i, mul_left_comm, ← hd4, inv_mul_cancel, hd3 1 (map_one r'), mul_one]`. Use `fin_cases i`. Use `exacts [e1 0, e1 1, e2 1, e2 0]`. Establish `h1 : ∀ g, r' g = 1 → u * (Matrix.diagonal fun i => algebraMap E B (χ i g) * F g i) * adj u = 1` using `fun g hg => by`. Simplify using `[hχ2 g hg, hF4 g hg, b2]`.

Use `⟨⟨⟨fun g => u * (Matrix.diagonal fun i => algebraMap E B (χ i g) * F g i) * adj u, h1 1 (map_one r')⟩, fun g h => ?_⟩, fun a b => ?_, fun g => ?_, h1, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc _ (adj u), ← mul_assoc (adj u), ← mul_assoc (adj u), b1, one_mul, ← mul_assoc, mul_assoc u, Matrix.diagonal_mul_diagonal]`. Simplify using `only [map_mul, hF2, Pi.mul_apply, mul_mul_mul_comm]`. Conclude with `((continuous_const.mul (continuous_pi fun i => (hχc i).1.mul ((continuous_apply i).comp hF1)).matrix_diagonal).mul continuous_const).matrix_elem a b`. Use `show adj (u * _ * adj u) * (u * _ * adj u) = _`.

Rewrite using `[adj_mul, adj_mul, adj_adj, adj_diag, mul_assoc, mul_assoc, ← mul_assoc (adj u), ← mul_assoc (adj u), b1, one_mul, ← mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]`. Establish `e : ∀ i : Fin 4, algebraMap E B (χ i.rev g) * F g i.rev * (algebraMap E B (χ i g) * F g i) = algebraMap E B (θ g)` using `fun i => by rw [mul_mul_mul_comm, ← map_mul, hθ, hF3, mul_one]`. Simplify using `only [e]`. Rewrite using `[← Matrix.smul_one_eq_diagonal, smul_mul_assoc, one_mul, mul_smul_comm, b2]`. Use `show (u * _ * adj u).map _ = _`.

Rewrite using `[Matrix.map_mul, Matrix.map_mul, ← adj_map, hu4, Matrix.diagonal_map (map_zero _)]`. Simplify using `only [map_mul, RingHom.coe_coe, AlgHom.commutes, hF5]`. Rewrite using `[← hd, mul_assoc, a2, mul_one]`.
-/
private theorem core {l : ℕ} [Fact l.Prime] {H E B B' : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E]
    [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B]
    [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra E B'] [IsScalarTower ℚ_[l] E B']
    (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a)
    (p : B →ₐ[E] B') (hp : Function.Surjective p) (hpc : π'.comp p = π)
    (χ : Fin 4 → H →* E) (θ : H → E)
    (hθ : ∀ g i, χ i.rev g * χ i g = θ g) (hχ : ∀ i j, i ≠ j → ∃ g, χ i g ≠ χ j g) (r' : H →* M4 B')
    (hc : ∀ g h, r' g * r' h = r' h * r' g) (hr : ∀ g, (r' g).map (π' : B' →+* E) = Matrix.diagonal fun i => χ i g)
    (hG : ∀ g, IsGSp (algebraMap E B' (θ g)) (r' g)) (hcont : ∀ a b, QCont l fun g => r' g a b) :
    ∃ r : H →* M4 B, (∀ a b, QCont l fun g => r g a b) ∧ (∀ g, IsGSp (algebraMap E B (θ g)) (r g)) ∧
      (∀ g, r' g = 1 → r g = 1) ∧ ∀ g, (r g).map (p : B →+* B') = r' g := by
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  letI : Algebra ℚ B := ((algebraMap ℚ_[l] B).comp (algebraMap ℚ ℚ_[l])).toAlgebra
  letI : Algebra ℚ B' := ((algebraMap ℚ_[l] B').comp (algebraMap ℚ ℚ_[l])).toAlgebra
  letI := moduleTopology ℚ_[l] B
  letI := moduleTopology ℚ_[l] B'
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  haveI : IsTopologicalRing B' := IsModuleTopology.isTopologicalRing ℚ_[l] B'
  haveI : IsNoetherianRing B := isNoetherian_of_tower ℚ_[l] inferInstance
  haveI : IsNoetherianRing B' := isNoetherian_of_tower ℚ_[l] inferInstance
  obtain ⟨n, hn⟩ : IsNilpotent (RingHom.ker π) :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).2 hπ
  obtain ⟨n', hn'⟩ : IsNilpotent (RingHom.ker π') :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).2 hπ'
  obtain ⟨s, hs⟩ := p.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
  have hs1 : ∀ x, p (s x) = x := LinearMap.congr_fun hs
  have hs2 : Continuous s := IsModuleTopology.continuous_of_linearMap (s.restrictScalars ℚ_[l])
  have hpπ : ∀ x, π' (p x) = π x := fun x => by rw [← hpc]; rfl
  have hr'c : Continuous r' := continuous_matrix hcont
  have hχc : ∀ i, (Continuous fun g => algebraMap E B (χ i g)) ∧ Continuous fun g => algebraMap E B' (χ i g) := fun i => by
    have e : ∀ g, χ i g = π' (r' g i i) := fun g => by simpa using (congrFun (congrFun (hr g) i) i).symm
    simp only [e]
    exact ⟨(IsModuleTopology.continuous_of_linearMap
      ((Algebra.linearMap E B ∘ₗ π'.toLinearMap).restrictScalars ℚ_[l])).comp (hcont i i),
      (IsModuleTopology.continuous_of_linearMap
      ((Algebra.linearMap E B' ∘ₗ π'.toLinearMap).restrictScalars ℚ_[l])).comp (hcont i i)⟩
  obtain ⟨u', hu1, hu2, hu3⟩ := diagAll π' hπ' χ θ hθ hχ r' hc hr hG
  obtain ⟨u, hu4, hu5⟩ := liftSp π hπ π' hπ' p hp hpc u' hu1 hu2
  have a1 : adj u' * u' = 1 := by simpa [IsGSp] using hu2
  have a2 : u' * adj u' = 1 := mul_eq_one_comm.1 a1
  have b1 : adj u * u = 1 := by simpa [IsGSp] using hu5
  have b2 : u * adj u = 1 := mul_eq_one_comm.1 b1
  choose d hd using hu3
  have hd1 : ∀ g, Matrix.diagonal (d g) = adj u' * r' g * u' := fun g => by
    rw [mul_assoc, hd, ← mul_assoc, a1, one_mul]
  have hd2 : ∀ g i, d g i = (adj u' * r' g * u') i i := fun g i => by rw [← hd1, Matrix.diagonal_apply_eq]
  have hd3 : ∀ g, r' g = 1 → ∀ i, d g i = 1 := fun g hg i => by rw [hd2, hg, mul_one, a1, Matrix.one_apply_eq]
  have hd4 : ∀ g h i, d (g * h) i = d g i * d h i := fun g h i => by
    have : Matrix.diagonal (d (g * h)) = Matrix.diagonal (d g) * Matrix.diagonal (d h) := by
      rw [hd1, hd1, hd1, map_mul, mul_assoc _ u', ← mul_assoc u', ← mul_assoc u', a2, one_mul]
      simp only [mul_assoc]
    rw [Matrix.diagonal_mul_diagonal] at this
    exact congrFun (Matrix.diagonal_injective this) i
  have hd5 : ∀ g i, π' (d g i) = χ i g := fun g i => by
    have := congrArg (fun M : M4 B' => M.map (π' : B' →+* E)) (hd g)
    simp only [Matrix.map_mul, hu1, hr, Matrix.diagonal_map (map_zero _), mul_one, one_mul] at this
    exact (congrFun (Matrix.diagonal_injective this) i).symm
  have hd6 : ∀ g i, d g i.rev * d g i = algebraMap E B' (θ g) := fun g i => by
    have h3 : adj (r' g) * r' g = _ := hG g
    have : adj (Matrix.diagonal (d g)) * Matrix.diagonal (d g) = algebraMap E B' (θ g) • (1 : M4 B') := by
      rw [hd1, adj_mul, adj_mul, adj_adj, mul_assoc, mul_assoc, ← mul_assoc u', ← mul_assoc u', a2, one_mul,
        ← mul_assoc (adj (r' g)), h3, smul_mul_assoc, one_mul, mul_smul_comm, a1]
    rw [adj_diag, Matrix.diagonal_mul_diagonal] at this
    simpa using congrFun (congrFun this i) i
  have hχ1 : ∀ i g, χ i g * χ i g⁻¹ = 1 := fun i g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hχ2 : ∀ g, r' g = 1 → ∀ i, χ i g = 1 := fun g hg i => by rw [← hd5, hd3 g hg, map_one]
  have hf : ∀ i, ∃ f : H →* B, Continuous f ∧ (∀ g, p (f g) = d g i * algebraMap E B' (χ i g⁻¹)) ∧
      ∀ g, r' g = 1 → f g = 1 := fun i => by
    obtain ⟨f, h1, h2, h3⟩ := liftChar hn hn' (p : B →+* B') s.toAddMonoidHom hs2 hs1
      (fun x hx => by
        show π (s x) = 0
        rw [← hpπ, hs1]
        exact hx)
      ⟨⟨fun g => d g i * algebraMap E B' (χ i g⁻¹), by simp [hd3 1 (map_one r')]⟩, fun a b => by
        simp only [hd4, mul_inv_rev, map_mul]
        ring⟩
      (by
        show Continuous fun g => d g i * algebraMap E B' (χ i g⁻¹)
        simp only [hd2]
        exact (((continuous_const.mul hr'c).mul continuous_const).matrix_elem i i).mul
          ((hχc i).2.comp continuous_inv))
      (fun g => by
        show π' (d g i * algebraMap E B' (χ i g⁻¹) - 1) = 0
        rw [map_sub, map_mul, hd5, AlgHom.commutes, map_one]
        exact sub_eq_zero.2 (hχ1 i g))
    refine ⟨f, h1, h2, fun g hg => h3 g ?_⟩
    show d g i * algebraMap E B' (χ i g⁻¹) = 1
    have := hχ1 i g
    rw [hχ2 g hg, one_mul] at this
    rw [hd3 g hg, this, map_one, one_mul]
  choose f hf1 hf2 hf3 using hf
  have hf4 : ∀ i g, f i g * f i g⁻¹ = 1 := fun i g => by rw [← map_mul, mul_inv_cancel, map_one]
  obtain ⟨F, hF1, hF2, hF3, hF4, hF5⟩ : ∃ F : H → Fin 4 → B, Continuous F ∧ (∀ g h, F (g * h) = F g * F h) ∧
      (∀ g i, F g i.rev * F g i = 1) ∧ (∀ g, r' g = 1 → F g = 1) ∧
      ∀ g i, algebraMap E B' (χ i g) * p (F g i) = d g i := by
    refine ⟨fun g => ![f 0 g, f 1 g, f 1 g⁻¹, f 0 g⁻¹], ?_, fun g h => ?_, fun g i => ?_, fun g hg => ?_, fun g i => ?_⟩
    · fun_prop
    · ext i
      fin_cases i <;> simp [mul_comm]
    · fin_cases i
      exacts [(mul_comm _ _).trans (hf4 0 g), (mul_comm _ _).trans (hf4 1 g), hf4 1 g, hf4 0 g]
    · have : r' g⁻¹ = 1 := by
        have := map_mul r' g g⁻¹
        rw [mul_inv_cancel, map_one, hg, one_mul] at this
        exact this.symm
      ext i
      fin_cases i <;> simp [hf3 _ _ hg, hf3 _ _ this]
    · have e1 : ∀ i, algebraMap E B' (χ i g) * p (f i g) = d g i := fun i => by
        rw [hf2, mul_left_comm, ← map_mul, hχ1, map_one, mul_one]
      have e2 : ∀ i : Fin 4, algebraMap E B' (χ i.rev g) * p (f i g⁻¹) = d g i.rev := fun i => by
        rw [hf2, inv_inv, mul_left_comm, ← map_mul, hθ, ← hd6 g i, mul_left_comm, ← hd4, inv_mul_cancel,
          hd3 1 (map_one r'), mul_one]
      fin_cases i
      exacts [e1 0, e1 1, e2 1, e2 0]
  have h1 : ∀ g, r' g = 1 → u * (Matrix.diagonal fun i => algebraMap E B (χ i g) * F g i) * adj u = 1 := fun g hg => by
    simp [hχ2 g hg, hF4 g hg, b2]
  refine ⟨⟨⟨fun g => u * (Matrix.diagonal fun i => algebraMap E B (χ i g) * F g i) * adj u, h1 1 (map_one r')⟩,
    fun g h => ?_⟩, fun a b => ?_, fun g => ?_, h1, fun g => ?_⟩
  · rw [mul_assoc _ (adj u), ← mul_assoc (adj u), ← mul_assoc (adj u), b1, one_mul, ← mul_assoc, mul_assoc u,
      Matrix.diagonal_mul_diagonal]
    simp only [map_mul, hF2, Pi.mul_apply, mul_mul_mul_comm]
  · exact ((continuous_const.mul (continuous_pi fun i => (hχc i).1.mul
      ((continuous_apply i).comp hF1)).matrix_diagonal).mul continuous_const).matrix_elem a b
  · show adj (u * _ * adj u) * (u * _ * adj u) = _
    rw [adj_mul, adj_mul, adj_adj, adj_diag, mul_assoc, mul_assoc, ← mul_assoc (adj u), ← mul_assoc (adj u), b1, one_mul,
      ← mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    have e : ∀ i : Fin 4, algebraMap E B (χ i.rev g) * F g i.rev * (algebraMap E B (χ i g) * F g i) =
        algebraMap E B (θ g) := fun i => by rw [mul_mul_mul_comm, ← map_mul, hθ, hF3, mul_one]
    simp only [e]
    rw [← Matrix.smul_one_eq_diagonal, smul_mul_assoc, one_mul, mul_smul_comm, b2]
  · show (u * _ * adj u).map _ = _
    rw [Matrix.map_mul, Matrix.map_mul, ← adj_map, hu4, Matrix.diagonal_map (map_zero _)]
    simp only [map_mul, RingHom.coe_coe, AlgHom.commutes, hF5]
    rw [← hd, mul_assoc, a2, mul_one]

end UpperTheory.V.Loc.RankFourLocalLifting

open UpperTheory.V.Loc.RankFourLocalLifting in
/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD q hq E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hpc r' hL hE`. Take `⟨-, f2, -, -, f5, f6, -⟩` from `UpperTheory.V.GradeZeroInterpolatingElement.facts D hD`. Take `⟨⟨τ, hτ, hτ1, -⟩, hab⟩` from `UpperTheory.V.GradeZeroInterpolatingElement.abP D hD q hq`. Take `⟨hσ, -, hσ1⟩` from `f2 q (Finset.mem_insert_of_mem hq)`. Take `⟨t1, t2, t3⟩` from `f5 q hq τ hτ`.

Establish `hinj : Function.Injective (algebraMap c.O E)` using `IsFractionRing.injective _ _`. Set `χ : Fin 4 → D.Gp q →* E` to `fun i => (algebraMap c.O E).toMonoidHom.comp ((Units.coeHom c.O).comp ((D.ps i).comp (D.Gp q).subtype))`. Establish `hχ : ∀ i (g : D.Gp q), χ i g = algebraMap c.O E (D.ps i g)` using `fun _ _ => rfl`. Establish `hred : ∀ g : D.Gp q, mapRep (algebraMap c.O E) (D.r0At q) g = Matrix.diagonal fun i => χ i g` using `fun g => Matrix.diagonal_map (d := fun i => (D.ps i g : c.O)) (map_zero (algebraMap c.O E))`. Take `⟨r, h1, h2, h3, h4⟩` from `core π hπ π' hπ' p hp hpc χ (fun g => algebraMap c.O E (D.th g)) (fun g i => by rw [hχ, hχ, ← map_mul, ← Units.val_mul, mul_comm, ← MonoidHom.mul_apply, f6]) (fun i j hij => by`.

Distinguish the cases in `h : lamW i = lamW j`. Use `⟨⟨τ, hτ.1⟩, fun e => ?_⟩` and prove the remaining obligations. Establish `e1 : D.ps i τ = D.ps j τ` using `Units.ext (hinj e)`. Use `revert i j`. Simplify using `[Fin.forall_fin_succ, Raw.ps, lamW, t1, t2, t3, hτ1, hτ1.symm]`.

Conclude with `⟨⟨_, hσ⟩, fun e => hσ1 i j h (congrArg (residue c.O) (hinj e))⟩)`. Use the proof step `r' (fun g h => by`. Use `hE.2 (g * h * g⁻¹ * h⁻¹) (hab g g.2 h h.2)` as an intermediate fact. Establish `e : g * h = g * h * g⁻¹ * h⁻¹ * (h * g)` using `by group`. Rewrite using `[← map_mul, e, map_mul, this, one_mul, map_mul])`.

Use the proof step `(fun g => (DFunLike.congr_fun hL.red g).trans (hred g))`. Use the proof step `(fun g => by`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Conclude with `hE.1 g) hL.cont`. Establish `h5 : mapRep (p : B →+* B') r = r'` using `MonoidHom.ext h4`.

Use `⟨r, ⟨?_, h1⟩, ⟨fun g => ?_, fun g hg => h3 g (hE.2 g hg)⟩, h5⟩` and prove the remaining obligations. Rewrite using `[← hL.red, ← h5, ← hpc]`. Both sides reduce to the same expression. Rewrite using `[IsScalarTower.algebraMap_apply c.O E B]`. Conclude with `h2 g`.
-/
theorem UpperTheory.V.Loc.spLiftP :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (q : ℕ), q ∈ D.Sb → ∀ (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra ↥c.O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ↥c.O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ↥c.O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra ↥c.O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ↥c.O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower ↥c.O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ r' : D.Gp q →* M4 B', IsContinuousLiftOfRZero D (π' : B' →+* E) q r' → EqP D q r' → ∃ r : D.Gp q →* M4 B, IsContinuousLiftOfRZero D (π : B →+* E) q r ∧ EqP D q r ∧ mapRep (p : B →+* B') r = r' := by
  intro Ω _ _ _ l _ c D hD q hq E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hpc r' hL hE
  obtain ⟨-, f2, -, -, f5, f6, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  obtain ⟨⟨τ, hτ, hτ1, -⟩, hab⟩ := UpperTheory.V.GradeZeroInterpolatingElement.abP D hD q hq
  obtain ⟨hσ, -, hσ1⟩ := f2 q (Finset.mem_insert_of_mem hq)
  obtain ⟨t1, t2, t3⟩ := f5 q hq τ hτ
  have hinj : Function.Injective (algebraMap c.O E) := IsFractionRing.injective _ _
  let χ : Fin 4 → D.Gp q →* E := fun i =>
    (algebraMap c.O E).toMonoidHom.comp ((Units.coeHom c.O).comp ((D.ps i).comp (D.Gp q).subtype))
  have hχ : ∀ i (g : D.Gp q), χ i g = algebraMap c.O E (D.ps i g) := fun _ _ => rfl
  have hred : ∀ g : D.Gp q, mapRep (algebraMap c.O E) (D.r0At q) g = Matrix.diagonal fun i => χ i g := fun g =>
    Matrix.diagonal_map (d := fun i => (D.ps i g : c.O)) (map_zero (algebraMap c.O E))
  obtain ⟨r, h1, h2, h3, h4⟩ := core π hπ π' hπ' p hp hpc χ (fun g => algebraMap c.O E (D.th g))
    (fun g i => by rw [hχ, hχ, ← map_mul, ← Units.val_mul, mul_comm, ← MonoidHom.mul_apply, f6])
    (fun i j hij => by
      by_cases h : lamW i = lamW j
      · refine ⟨⟨τ, hτ.1⟩, fun e => ?_⟩
        have e1 : D.ps i τ = D.ps j τ := Units.ext (hinj e)
        revert i j
        simp [Fin.forall_fin_succ, Raw.ps, lamW, t1, t2, t3, hτ1, hτ1.symm]
      · exact ⟨⟨_, hσ⟩, fun e => hσ1 i j h (congrArg (residue c.O) (hinj e))⟩)
    r' (fun g h => by
      have := hE.2 (g * h * g⁻¹ * h⁻¹) (hab g g.2 h h.2)
      have e : g * h = g * h * g⁻¹ * h⁻¹ * (h * g) := by group
      rw [← map_mul, e, map_mul, this, one_mul, map_mul])
    (fun g => (DFunLike.congr_fun hL.red g).trans (hred g))
    (fun g => by
      rw [← IsScalarTower.algebraMap_apply]
      exact hE.1 g) hL.cont
  have h5 : mapRep (p : B →+* B') r = r' := MonoidHom.ext h4
  refine ⟨r, ⟨?_, h1⟩, ⟨fun g => ?_, fun g hg => h3 g (hE.2 g hg)⟩, h5⟩
  · rw [← hL.red, ← h5, ← hpc]
    rfl
  · rw [IsScalarTower.algebraMap_apply c.O E B]
    exact h2 g
