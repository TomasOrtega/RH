import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

/- English proof (translation)
Set `S` to `Equiv.Perm.SameCycle.setoid π`. Establish `hk : ∀ x : X, ∃ k : ℕ, (π ^ k) (Quotient.out (Quotient.mk S x)) = x` using `fun x => by`. Establish `hr : π.SameCycle (Quotient.out (Quotient.mk S x)) x` using `Quotient.mk_out (s := S) x`. Take `⟨i, _, hi⟩` from `hr.exists_pow_eq'`. Conclude with `⟨i, hi⟩`.

Use `choose k hk using hk`. Establish `hsame : ∀ y : X, ∀ p q : ℕ, (π ^ p) y = (π ^ q) y → ζ ^ p = ζ ^ q`. Introduce `y p q hpq`. Use `wlog hle : p ≤ q generalizing p q`. Conclude with `(this q p hpq.symm (by omega)).symm`.

Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hle`. Establish `hfix : (π ^ d) ((π ^ p) y) = (π ^ p) y`. Rewrite using `[← Equiv.Perm.mul_apply, ← pow_add, add_comm]`. Conclude with `hpq.symm`. Take `⟨m, rfl⟩` from `(h d _).1 hfix`.

Rewrite using `[pow_add, pow_mul, hζ, one_pow, mul_one]`. Use `⟨fun x => ζ ^ k x, fun x => pow_ne_zero _ hζ0, fun x => ?_⟩` and prove the remaining obligations. Establish `hq : Quotient.mk S (π x) = Quotient.mk S x` using `Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl π x))`. Establish `e1` using `hk (π x)`. Rewrite `e1` using `[hq]`.

Establish `e2 : (π ^ (k x + 1)) (Quotient.out (Quotient.mk S x)) = π x`. Rewrite using `[pow_succ', Equiv.Perm.mul_apply, hk x]`. Use `show ζ ^ k (π x) = ζ * ζ ^ k x`. Rewrite using `[← pow_succ']`. Conclude with `hsame _ _ _ (e1.trans e2.symm)`.
-/
private theorem permDet_weight {X : Type} [Fintype X] [DecidableEq X] (π : Equiv.Perm X) (n : ℕ)
    (h : ∀ (k : ℕ) (x : X), (π ^ k) x = x ↔ n ∣ k) (ζ : ℂ) (hζ : ζ ^ n = 1) (hζ0 : ζ ≠ 0) :
    ∃ c : X → ℂ, (∀ x, c x ≠ 0) ∧ ∀ x, c (π x) = ζ * c x := by
  classical
  let S := Equiv.Perm.SameCycle.setoid π
  have hk : ∀ x : X, ∃ k : ℕ, (π ^ k) (Quotient.out (Quotient.mk S x)) = x := fun x => by
    have hr : π.SameCycle (Quotient.out (Quotient.mk S x)) x := Quotient.mk_out (s := S) x
    obtain ⟨i, _, hi⟩ := hr.exists_pow_eq'
    exact ⟨i, hi⟩
  choose k hk using hk
  have hsame : ∀ y : X, ∀ p q : ℕ, (π ^ p) y = (π ^ q) y → ζ ^ p = ζ ^ q := by
    intro y p q hpq
    wlog hle : p ≤ q generalizing p q
    · exact (this q p hpq.symm (by omega)).symm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hfix : (π ^ d) ((π ^ p) y) = (π ^ p) y := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm]
      exact hpq.symm
    obtain ⟨m, rfl⟩ := (h d _).1 hfix
    rw [pow_add, pow_mul, hζ, one_pow, mul_one]
  refine ⟨fun x => ζ ^ k x, fun x => pow_ne_zero _ hζ0, fun x => ?_⟩
  have hq : Quotient.mk S (π x) = Quotient.mk S x :=
    Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl π x))
  have e1 := hk (π x)
  rw [hq] at e1
  have e2 : (π ^ (k x + 1)) (Quotient.out (Quotient.mk S x)) = π x := by
    rw [pow_succ', Equiv.Perm.mul_apply, hk x]
  show ζ ^ k (π x) = ζ * ζ ^ k x
  rw [← pow_succ']
  exact hsame _ _ _ (e1.trans e2.symm)

/- English proof (translation)
Establish `key : Matrix.diagonal c * (a • (1 : Matrix X X ℂ) - ζ • π.permMatrix ℂ) = (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ) * Matrix.diagonal c`. Use extensionality with `i j`. Simplify using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.diagonal_mul, Matrix.mul_diagonal, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.one_apply]`. Distinguish the cases in `h2 : π i = j`. Substitute `h2` using the available equality.

Rewrite using `[hc]`. Distinguish the cases in `h1 : i = π i`. Establish `e` using `hc i`. Rewrite `e` using `[← h1]`. Establish `hz : ζ = 1` using `mul_right_cancel₀ (hc0 i) (e.symm.trans (one_mul _).symm)`.

Rewrite using `[if_pos h1, if_pos rfl, if_pos rfl, hz]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h1, if_pos rfl, if_pos rfl]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h2, if_neg h2] split_ifs with h1`.

Substitute `h1` using the available equality. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree. Establish `hd : (Matrix.diagonal c).det ≠ 0`. Rewrite using `[Matrix.det_diagonal]`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun x _ => hc0 x`. Use `congrArg Matrix.det key` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, mul_comm ((a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det)]`. Conclude with `mul_left_cancel₀ hd this`.
-/
private theorem permDet_twist {X : Type} [Fintype X] [DecidableEq X] (π : Equiv.Perm X)
    (ζ a : ℂ) (c : X → ℂ) (hc0 : ∀ x, c x ≠ 0) (hc : ∀ x, c (π x) = ζ * c x) :
    (a • (1 : Matrix X X ℂ) - ζ • π.permMatrix ℂ).det = (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det := by
  have key : Matrix.diagonal c * (a • (1 : Matrix X X ℂ) - ζ • π.permMatrix ℂ) =
      (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ) * Matrix.diagonal c := by
    ext i j
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.diagonal_mul, Matrix.mul_diagonal, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Matrix.one_apply]
    by_cases h2 : π i = j
    · subst h2
      rw [hc]
      by_cases h1 : i = π i
      · have e := hc i
        rw [← h1] at e
        have hz : ζ = 1 := mul_right_cancel₀ (hc0 i) (e.symm.trans (one_mul _).symm)
        rw [if_pos h1, if_pos rfl, if_pos rfl, hz]
        ring
      · rw [if_neg h1, if_pos rfl, if_pos rfl]
        ring
    · rw [if_neg h2, if_neg h2]
      split_ifs with h1
      · subst h1
        ring
      · ring
  have hd : (Matrix.diagonal c).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun x _ => hc0 x
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm ((a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det)] at this
  exact mul_left_cancel₀ hd this

/- English proof (translation)
Establish `hpow : ∀ k : ℕ, (π.permMatrix ℂ) ^ k = (π ^ k).permMatrix ℂ`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, pow_zero, Matrix.permMatrix_one]`. Consider the case `succ k ih => rw [pow_succ', pow_succ, Matrix.permMatrix_mul, ih]`.

Establish `hπn : π ^ n = 1` using `Equiv.ext fun x => (h n x).2 dvd_rfl`. Establish `hPn : (π.permMatrix ℂ) ^ n = 1` using `by rw [hpow, hπn, Matrix.permMatrix_one]`. Establish `hprim` using `Complex.isPrimitiveRoot_exp n hn.ne'`. Take `⟨S, hS⟩ : ∃ S, S = Polynomial.nthRootsFinset n (1 : ℂ)` from `⟨_, rfl⟩`. Establish `hcard : S.card = n` using `by rw [hS]; exact hprim.card_nthRootsFinset`.

Establish `hmem : ∀ ζ ∈ S, ζ ^ n = 1` using `fun ζ hζ => by`. Rewrite `hζ` using `[hS]`. Conclude with `(Polynomial.mem_nthRootsFinset hn 1).1 hζ`. Establish `hpt : ∀ t : ℂ, ∏ ζ ∈ S, (a - ζ * t) = a ^ n - t ^ n`. Introduce `t`.

Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Simplify using `[Finset.prod_const, hcard, hn.ne']`. Establish `e` using `congrArg (Polynomial.eval (a / t)) (Polynomial.X_pow_sub_one_eq_prod hn hprim)`. Rewrite `e` using `[← hS]`.

Simplify using `only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_prod, Polynomial.eval_C] at e`. Establish `e2 : ∏ ζ ∈ S, (a - ζ * t) = ∏ ζ ∈ S, (t * (a / t - ζ))` using `Finset.prod_congr rfl fun ζ _ => by field_simp`. Rewrite using `[e2, Finset.prod_mul_distrib, Finset.prod_const, hcard, ← e, div_pow]`. Clear the denominators using the available nonvanishing facts. Establish `hpoly : ∏ ζ ∈ S, (Polynomial.C a - Polynomial.C ζ * Polynomial.X) = Polynomial.C (a ^ n) - Polynomial.X ^ n`.

Apply `Polynomial.funext` to reduce the goal to its premises. Introduce `t`. Simplify using `only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]`. Conclude with `hpt t`. Set `f : Polynomial ℂ →* ℂ` to `Matrix.detMonoidHom.comp (Polynomial.aeval (π.permMatrix ℂ)).toRingHom.toMonoidHom`.

Establish `hf : ∀ q, f q = (Polynomial.aeval (π.permMatrix ℂ) q).det` using `fun q => rfl`. Establish `hdet` using `congrArg f hpoly`. Rewrite `hdet` using `[map_prod, hf]`. Establish `hfac : ∀ ζ ∈ S, f (Polynomial.C a - Polynomial.C ζ * Polynomial.X) = (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det`. Introduce `ζ hζ`.

Establish `hz0 : ζ ≠ 0`. Introduce and unpack `rfl`. Use `hmem 0 hζ` as an intermediate fact. Rewrite `this` using `[zero_pow hn.ne']`. Conclude with `zero_ne_one this`.

Take `⟨c, hc0, hc⟩` from `permDet_weight π n h ζ (hmem ζ hζ) hz0`. Rewrite using `[hf, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]`. Conclude with `permDet_twist π ζ a c hc0 hc`. Rewrite `hdet` using `[Finset.prod_congr rfl hfac, Finset.prod_const, hcard]`. Rewrite using `[hdet, map_sub, Polynomial.aeval_C, Polynomial.aeval_X_pow, hPn, Algebra.algebraMap_eq_smul_one]`.

Establish `e3 : (a ^ n • (1 : Matrix X X ℂ) - 1) = (a ^ n - 1) • (1 : Matrix X X ℂ)`. Rewrite using `[sub_smul, one_smul]`. Rewrite using `[e3, Matrix.det_smul, Matrix.det_one, mul_one]`.
-/
private theorem permDet_pow {X : Type} [Fintype X] [DecidableEq X] (π : Equiv.Perm X) (n : ℕ)
    (hn : 0 < n) (h : ∀ (k : ℕ) (x : X), (π ^ k) x = x ↔ n ∣ k) (a : ℂ) :
    (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det ^ n = (a ^ n - 1) ^ Fintype.card X := by
  classical
  have hpow : ∀ k : ℕ, (π.permMatrix ℂ) ^ k = (π ^ k).permMatrix ℂ := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.permMatrix_one]
    | succ k ih => rw [pow_succ', pow_succ, Matrix.permMatrix_mul, ih]
  have hπn : π ^ n = 1 := Equiv.ext fun x => (h n x).2 dvd_rfl
  have hPn : (π.permMatrix ℂ) ^ n = 1 := by rw [hpow, hπn, Matrix.permMatrix_one]
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨S, hS⟩ : ∃ S, S = Polynomial.nthRootsFinset n (1 : ℂ) := ⟨_, rfl⟩
  have hcard : S.card = n := by rw [hS]; exact hprim.card_nthRootsFinset
  have hmem : ∀ ζ ∈ S, ζ ^ n = 1 := fun ζ hζ => by
    rw [hS] at hζ
    exact (Polynomial.mem_nthRootsFinset hn 1).1 hζ
  have hpt : ∀ t : ℂ, ∏ ζ ∈ S, (a - ζ * t) = a ^ n - t ^ n := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp [Finset.prod_const, hcard, hn.ne']
    · have e := congrArg (Polynomial.eval (a / t)) (Polynomial.X_pow_sub_one_eq_prod hn hprim)
      rw [← hS] at e
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_prod, Polynomial.eval_C] at e
      have e2 : ∏ ζ ∈ S, (a - ζ * t) = ∏ ζ ∈ S, (t * (a / t - ζ)) :=
        Finset.prod_congr rfl fun ζ _ => by field_simp
      rw [e2, Finset.prod_mul_distrib, Finset.prod_const, hcard, ← e, div_pow]
      field_simp
  have hpoly : ∏ ζ ∈ S, (Polynomial.C a - Polynomial.C ζ * Polynomial.X) =
      Polynomial.C (a ^ n) - Polynomial.X ^ n := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    exact hpt t
  let f : Polynomial ℂ →* ℂ :=
    Matrix.detMonoidHom.comp (Polynomial.aeval (π.permMatrix ℂ)).toRingHom.toMonoidHom
  have hf : ∀ q, f q = (Polynomial.aeval (π.permMatrix ℂ) q).det := fun q => rfl
  have hdet := congrArg f hpoly
  rw [map_prod, hf] at hdet
  have hfac : ∀ ζ ∈ S, f (Polynomial.C a - Polynomial.C ζ * Polynomial.X) =
      (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det := by
    intro ζ hζ
    have hz0 : ζ ≠ 0 := by
      rintro rfl
      have := hmem 0 hζ
      rw [zero_pow hn.ne'] at this
      exact zero_ne_one this
    obtain ⟨c, hc0, hc⟩ := permDet_weight π n h ζ (hmem ζ hζ) hz0
    rw [hf, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact permDet_twist π ζ a c hc0 hc
  rw [Finset.prod_congr rfl hfac, Finset.prod_const, hcard] at hdet
  rw [hdet, map_sub, Polynomial.aeval_C, Polynomial.aeval_X_pow, hPn, Algebra.algebraMap_eq_smul_one]
  have e3 : (a ^ n • (1 : Matrix X X ℂ) - 1) = (a ^ n - 1) • (1 : Matrix X X ℂ) := by
    rw [sub_smul, one_smul]
  rw [e3, Matrix.det_smul, Matrix.det_one, mul_one]

/- English proof (translation)
Introduce `X _ _ π n r a hn ha hcard h`. Establish `hlin : LinearMap.funLeft ℝ ℝ π - a • (LinearMap.id : (X → ℝ) →ₗ[ℝ] (X → ℝ)) = Matrix.toLin' (π.permMatrix ℝ - a • (1 : Matrix X X ℝ))`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.permMatrix_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]`.

Both sides reduce to the same expression. Rewrite using `[hlin, LinearMap.det_toLin']`. Establish `hneg : π.permMatrix ℝ - a • (1 : Matrix X X ℝ) = -(a • (1 : Matrix X X ℝ) - π.permMatrix ℝ)`. Rewrite using `[neg_sub]`. Rewrite using `[hneg, Matrix.det_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]`.

Establish `hC` using `permDet_pow π n hn h (a : ℂ)`. Establish `hmap : ((a • (1 : Matrix X X ℝ) - π.permMatrix ℝ).det : ℂ) = ((a : ℂ) • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det`. Establish `e` using `RingHom.map_det Complex.ofRealHom (a • (1 : Matrix X X ℝ) - π.permMatrix ℝ)`. Rewrite `e` using `[Complex.ofRealHom_eq_coe]`. Rewrite using `[e]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply, PEquiv.toMatrix_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hR : (a • (1 : Matrix X X ℝ) - π.permMatrix ℝ).det ^ n = ((a ^ n - 1) ^ r) ^ n`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[hmap, hC, hcard, pow_mul']`. Establish `hnn : 0 ≤ a ^ n - 1` using `sub_nonneg.mpr (one_le_pow₀ ha)`. Rewrite using `[← pow_left_inj₀ (abs_nonneg _) (pow_nonneg hnn r) hn.ne', ← abs_pow, hR, abs_of_nonneg (pow_nonneg (pow_nonneg hnn r) n)]`.
-/
theorem UpperTheory.V.ZK.Ct.permDet :
    ∀ (X : Type) [Fintype X] [DecidableEq X] (π : Equiv.Perm X) (n r : ℕ) (a : ℝ), 0 < n → 1 ≤ a → Fintype.card X = n * r → (∀ (k : ℕ) (x : X), (π ^ k) x = x ↔ n ∣ k) → |LinearMap.det (LinearMap.funLeft ℝ ℝ π - a • (LinearMap.id : (X → ℝ) →ₗ[ℝ] (X → ℝ)))| = (a ^ n - 1) ^ r := by
  intro X _ _ π n r a hn ha hcard h
  classical
  have hlin : LinearMap.funLeft ℝ ℝ π - a • (LinearMap.id : (X → ℝ) →ₗ[ℝ] (X → ℝ)) =
      Matrix.toLin' (π.permMatrix ℝ - a • (1 : Matrix X X ℝ)) := by
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.permMatrix_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    rfl
  rw [hlin, LinearMap.det_toLin']
  have hneg : π.permMatrix ℝ - a • (1 : Matrix X X ℝ) = -(a • (1 : Matrix X X ℝ) - π.permMatrix ℝ) := by
    rw [neg_sub]
  rw [hneg, Matrix.det_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hC := permDet_pow π n hn h (a : ℂ)
  have hmap : ((a • (1 : Matrix X X ℝ) - π.permMatrix ℝ).det : ℂ) =
      ((a : ℂ) • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det := by
    have e := RingHom.map_det Complex.ofRealHom (a • (1 : Matrix X X ℝ) - π.permMatrix ℝ)
    rw [Complex.ofRealHom_eq_coe] at e
    rw [e]
    congr 1
    ext i j
    simp [Matrix.one_apply, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  have hR : (a • (1 : Matrix X X ℝ) - π.permMatrix ℝ).det ^ n = ((a ^ n - 1) ^ r) ^ n := by
    apply Complex.ofReal_injective
    push_cast
    rw [hmap, hC, hcard, pow_mul']
  have hnn : 0 ≤ a ^ n - 1 := sub_nonneg.mpr (one_le_pow₀ ha)
  rw [← pow_left_inj₀ (abs_nonneg _) (pow_nonneg hnn r) hn.ne', ← abs_pow, hR,
    abs_of_nonneg (pow_nonneg (pow_nonneg hnn r) n)]
