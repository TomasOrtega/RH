import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import GroundTheory.PAdicHodge.SemilinearResidue

noncomputable section

namespace GlobalTheory.PMonE.LangOnto

open Polynomial Finset GlobalTheory.PMonE

def backPoly {k : Type*} [Field k] (q n : ℕ) (c : ℕ → k) (j : ℕ) : k[X] :=
  Nat.rec X (fun j P => P ^ q - C (c (n - j)) * X) j

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem backPoly_zero {k : Type*} [Field k] (q n : ℕ) (c : ℕ → k) : backPoly q n c 0 = X := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem backPoly_succ {k : Type*} [Field k] (q n : ℕ) (c : ℕ → k) (j : ℕ) :
    backPoly q n c (j + 1) = backPoly q n c j ^ q - C (c (n - j)) * X := rfl

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp [backPoly_zero]`. Consider the case `succ j ih`. Establish `h1 : (C (c (n - j)) * X : k[X]).natDegree ≤ 1`.

Use `(natDegree_C_mul_le _ _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `h2 : 2 ≤ (backPoly q n c j ^ q).natDegree`. Rewrite using `[natDegree_pow]`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[backPoly_succ, natDegree_sub_eq_left_of_natDegree_lt (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem backPoly_natDegree {k : Type*} [Field k] {q : ℕ} (hq : 2 ≤ q) (n : ℕ) (c : ℕ → k) :
    ∀ j, 1 ≤ (backPoly q n c j).natDegree := by
  intro j
  induction j with
  | zero => simp [backPoly_zero]
  | succ j ih =>
    have h1 : (C (c (n - j)) * X : k[X]).natDegree ≤ 1 := by
      refine (natDegree_C_mul_le _ _).trans ?_
      simp
    have h2 : 2 ≤ (backPoly q n c j ^ q).natDegree := by
      rw [natDegree_pow]; nlinarith
    rw [backPoly_succ, natDegree_sub_eq_left_of_natDegree_lt (by omega)]
    omega

/- English proof (translation)
Take `⟨m, ⟨c, hrel⟩, -⟩` from `GroundTheory.PAdicHodge.SemilinearResidue.exists_rel k (fun i => (⇑ψ)^[i] z)`. Consider the cases of `m with`. Consider the case `zero => exact ⟨0, by simpa using hrel.symm⟩`. Consider the case `succ n`. Establish `hdeg : (backPoly q n c (n + 1) - C 1).degree ≠ 0`.

Rewrite using `[degree_sub_C (natDegree_pos_iff_degree_pos.mp (backPoly_natDegree hq n c (n + 1)))]`. Conclude with `(natDegree_pos_iff_degree_pos.mp (backPoly_natDegree hq n c (n + 1))).ne'`. Take `⟨t, ht⟩` from `IsAlgClosed.exists_root _ hdeg`. Use `set u : ℕ → k := fun i => (backPoly q n c (n - i)).eval t with hu`. Establish `h0 : u 0 ^ q = 1 + c 0 * t`.

Use `ht.eq_zero` as an intermediate fact. Simplify using `only [backPoly_succ, eval_sub, eval_pow, eval_mul, eval_C, eval_X, Nat.sub_self] at this`. Simplify using `only [hu, Nat.sub_zero]`. Take the linear combination `this`. Establish `hn : u n = t` using `by simp [hu, backPoly_zero]`.

Establish `hs : ∀ i ∈ range n, u (i + 1) ^ q = u i + c (i + 1) * t`. Introduce `i hi`. Establish `hi' : i < n` using `mem_range.mp hi`. Establish `e1 : n - i = (n - (i + 1)) + 1` using `by omega`. Establish `e2 : n - (n - (i + 1)) = i + 1` using `by omega`.

Simplify using `only [hu]`. Rewrite using `[e1]`. Simplify using `only [backPoly_succ, eval_sub, eval_pow, eval_mul, eval_C, eval_X, e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hit : ∀ i, ψ ((⇑ψ)^[i] z) = (⇑ψ)^[i + 1] z` using `fun i => (Function.iterate_succ_apply' _ _ _).symm`.

Use `⟨∑ i ∈ range (n + 1), u i ^ q • (⇑ψ)^[i] z, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Repeatedly rewrite using `[hψ, hit]`. Establish `hA : ∑ i ∈ range n, u (i + 1) ^ q • (⇑ψ)^[i + 1] z = ∑ i ∈ range n, (u i + c (i + 1) * t) • (⇑ψ)^[i + 1] z` using `sum_congr rfl (fun i hi => by rw [hs i hi])`. Rewrite using `[sum_range_succ (fun i => u i • (⇑ψ)^[i + 1] z), hn, hrel, smul_sum, sum_range_succ' _ n, sum_range_succ' (fun i => t • c i • (⇑ψ)^[i] z) n, hA, h0]`.

Simplify using `only [Function.iterate_zero, id, smul_smul, add_smul, sum_add_distrib, one_smul, mul_comm t]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_sub_eq_inv {k : Type*} [Field k] [IsAlgClosed k] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {q : ℕ} (hq : 2 ≤ q) (ψ : V →+ V)
    (hψ : ∀ (c : k) (x : V), ψ (c ^ q • x) = c • ψ x) (z : V) : ∃ y, y - ψ y = z := by
  obtain ⟨m, ⟨c, hrel⟩, -⟩ := GroundTheory.PAdicHodge.SemilinearResidue.exists_rel k (fun i => (⇑ψ)^[i] z)
  cases m with
  | zero => exact ⟨0, by simpa using hrel.symm⟩
  | succ n =>
    have hdeg : (backPoly q n c (n + 1) - C 1).degree ≠ 0 := by
      rw [degree_sub_C (natDegree_pos_iff_degree_pos.mp (backPoly_natDegree hq n c (n + 1)))]
      exact (natDegree_pos_iff_degree_pos.mp (backPoly_natDegree hq n c (n + 1))).ne'
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root _ hdeg
    set u : ℕ → k := fun i => (backPoly q n c (n - i)).eval t with hu
    have h0 : u 0 ^ q = 1 + c 0 * t := by
      have := ht.eq_zero
      simp only [backPoly_succ, eval_sub, eval_pow, eval_mul, eval_C, eval_X, Nat.sub_self] at this
      simp only [hu, Nat.sub_zero]
      linear_combination this
    have hn : u n = t := by simp [hu, backPoly_zero]
    have hs : ∀ i ∈ range n, u (i + 1) ^ q = u i + c (i + 1) * t := by
      intro i hi
      have hi' : i < n := mem_range.mp hi
      have e1 : n - i = (n - (i + 1)) + 1 := by omega
      have e2 : n - (n - (i + 1)) = i + 1 := by omega
      simp only [hu]
      rw [e1]
      simp only [backPoly_succ, eval_sub, eval_pow, eval_mul, eval_C, eval_X, e2]
      ring
    have hit : ∀ i, ψ ((⇑ψ)^[i] z) = (⇑ψ)^[i + 1] z := fun i =>
      (Function.iterate_succ_apply' _ _ _).symm
    refine ⟨∑ i ∈ range (n + 1), u i ^ q • (⇑ψ)^[i] z, ?_⟩
    rw [map_sum]
    simp_rw [hψ, hit]
    have hA : ∑ i ∈ range n, u (i + 1) ^ q • (⇑ψ)^[i + 1] z
        = ∑ i ∈ range n, (u i + c (i + 1) * t) • (⇑ψ)^[i + 1] z :=
      sum_congr rfl (fun i hi => by rw [hs i hi])
    rw [sum_range_succ (fun i => u i • (⇑ψ)^[i + 1] z), hn, hrel, smul_sum, sum_range_succ' _ n,
      sum_range_succ' (fun i => t • c i • (⇑ψ)^[i] z) n, hA, h0]
    simp only [Function.iterate_zero, id, smul_smul, add_smul, sum_add_distrib, one_smul, mul_comm t]
    abel

/- English proof (translation)
Establish `: ExpChar F p` using `ExpChar.prime hp.out`. Establish `hq : 2 ≤ p ^ e` using `GroundTheory.PAdicHodge.SemilinearResidue.two_le_pow he`. Set `r : F ≃+* F` to `(iterateFrobeniusEquiv F p e).symm`. Establish `hr : ∀ a : F, r a ^ p ^ e = a` using `fun a => by`. Rewrite using `[← iterateFrobeniusEquiv_def]`.

Conclude with `(iterateFrobeniusEquiv F p e).apply_symm_apply a`. Establish `hr' : ∀ a : F, r (a ^ p ^ e) = a` using `fun a => by`. Rewrite using `[← iterateFrobeniusEquiv_def]`. Conclude with `(iterateFrobeniusEquiv F p e).symm_apply_apply a`. Set `ψ : (m → F) →+ (m → F)` to `AddMonoidHom.mk' (fun y => A.mulVec (fun i => r (y i))) (fun y y' => by`.

Rewrite using `[← Matrix.mulVec_add]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Use the proof step `simp)`. Establish `hψ : ∀ (c : F) (x : m → F), ψ (c ^ p ^ e • x) = c • ψ x`.

Introduce `c x`. Express the relevant statement in the definitionally equal form `A.mulVec _ = c • A.mulVec _`. Rewrite using `[← Matrix.mulVec_smul]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, hr']`. Take `⟨y, hy⟩` from `exists_sub_eq_inv hq ψ hψ b`. Use `⟨fun i => r (y i), fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hr, ← hy]`. Both sides reduce to the same expression.
-/
theorem exists_sol {F : Type*} [Field F] [IsAlgClosed F] (p : ℕ) [hp : Fact p.Prime] [CharP F p] {m : Type*}
    [Fintype m] {e : ℕ} (he : 0 < e) (A : Matrix m m F) (b : m → F) :
    ∃ x : m → F, ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by
  have : ExpChar F p := ExpChar.prime hp.out
  have hq : 2 ≤ p ^ e := GroundTheory.PAdicHodge.SemilinearResidue.two_le_pow he
  let r : F ≃+* F := (iterateFrobeniusEquiv F p e).symm
  have hr : ∀ a : F, r a ^ p ^ e = a := fun a => by
    rw [← iterateFrobeniusEquiv_def]
    exact (iterateFrobeniusEquiv F p e).apply_symm_apply a
  have hr' : ∀ a : F, r (a ^ p ^ e) = a := fun a => by
    rw [← iterateFrobeniusEquiv_def]
    exact (iterateFrobeniusEquiv F p e).symm_apply_apply a
  let ψ : (m → F) →+ (m → F) := AddMonoidHom.mk' (fun y => A.mulVec (fun i => r (y i))) (fun y y' => by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp)
  have hψ : ∀ (c : F) (x : m → F), ψ (c ^ p ^ e • x) = c • ψ x := by
    intro c x
    change A.mulVec _ = c • A.mulVec _
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hr']
  obtain ⟨y, hy⟩ := exists_sub_eq_inv hq ψ hψ b
  refine ⟨fun i => r (y i), fun i => ?_⟩
  rw [hr, ← hy]
  rfl

/- English proof (translation)
Introduce `F _ _ _ p _ _ m _ _ e he A hA b hb`. Take `⟨x, hx⟩` from `exists_sol p he A b`. Use `⟨x, ?_, hx⟩` and prove the remaining obligations. Establish `hq : 2 ≤ p ^ e` using `GroundTheory.PAdicHodge.SemilinearResidue.two_le_pow he`. Introduce `i₀`.

Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Take `⟨i, -, hi⟩` from `exists_max_image univ (fun j => ‖x j‖) ⟨i₀, mem_univ _⟩`. Establish `hR : 1 < ‖x i‖` using `hlt.trans_le (hi i₀ (mem_univ _))`. Establish `h1 : ‖A.mulVec x i‖ ≤ ‖x i‖`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : x i ^ p ^ e = b i + A.mulVec x i` using `by rw [← hx i]; ring`.

Establish `h3 : ‖x i‖ ^ p ^ e ≤ ‖x i‖`. Rewrite using `[← norm_pow, h2]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hb i).trans hR.le) h1)`. Establish `h4 : ‖x i‖ ^ 1 < ‖x i‖ ^ p ^ e` using `pow_lt_pow_right₀ hR (by omega)`. Rewrite `h4` using `[pow_one]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lang_onto : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ)
    [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F,
    (∀ i j, ‖A i j‖ ≤ 1) → ∀ b : m → F, Integral b →
      ∃ x : m → F, Integral x ∧ ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by
  intro F _ _ _ p _ _ m _ _ e he A hA b hb
  obtain ⟨x, hx⟩ := exists_sol p he A b
  refine ⟨x, ?_, hx⟩
  have hq : 2 ≤ p ^ e := GroundTheory.PAdicHodge.SemilinearResidue.two_le_pow he
  intro i₀
  by_contra hlt
  push Not at hlt
  obtain ⟨i, -, hi⟩ := exists_max_image univ (fun j => ‖x j‖) ⟨i₀, mem_univ _⟩
  have hR : 1 < ‖x i‖ := hlt.trans_le (hi i₀ (mem_univ _))
  have h1 : ‖A.mulVec x i‖ ≤ ‖x i‖ := by
    simp only [Matrix.mulVec, dotProduct]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun j _ => ?_)
    rw [norm_mul]
    calc ‖A i j‖ * ‖x j‖ ≤ 1 * ‖x j‖ := mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)
      _ ≤ ‖x i‖ := by rw [one_mul]; exact hi j (mem_univ _)
  have h2 : x i ^ p ^ e = b i + A.mulVec x i := by rw [← hx i]; ring
  have h3 : ‖x i‖ ^ p ^ e ≤ ‖x i‖ := by
    rw [← norm_pow, h2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hb i).trans hR.le) h1)
  have h4 : ‖x i‖ ^ 1 < ‖x i‖ ^ p ^ e := pow_lt_pow_right₀ hR (by omega)
  rw [pow_one] at h4
  linarith

end GlobalTheory.PMonE.LangOnto

end
