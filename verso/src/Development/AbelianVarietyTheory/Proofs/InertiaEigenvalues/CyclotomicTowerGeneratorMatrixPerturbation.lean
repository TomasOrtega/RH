import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateOperatorLevelComplement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowSubOneLe

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CycPerturb

section Abstract

variable {C : Type} [NormedField C] [IsUltrametricDist C]

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun b _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hB a b) (norm_le_pi_norm v b) (norm_nonneg _) hc`.
-/
theorem norm_mulVec_le {r : ℕ} (B : Matrix (Fin r) (Fin r) C) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ a b, ‖B a b‖ ≤ c) (v : Fin r → C) (a : Fin r) : ‖B.mulVec v a‖ ≤ c * ‖v‖ := by
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun b _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hB a b) (norm_le_pi_norm v b) (norm_nonneg _) hc

omit [IsUltrametricDist C] in
/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `X.sum_mem fun b _ => hB a b _ (hv b)`.
-/
theorem mulVec_mem {r : ℕ} (X : AddSubgroup C) (B : Matrix (Fin r) (Fin r) C)
    (hB : ∀ a b, ∀ x ∈ X, B a b * x ∈ X) (v : Fin r → C) (hv : ∀ a, v a ∈ X) (a : Fin r) :
    B.mulVec v a ∈ X := by
  simp only [Matrix.mulVec, dotProduct]
  exact X.sum_mem fun b _ => hB a b _ (hv b)

/- English proof (translation)
Establish `key : ∀ k : ℕ, ∃ z : Fin r → C, (∀ a, z a ∈ X) ∧ ∀ a, y a = (-π) ^ k * z a`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨y, hy, fun a => by simp⟩`. Consider the case `succ k ih`.

Take `⟨z, hz, hyz⟩` from `ih`. Establish `hm : ∀ a, B.mulVec (fun b => g (z b)) a ∈ X` using `mulVec_mem X B hBX _ (fun b => hgX _ (hz b))`. Use `⟨fun a => S (B.mulVec (fun b => g (z b)) a), fun a => (hS _ (hm a)).1, fun a => ?_⟩` and prove the remaining obligations. Establish `e : g (y a) - y a = p * (-π) ^ (k + 1) * B.mulVec (fun b => g (z b)) a`. Rewrite using `[eq_neg_of_add_eq_zero_left (h a)]`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, hyz, map_mul, map_pow, map_neg, hgπ, Finset.mul_sum, ← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun b _ => by ring`. Establish `h1` using `(hS _ (hy a)).2`. Rewrite `h1` using `[e, hlin _ _ (hm a), mul_assoc]`. Conclude with `(mul_left_cancel₀ hp h1).symm`.

Use function extensionality and compare the values at `a`. Establish `hle : ∀ k : ℕ, ‖y a‖ ≤ ‖π‖ ^ k`. Introduce `k`. Take `⟨z, hz, hyz⟩` from `key k`. Rewrite using `[hyz, norm_mul, norm_pow, norm_neg]`.

Conclude with `mul_le_of_le_one_right (by positivity) (hX1 _ (hz a))`. Use `ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hπ) hle` as an intermediate fact. Conclude with `norm_le_zero_iff.1 this`.
-/
theorem inj_of_lattice {r : ℕ} (X : AddSubgroup C) (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (g : C ≃+* C)
    (hgX : ∀ x ∈ X, g x ∈ X) (p : C) (hp : p ≠ 0) (π : C) (hπ : ‖π‖ < 1) (hgπ : g π = π)
    (S : C → C) (hS : ∀ x ∈ X, S x ∈ X ∧ S (g x - x) = p * x)
    (hlin : ∀ (k : ℕ), ∀ x ∈ X, S (p * (-π) ^ k * x) = p * (-π) ^ k * S x)
    (B : Matrix (Fin r) (Fin r) C) (hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X)
    (y : Fin r → C) (hy : ∀ a, y a ∈ X)
    (h : ∀ a, g (y a) - y a + p * (π • B).mulVec (fun b => g (y b)) a = 0) : y = 0 := by
  have key : ∀ k : ℕ, ∃ z : Fin r → C, (∀ a, z a ∈ X) ∧ ∀ a, y a = (-π) ^ k * z a := by
    intro k
    induction k with
    | zero => exact ⟨y, hy, fun a => by simp⟩
    | succ k ih =>
      obtain ⟨z, hz, hyz⟩ := ih
      have hm : ∀ a, B.mulVec (fun b => g (z b)) a ∈ X :=
        mulVec_mem X B hBX _ (fun b => hgX _ (hz b))
      refine ⟨fun a => S (B.mulVec (fun b => g (z b)) a), fun a => (hS _ (hm a)).1, fun a => ?_⟩
      have e : g (y a) - y a = p * (-π) ^ (k + 1) * B.mulVec (fun b => g (z b)) a := by
        rw [eq_neg_of_add_eq_zero_left (h a)]
        simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, hyz, map_mul, map_pow,
          map_neg, hgπ, Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun b _ => by ring
      have h1 := (hS _ (hy a)).2
      rw [e, hlin _ _ (hm a), mul_assoc] at h1
      exact (mul_left_cancel₀ hp h1).symm
  funext a
  have hle : ∀ k : ℕ, ‖y a‖ ≤ ‖π‖ ^ k := by
    intro k
    obtain ⟨z, hz, hyz⟩ := key k
    rw [hyz, norm_mul, norm_pow, norm_neg]
    exact mul_le_of_le_one_right (by positivity) (hX1 _ (hz a))
  have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hπ) hle
  exact norm_le_zero_iff.1 this

/- English proof (translation)
Set `T : (Fin r → C) → (Fin r → C)` to `fun v => B.mulVec (fun b => g (S (v b)))`. Set `u : ℕ → Fin r → C` to `fun k => T^[k] w`. Establish `hu0 : u 0 = w` using `rfl`. Establish `hus : ∀ k, u (k + 1) = B.mulVec (fun b => g (S (u k b)))` using `fun k => Function.iterate_succ_apply' T k w`. Establish `huX : ∀ k a, u k a ∈ X`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact hw`. Consider the case `succ k ih => rw [hus]`. Conclude with `mulVec_mem X B hBX _ (fun b => hgX _ (hS _ (ih b)).1)`.

Establish `hpow : ∀ (k : ℕ), ∀ x ∈ X, (-π) ^ k * x ∈ X`. Introduce `k x hx`. Proceed by induction on `k with`. Consider the case `zero => simpa using hx`. Consider the case `succ k ih`.

Establish `: (-π) ^ (k + 1) * x = -(π * ((-π) ^ k * x))` using `by ring`. Rewrite using `[this]`. Conclude with `X.neg_mem (hπX _ ih)`. Establish `hbd : ∀ (k : ℕ), ∀ x ∈ X, ‖(-π) ^ k * x‖ ≤ ‖π‖ ^ k`. Introduce `k x hx`.

Rewrite using `[norm_mul, norm_pow, norm_neg]`. Conclude with `mul_le_of_le_one_right (by positivity) (hX1 _ hx)`. Establish `hsum : ∀ a, Summable fun k : ℕ => (-π) ^ k * S (u k a)` using `fun a => Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg π) hπ) fun k => hbd k _ (hS _ (huX k a)).1`. Set `P : ℕ → Fin r → C` to `fun n a => ∑ k ∈ Finset.range n, (-π) ^ k * S (u k a)`. Set `y : Fin r → C` to `fun a => ∑' k : ℕ, (-π) ^ k * S (u k a)`.

Establish `hP : ∀ a, Filter.Tendsto (fun n => P n a) Filter.atTop (nhds (y a))` using `fun a => (hsum a).hasSum.tendsto_sum_nat`. Establish `hgc : Continuous g` using `(AddMonoidHomClass.isometry_of_norm g hg).continuous`. Establish `hL : ∀ n a, g (P n a) - P n a + p * ∑ b, π * B a b * g (P n b) = p * w a - p * ((-π) ^ n * u n a)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro a`. Simplify using `[P, hu0]`. Consider the case `succ n ih`. Introduce `a`. Establish `e : ∀ b, P (n + 1) b = P n b + (-π) ^ n * S (u n b)` using `fun b => Finset.sum_range_succ _ _`.

Establish `h1` using `(hS _ (huX n a)).2`. Establish `h2 : u (n + 1) a = ∑ b, B a b * g (S (u n b))` using `by rw [hus]; rfl`. Establish `h3 : ∑ b, π * B a b * g (P (n + 1) b) = ∑ b, π * B a b * g (P n b) + π * (-π) ^ n * u (n + 1) a`. Rewrite using `[h2, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[e, map_add, map_mul, map_pow, map_neg, hgπ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3, e, map_add, map_mul, map_pow, map_neg, hgπ]`. Take the linear combination `ih a + (-π) ^ n * h1`. Use `⟨y, fun a => hX.mem_of_tendsto (hP a) (Filter.Eventually.of_forall fun n => X.sum_mem fun k _ => hpow k _ (hS _ (huX k a)).1), fun a => ?_⟩` and prove the remaining obligations.

Establish `t1 : Filter.Tendsto (fun n => g (P n a) - P n a + p * ∑ b, π * B a b * g (P n b)) Filter.atTop (nhds (g (y a) - y a + p * ∑ b, π * B a b * g (y b)))` using `(((hgc.tendsto _).comp (hP a)).sub (hP a)).add ((tendsto_finset_sum _ fun b _ => ((hgc.tendsto _).comp (hP b)).const_mul _).const_mul p)`. Establish `t0 : Filter.Tendsto (fun n : ℕ => (-π) ^ n * u n a) Filter.atTop (nhds 0)` using `squeeze_zero_norm (fun n => hbd n _ (huX n a)) (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hπ)`. Establish `t2 : Filter.Tendsto (fun n : ℕ => p * w a - p * ((-π) ^ n * u n a)) Filter.atTop (nhds (p * w a - p * 0))` using `(t0.const_mul p).const_sub _`. Simplify using `only [hL] at t1`. Use `tendsto_nhds_unique t1 t2` as an intermediate fact.

Rewrite `this` using `[mul_zero, sub_zero]`. Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
theorem surj_of_lattice [CompleteSpace C] {r : ℕ} (X : AddSubgroup C) (hX : IsClosed (X : Set C))
    (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (g : C ≃+* C) (hg : ∀ x, ‖g x‖ = ‖x‖) (hgX : ∀ x ∈ X, g x ∈ X)
    (p : C) (π : C) (hπ : ‖π‖ < 1) (hgπ : g π = π) (hπX : ∀ x ∈ X, π * x ∈ X)
    (S : C → C) (hS : ∀ x ∈ X, S x ∈ X ∧ g (S x) - S x = p * x)
    (B : Matrix (Fin r) (Fin r) C) (hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X)
    (w : Fin r → C) (hw : ∀ a, w a ∈ X) :
    ∃ y : Fin r → C, (∀ a, y a ∈ X) ∧
      ∀ a, g (y a) - y a + p * (π • B).mulVec (fun b => g (y b)) a = p * w a := by
  let T : (Fin r → C) → (Fin r → C) := fun v => B.mulVec (fun b => g (S (v b)))
  let u : ℕ → Fin r → C := fun k => T^[k] w
  have hu0 : u 0 = w := rfl
  have hus : ∀ k, u (k + 1) = B.mulVec (fun b => g (S (u k b))) := fun k =>
    Function.iterate_succ_apply' T k w
  have huX : ∀ k a, u k a ∈ X := by
    intro k
    induction k with
    | zero => exact hw
    | succ k ih => rw [hus]; exact mulVec_mem X B hBX _ (fun b => hgX _ (hS _ (ih b)).1)
  have hpow : ∀ (k : ℕ), ∀ x ∈ X, (-π) ^ k * x ∈ X := by
    intro k x hx
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have : (-π) ^ (k + 1) * x = -(π * ((-π) ^ k * x)) := by ring
      rw [this]; exact X.neg_mem (hπX _ ih)
  have hbd : ∀ (k : ℕ), ∀ x ∈ X, ‖(-π) ^ k * x‖ ≤ ‖π‖ ^ k := by
    intro k x hx
    rw [norm_mul, norm_pow, norm_neg]
    exact mul_le_of_le_one_right (by positivity) (hX1 _ hx)
  have hsum : ∀ a, Summable fun k : ℕ => (-π) ^ k * S (u k a) := fun a =>
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg π) hπ)
      fun k => hbd k _ (hS _ (huX k a)).1
  let P : ℕ → Fin r → C := fun n a => ∑ k ∈ Finset.range n, (-π) ^ k * S (u k a)
  let y : Fin r → C := fun a => ∑' k : ℕ, (-π) ^ k * S (u k a)
  have hP : ∀ a, Filter.Tendsto (fun n => P n a) Filter.atTop (nhds (y a)) := fun a =>
    (hsum a).hasSum.tendsto_sum_nat
  have hgc : Continuous g := (AddMonoidHomClass.isometry_of_norm g hg).continuous
  have hL : ∀ n a, g (P n a) - P n a + p * ∑ b, π * B a b * g (P n b)
      = p * w a - p * ((-π) ^ n * u n a) := by
    intro n
    induction n with
    | zero => intro a; simp [P, hu0]
    | succ n ih =>
      intro a
      have e : ∀ b, P (n + 1) b = P n b + (-π) ^ n * S (u n b) := fun b => Finset.sum_range_succ _ _
      have h1 := (hS _ (huX n a)).2
      have h2 : u (n + 1) a = ∑ b, B a b * g (S (u n b)) := by rw [hus]; rfl
      have h3 : ∑ b, π * B a b * g (P (n + 1) b)
          = ∑ b, π * B a b * g (P n b) + π * (-π) ^ n * u (n + 1) a := by
        rw [h2, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [e, map_add, map_mul, map_pow, map_neg, hgπ]; ring
      rw [h3, e, map_add, map_mul, map_pow, map_neg, hgπ]
      linear_combination ih a + (-π) ^ n * h1
  refine ⟨y, fun a => hX.mem_of_tendsto (hP a) (Filter.Eventually.of_forall fun n =>
    X.sum_mem fun k _ => hpow k _ (hS _ (huX k a)).1), fun a => ?_⟩
  have t1 : Filter.Tendsto (fun n => g (P n a) - P n a + p * ∑ b, π * B a b * g (P n b))
      Filter.atTop (nhds (g (y a) - y a + p * ∑ b, π * B a b * g (y b))) :=
    (((hgc.tendsto _).comp (hP a)).sub (hP a)).add
      ((tendsto_finset_sum _ fun b _ => ((hgc.tendsto _).comp (hP b)).const_mul _).const_mul p)
  have t0 : Filter.Tendsto (fun n : ℕ => (-π) ^ n * u n a) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun n => hbd n _ (huX n a))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hπ)
  have t2 : Filter.Tendsto (fun n : ℕ => p * w a - p * ((-π) ^ n * u n a)) Filter.atTop
      (nhds (p * w a - p * 0)) := (t0.const_mul p).const_sub _
  simp only [hL] at t1
  have := tendsto_nhds_unique t1 t2
  rw [mul_zero, sub_zero] at this
  rw [← this]
  rfl

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le`. Consider the case `exact _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le`. Consider the case `(apply _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le ..)`.
-/
theorem norm_zpow_sub_one_le (u : C) (hu : ‖u - 1‖ < 1) (i : ℤ) : ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
  first
  | exact @_root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le
  | exact _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le
  | (apply _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le ..)

end Abstract

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Establish `h2 : 2 ≤ l` using `hl.1.two_le`. Establish `h1 : (1 : ℝ) < l` using `by exact_mod_cast hl.1.one_lt`. Rewrite using `[rho1, ← Real.rpow_intCast]`. Apply `Real.rpow_lt_rpow_of_exponent_lt h1` to reduce the goal to its premises. Rewrite using `[lt_div_iff₀ (by linarith)]`.

Use `push_cast`. Establish `hj1 : (1 : ℝ) ≤ j` using `by exact_mod_cast hj.1`. Break down `h2.eq_or_lt with h | h` into its components or cases. Establish `hj2 : (2 : ℝ) ≤ j` using `by exact_mod_cast hj.2 h.symm`. Establish `: (l : ℝ) = 2` using `by exact_mod_cast h.symm`.

Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: (3 : ℝ) ≤ l` using `by exact_mod_cast h`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pow_lt_rho {j : ℕ} (hj : Lev l j) : (l : ℝ) ^ (-(j : ℤ)) < rho1 l := by
  have h2 : 2 ≤ l := hl.1.two_le
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  rw [rho1, ← Real.rpow_intCast]
  apply Real.rpow_lt_rpow_of_exponent_lt h1
  rw [lt_div_iff₀ (by linarith)]
  push_cast
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
  rcases h2.eq_or_lt with h | h
  · have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj.2 h.symm
    have : (l : ℝ) = 2 := by exact_mod_cast h.symm
    rw [this]; linarith
  · have : (3 : ℝ) ≤ l := by exact_mod_cast h
    nlinarith

/- English proof (translation)
Establish `h1 : (1 : ℝ) < l` using `by exact_mod_cast hl.1.one_lt`. Rewrite using `[rho1]`. Apply `Real.rpow_lt_one_of_one_lt_of_neg h1` to reduce the goal to its premises. Conclude with `div_neg_of_neg_of_pos (by norm_num) (by linarith)`.
-/
theorem rho_lt_one : rho1 l < 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  rw [rho1]
  apply Real.rpow_lt_one_of_one_lt_of_neg h1
  exact div_neg_of_neg_of_pos (by norm_num) (by linarith)

/- English proof (translation)
Use `GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl ζ (by rwa [pow_one])` as an intermediate fact. Simplify `this` using `[rho1]`.
-/
theorem norm_root_sub_one {ζ : PadicComplex l} (h : IsPrimitiveRoot ζ l) : ‖ζ - 1‖ = rho1 l := by
  have := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl ζ (by rwa [pow_one])
  simpa [rho1] using this

/- English proof (translation)
Simplify using `[inC, PadicComplex.coe_eq]`.
-/
theorem mem_inC_iff (F : IntermediateField ℚ_[l] (Om l)) (y : PadicComplex l) :
    y ∈ inC F ↔ y ∈ F.toSubfield.map (algebraMap (Om l) (PadicComplex l)) := by
  simp [inC, PadicComplex.coe_eq]

/- English proof (translation)
Use `haveI : NeZero l := ⟨hl.1.ne_zero⟩`. Take `⟨η, hη⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l`. Establish `hη'` using `hη.map_of_injective (algebraMap (Om l) (PadicComplex l)).injective`. Take `⟨k, -, hk⟩` from `hη'.eq_pow_of_pow_eq_one h.pow_eq_one`. Use `⟨η ^ k, ?_, ?_⟩` and prove the remaining obligations.

Use `pow_mem (?_ : η ∈ Ks K j) k` and prove the remaining obligations. Use `(le_sup_right : _ ≤ Ks K j) (IntermediateField.subset_adjoin _ _ ?_)` and prove the remaining obligations. Conclude with `(hη.pow_eq_one_iff_dvd _).2 (dvd_pow_self l (by omega))`. Simplify using `only [PadicComplex.coe_eq, map_pow]`. Conclude with `hk`.
-/
theorem root_mem_inC (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {ζ : PadicComplex l}
    (h : IsPrimitiveRoot ζ l) : ζ ∈ inC (Ks K j) := by
  haveI : NeZero l := ⟨hl.1.ne_zero⟩
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hη' := hη.map_of_injective (algebraMap (Om l) (PadicComplex l)).injective
  obtain ⟨k, -, hk⟩ := hη'.eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨η ^ k, ?_, ?_⟩
  · refine pow_mem (?_ : η ∈ Ks K j) k
    refine (le_sup_right : _ ≤ Ks K j) (IntermediateField.subset_adjoin _ _ ?_)
    exact (hη.pow_eq_one_iff_dvd _).2 (dvd_pow_self l (by omega))
  · simp only [PadicComplex.coe_eq, map_pow]
    exact hk

/- English proof (translation)
Assemble the required witnesses or components as `⟨algebraMap ℚ_[l] (Om l) _, F.algebraMap_mem _, rfl⟩`.
-/
theorem chiC_mem_inC (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g : GQ l)
    (F : IntermediateField ℚ_[l] (Om l)) : chiC χ i g ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) _, F.algebraMap_mem _, rfl⟩

/- English proof (translation)
Establish `h1 : ‖(χ g : ℚ_[l]) - 1‖ < rho1 l` using `hg.2 ▸ pow_lt_rho hj`. Establish `h2` using `norm_zpow_sub_one_le _ (h1.trans rho_lt_one) i`. Establish `e : chiC χ i g - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1)`. Simplify using `[chiC]`. Rewrite using `[e, norm_algebraMap']`.

Conclude with `h2.trans_lt h1`.
-/
theorem norm_chiC_sub_one {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) (i : ℤ) : ‖chiC χ i g - 1‖ < rho1 l := by
  have h1 : ‖(χ g : ℚ_[l]) - 1‖ < rho1 l := hg.2 ▸ pow_lt_rho hj
  have h2 := norm_zpow_sub_one_le _ (h1.trans rho_lt_one) i
  have e : chiC χ i g - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1) := by
    simp [chiC]
  rw [e, norm_algebraMap']
  exact h2.trans_lt h1

/- English proof (translation)
Establish `hz` using `norm_root_sub_one h`. Establish `hz0 : ζ - 1 ≠ 0` using `sub_ne_zero.2 (h.ne_one hl.1.one_lt)`. Establish `hzp : 0 < ‖ζ - 1‖` using `norm_pos_iff.2 hz0`. Establish `hc` using `norm_chiC_sub_one hj hg i`. Establish `hc1 : ‖chiC χ i g‖ ≤ 1`.

Use `IsUltrametricDist.norm_add_le_max (chiC χ i g - 1) 1` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, norm_one]`. Conclude with `this.trans (max_le (hc.trans rho_lt_one).le le_rfl)`. Set `B : Matrix (Fin r) (Fin r) (PadicComplex l)` to `(ζ - 1)⁻¹ • (chiC χ i g • U - 1)`. Establish `hB : ∀ a b, ‖B a b‖ < 1`.

Introduce `a b`. Establish `e : B a b = (ζ - 1)⁻¹ * (chiC χ i g * (U - 1) a b + (chiC χ i g - 1) * (1 : Matrix (Fin r) (Fin r) (PadicComplex l)) a b)`. Simplify using `only [B, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_mul, norm_inv, inv_mul_lt_iff₀ hzp, mul_one, hz]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hc1).trans_lt (hU1 a b)`. Rewrite using `[norm_mul]`. Use `(mul_le_of_le_one_right (norm_nonneg _) ?_).trans_lt hc` and prove the remaining obligations.

Apply the tactic sequence `rw [Matrix.one_apply]; split_ifs <;> simp`. Use `⟨B, ‖fun p : Fin r × Fin r => B p.1 p.2‖, norm_nonneg _, (pi_norm_lt_iff one_pos).2 fun p => hB _ _, fun a b => norm_le_pi_norm (fun p : Fin r × Fin r => B p.1 p.2) (a, b), fun a b => ⟨?_, (hB a b).le⟩, ?_⟩` and prove the remaining obligations. Establish `m1` using `(mem_inC_iff _ _).1 (root_mem_inC K hj.1 h)`. Establish `m2` using `(mem_inC_iff _ _).1 (chiC_mem_inC χ i g (Ks K j))`. Establish `m3` using `(mem_inC_iff _ _).1 (hU a b).1`.

Rewrite using `[mem_inC_iff]`. Simplify using `only [B, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]`. Use `mul_mem (inv_mem (sub_mem m1 (one_mem _))) (sub_mem (mul_mem m2 m3) ?_)` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Simplify using `only [B, smul_smul, mul_inv_cancel₀ hz0, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_quot {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) {r : ℕ} (U : Matrix (Fin r) (Fin r) (PadicComplex l))
    (hU : ∀ a b, U a b ∈ intC (Ks K j)) (hU1 : ∀ a b, ‖(U - 1) a b‖ < rho1 l) (i : ℤ)
    {ζ : PadicComplex l} (h : IsPrimitiveRoot ζ l) :
    ∃ (B : Matrix (Fin r) (Fin r) (PadicComplex l)) (c : ℝ), 0 ≤ c ∧ c < 1 ∧
      (∀ a b, ‖B a b‖ ≤ c) ∧ (∀ a b, B a b ∈ intC (Ks K j)) ∧
      chiC χ i g • U = 1 + (ζ - 1) • B := by
  have hz := norm_root_sub_one h
  have hz0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (h.ne_one hl.1.one_lt)
  have hzp : 0 < ‖ζ - 1‖ := norm_pos_iff.2 hz0
  have hc := norm_chiC_sub_one hj hg i
  have hc1 : ‖chiC χ i g‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (chiC χ i g - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le (hc.trans rho_lt_one).le le_rfl)
  let B : Matrix (Fin r) (Fin r) (PadicComplex l) := (ζ - 1)⁻¹ • (chiC χ i g • U - 1)
  have hB : ∀ a b, ‖B a b‖ < 1 := by
    intro a b
    have e : B a b = (ζ - 1)⁻¹ * (chiC χ i g * (U - 1) a b
        + (chiC χ i g - 1) * (1 : Matrix (Fin r) (Fin r) (PadicComplex l)) a b) := by
      simp only [B, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]; ring
    rw [e, norm_mul, norm_inv, inv_mul_lt_iff₀ hzp, mul_one, hz]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hc1).trans_lt (hU1 a b)
    · rw [norm_mul]
      refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans_lt hc
      rw [Matrix.one_apply]; split_ifs <;> simp
  refine ⟨B, ‖fun p : Fin r × Fin r => B p.1 p.2‖, norm_nonneg _,
    (pi_norm_lt_iff one_pos).2 fun p => hB _ _,
    fun a b => norm_le_pi_norm (fun p : Fin r × Fin r => B p.1 p.2) (a, b),
    fun a b => ⟨?_, (hB a b).le⟩, ?_⟩
  · have m1 := (mem_inC_iff _ _).1 (root_mem_inC K hj.1 h)
    have m2 := (mem_inC_iff _ _).1 (chiC_mem_inC χ i g (Ks K j))
    have m3 := (mem_inC_iff _ _).1 (hU a b).1
    rw [mem_inC_iff]
    simp only [B, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    refine mul_mem (inv_mem (sub_mem m1 (one_mem _))) (sub_mem (mul_mem m2 m3) ?_)
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  · simp only [B, smul_smul, mul_inv_cancel₀ hz0, one_smul]; abel

/- English proof (translation)
Rewrite using `[twAct, ← Matrix.smul_mulVec, h, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]`. Simplify using `only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem twAct_sub {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ} {i : ℤ}
    {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l} {p : PadicComplex l}
    {B : Matrix (Fin r) (Fin r) (PadicComplex l)} (h : chiC χ i g • U g = 1 + p • B)
    (y : Fin r → PadicComplex l) (a : Fin r) :
    (twAct act χ i U g y - y) a
      = act g (y a) - y a + p * B.mulVec (fun b => act g (y b)) a := by
  rw [twAct, ← Matrix.smul_mulVec, h, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨(mem_inC_iff _ _).2 (mul_mem ((mem_inC_iff _ _).1 hx.1) ((mem_inC_iff _ _).1 hy.1)), by rw [norm_mul]; exact mul_le_one₀ hx.2 (norm_nonneg _) hy.2⟩`.
-/
theorem mul_mem_intC {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l}
    (hx : x ∈ intC F) (hy : y ∈ intC F) : x * y ∈ intC F :=
  ⟨(mem_inC_iff _ _).2 (mul_mem ((mem_inC_iff _ _).1 hx.1) ((mem_inC_iff _ _).1 hy.1)), by
    rw [norm_mul]; exact mul_le_one₀ hx.2 (norm_nonneg _) hy.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨(mem_inC_iff _ _).2 (pow_mem (neg_mem ((mem_inC_iff _ _).1 hx.1)) k), by rw [norm_pow, norm_neg]; exact pow_le_one₀ (norm_nonneg _) hx.2⟩`.
-/
theorem neg_pow_mem_intC {F : IntermediateField ℚ_[l] (Om l)} {x : PadicComplex l}
    (hx : x ∈ intC F) (k : ℕ) : (-x) ^ k ∈ intC F :=
  ⟨(mem_inC_iff _ _).2 (pow_mem (neg_mem ((mem_inC_iff _ _).1 hx.1)) k), by
    rw [norm_pow, norm_neg]; exact pow_le_one₀ (norm_nonneg _) hx.2⟩

/- English proof (translation)
Establish `h0 : (0 : PadicComplex l) ∈ intC F` using `⟨(mem_inC_iff _ _).2 (zero_mem _), by simp⟩`. Distinguish the cases in `hz : B = 0`. Conclude with `⟨0, 0, h0, by simp, fun a b => h0, by simp [hz]⟩`. Choose the witnesses or unpack the hypotheses as in `⟨a₀, b₀, hne⟩ : ∃ a b, B a b ≠ 0 := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `hz (Matrix.ext hcon)`. Use `haveI : Nonempty (Fin r × Fin r) := ⟨(a₀, b₀)⟩`. Take `⟨q, hq⟩` from `Finite.exists_max fun q : Fin r × Fin r => ‖B q.1 q.2‖`. Establish `hpos : 0 < ‖B q.1 q.2‖` using `(norm_pos_iff.2 hne).trans_le (hq (a₀, b₀))`.

Establish `hq0 : B q.1 q.2 ≠ 0` using `norm_pos_iff.1 hpos`. Use `⟨B q.1 q.2, (B q.1 q.2)⁻¹ • B, hBO _ _, hB _ _, fun a b => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, smul_eq_mul, mem_inC_iff]`. Conclude with `mul_mem (inv_mem ((mem_inC_iff _ _).1 (hBO _ _).1)) ((mem_inC_iff _ _).1 (hBO _ _).1)`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ hpos, mul_one]`.

Conclude with `hq (a, b)`. Rewrite using `[smul_smul, mul_inv_cancel₀ hq0, one_smul]`.
-/
theorem exists_factor {F : IntermediateField ℚ_[l] (Om l)} {r : ℕ}
    (B : Matrix (Fin r) (Fin r) (PadicComplex l)) (hB : ∀ a b, ‖B a b‖ < 1)
    (hBO : ∀ a b, B a b ∈ intC F) :
    ∃ (π : PadicComplex l) (B' : Matrix (Fin r) (Fin r) (PadicComplex l)), π ∈ intC F ∧ ‖π‖ < 1 ∧
      (∀ a b, B' a b ∈ intC F) ∧ B = π • B' := by
  have h0 : (0 : PadicComplex l) ∈ intC F := ⟨(mem_inC_iff _ _).2 (zero_mem _), by simp⟩
  by_cases hz : B = 0
  · exact ⟨0, 0, h0, by simp, fun a b => h0, by simp [hz]⟩
  obtain ⟨a₀, b₀, hne⟩ : ∃ a b, B a b ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hz (Matrix.ext hcon)
  haveI : Nonempty (Fin r × Fin r) := ⟨(a₀, b₀)⟩
  obtain ⟨q, hq⟩ := Finite.exists_max fun q : Fin r × Fin r => ‖B q.1 q.2‖
  have hpos : 0 < ‖B q.1 q.2‖ := (norm_pos_iff.2 hne).trans_le (hq (a₀, b₀))
  have hq0 : B q.1 q.2 ≠ 0 := norm_pos_iff.1 hpos
  refine ⟨B q.1 q.2, (B q.1 q.2)⁻¹ • B, hBO _ _, hB _ _, fun a b => ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.smul_apply, smul_eq_mul, mem_inC_iff]
    exact mul_mem (inv_mem ((mem_inC_iff _ _).1 (hBO _ _).1)) ((mem_inC_iff _ _).1 (hBO _ _).1)
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ hpos, mul_one]
    exact hq (a, b)
  · rw [smul_smul, mul_inv_cancel₀ hq0, one_smul]

/- English proof (translation)
Take `⟨x, hx, rfl⟩` from `hy`. Use `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x hx` as an intermediate fact. Express the relevant statement in the definitionally equal form `act g (x : PadicComplex l) = (x : PadicComplex l)`. Rewrite using `[hact.1, this]`.
-/
theorem act_fix {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act)
    {K : FinExt l} {j : ℕ} {g : GQ l} (hg : g ∈ Gj K j) {y : PadicComplex l}
    (hy : y ∈ inC (Ks K j)) : act g y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x hx
  change act g (x : PadicComplex l) = (x : PadicComplex l)
  rw [hact.1, this]

/- English proof (translation)
The claim follows from `closure_minimal (t := {y : PadicComplex l | ‖y‖ ≤ 1}) (fun _ h => h.2) (isClosed_le continuous_norm continuous_const) hx`.
-/
theorem norm_le_one_of_mem_Ohat {K : FinExt l} {x : PadicComplex l} (hx : x ∈ Ohat K) :
    ‖x‖ ≤ 1 :=
  closure_minimal (t := {y : PadicComplex l | ‖y‖ ≤ 1}) (fun _ h => h.2)
    (isClosed_le continuous_norm continuous_const) hx

/- English proof (translation)
Introduce `l hl act χ hact hχ K j hj g hg r U hU hU1 i`. Take `⟨-, -, hO, hmul, hstab, -⟩` from `GlobalTheory.TateDecomp.tate_decomposition l act χ hact hχ K j hj.1`. Establish `hg0 : g ∈ (K0 K).fixingSubgroup` using `IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Ks K j) hg.1`. Establish `hgX` using `hstab g hg0`. Establish `hX1 : ∀ x ∈ Xj K j, ‖x‖ ≤ 1` using `fun x hx => norm_le_one_of_mem_Ohat (hO x hx)`.

Prove the components needed by the constructor for the conclusion. Introduce `y hy hfix haveI : NeZero l := ⟨hl.1.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (PadicComplex l) l`. Take `⟨S, hS, -, hlin⟩` from `GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ`. Take `⟨B, c, -, hc1, hB, hBO, hBe⟩` from `exists_quot hj hg (U g) hU hU1 i hζ`.

Take `⟨π, B', hπO, hπ, hB'O, rfl⟩` from `exists_factor B (fun a b => (hB a b).trans_lt hc1) hBO`. Establish `hp : ζ - 1 ∈ intC (Ks K j)` using `⟨(mem_inC_iff _ _).2 (sub_mem ((mem_inC_iff _ _).1 (root_mem_inC K hj.1 hζ)) (one_mem _)), ((norm_root_sub_one hζ).trans_lt rho_lt_one).le⟩`. Use `inj_of_lattice (Xj K j) hX1 (act g) hgX (ζ - 1) (sub_ne_zero.2 (hζ.ne_one hl.1.one_lt)) π hπ (act_fix hact hg.1 hπO.1) S (fun x hx => ⟨(hS x hx).1, (hS x hx).2.2⟩) (fun k x hx => hlin _ (mul_mem_intC hp (neg_pow_mem_intC hπO k)) x hx) B' (fun a b => hmul _ (hB'O a b)) y hy fun a …` and prove the remaining obligations. Rewrite using `[← twAct_sub hBe, hfix, sub_self, Pi.zero_apply]`. Introduce `ζ hζ w hw`.

Take `⟨S, hS, -, -⟩` from `GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ`. Take `⟨B, c, -, hc1, hB, hBO, hBe⟩` from `exists_quot hj hg (U g) hU hU1 i hζ`. Take `⟨π, B', hπO, hπ, hB'O, rfl⟩` from `exists_factor B (fun a b => (hB a b).trans_lt hc1) hBO`. Take `⟨y, hy, he⟩` from `surj_of_lattice (Xj K j) (AddSubgroup.isClosed_topologicalClosure _) hX1 (act g) (hact.2 g) hgX (ζ - 1) π hπ (act_fix hact hg.1 hπO.1) (hmul _ hπO) S (fun x hx => ⟨(hS x hx).1, (hS x hx).2.1⟩) B' (fun a b => hmul _ (hB'O a b)) w hw`. Use `⟨y, hy, funext fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[twAct_sub hBe, he, Pi.smul_apply, smul_eq_mul]`.
-/
theorem perturbation : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ g, IsGen χ K j g → ∀ (r : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)), (∀ a b, U g a b ∈ intC (Ks K j)) → (∀ a b, ‖(U g - 1) a b‖ < rho1 l) → ∀ i : ℤ, (∀ y : Fin r → PadicComplex l, (∀ a, y a ∈ Xj K j) → twAct act χ i U g y = y → y = 0) ∧ ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ l → ∀ w : Fin r → PadicComplex l, (∀ a, w a ∈ Xj K j) → ∃ y : Fin r → PadicComplex l, (∀ a, y a ∈ Xj K j) ∧ twAct act χ i U g y - y = (ζ - 1) • w := by
  intro l hl act χ hact hχ K j hj g hg r U hU hU1 i
  obtain ⟨-, -, hO, hmul, hstab, -⟩ := GlobalTheory.TateDecomp.tate_decomposition l act χ hact hχ K j hj.1
  have hg0 : g ∈ (K0 K).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Ks K j) hg.1
  have hgX := hstab g hg0
  have hX1 : ∀ x ∈ Xj K j, ‖x‖ ≤ 1 := fun x hx => norm_le_one_of_mem_Ohat (hO x hx)
  constructor
  · intro y hy hfix
    haveI : NeZero l := ⟨hl.1.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicComplex l) l
    obtain ⟨S, hS, -, hlin⟩ := GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ
    obtain ⟨B, c, -, hc1, hB, hBO, hBe⟩ := exists_quot hj hg (U g) hU hU1 i hζ
    obtain ⟨π, B', hπO, hπ, hB'O, rfl⟩ := exists_factor B (fun a b => (hB a b).trans_lt hc1) hBO
    have hp : ζ - 1 ∈ intC (Ks K j) :=
      ⟨(mem_inC_iff _ _).2 (sub_mem ((mem_inC_iff _ _).1 (root_mem_inC K hj.1 hζ)) (one_mem _)),
        ((norm_root_sub_one hζ).trans_lt rho_lt_one).le⟩
    refine inj_of_lattice (Xj K j) hX1 (act g) hgX (ζ - 1)
      (sub_ne_zero.2 (hζ.ne_one hl.1.one_lt)) π hπ (act_fix hact hg.1 hπO.1) S
      (fun x hx => ⟨(hS x hx).1, (hS x hx).2.2⟩)
      (fun k x hx => hlin _ (mul_mem_intC hp (neg_pow_mem_intC hπO k)) x hx)
      B' (fun a b => hmul _ (hB'O a b)) y hy fun a => ?_
    rw [← twAct_sub hBe, hfix, sub_self, Pi.zero_apply]
  · intro ζ hζ w hw
    obtain ⟨S, hS, -, -⟩ := GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ
    obtain ⟨B, c, -, hc1, hB, hBO, hBe⟩ := exists_quot hj hg (U g) hU hU1 i hζ
    obtain ⟨π, B', hπO, hπ, hB'O, rfl⟩ := exists_factor B (fun a b => (hB a b).trans_lt hc1) hBO
    obtain ⟨y, hy, he⟩ := surj_of_lattice (Xj K j) (AddSubgroup.isClosed_topologicalClosure _) hX1
      (act g) (hact.2 g) hgX (ζ - 1) π hπ (act_fix hact hg.1 hπO.1) (hmul _ hπO) S
      (fun x hx => ⟨(hS x hx).1, (hS x hx).2.1⟩) B' (fun a b => hmul _ (hB'O a b)) w hw
    refine ⟨y, hy, funext fun a => ?_⟩
    rw [twAct_sub hBe, he, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.CycPerturb
