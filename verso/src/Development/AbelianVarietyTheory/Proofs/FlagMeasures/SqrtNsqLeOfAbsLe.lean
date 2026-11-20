import Mathlib
import Formalism.RealPlaceAnalysis.StatementU
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SumOfSquaresIdentityHolds
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RhoNNormLeAndCasimirArith
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KtypesWithinSteps

open Formalism.REAL Finset
open scoped InnerProductSpace

namespace GlobalTheory.AlgStep

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq]`. Simplify using `[nsq, dot, sq]`.
-/
theorem sqrt_nsq_eq_norm {n : ℕ} (u : Fin n → ℝ) :
    Real.sqrt (nsq u) = ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [nsq, dot, sq]

/- English proof (translation)
Simplify using `only [sqrt_nsq_eq_norm, WithLp.toLp_add]`. Conclude with `norm_add_le _ _`.
-/
theorem sqrt_nsq_add_le {n : ℕ} (u v : Fin n → ℝ) :
    Real.sqrt (nsq (u + v)) ≤ Real.sqrt (nsq u) + Real.sqrt (nsq v) := by
  simp only [sqrt_nsq_eq_norm, WithLp.toLp_add]
  exact norm_add_le _ _

/- English proof (translation)
Unfold `nsq dot`. Conclude with `Finset.sum_nonneg fun a _ => mul_self_nonneg (u a)`.
-/
theorem nsq_nonneg' {n : ℕ} (u : Fin n → ℝ) : 0 ≤ nsq u := by
  unfold nsq dot
  exact Finset.sum_nonneg fun a _ => mul_self_nonneg (u a)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [Finset.sum_range_succ, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_range_sub_sq (c : ℝ) (n : ℕ) :
    ∑ i ∈ range n, (c - (i : ℝ)) * (c - (i : ℝ)) =
      n * c ^ 2 - c * n * (n - 1) + (n - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/- English proof (translation)
Establish `h : nsq (rhoC ε + rhoN ε) = ∑ i ∈ range n, (((n : ℝ) - 1) / 2 - (i : ℝ)) * (((n : ℝ) - 1) / 2 - (i : ℝ))`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun i : ℕ => (((n : ℝ) - 1) / 2 - (i : ℝ)) * (((n : ℝ) - 1) / 2 - (i : ℝ)))]`. Unfold `nsq dot`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.add_apply, half_sum_roots_standard n ε a]`.

Rewrite using `[h, sum_range_sub_sq]`. Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nsq_rho_le {n : ℕ} (ε : Fin n → Bool) : nsq (rhoC ε + rhoN ε) ≤ (n : ℝ) ^ 3 / 12 := by
  have h : nsq (rhoC ε + rhoN ε) =
      ∑ i ∈ range n, (((n : ℝ) - 1) / 2 - (i : ℝ)) * (((n : ℝ) - 1) / 2 - (i : ℝ)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => (((n : ℝ) - 1) / 2 - (i : ℝ)) * (((n : ℝ) - 1) / 2 - (i : ℝ)))]
    unfold nsq dot
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.add_apply, half_sum_roots_standard n ε a]
  rw [h, sum_range_sub_sq]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/- English proof (translation)
Introduce `y hy`. Take `⟨m, x, μ, h1, h2, h3⟩` from `kDecomp V n ε F S hfin hr hu hS`. Establish `hy' : y ∈ ⨆ i ∈ (univ : Finset (Fin m)), kSpan ε F (x i)` using `by simpa [h3] using hy`. Take `⟨v, hv⟩` from `(Submodule.mem_iSup_finset_iff_exists_sum _ y).1 hy'`. Establish `hC : CasK ε F y = ∑ i, ((ckv ε (μ i) : ℝ) : ℂ) • (v i : V)`.

Rewrite using `[← hv, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => kCasSpan V n ε F (μ i) (x i) hr (h1 i).2.2 _ (v i).2`. Establish `key : ∀ c : Fin m → ℂ, ⟪y, ∑ i, c i • (v i : V)⟫_ℂ = ∑ i, c i * ⟪(v i : V), (v i : V)⟫_ℂ`. Introduce `c`. Rewrite using `[← hv, sum_inner]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[inner_sum, Finset.sum_eq_single j]`. Rewrite using `[inner_smul_right]`. Introduce `i _ hij`. Rewrite using `[inner_smul_right, h2 j i (Ne.symm hij) _ (v j).2 _ (v i).2, mul_zero]`.

Simplify using the standard rewrite rules. Establish `hvv : ∀ i, ⟪(v i : V), (v i : V)⟫_ℂ = ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ)` using `fun i => by`. Rewrite using `[inner_self_eq_norm_sq_to_K]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hn : ‖y‖ ^ 2 = ∑ i, ‖(v i : V)‖ ^ 2`. Establish `h` using `key (fun _ => 1)`. Simplify using `only [one_smul, one_mul, hv, inner_self_eq_norm_sq_to_K] at h`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`.

Conclude with `h`. Establish `key2` using `key (fun i => ((ckv ε (μ i) : ℝ) : ℂ))`. Rewrite using `[hC, key2]`. Simplify using `only [hvv]`. Establish `hre : (∑ i, ((ckv ε (μ i) : ℝ) : ℂ) * ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ)).re = ∑ i, ckv ε (μ i) * ‖(v i : V)‖ ^ 2`.

Simplify using `only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]`. Rewrite using `[hre, hn, Finset.mul_sum]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Apply `mul_le_mul_of_nonneg_right _ (sq_nonneg _)` to reduce the goal to its premises.

Conclude with `hw (μ i) (x i) (h1 i).1 (h1 i).2.1 (h1 i).2.2`.
-/
theorem casK_form_le (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (M : ℝ) (hfin : FiniteDimensional ℂ S)
    (hr : KRel ε F) (hu : KUnit ε F) (hS : KStable ε F S)
    (hw : ∀ (μ : Fin n → ℝ), ∀ x ∈ S, x ≠ 0 → KHighest ε F μ x → ckv ε μ ≤ M) :
    ∀ y ∈ S, (⟪y, CasK ε F y⟫_ℂ).re ≤ M * ‖y‖ ^ 2 := by
  intro y hy
  obtain ⟨m, x, μ, h1, h2, h3⟩ := kDecomp V n ε F S hfin hr hu hS
  have hy' : y ∈ ⨆ i ∈ (univ : Finset (Fin m)), kSpan ε F (x i) := by simpa [h3] using hy
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ y).1 hy'
  have hC : CasK ε F y = ∑ i, ((ckv ε (μ i) : ℝ) : ℂ) • (v i : V) := by
    rw [← hv, map_sum]
    exact Finset.sum_congr rfl fun i _ => kCasSpan V n ε F (μ i) (x i) hr (h1 i).2.2 _ (v i).2
  have key : ∀ c : Fin m → ℂ,
      ⟪y, ∑ i, c i • (v i : V)⟫_ℂ = ∑ i, c i * ⟪(v i : V), (v i : V)⟫_ℂ := by
    intro c
    rw [← hv, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_right]
    · intro i _ hij
      rw [inner_smul_right, h2 j i (Ne.symm hij) _ (v j).2 _ (v i).2, mul_zero]
    · simp
  have hvv : ∀ i, ⟪(v i : V), (v i : V)⟫_ℂ = ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hn : ‖y‖ ^ 2 = ∑ i, ‖(v i : V)‖ ^ 2 := by
    have h := key (fun _ => 1)
    simp only [one_smul, one_mul, hv, inner_self_eq_norm_sq_to_K] at h
    apply Complex.ofReal_injective
    push_cast
    exact h
  have key2 := key (fun i => ((ckv ε (μ i) : ℝ) : ℂ))
  rw [hC, key2]
  simp only [hvv]
  have hre : (∑ i, ((ckv ε (μ i) : ℝ) : ℂ) * ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ)).re =
      ∑ i, ckv ε (μ i) * ‖(v i : V)‖ ^ 2 := by
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hre, hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact hw (μ i) (x i) (h1 i).1 (h1 i).2.1 (h1 i).2.2

/- English proof (translation)
Establish `h1 : nsq lam ≤ (n : ℝ) * (b ^ 2) ^ 2`. Establish `: ∑ a : Fin n, lam a * lam a ≤ ∑ _a : Fin n, (b ^ 2) ^ 2`. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← sq, ← sq_abs]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) (h a) 2`.

Simplify `this` using `[nsq, dot]`. Rewrite using `[← Real.sqrt_eq_rpow]`. Use `(Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (sq_nonneg b)]`.
-/
theorem sqrt_nsq_le_of_abs_le {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (h : ∀ a, |lam a| ≤ b ^ 2) :
    Real.sqrt (nsq lam) ≤ (n : ℝ) ^ (1 / 2 : ℝ) * b ^ 2 := by
  have h1 : nsq lam ≤ (n : ℝ) * (b ^ 2) ^ 2 := by
    have : ∑ a : Fin n, lam a * lam a ≤ ∑ _a : Fin n, (b ^ 2) ^ 2 := by
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h a) 2
    simpa [nsq, dot] using this
  rw [← Real.sqrt_eq_rpow]
  refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (sq_nonneg b)]

end GlobalTheory.AlgStep

namespace GlobalTheory

open GlobalTheory.AlgStep

/- English proof (translation)
Introduce `V _ _ n ε E lam u b hg hu hk hb j x hx`. Take `⟨hhi, hcas, hfin⟩` from `hk`. Take `⟨-, -, hst, -, hcyc, -, hfd⟩` from `pfilFacts V n ε E u hg`. Use `set L := Real.sqrt (nsq lam) with hL`. Use `set A := Real.sqrt (nsq (rhoN ε)) + Real.sqrt 2 * j with hA`.

Establish `hL0 : 0 ≤ L` using `Real.sqrt_nonneg _`. Establish `hA0 : 0 ≤ A` using `by positivity`. Establish `hK` using `casK_form_le V n ε E (pfil ε E u j) ((L + A) ^ 2) (hfd hfin j) (glRel_kRel ε E hg) (isUnitary_kUnit ε E hu) (hst j) (by`. Introduce `μ y hy hy0 hyh`. Establish `h1` using `GlobalTheory.KTypeSteps.ktypes_within_steps V n ε E (LamOf ε lam) u hg hu hhi hfin j μ y hy hy0 hyh`.

Establish `h2 : μ + rhoC ε = (lam + rhoN ε) + (μ - LamOf ε lam)`. Unfold `LamOf`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : Real.sqrt (nsq (μ + rhoC ε)) ≤ L + A`. Rewrite using `[h2]`.

Use `sqrt_nsq_add_le (lam + rhoN ε) (μ - LamOf ε lam)` as an intermediate fact. Use `sqrt_nsq_add_le lam (rhoN ε)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4` using `(Real.sqrt_le_iff.mp h3).2`. Establish `h5` using `nsq_nonneg' (rhoC ε)`.

Unfold `ckv`. Use the proof step `linarith) x hx`. Establish `hC : Cas E x = ((cvalR ε lam : ℝ) : ℂ) • x` using `casOnCyc V n E _ u hg hcas x (hcyc j hx)`. Establish `hS` using `congrArg Complex.re (sumOfSquaresIdentity_holds V n ε E x hu)`. Establish `hxx : ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ)`.

Rewrite using `[inner_self_eq_norm_sq_to_K]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite `hS` using `[Complex.ofReal_re, LinearMap.sub_apply, two_smul, LinearMap.add_apply, hC, inner_sub_right, inner_add_right, inner_smul_right, hxx, ← Complex.ofReal_mul, Complex.sub_re, Complex.add_re, Complex.ofReal_re]`. Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`.

Establish `har` using `rhoN_norm_le_and_casimir_arith.2 L A n hL0 hA0 hn`. Establish `hr` using `rhoN_norm_le_and_casimir_arith.1 n ε`. Establish `hp : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 2)` using `Real.rpow_nonneg hn _`. Establish `hLb` using `sqrt_nsq_le_of_abs_le lam b hb`. Establish `h2 : Real.sqrt 2 ≤ 3 / 2` using `Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩`.

Establish `hj : Real.sqrt 2 * j ≤ 3 / 2 * j` using `mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg j)`. Establish `hle : L + 2 * A + 0.3 * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsq : (L + 2 * A + 0.3 * (n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j ^ 2` using `pow_le_pow_left₀ (by positivity) hle 2`.

Establish `hL2 : L ^ 2 = nsq lam` using `Real.sq_sqrt (nsq_nonneg' lam)`. Establish `hrho` using `nsq_rho_le ε`. Establish `hc : 2 * (L + A) ^ 2 - cvalR ε lam ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j ^ 2`. Unfold `cvalR`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖)` as an intermediate fact. Rewrite using `[hS]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem algebraic_step_bound : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ)
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V) (b : ℝ),
    GlRel E → IsUnitary ε E → KindA ε E lam u → (∀ a, |lam a| ≤ b ^ 2) →
    ∀ (j : ℕ), ∀ x ∈ pfil ε E u j,
      ∑ a, ∑ c, ‖E a c x‖ ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j ^ 2 * ‖x‖ ^ 2 := by
  intro V _ _ n ε E lam u b hg hu hk hb j x hx
  obtain ⟨hhi, hcas, hfin⟩ := hk
  obtain ⟨-, -, hst, -, hcyc, -, hfd⟩ := pfilFacts V n ε E u hg
  set L := Real.sqrt (nsq lam) with hL
  set A := Real.sqrt (nsq (rhoN ε)) + Real.sqrt 2 * j with hA
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := by positivity
  have hK := casK_form_le V n ε E (pfil ε E u j) ((L + A) ^ 2) (hfd hfin j) (glRel_kRel ε E hg)
    (isUnitary_kUnit ε E hu) (hst j) (by
      intro μ y hy hy0 hyh
      have h1 := GlobalTheory.KTypeSteps.ktypes_within_steps V n ε E (LamOf ε lam) u hg hu hhi hfin j μ y hy hy0 hyh
      have h2 : μ + rhoC ε = (lam + rhoN ε) + (μ - LamOf ε lam) := by
        unfold LamOf; ring
      have h3 : Real.sqrt (nsq (μ + rhoC ε)) ≤ L + A := by
        rw [h2]
        have := sqrt_nsq_add_le (lam + rhoN ε) (μ - LamOf ε lam)
        have := sqrt_nsq_add_le lam (rhoN ε)
        linarith
      have h4 := (Real.sqrt_le_iff.mp h3).2
      have h5 := nsq_nonneg' (rhoC ε)
      unfold ckv
      linarith) x hx
  have hC : Cas E x = ((cvalR ε lam : ℝ) : ℂ) • x := casOnCyc V n E _ u hg hcas x (hcyc j hx)
  have hS := congrArg Complex.re (sumOfSquaresIdentity_holds V n ε E x hu)
  have hxx : ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [Complex.ofReal_re, LinearMap.sub_apply, two_smul, LinearMap.add_apply, hC, inner_sub_right,
    inner_add_right, inner_smul_right, hxx, ← Complex.ofReal_mul, Complex.sub_re, Complex.add_re,
    Complex.ofReal_re] at hS
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have har := rhoN_norm_le_and_casimir_arith.2 L A n hL0 hA0 hn
  have hr := rhoN_norm_le_and_casimir_arith.1 n ε
  have hp : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hn _
  have hLb := sqrt_nsq_le_of_abs_le lam b hb
  have h2 : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hj : Real.sqrt 2 * j ≤ 3 / 2 * j := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg j)
  have hle : L + 2 * A + 0.3 * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst
    linarith
  have hsq : (L + 2 * A + 0.3 * (n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j ^ 2 :=
    pow_le_pow_left₀ (by positivity) hle 2
  have hL2 : L ^ 2 = nsq lam := Real.sq_sqrt (nsq_nonneg' lam)
  have hrho := nsq_rho_le ε
  have hc : 2 * (L + A) ^ 2 - cvalR ε lam ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j ^ 2 := by
    unfold cvalR
    linarith
  have := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖)
  rw [hS]
  linarith

end GlobalTheory
