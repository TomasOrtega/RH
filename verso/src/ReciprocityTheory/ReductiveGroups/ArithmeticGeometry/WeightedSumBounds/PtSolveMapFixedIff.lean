import Mathlib
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst

namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

open Classical

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def PTGood (v : AddValuation C (WithTop ℝ)) {ι τ : Type*} (x : ι → MvPowerSeries τ C) : Prop :=
  ∀ i, constantCoeff (x i) = 0 ∧ x i ∈ ptIntSer v τ

/- English proof (translation)
Introduce `_` and use `⟨map_zero _, zero_mem _⟩`.
-/
theorem ptGood_zero {ι τ : Type*} : PTGood v (0 : ι → MvPowerSeries τ C) := fun _ => ⟨map_zero _, zero_mem _⟩

/- English proof (translation)
Introduce `i`. Establish `hc : ∀ e, coeff e (x i) = coeff e ((T^[e.degree + 1] 0) i)` using `fun e => hx (e.degree + 1) i e (Nat.lt_succ_self _)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `(hP _ i).1`.

Use `show ∀ α, coeff α (x i) ∈ ptIntSub v`. Introduce `α`. Establish `h : ∀ β, coeff β ((T^[α.degree + 1] 0) i) ∈ ptIntSub v` using `(hP _ i).2`. Rewrite using `[hc]`. Conclude with `h α`.
-/
theorem ptGood_lim {ι τ : Type*} {T : (ι → MvPowerSeries τ C) → (ι → MvPowerSeries τ C)}
    (hP : ∀ n, PTGood v (T^[n] 0)) (x : ι → MvPowerSeries τ C)
    (hx : ∀ n, PTAgree n x (T^[n] 0)) : PTGood v x := by
  intro i
  have hc : ∀ e, coeff e (x i) = coeff e ((T^[e.degree + 1] 0) i) :=
    fun e => hx (e.degree + 1) i e (Nat.lt_succ_self _)
  refine ⟨?_, ?_⟩
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hP _ i).1
  · show ∀ α, coeff α (x i) ∈ ptIntSub v
    intro α
    have h : ∀ β, coeff β ((T^[α.degree + 1] 0) i) ∈ ptIntSub v := (hP _ i).2
    rw [hc]
    exact h α

/- English proof (translation)
Establish `hs : subst x (∑ a, m a • X a : MvPowerSeries σ C) = ∑ a, m a • x a`. Rewrite using `[← MvPowerSeries.coe_substAlgHom hx, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coe_substAlgHom hx, MvPowerSeries.subst_smul hx, MvPowerSeries.subst_X hx]`. Rewrite using `[MvPowerSeries.subst_sub hx, hs]`.

Normalize the expressions using the abelian group laws.
-/
theorem pt_subst_lin_split {σ τ : Type*} [Fintype σ] {x : σ → MvPowerSeries τ C}
    (hx : HasSubst x) (Φ : MvPowerSeries σ C) (m : σ → C) :
    subst x Φ = ∑ a, m a • x a + subst x (Φ - ∑ a, m a • X a) := by
  have hs : subst x (∑ a, m a • X a : MvPowerSeries σ C) = ∑ a, m a • x a := by
    rw [← MvPowerSeries.coe_substAlgHom hx, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hx, MvPowerSeries.subst_smul hx, MvPowerSeries.subst_X hx]
  rw [MvPowerSeries.subst_sub hx, hs]
  abel

/- English proof (translation)
Introduce `α hα`. Rewrite using `[map_sub, map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Break down `Nat.le_one_iff_eq_zero_or_eq_one.mp hα with h | h` into its components or cases. Take `rfl` from `(Finsupp.degree_eq_zero_iff α).mp h`.

Simplify using `[MvPowerSeries.coeff_X, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]`. Use `Finset.sum_eq_zero fun a _ => if_neg ?_` and prove the remaining obligations. Conclude with `fun e => (Finsupp.single_ne_zero.mpr one_ne_zero) e.symm`. Establish `hne : α ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at h`. Take `⟨s, hs⟩` from `Finsupp.ne_iff.mp hne`. Simplify using `only [Finsupp.coe_zero, Pi.zero_apply] at hs`. Establish `hle : Finsupp.single s 1 ≤ α`. Rewrite using `[Finsupp.le_def]`.

Introduce `i`. Distinguish the cases in `hi : i = s`. Substitute `hi` using the available equality. Simplify using `only [Finsupp.single_eq_same]`. Use linear arithmetic over natural numbers and integers.

Simplify using `[Finsupp.single_apply, Ne.symm hi]`. Establish `hadd` using `add_tsub_cancel_of_le hle`. Establish `hd` using `congrArg Finsupp.degree hadd`. Rewrite `hd` using `[map_add, Finsupp.degree_single, h]`. Establish `h0' : α - Finsupp.single s 1 = 0` using `(Finsupp.degree_eq_zero_iff _).mp (by omega)`.

Rewrite using `[← hadd, h0', add_zero]`. Simplify using `[MvPowerSeries.coeff_X, hm, Finsupp.single_left_inj one_ne_zero]`.
-/
theorem pt_low_of_lin {σ : Type*} [Fintype σ] {Φ : MvPowerSeries σ C}
    (h0 : constantCoeff Φ = 0) (m : σ → C)
    (hm : ∀ s, coeff (Finsupp.single s 1) Φ = m s) :
    ∀ α : σ →₀ ℕ, α.degree ≤ 1 → coeff α (Φ - ∑ a, m a • X a) = 0 := by
  intro α hα
  rw [map_sub, map_sum]
  simp only [map_smul, smul_eq_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hα with h | h
  · obtain rfl := (Finsupp.degree_eq_zero_iff α).mp h
    simp [MvPowerSeries.coeff_X, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    refine Finset.sum_eq_zero fun a _ => if_neg ?_
    exact fun e => (Finsupp.single_ne_zero.mpr one_ne_zero) e.symm
  · have hne : α ≠ 0 := by
      rintro rfl
      simp at h
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hne
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hs
    have hle : Finsupp.single s 1 ≤ α := by
      rw [Finsupp.le_def]
      intro i
      by_cases hi : i = s
      · subst hi
        simp only [Finsupp.single_eq_same]
        omega
      · simp [Finsupp.single_apply, Ne.symm hi]
    have hadd := add_tsub_cancel_of_le hle
    have hd := congrArg Finsupp.degree hadd
    rw [map_add, Finsupp.degree_single, h] at hd
    have h0' : α - Finsupp.single s 1 = 0 := (Finsupp.degree_eq_zero_iff _).mp (by omega)
    rw [← hadd, h0', add_zero]
    simp [MvPowerSeries.coeff_X, hm, Finsupp.single_left_inj one_ne_zero]

section Solve

variable {d : ℕ} {σ τ : Type*} [Finite σ]
  (A : (Fin d → MvPowerSeries τ C) → σ → MvPowerSeries τ C)
  (K : Fin d → MvPowerSeries σ C) (M N : Matrix (Fin d) (Fin d) C)
  (f : Fin d → MvPowerSeries τ C)

def ptSolveMap (x : Fin d → MvPowerSeries τ C) : Fin d → MvPowerSeries τ C :=
  fun c => ∑ b, N b c • (f b - subst (A x) (K b))

/- English proof (translation)
Repeatedly rewrite using `[Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul]`. Establish `e : ∀ a, ∑ b, Q b c * P a b = (P * Q) a c` using `fun a => by`. Rewrite using `[Matrix.mul_apply]`.

Conclude with `Finset.sum_congr rfl fun b _ => mul_comm _ _`. Repeatedly rewrite using `[e, hPQ, Matrix.one_apply, ite_smul, one_smul, zero_smul]`. Simplify using the standard rewrite rules.
-/
private lemma sum_smul_sum_smul_eq_of_mul_eq_one (P Q : Matrix (Fin d) (Fin d) C) (hPQ : P * Q = 1)
    (z : Fin d → MvPowerSeries τ C) (c : Fin d) : ∑ b, Q b c • ∑ a, P a b • z a = z c := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have e : ∀ a, ∑ b, Q b c * P a b = (P * Q) a c := fun a => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  simp_rw [e, hPQ, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx b`. Establish `e` using `sum_smul_sum_smul_eq_of_mul_eq_one N M hNM (fun c => f c - subst (A x) (K c)) b`. Establish `hx' : ∀ a, ∑ c, N c a • (f c - subst (A x) (K c)) = x a` using `fun a => congrFun hx a`. Rewrite `e` using `[hx']`.

Rewrite using `[e]`. Normalize the expressions using the abelian group laws. Introduce `h`. Use function extensionality and compare the values at `c`. Establish `hy : ∀ b, f b - subst (A x) (K b) = ∑ a, M a b • x a` using `fun b => by`.

Rewrite using `[← h b]`. Normalize the expressions using the abelian group laws. Simplify using `only [ptSolveMap]`. Repeatedly rewrite using `[hy]`. Conclude with `sum_smul_sum_smul_eq_of_mul_eq_one M N hMN x c`.
-/
theorem ptSolveMap_fixed_iff (hNM : N * M = 1) (hMN : M * N = 1)
    (x : Fin d → MvPowerSeries τ C) :
    ptSolveMap A K N f x = x ↔ ∀ b, ∑ a, M a b • x a + subst (A x) (K b) = f b := by
  constructor
  · intro hx b
    have e := sum_smul_sum_smul_eq_of_mul_eq_one N M hNM (fun c => f c - subst (A x) (K c)) b
    have hx' : ∀ a, ∑ c, N c a • (f c - subst (A x) (K c)) = x a := fun a => congrFun hx a
    simp_rw [hx'] at e
    rw [e]
    abel
  · intro h
    funext c
    have hy : ∀ b, f b - subst (A x) (K b) = ∑ a, M a b • x a := fun b => by
      rw [← h b]
      abel
    simp only [ptSolveMap]
    simp_rw [hy]
    exact sum_smul_sum_smul_eq_of_mul_eq_one M N hMN x c

variable {A K}

/- English proof (translation)
Introduce `c e he`. Simplify using `only [ptSolveMap, map_sum, coeff_smul, map_sub]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[pt_subst_agree (hasSubst_of_constantCoeff_zero (hA0 x hx)) (hasSubst_of_constantCoeff_zero (hA0 y hy)) (hA0 x hx) (hA0 y hy) (K b) k (hAag k x y hx hy hxy) (fun α hα => (hK b α hα).imp id (fun h => h x y hx hy)) e he]`.
-/
theorem ptSolveMap_agree
    (hA0 : ∀ x, PTGood v x → ∀ s, constantCoeff (A x s) = 0)
    (hAag : ∀ k x y, PTGood v x → PTGood v y → PTAgree k x y →
      ∀ s (e : τ →₀ ℕ), e.degree < k → coeff e (A x s) = coeff e (A y s))
    (hK : ∀ b α, coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y, PTGood v x → PTGood v y → ∀ s ∈ α.support, A x s = A y s)
    (k : ℕ) (x y : Fin d → MvPowerSeries τ C) (hx : PTGood v x) (hy : PTGood v y)
    (hxy : PTAgree k x y) :
    PTAgree (k + 1) (ptSolveMap A K N f x) (ptSolveMap A K N f y) := by
  intro c e he
  simp only [ptSolveMap, map_sum, coeff_smul, map_sub]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [pt_subst_agree (hasSubst_of_constantCoeff_zero (hA0 x hx))
    (hasSubst_of_constantCoeff_zero (hA0 y hy)) (hA0 x hx) (hA0 y hy) (K b) k
    (hAag k x y hx hy hxy) (fun α hα => (hK b α hα).imp id (fun h => h x y hx hy)) e he]

/- English proof (translation)
Introduce `c`. Establish `hs` using `hasSubst_of_constantCoeff_zero (hA0 x hx)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Simplify using `only [ptSolveMap, map_sum, coeff_smul, map_sub, coeff_zero_eq_constantCoeff_apply, (hf _).1, constantCoeff_subst_eq_zero hs (hA0 x hx) (hK0 _), sub_zero, mul_zero, Finset.sum_const_zero]`.

Conclude with `Subring.sum_mem _ fun b _ => ptIntSer_smul (hN b c) (Subring.sub_mem _ (hf b).2 (ptIntSer_subst hs (hAi x hx) (hKi b)))`.
-/
theorem ptSolveMap_good (hN : ∀ i j, N i j ∈ ptIntSub v) (hf : PTGood v f)
    (hA0 : ∀ x, PTGood v x → ∀ s, constantCoeff (A x s) = 0)
    (hAi : ∀ x, PTGood v x → ∀ s, A x s ∈ ptIntSer v τ)
    (hKi : ∀ b, K b ∈ ptIntSer v σ) (hK0 : ∀ b, constantCoeff (K b) = 0)
    (x : Fin d → MvPowerSeries τ C) (hx : PTGood v x) :
    PTGood v (ptSolveMap A K N f x) := by
  intro c
  have hs := hasSubst_of_constantCoeff_zero (hA0 x hx)
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply]
    simp only [ptSolveMap, map_sum, coeff_smul, map_sub, coeff_zero_eq_constantCoeff_apply,
      (hf _).1, constantCoeff_subst_eq_zero hs (hA0 x hx) (hK0 _), sub_zero, mul_zero,
      Finset.sum_const_zero]
  · exact Subring.sum_mem _ fun b _ => ptIntSer_smul (hN b c)
      (Subring.sub_mem _ (hf b).2 (ptIntSer_subst hs (hAi x hx) (hKi b)))

/- English proof (translation)
Establish `hag : ∀ k (x y : Fin d → MvPowerSeries τ C), PTGood v x → PTGood v y → PTAgree k x y → PTAgree (k + 1) (ptSolveMap A K N f x) (ptSolveMap A K N f y)` using `fun k x y hx hy hxy => ptSolveMap_agree (N := N) (f := f) hA0 hAag hK k x y hx hy hxy`. Establish `hgood : ∀ x, PTGood v x → PTGood v (ptSolveMap A K N f x)` using `fun x hx => ptSolveMap_good (N := N) (f := f) hN hf hA0 hAi hKi hK0 x hx`. Establish `hzero : ∀ x y : Fin d → MvPowerSeries τ C, PTAgree 0 x y` using `fun x y i e he => absurd he (Nat.not_lt_zero _)`. Establish `hmono : ∀ k l (x y : Fin d → MvPowerSeries τ C), l ≤ k → PTAgree k x y → PTAgree l x y` using `fun k l x y hlk h i e he => h i e (lt_of_lt_of_le he hlk)`. Establish `htrans : ∀ k (x y z : Fin d → MvPowerSeries τ C), PTAgree k x y → PTAgree k y z → PTAgree k x z` using `fun k x y z h1 h2 i e he => (h1 i e he).trans (h2 i e he)`.

Establish `hit : ∀ n, PTGood v ((ptSolveMap A K N f)^[n] 0)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact ptGood_zero`. Consider the case `succ n ih`.

Rewrite using `[Function.iterate_succ_apply']`. Conclude with `hgood _ ih`. Establish `hstep : ∀ k, PTAgree k ((ptSolveMap A K N f)^[k] 0) ((ptSolveMap A K N f)^[k + 1] 0)`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => exact hzero _ _`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply' _ (k + 1)]`. Conclude with `hag k _ _ (hit k) (hit (k + 1)) ih`. Establish `hchain : ∀ k m, PTAgree k ((ptSolveMap A K N f)^[k] 0) ((ptSolveMap A K N f)^[k + m] 0)`.

Introduce `k m`. Proceed by induction on `m with`. Consider the case `zero => exact fun i e he => rfl`. Consider the case `succ m ih`. Conclude with `htrans k _ _ _ ih (hmono (k + m) k _ _ (Nat.le_add_right k m) (hstep (k + m)))`.

Set `x : Fin d → MvPowerSeries τ C` to `fun i e => coeff e ((ptSolveMap A K N f)^[e.degree + 1] 0 i)`. Establish `hx : ∀ n, PTAgree n x ((ptSolveMap A K N f)^[n] 0)`. Introduce `n i e he`. Use `show coeff e ((ptSolveMap A K N f)^[e.degree + 1] 0 i) = _`. Establish `hle : e.degree + 1 ≤ n` using `he`.

Establish `h1` using `hchain (e.degree + 1) (n - (e.degree + 1))`. Rewrite `h1` using `[Nat.add_sub_cancel' hle]`. Conclude with `h1 i e (Nat.lt_succ_self _)`. Establish `hxg : PTGood v x` using `ptGood_lim hit x hx`. Establish `hfix : ptSolveMap A K N f x = x`.

Apply `PTAgree.eq` to reduce the goal to its premises. Introduce `k`. Consider the cases of `k with`. Consider the case `zero => exact hzero _ _`. Consider the case `succ k`.

Establish `h1 : PTAgree (k + 1) (ptSolveMap A K N f x) ((ptSolveMap A K N f)^[k + 1] 0)`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `hag k _ _ hxg (hit k) (hx k)`. Conclude with `htrans _ _ _ _ h1 (fun i e he => ((hx (k + 1)) i e he).symm)`. Use `⟨x, ⟨hxg, (ptSolveMap_fixed_iff (A := A) (K := K) (M := M) (N := N) (f := f) hNM hMN x).mp hfix⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `y ⟨hyg, hy⟩`. Establish `hyfix` using `(ptSolveMap_fixed_iff (A := A) (K := K) (M := M) (N := N) (f := f) hNM hMN y).mpr hy`. Apply `PTAgree.eq` to reduce the goal to its premises. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => exact hzero _ _`. Consider the case `succ k ih`. Establish `h2` using `hag k y x hyg hxg ih`. Rewrite `h2` using `[hyfix, hfix]`. Then use the resulting hypothesis.
-/
theorem pt_solve (hNM : N * M = 1) (hMN : M * N = 1) (hN : ∀ i j, N i j ∈ ptIntSub v)
    (hf : PTGood v f)
    (hA0 : ∀ x, PTGood v x → ∀ s, constantCoeff (A x s) = 0)
    (hAi : ∀ x, PTGood v x → ∀ s, A x s ∈ ptIntSer v τ)
    (hAag : ∀ k x y, PTGood v x → PTGood v y → PTAgree k x y →
      ∀ s (e : τ →₀ ℕ), e.degree < k → coeff e (A x s) = coeff e (A y s))
    (hK : ∀ b α, coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y, PTGood v x → PTGood v y → ∀ s ∈ α.support, A x s = A y s)
    (hKi : ∀ b, K b ∈ ptIntSer v σ) (hK0 : ∀ b, constantCoeff (K b) = 0) :
    ∃! x : Fin d → MvPowerSeries τ C,
      PTGood v x ∧ ∀ b, ∑ a, M a b • x a + subst (A x) (K b) = f b := by
  have hag : ∀ k (x y : Fin d → MvPowerSeries τ C), PTGood v x → PTGood v y → PTAgree k x y →
      PTAgree (k + 1) (ptSolveMap A K N f x) (ptSolveMap A K N f y) :=
    fun k x y hx hy hxy => ptSolveMap_agree (N := N) (f := f) hA0 hAag hK k x y hx hy hxy
  have hgood : ∀ x, PTGood v x → PTGood v (ptSolveMap A K N f x) :=
    fun x hx => ptSolveMap_good (N := N) (f := f) hN hf hA0 hAi hKi hK0 x hx
  have hzero : ∀ x y : Fin d → MvPowerSeries τ C, PTAgree 0 x y :=
    fun x y i e he => absurd he (Nat.not_lt_zero _)
  have hmono : ∀ k l (x y : Fin d → MvPowerSeries τ C), l ≤ k → PTAgree k x y → PTAgree l x y :=
    fun k l x y hlk h i e he => h i e (lt_of_lt_of_le he hlk)
  have htrans : ∀ k (x y z : Fin d → MvPowerSeries τ C), PTAgree k x y → PTAgree k y z →
      PTAgree k x z :=
    fun k x y z h1 h2 i e he => (h1 i e he).trans (h2 i e he)
  have hit : ∀ n, PTGood v ((ptSolveMap A K N f)^[n] 0) := by
    intro n
    induction n with
    | zero => exact ptGood_zero
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hgood _ ih
  have hstep : ∀ k, PTAgree k ((ptSolveMap A K N f)^[k] 0) ((ptSolveMap A K N f)^[k + 1] 0) := by
    intro k
    induction k with
    | zero => exact hzero _ _
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply' _ (k + 1)]
      exact hag k _ _ (hit k) (hit (k + 1)) ih
  have hchain : ∀ k m, PTAgree k ((ptSolveMap A K N f)^[k] 0) ((ptSolveMap A K N f)^[k + m] 0) := by
    intro k m
    induction m with
    | zero => exact fun i e he => rfl
    | succ m ih =>
      exact htrans k _ _ _ ih (hmono (k + m) k _ _ (Nat.le_add_right k m) (hstep (k + m)))
  let x : Fin d → MvPowerSeries τ C :=
    fun i e => coeff e ((ptSolveMap A K N f)^[e.degree + 1] 0 i)
  have hx : ∀ n, PTAgree n x ((ptSolveMap A K N f)^[n] 0) := by
    intro n i e he
    show coeff e ((ptSolveMap A K N f)^[e.degree + 1] 0 i) = _
    have hle : e.degree + 1 ≤ n := he
    have h1 := hchain (e.degree + 1) (n - (e.degree + 1))
    rw [Nat.add_sub_cancel' hle] at h1
    exact h1 i e (Nat.lt_succ_self _)
  have hxg : PTGood v x := ptGood_lim hit x hx
  have hfix : ptSolveMap A K N f x = x := by
    apply PTAgree.eq
    intro k
    cases k with
    | zero => exact hzero _ _
    | succ k =>
      have h1 : PTAgree (k + 1) (ptSolveMap A K N f x) ((ptSolveMap A K N f)^[k + 1] 0) := by
        rw [Function.iterate_succ_apply']
        exact hag k _ _ hxg (hit k) (hx k)
      exact htrans _ _ _ _ h1 (fun i e he => ((hx (k + 1)) i e he).symm)
  refine ⟨x, ⟨hxg, (ptSolveMap_fixed_iff (A := A) (K := K) (M := M) (N := N) (f := f)
    hNM hMN x).mp hfix⟩, ?_⟩
  rintro y ⟨hyg, hy⟩
  have hyfix := (ptSolveMap_fixed_iff (A := A) (K := K) (M := M) (N := N) (f := f)
    hNM hMN y).mpr hy
  apply PTAgree.eq
  intro k
  induction k with
  | zero => exact hzero _ _
  | succ k ih =>
    have h2 := hag k y x hyg hxg ih
    rwa [hyfix, hfix] at h2

end Solve

end

end ReciprocityTheory.ChartRestriction.G.Sh
