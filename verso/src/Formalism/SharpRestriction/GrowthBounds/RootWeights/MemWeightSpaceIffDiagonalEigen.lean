import Formalism.SharpRestriction.GrowthBounds.RootWeights.NontrivialIsotypicWeightZeroKilled

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Simplify using `only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`.
-/
theorem mem_weightSpace_iff_diagonal_eigen (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]

/- English proof (translation)
Introduce `a b ν x hx`. Rewrite `hx`, the goal using `[mem_weightSpace_iff_diagonal_eigen]`. Introduce `c`. Establish `h1` using `congrArg (fun T : Module.End K V => T x) (hE.1 c c a b)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at h1`.

Rewrite `h1` using `[sub_eq_iff_eq_add]`. Rewrite using `[h1]`. Simplify using `only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply]`. Apply the tactic sequence `by_cases hca : c = a <;> by_cases hcb : c = b`. Substitute `hca` using the available equality.

Substitute `hcb` using the available equality. Simplify using the standard rewrite rules. Substitute `hca` using the available equality. Establish `: ¬ b = c` using `fun h => hcb h.symm`. Simplify using `[hcb, this]`.

Use `module`. Substitute `hcb` using the available equality. Simplify using `[hca]`. Use `module`. Establish `: ¬ b = c` using `fun h => hcb h.symm`.

Simplify using `[hca, hcb, this]`.
-/
theorem gl_rep_shifts_weights {E : GLOps n K V} (hE : IsGLRep E) : OperatorsShiftWeightsByRoots E := by
  intro a b ν x hx
  rw [mem_weightSpace_iff_diagonal_eigen] at hx ⊢
  intro c
  have h1 := congrArg (fun T : Module.End K V => T x) (hE.1 c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at h1
  rw [sub_eq_iff_eq_add] at h1
  rw [h1]
  simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb; simp
  · subst hca
    have : ¬ b = c := fun h => hcb h.symm
    simp [hcb, this]; module
  · subst hcb
    simp [hca]; module
  · have : ¬ b = c := fun h => hcb h.symm
    simp [hca, hcb, this]

/- English proof (translation)
Establish `hfin : ∀ a, Set.Finite {t : ℤ | (E a a).HasEigenvalue (t : K)}` using `fun a => (Module.End.finite_hasEigenvalue (E a a)).preimage (fun x _ y _ h => by exact_mod_cast h)`. Establish `hT : Set.Finite (⋃ a, {t : ℤ | (E a a).HasEigenvalue (t : K)})` using `Set.finite_iUnion hfin`. Take `⟨m, hm⟩` from `(hT.image Int.natAbs).bddAbove`. Use `⟨m, fun ν hν a => ?_⟩` and prove the remaining obligations. Establish `hev : (E a a).HasEigenvalue ((ν a : ℤ) : K)`.

Rewrite using `[Module.End.hasEigenvalue_iff]`. Take `⟨x, hx, hx0⟩` from `Submodule.ne_bot_iff _ |>.mp hν`. Rewrite `hx` using `[mem_weightSpace_iff_diagonal_eigen]`. Rewrite using `[Submodule.ne_bot_iff]`. Conclude with `⟨x, Module.End.mem_eigenspace_iff.mpr (hx a), hx0⟩`.

Use `hm ⟨ν a, Set.mem_iUnion.mpr ⟨a, hev⟩, rfl⟩` as an intermediate fact. Rewrite using `[Int.abs_eq_natAbs]`. Conclude with `this` after adjusting the coercions.
-/
theorem findim_weights_bounded [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) : WeightsBounded E := by
  classical
  have hfin : ∀ a, Set.Finite {t : ℤ | (E a a).HasEigenvalue (t : K)} := fun a =>
    (Module.End.finite_hasEigenvalue (E a a)).preimage
      (fun x _ y _ h => by exact_mod_cast h)
  have hT : Set.Finite (⋃ a, {t : ℤ | (E a a).HasEigenvalue (t : K)}) := Set.finite_iUnion hfin
  obtain ⟨m, hm⟩ := (hT.image Int.natAbs).bddAbove
  refine ⟨m, fun ν hν a => ?_⟩
  have hev : (E a a).HasEigenvalue ((ν a : ℤ) : K) := by
    rw [Module.End.hasEigenvalue_iff]
    obtain ⟨x, hx, hx0⟩ := Submodule.ne_bot_iff _ |>.mp hν
    rw [mem_weightSpace_iff_diagonal_eigen] at hx
    rw [Submodule.ne_bot_iff]
    exact ⟨x, Module.End.mem_eigenspace_iff.mpr (hx a), hx0⟩
  have := hm ⟨ν a, Set.mem_iUnion.mpr ⟨a, hev⟩, rfl⟩
  rw [Int.abs_eq_natAbs]
  exact_mod_cast this

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ]`. Simplify using `only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`.

Rewrite using `[(mem_weightSpace_iff_diagonal_eigen E ν x).mp hx a, ← sub_smul, map_smul, ih, smul_smul, mul_comm]`.
-/
theorem diagonal_list_prod_eigen_apply (E : GLOps n K V) (a : Fin n) (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) (k : ℕ) :
    (((List.range k).map fun j : ℕ => E a a - (j : K) • (1 : Module.End K V)).prod) x =
      (∏ j ∈ Finset.range k, ((ν a : K) - (j : K))) • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [(mem_weightSpace_iff_diagonal_eigen E ν x).mp hx a, ← sub_smul, map_smul, ih, smul_smul, mul_comm]

/- English proof (translation)
Establish `hk : (k.factorial : K) ≠ 0` using `by exact_mod_cast k.factorial_ne_zero`. Establish `hZ : (k.factorial : ℤ) * Ring.choose (ν a) k = ∏ j ∈ Finset.range k, (ν a - (j : ℤ))`. Rewrite using `[← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]`. Establish `hK : (k.factorial : K) * ((Ring.choose (ν a) k : ℤ) : K) = ∏ j ∈ Finset.range k, ((ν a : K) - (j : K))`. Use `congrArg (fun t : ℤ => (t : K)) hZ` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Rewrite using `[binomE, LinearMap.smul_apply, diagonal_list_prod_eigen_apply E a ν x hx k, ← hK, smul_smul, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]`.
-/
theorem binomial_diagonal_apply_weight [CharZero K] (E : GLOps n K V) (a : Fin n) (ν : Fin n → ℤ) (x : V)
    (hx : x ∈ weightSp E ν) (k : ℕ) :
    binomE E a k x = ((Ring.choose (ν a) k : ℤ) : K) • x := by
  have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hZ : (k.factorial : ℤ) * Ring.choose (ν a) k = ∏ j ∈ Finset.range k, (ν a - (j : ℤ)) := by
    rw [← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval,
      Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
  have hK : (k.factorial : K) * ((Ring.choose (ν a) k : ℤ) : K) =
      ∏ j ∈ Finset.range k, ((ν a : K) - (j : K)) := by
    have := congrArg (fun t : ℤ => (t : K)) hZ
    push_cast at this
    exact this
  rw [binomE, LinearMap.smul_apply, diagonal_list_prod_eigen_apply E a ν x hx k, ← hK, smul_smul,
    ← mul_assoc, inv_mul_cancel₀ hk, one_mul]

def ActsByIntegralPolynomial (E : GLOps n K V) (a : Fin n) (g : ℤ → ℤ) : Prop :=
  ∃ u ∈ binomialDiagonalSubring E, ∀ ν, ∀ x ∈ weightSp E ν, u x = ((g (ν a) : ℤ) : K) • x

/- English proof (translation)
Assemble the required witnesses or components as `⟨binomE E a i, Subring.subset_closure ⟨a, i, rfl⟩, fun ν x hx => binomial_diagonal_apply_weight E a ν x hx i⟩`.
-/
theorem binomial_polynomial_acts_by_choose [CharZero K] (E : GLOps n K V) (a : Fin n) (i : ℕ) :
    ActsByIntegralPolynomial E a (fun z => Ring.choose z i) := ⟨binomE E a i, Subring.subset_closure ⟨a, i, rfl⟩,
    fun ν x hx => binomial_diagonal_apply_weight E a ν x hx i⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, Subring.zero_mem _, fun ν x _ => by simp⟩`.
-/
theorem action_zero (E : GLOps n K V) (a : Fin n) : ActsByIntegralPolynomial E a (fun _ => 0) := ⟨0, Subring.zero_mem _, fun ν x _ => by simp⟩

/- English proof (translation)
Take `⟨u, hu, hux⟩` from `hg`. Take `⟨v, hv, hvx⟩` from `hh`. Use `⟨u + v, Subring.add_mem _ hu hv, fun ν x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.add_apply, hux ν x hx, hvx ν x hx, ← add_smul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem binomial_polynomial_action_add {E : GLOps n K V} {a : Fin n} {g h : ℤ → ℤ} (hg : ActsByIntegralPolynomial E a g) (hh : ActsByIntegralPolynomial E a h) :
    ActsByIntegralPolynomial E a (fun z => g z + h z) := by
  obtain ⟨u, hu, hux⟩ := hg
  obtain ⟨v, hv, hvx⟩ := hh
  refine ⟨u + v, Subring.add_mem _ hu hv, fun ν x hx => ?_⟩
  rw [LinearMap.add_apply, hux ν x hx, hvx ν x hx, ← add_smul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Take `⟨u, hu, hux⟩` from `hg`. Use `⟨u * ((c : Module.End K V)), Subring.mul_mem _ hu (intCast_mem (binomialDiagonalSubring E) c), fun ν x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, Module.End.intCast_apply, map_zsmul, hux ν x hx, ← Int.cast_smul_eq_zsmul K, smul_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem action_mul_const {E : GLOps n K V} {a : Fin n} {g : ℤ → ℤ} (hg : ActsByIntegralPolynomial E a g) (c : ℤ) :
    ActsByIntegralPolynomial E a (fun z => g z * c) := by
  obtain ⟨u, hu, hux⟩ := hg
  refine ⟨u * ((c : Module.End K V)), Subring.mul_mem _ hu (intCast_mem (binomialDiagonalSubring E) c), fun ν x hx => ?_⟩
  rw [Module.End.mul_apply, Module.End.intCast_apply, map_zsmul, hux ν x hx,
    ← Int.cast_smul_eq_zsmul K, smul_smul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using action_zero E a`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.sum_insert hi]`. Conclude with `binomial_polynomial_action_add (hg i (Finset.mem_insert_self i s)) (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))`.
-/
theorem action_finset_sum {E : GLOps n K V} {a : Fin n} {ι : Type*} (s : Finset ι) (g : ι → ℤ → ℤ)
    (hg : ∀ i ∈ s, ActsByIntegralPolynomial E a (g i)) : ActsByIntegralPolynomial E a (fun z => ∑ i ∈ s, g i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using action_zero E a
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact binomial_polynomial_action_add (hg i (Finset.mem_insert_self i s))
      (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Establish `h : (fun z : ℤ => Ring.choose (z + (m : ℤ)) k) = fun z => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, Ring.choose z ij.1 * Ring.choose (m : ℤ) ij.2`. Use function extensionality and compare the values at `z`. Conclude with `Ring.add_choose_eq k (Commute.all z (m : ℤ))`. Rewrite using `[h]`. Conclude with `action_finset_sum _ _ fun ij _ => action_mul_const (binomial_polynomial_acts_by_choose E a ij.1) _`.
-/
theorem binomial_shifted_action [CharZero K] (E : GLOps n K V) (a : Fin n) (m k : ℕ) :
    ActsByIntegralPolynomial E a (fun z => Ring.choose (z + (m : ℤ)) k) := by
  have h : (fun z : ℤ => Ring.choose (z + (m : ℤ)) k) = fun z =>
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, Ring.choose z ij.1 * Ring.choose (m : ℤ) ij.2 := by
    funext z
    exact Ring.add_choose_eq k (Commute.all z (m : ℤ))
  rw [h]
  exact action_finset_sum _ _ fun ij _ => action_mul_const (binomial_polynomial_acts_by_choose E a ij.1) _

/- English proof (translation)
Proceed by induction on `M with`. Consider the case `zero`. Use `⟨fun _ => f 0, fun N hN => ?_⟩` and prove the remaining obligations. Take `rfl : N = 0` from `Nat.le_zero.mp hN`. Simplify using the standard rewrite rules.

Consider the case `succ M ih`. Take `⟨d, hd⟩` from `ih`. Use `set s := ∑ j ∈ Finset.range (M + 1), ((M + 1).choose j : ℤ) * d j with hs`. Use `⟨fun k => if k = M + 1 then f (M + 1) - s else d k, fun N hN => ?_⟩` and prove the remaining obligations. Use `beta_reduce`.

Break down `Nat.lt_or_ge N (M + 1) with h | h` into its components or cases. Establish `e : ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * (if k = M + 1 then f (M + 1) - s else d k) = ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * d k` using `Finset.sum_congr rfl fun k hk => by rw [if_neg (by simp at hk; omega)]`. Rewrite using `[e, hd N (by omega)]`. Take `rfl : N = M + 1` from `by omega`. Rewrite using `[Finset.sum_range_succ]`.

Establish `e : ∑ k ∈ Finset.range (M + 1), ((M + 1).choose k : ℤ) * (if k = M + 1 then f (M + 1) - s else d k) = s`. Rewrite using `[hs]`. Conclude with `Finset.sum_congr rfl fun k hk => by rw [if_neg (by simp at hk; omega)]`. Rewrite using `[e]`. Simplify using the standard rewrite rules.
-/
private theorem exists_binomial_transform_inverse (f : ℕ → ℤ) (M : ℕ) : ∃ d : ℕ → ℤ, ∀ N ≤ M,
    ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * d k = f N := by
  induction M with
  | zero =>
    refine ⟨fun _ => f 0, fun N hN => ?_⟩
    obtain rfl : N = 0 := Nat.le_zero.mp hN
    simp
  | succ M ih =>
    obtain ⟨d, hd⟩ := ih
    set s := ∑ j ∈ Finset.range (M + 1), ((M + 1).choose j : ℤ) * d j with hs
    refine ⟨fun k => if k = M + 1 then f (M + 1) - s else d k, fun N hN => ?_⟩
    beta_reduce
    rcases Nat.lt_or_ge N (M + 1) with h | h
    · have e : ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * (if k = M + 1 then f (M + 1) - s else d k)
          = ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * d k :=
        Finset.sum_congr rfl fun k hk => by rw [if_neg (by simp at hk; omega)]
      rw [e, hd N (by omega)]
    · obtain rfl : N = M + 1 := by omega
      rw [Finset.sum_range_succ]
      have e : ∑ k ∈ Finset.range (M + 1), ((M + 1).choose k : ℤ) *
          (if k = M + 1 then f (M + 1) - s else d k) = s := by
        rw [hs]
        exact Finset.sum_congr rfl fun k hk => by rw [if_neg (by simp at hk; omega)]
      rw [e]
      simp

/- English proof (translation)
Take `⟨d, hd⟩` from `exists_binomial_transform_inverse (fun N => if (N : ℤ) - (m : ℤ) = c then 1 else 0) (2 * m)`. Use `⟨d, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `abs_le.mp hz`. Take `⟨N, hN⟩ : ∃ N : ℕ, z + (m : ℤ) = N` from `⟨(z + m).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩`. Establish `hN2 : N ≤ 2 * m` using `by omega`.

Rewrite using `[hN]`. Establish `hc : ∀ k ∈ range (2 * m + 1), Ring.choose (N : ℤ) k * d k = (N.choose k : ℤ) * d k`. Introduce `k _`. Rewrite using `[Ring.choose_natCast]`. Rewrite using `[Finset.sum_congr rfl hc, ← Finset.sum_range_add_sum_Ico _ (show N + 1 ≤ 2 * m + 1 by omega)]`.

Rewrite using `[Finset.sum_eq_zero (s := Finset.Ico (N + 1) (2 * m + 1)) (fun k hk => by`. Rewrite using `[Nat.choose_eq_zero_of_lt (by simp at hk; omega)]; simp), add_zero, hd N hN2]`. Take `rfl : z = (N : ℤ) - m` from `by omega`. Both sides reduce to the same expression.
-/
theorem newton_interpolation_indicator (m : ℕ) (c : ℤ) : ∃ d : ℕ → ℤ, ∀ z : ℤ, |z| ≤ (m : ℤ) →
    ∑ k ∈ range (2 * m + 1), Ring.choose (z + (m : ℤ)) k * d k = if z = c then 1 else 0 := by
  obtain ⟨d, hd⟩ := exists_binomial_transform_inverse (fun N => if (N : ℤ) - (m : ℤ) = c then 1 else 0) (2 * m)
  refine ⟨d, fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := abs_le.mp hz
  obtain ⟨N, hN⟩ : ∃ N : ℕ, z + (m : ℤ) = N := ⟨(z + m).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hN2 : N ≤ 2 * m := by omega
  rw [hN]
  have hc : ∀ k ∈ range (2 * m + 1), Ring.choose (N : ℤ) k * d k = (N.choose k : ℤ) * d k := by
    intro k _
    rw [Ring.choose_natCast]
  rw [Finset.sum_congr rfl hc, ← Finset.sum_range_add_sum_Ico _ (show N + 1 ≤ 2 * m + 1 by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (N + 1) (2 * m + 1)) (fun k hk => by
      rw [Nat.choose_eq_zero_of_lt (by simp at hk; omega)]; simp), add_zero, hd N hN2]
  obtain rfl : z = (N : ℤ) - m := by omega
  rfl

/- English proof (translation)
Take `⟨d, hd⟩` from `newton_interpolation_indicator m c`. Take `⟨u, hu, hux⟩` from `action_finset_sum (E := E) (a := a) (range (2 * m + 1)) (fun k z => Ring.choose (z + (m : ℤ)) k * d k) (fun k _ => action_mul_const (binomial_shifted_action E a m k) (d k))`. Use `⟨u, hu, fun ν x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[hux ν x hx]`. Distinguish the cases in `h0 : weightSp E ν = ⊥`.

Establish `: x = 0` using `by rw [h0] at hx; exact (Submodule.mem_bot K).mp hx`. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Apply the tactic sequence `simp only [hd (ν a) (hm ν h0 a)] split_ifs <;> simp`.
-/
theorem binomial_indicator_exists [CharZero K] (E : GLOps n K V) (a : Fin n) (m : ℕ)
    (hm : ∀ ν, weightSp E ν ≠ ⊥ → ∀ a, |ν a| ≤ (m : ℤ)) (c : ℤ) :
    ∃ u ∈ binomialDiagonalSubring E, ∀ ν, ∀ x ∈ weightSp E ν, u x = if ν a = c then x else 0 := by
  obtain ⟨d, hd⟩ := newton_interpolation_indicator m c
  obtain ⟨u, hu, hux⟩ := action_finset_sum (E := E) (a := a) (range (2 * m + 1))
    (fun k z => Ring.choose (z + (m : ℤ)) k * d k)
    (fun k _ => action_mul_const (binomial_shifted_action E a m k) (d k))
  refine ⟨u, hu, fun ν x hx => ?_⟩
  rw [hux ν x hx]
  by_cases h0 : weightSp E ν = ⊥
  · have : x = 0 := by rw [h0] at hx; exact (Submodule.mem_bot K).mp hx
    subst this
    simp
  · simp only [hd (ν a) (hm ν h0 a)]
    split_ifs <;> simp

/- English proof (translation)
Take `⟨m, hm⟩` from `findim_weights_bounded E`. Establish `h` using `fun (μ : Fin n → ℤ) (a : Fin n) => binomial_indicator_exists E a m hm (μ a)`. Use `choose u hu hux using h`. Use `⟨fun μ => ((List.finRange n).map (u μ)).prod, fun μ => ?_, fun μ ν x hx => ?_⟩` and prove the remaining obligations. Apply `Subring.list_prod_mem` to reduce the goal to its premises.

Introduce `y hy`. Take `⟨a, _, rfl⟩` from `List.mem_map.mp hy`. Conclude with `hu μ a`. Establish `key : ∀ L : List (Fin n), (L.map (u μ)).prod x = if ∀ a ∈ L, ν a = μ a then x else 0`. Introduce `L`.

Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons b L ih`. Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply, ih]`. Distinguish the cases in `hL : ∀ a ∈ L, ν a = μ a`.

Rewrite using `[if_pos hL, hux μ b ν x hx]`. Distinguish the cases in `hb : ν b = μ b`. Rewrite using `[if_pos hb, if_pos (fun a ha => by rcases List.mem_cons.mp ha with rfl | ha; exacts [hb, hL a ha])]`. Rewrite using `[if_neg hb, if_neg (fun h => hb (h b (List.mem_cons.mpr (Or.inl rfl))))]`. Rewrite using `[if_neg hL, map_zero, if_neg (fun h => hL fun a ha => h a (List.mem_cons_of_mem _ ha))]`.

Use `show ((List.finRange n).map (u μ)).prod x = _`. Rewrite using `[key]`. Distinguish the cases in `h : ν = μ`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h, if_neg]`. Introduce `h'`. Conclude with `h (funext fun a => h' a (List.mem_finRange a))`.
-/
theorem weight_projections_integral_findim [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) : WeightProjectionsIntegralBinomial E := by
  obtain ⟨m, hm⟩ := findim_weights_bounded E
  have h := fun (μ : Fin n → ℤ) (a : Fin n) => binomial_indicator_exists E a m hm (μ a)
  choose u hu hux using h
  refine ⟨fun μ => ((List.finRange n).map (u μ)).prod, fun μ => ?_, fun μ ν x hx => ?_⟩
  · apply Subring.list_prod_mem
    intro y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
    exact hu μ a
  · have key : ∀ L : List (Fin n),
        (L.map (u μ)).prod x = if ∀ a ∈ L, ν a = μ a then x else 0 := by
      intro L
      induction L with
      | nil => simp
      | cons b L ih =>
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
        by_cases hL : ∀ a ∈ L, ν a = μ a
        · rw [if_pos hL, hux μ b ν x hx]
          by_cases hb : ν b = μ b
          · rw [if_pos hb, if_pos (fun a ha => by rcases List.mem_cons.mp ha with rfl | ha; exacts [hb, hL a ha])]
          · rw [if_neg hb, if_neg (fun h => hb (h b (List.mem_cons.mpr (Or.inl rfl))))]
        · rw [if_neg hL, map_zero, if_neg (fun h => hL fun a ha => h a (List.mem_cons_of_mem _ ha))]
    show ((List.finRange n).map (u μ)).prod x = _
    rw [key]
    by_cases h : ν = μ
    · subst h
      simp
    · rw [if_neg h, if_neg]
      intro h'
      exact h (funext fun a => h' a (List.mem_finRange a))

end Formalism.MainNotions.G.GLWeightTheory
