import Formalism.MahlerMeasure.IsFrozenInv

namespace Formalism.GM.FrozenVariableLemmas

open MvPolynomial Finset

/- English proof (translation)
Rewrite using `[aeval_def, eval₂_eq]`. Use `IsWeightedHomogeneous.sum _ _ _ (fun m hm => ?_)` and prove the remaining obligations. Establish `hdeg : Finsupp.weight w' m = d` using `hf (mem_support_iff.mp hm)`. Establish `hprod : IsWeightedHomogeneous w (∏ i ∈ m.support, g i ^ m i) (∑ i ∈ m.support, m i • w' i)` using `IsWeightedHomogeneous.prod _ _ _ (fun i _ => (hg i).pow (m i))`. Establish `hC` using `(isWeightedHomogeneous_C w (coeff m f)).mul hprod`.

Rewrite `hC` using `[zero_add]`. Rewrite using `[← hdeg, Finsupp.weight_apply]`. Conclude with `hC`.
-/
theorem aeval_isWH {σ τ R : Type} [CommSemiring R] (w' : σ → ℕ) (w : τ → ℕ)
    (g : σ → MvPolynomial τ R) (hg : ∀ x, IsWeightedHomogeneous w (g x) (w' x))
    {f : MvPolynomial σ R} {d : ℕ} (hf : IsWeightedHomogeneous w' f d) :
    IsWeightedHomogeneous w (aeval g f) d := by
  rw [aeval_def, eval₂_eq]
  refine IsWeightedHomogeneous.sum _ _ _ (fun m hm => ?_)
  have hdeg : Finsupp.weight w' m = d := hf (mem_support_iff.mp hm)
  have hprod : IsWeightedHomogeneous w (∏ i ∈ m.support, g i ^ m i) (∑ i ∈ m.support, m i • w' i) :=
    IsWeightedHomogeneous.prod _ _ _ (fun i _ => (hg i).pow (m i))
  have hC := (isWeightedHomogeneous_C w (coeff m f)).mul hprod
  rw [zero_add] at hC
  rw [← hdeg, Finsupp.weight_apply]
  exact hC

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • G i.1) (fun i => zero_smul _ _), Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_comm]`.
-/
theorem weight_fst {M r : ℕ} (G : Fin M → ℕ) (m : Fin M × Fin r →₀ ℕ) :
    Finsupp.weight (fun x : Fin M × Fin r => G x.1) m = ∑ b, G b * ∑ c, m (b, c) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • G i.1) (fun i => zero_smul _ _), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [smul_eq_mul, mul_comm]

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `h`.
-/
theorem isWH_of_eq {σ R : Type} [CommSemiring R] {w : σ → ℕ} {φ : MvPolynomial σ R} {a b : ℕ}
    (h : IsWeightedHomogeneous w φ a) (e : a = b) : IsWeightedHomogeneous w φ b := by
  subst e
  exact h

/- English proof (translation)
The claim follows from `isWeightedHomogeneous_X R _ (b, c)`.
-/
theorem isWH_X_fst {M r : ℕ} {R : Type} [CommSemiring R] (g : Fin M → ℕ) (b : Fin M) (c : Fin r) :
    IsWeightedHomogeneous (fun x : Fin M × Fin r => g x.1) (X (b, c) : MvPolynomial _ R) (g b) :=
  isWeightedHomogeneous_X R _ (b, c)

/- English proof (translation)
Take `⟨i, c⟩` from `x`. Simplify using `only [M.freezeSub]`. Use `split_ifs`. Conclude with `IsWeightedHomogeneous.sum _ _ _ (fun c' _ => (isWH_X_fst g _ c').mul (isWH_X_fst g _ c'))`. Conclude with `isWH_of_eq ((isWH_X_fst g _ ρ).mul (isWH_X_fst g _ c)) (add_comm _ _)`.

Conclude with `isWH_of_eq ((isWH_X_fst g _ ρ).mul (isWH_X_fst g _ ρ)) (add_comm _ _)`. Rewrite using `[← mem_weightedHomogeneousSubmodule]`. Use `Submodule.sub_mem _ ?_ ?_` and prove the remaining obligations. Conclude with `isWH_of_eq ((isWH_X_fst g _ ρ).mul (isWH_X_fst g _ c)) (add_comm _ _)`. Conclude with `(isWH_X_fst g _ ρ).mul (isWH_X_fst g _ c)`.
-/
theorem freezeSub_isWH (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r)
    (g : Fin (N + 1) → ℕ) (x : Fin N × Fin r) :
    IsWeightedHomogeneous (fun y : Fin (N + 1) × Fin r => g y.1) (M.freezeSub p LL ρ x)
      (g (Fin.castSucc x.1) + g (Fin.last N)) := by
  obtain ⟨i, c⟩ := x
  simp only [M.freezeSub]
  split_ifs
  · exact IsWeightedHomogeneous.sum _ _ _ (fun c' _ => (isWH_X_fst g _ c').mul (isWH_X_fst g _ c'))
  · exact isWH_of_eq ((isWH_X_fst g _ ρ).mul (isWH_X_fst g _ c)) (add_comm _ _)
  · exact isWH_of_eq ((isWH_X_fst g _ ρ).mul (isWH_X_fst g _ ρ)) (add_comm _ _)
  · rw [← mem_weightedHomogeneousSubmodule]
    refine Submodule.sub_mem _ ?_ ?_
    · exact isWH_of_eq ((isWH_X_fst g _ ρ).mul (isWH_X_fst g _ c)) (add_comm _ _)
    · exact (isWH_X_fst g _ ρ).mul (isWH_X_fst g _ c)

/- English proof (translation)
Introduce `m hm`. Establish `hf' : (↑f.support : Set (Fin N × Fin r →₀ ℕ)) ⊆ {m | M.MultiDeg LL m}` using `hf`. Establish `hms : M.MultiDeg LL m` using `hf' (mem_support_iff.mpr hm)`. Rewrite using `[weight_fst]`. Conclude with `Finset.sum_congr rfl (fun b _ => by rw [hms b])`.
-/
theorem pol_isWH (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (G : Fin N → ℕ)
    {f : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hf : f ∈ M.Pol p r LL) :
    IsWeightedHomogeneous (fun x : Fin N × Fin r => G x.1) f (∑ b, G b * LL.deg b) := by
  intro m hm
  have hf' : (↑f.support : Set (Fin N × Fin r →₀ ℕ)) ⊆ {m | M.MultiDeg LL m} := hf
  have hms : M.MultiDeg LL m := hf' (mem_support_iff.mpr hm)
  rw [weight_fst]
  exact Finset.sum_congr rfl (fun b _ => by rw [hms b])

/- English proof (translation)
Conclude with `((isWH_X_fst g (Fin.last N) ρ).pow _).mul (aeval_isWH (fun x => g (Fin.castSucc x.1) + g (Fin.last N)) (fun y => g y.1) (M.freezeSub p LL ρ) (fun x => freezeSub_isWH p LL ρ g x) (pol_isWH p LL (fun b => g (Fin.castSucc b) + g (Fin.last N)) hf))`.
-/
theorem freeze_isWH (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (g : Fin (N + 1) → ℕ) {f : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hf : f ∈ M.Pol p r LL) :
    IsWeightedHomogeneous (fun y : Fin (N + 1) × Fin r => g y.1) (M.freeze p LL ρ n f)
      ((n - LL.total) • g (Fin.last N) + ∑ b, (g (Fin.castSucc b) + g (Fin.last N)) * LL.deg b) := by
  exact ((isWH_X_fst g (Fin.last N) ρ).pow _).mul
    (aeval_isWH (fun x => g (Fin.castSucc x.1) + g (Fin.last N)) (fun y => g y.1) (M.freezeSub p LL ρ)
      (fun x => freezeSub_isWH p LL ρ g x) (pol_isWH p LL (fun b => g (Fin.castSucc b) + g (Fin.last N)) hf))

/- English proof (translation)
It suffices to establish `hs : (↑(M.freeze p LL ρ n f).support : Set (Fin (N + 1) × Fin r →₀ ℕ)) ⊆ {m | M.MultiDeg (LL.snoc n) m} from hs`. Introduce `m hm i`. Establish `key` using `freeze_isWH p LL ρ n (fun j => if j = i then 1 else 0) hf (mem_support_iff.mp hm)`. Establish `hw : Finsupp.weight (fun y : Fin (N + 1) × Fin r => if y.1 = i then 1 else 0) m = ∑ c, m (i, c)`. Rewrite using `[weight_fst (fun j => if j = i then 1 else 0) m]`.

Simplify using the standard rewrite rules. Rewrite using `[← hw, key]`. Establish `ht : LL.total = ∑ b, LL.deg b` using `rfl`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`.

Simplify using `only [Fin.castSucc_ne_last, if_false, if_true, zero_add, one_mul, smul_eq_mul, mul_one, M.Letters.snoc, Fin.lastCases_last]`. Rewrite using `[← ht]`. Use linear arithmetic over natural numbers and integers. Consider the case `cast j`. Simplify using `only [(Fin.castSucc_ne_last _).symm, Fin.castSucc_inj, if_false, add_zero, smul_eq_mul, mul_zero, zero_add, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, M.Letters.snoc, Fin.lastCases_castSucc]`.
-/
theorem freeze_mem_pol (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (hn : LL.total ≤ n) {f : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hf : f ∈ M.Pol p r LL) :
    M.freeze p LL ρ n f ∈ M.Pol p r (LL.snoc n) := by
  suffices hs : (↑(M.freeze p LL ρ n f).support : Set (Fin (N + 1) × Fin r →₀ ℕ)) ⊆
      {m | M.MultiDeg (LL.snoc n) m} from hs
  intro m hm i
  have key := freeze_isWH p LL ρ n (fun j => if j = i then 1 else 0) hf (mem_support_iff.mp hm)
  have hw : Finsupp.weight (fun y : Fin (N + 1) × Fin r => if y.1 = i then 1 else 0) m = ∑ c, m (i, c) := by
    rw [weight_fst (fun j => if j = i then 1 else 0) m]
    simp
  rw [← hw, key]
  have ht : LL.total = ∑ b, LL.deg b := rfl
  induction i using Fin.lastCases with
  | last =>
    simp only [Fin.castSucc_ne_last, if_false, if_true, zero_add, one_mul, smul_eq_mul, mul_one,
      M.Letters.snoc, Fin.lastCases_last]
    rw [← ht]
    omega
  | cast j =>
    simp only [(Fin.castSucc_ne_last _).symm, Fin.castSucc_inj, if_false, add_zero, smul_eq_mul, mul_zero,
      zero_add, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, M.Letters.snoc,
      Fin.lastCases_castSucc]

end Formalism.GM.FrozenVariableLemmas

namespace Formalism.GM.FrozenVariableLemmas

open MvPolynomial Finset

section
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} (L : M.Letters K) (c ρ : Fin r)

/- English proof (translation)
Unfold `M.glAct`. Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[if_pos i.isLt]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem glAct_full_apply (F : MvPolynomial (Fin K × Fin r) ℚ_[p]) :
    M.glAct p L K c ρ F = ∑ i : Fin K,
      (if L.vec i then X (i, c) * pderiv (i, ρ) F else -(X (i, ρ) * pderiv (i, c) F)) := by
  unfold M.glAct
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [if_pos i.isLt]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[glAct_full_apply, glAct_full_apply, glAct_full_apply, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem glAct_full_mul (F G : MvPolynomial (Fin K × Fin r) ℚ_[p]) :
    M.glAct p L K c ρ (F * G) = F * M.glAct p L K c ρ G + G * M.glAct p L K c ρ F := by
  rw [glAct_full_apply, glAct_full_apply, glAct_full_apply, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring

/- English proof (translation)
Rewrite using `[glAct_full_apply]`. Simplify using the standard rewrite rules.
-/
theorem glAct_full_C (a : ℚ_[p]) : M.glAct p L K c ρ (C a) = 0 := by
  rw [glAct_full_apply]
  simp

/- English proof (translation)
Rewrite using `[glAct_full_apply, Finset.sum_eq_single b]`. Distinguish the cases in `hv : L.vec b`. Apply the tactic sequence `by_cases hd : d = ρ <;> simp [hv, hd, pderiv_X, Pi.single_apply]`. Apply the tactic sequence `by_cases hd : d = c <;> simp [hv, hd, pderiv_X, Pi.single_apply]`. Introduce `i _ hi`.

Simplify using `[pderiv_X, Pi.single_apply, Ne.symm hi]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ b) h`.
-/
theorem glAct_full_X (b : Fin K) (d : Fin r) :
    M.glAct p L K c ρ (X (b, d)) =
      if L.vec b then (if d = ρ then X (b, c) else 0) else (if d = c then -X (b, ρ) else 0) := by
  rw [glAct_full_apply, Finset.sum_eq_single b]
  · by_cases hv : L.vec b
    · by_cases hd : d = ρ <;> simp [hv, hd, pderiv_X, Pi.single_apply]
    · by_cases hd : d = c <;> simp [hv, hd, pderiv_X, Pi.single_apply]
  · intro i _ hi
    simp [pderiv_X, Pi.single_apply, Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ b) h

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, ← C_1, glAct_full_C]`. Consider the case `succ k ih => rw [pow_succ, glAct_full_mul, hF, ih, mul_zero, mul_zero, add_zero]`.
-/
theorem glAct_full_pow (F : MvPolynomial (Fin K × Fin r) ℚ_[p]) (hF : M.glAct p L K c ρ F = 0)
    (k : ℕ) : M.glAct p L K c ρ (F ^ k) = 0 := by
  induction k with
  | zero => rw [pow_zero, ← C_1, glAct_full_C]
  | succ k ih => rw [pow_succ, glAct_full_mul, hF, ih, mul_zero, mul_zero, add_zero]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[aeval_C, MvPolynomial.algebraMap_eq, glAct_full_C]`. Consider the case `add f g hf hg`. Rewrite using `[_root_.map_add, _root_.map_add, hf, hg, add_zero]`.

Consider the case `mul_X f x hf`. Rewrite using `[_root_.map_mul, aeval_X, glAct_full_mul, hf, hσ x, mul_zero, mul_zero, add_zero]`.
-/
theorem glAct_full_aeval {τ : Type} (σ : τ → MvPolynomial (Fin K × Fin r) ℚ_[p])
    (hσ : ∀ x, M.glAct p L K c ρ (σ x) = 0) (f : MvPolynomial τ ℚ_[p]) :
    M.glAct p L K c ρ (aeval σ f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, MvPolynomial.algebraMap_eq, glAct_full_C]
  | add f g hf hg =>
    rw [_root_.map_add, _root_.map_add, hf, hg, add_zero]
  | mul_X f x hf =>
    rw [_root_.map_mul, aeval_X, glAct_full_mul, hf, hσ x, mul_zero, mul_zero, add_zero]
end

/- English proof (translation)
Simplify using `[M.Letters.snoc]`.
-/
theorem snoc_vec_castSucc {N : ℕ} (LL : M.Letters N) (n : ℕ) (i : Fin N) :
    (LL.snoc n).vec (Fin.castSucc i) = LL.vec i := by
  simp [M.Letters.snoc]

/- English proof (translation)
Simplify using `[M.Letters.snoc]`.
-/
theorem snoc_vec_last {N : ℕ} (LL : M.Letters N) (n : ℕ) :
    (LL.snoc n).vec (Fin.last N) = false := by
  simp [M.Letters.snoc]

/- English proof (translation)
Introduce `c hc`. Establish `hX` using `glAct_full_X p (LL.snoc n) c ρ`. Establish `hlast : M.glAct p (LL.snoc n) (N + 1) c ρ (X (Fin.last N, ρ)) = 0`. Rewrite using `[hX, snoc_vec_last]`. Simplify using `[Ne.symm hc]`.

Establish `hsub : ∀ x, M.glAct p (LL.snoc n) (N + 1) c ρ (M.freezeSub p LL ρ x) = 0`. Introduce and unpack `⟨i, c'⟩`. Simplify using `only [M.freezeSub]`. Distinguish the cases in `hv : LL.vec i`. Distinguish the cases in `hc' : c' = ρ`.

Rewrite using `[if_pos hv, if_pos hc', _root_.map_sum]`. Simplify using `only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, if_true, Bool.false_eq_true, if_false, mul_ite, mul_zero, mul_neg, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_pos hv, if_neg hc']`. Simplify using `only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, hc', Ne.symm hc, if_true, if_false, Bool.false_eq_true, mul_zero, add_zero]`.

Distinguish the cases in `hc' : c' = ρ`. Rewrite using `[if_neg hv, if_pos hc']`. Simplify using `only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, hc', Ne.symm hc, if_true, if_false, Bool.false_eq_true, mul_zero, add_zero]`. Rewrite using `[if_neg hv, if_neg hc', _root_.map_sub]`. Simplify using `only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, hc', Ne.symm hc, if_true, if_false, Bool.false_eq_true, mul_zero, add_zero]`.

Distinguish the cases in `hcc : c' = c`. Simplify using `only [hcc, if_true]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hcc, if_false, mul_zero, sub_zero]`. Unfold `M.freeze`.

Rewrite using `[glAct_full_mul, glAct_full_pow _ _ _ _ _ hlast, glAct_full_aeval _ _ _ _ _ hsub, mul_zero, mul_zero, add_zero]`.
-/
theorem freeze_inv (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) : M.IsFrozenInv p LL ρ n (M.freeze p LL ρ n f) := by
  intro c hc
  have hX := glAct_full_X p (LL.snoc n) c ρ
  have hlast : M.glAct p (LL.snoc n) (N + 1) c ρ (X (Fin.last N, ρ)) = 0 := by
    rw [hX, snoc_vec_last]
    simp [Ne.symm hc]
  have hsub : ∀ x, M.glAct p (LL.snoc n) (N + 1) c ρ (M.freezeSub p LL ρ x) = 0 := by
    rintro ⟨i, c'⟩
    simp only [M.freezeSub]
    by_cases hv : LL.vec i
    · by_cases hc' : c' = ρ
      · rw [if_pos hv, if_pos hc', _root_.map_sum]
        simp only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, if_true, Bool.false_eq_true,
          if_false, mul_ite, mul_zero, mul_neg, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ]
        ring
      · rw [if_pos hv, if_neg hc']
        simp only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, hc', Ne.symm hc, if_true, if_false, Bool.false_eq_true, mul_zero, add_zero]
    · by_cases hc' : c' = ρ
      · rw [if_neg hv, if_pos hc']
        simp only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, hc', Ne.symm hc, if_true, if_false, Bool.false_eq_true, mul_zero, add_zero]
      · rw [if_neg hv, if_neg hc', _root_.map_sub]
        simp only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, hc', Ne.symm hc, if_true, if_false, Bool.false_eq_true, mul_zero, add_zero]
        by_cases hcc : c' = c
        · simp only [hcc, if_true]
          ring
        · simp only [hcc, if_false, mul_zero, sub_zero]
  unfold M.freeze
  rw [glAct_full_mul, glAct_full_pow _ _ _ _ _ hlast, glAct_full_aeval _ _ _ _ _ hsub, mul_zero, mul_zero,
    add_zero]

end Formalism.GM.FrozenVariableLemmas

namespace Formalism.GM.FrozenVariableLemmas

open MvPolynomial Finset

section
variable (p : ℕ) [Fact p.Prime] {τ : Type}

/- English proof (translation)
Unfold `M.IntPol`. Rewrite using `[LinearMap.mem_range]`. Both sides reduce to the same expression.
-/
theorem intPol_iff (F : MvPolynomial τ ℚ_[p]) :
    F ∈ M.IntPol p τ ↔ ∃ F₀ : MvPolynomial τ ℤ_[p], map (algebraMap ℤ_[p] ℚ_[p]) F₀ = F := by
  unfold M.IntPol
  rw [LinearMap.mem_range]
  rfl

/- English proof (translation)
Rewrite `hF`, `hG`, the goal using `[intPol_iff]`. Take `⟨F₀, rfl⟩` from `hF`. Take `⟨G₀, rfl⟩` from `hG`. Conclude with `⟨F₀ * G₀, _root_.map_mul _ _ _⟩`.
-/
theorem intPol_mul {F G : MvPolynomial τ ℚ_[p]} (hF : F ∈ M.IntPol p τ) (hG : G ∈ M.IntPol p τ) :
    F * G ∈ M.IntPol p τ := by
  rw [intPol_iff] at hF hG ⊢
  obtain ⟨F₀, rfl⟩ := hF
  obtain ⟨G₀, rfl⟩ := hG
  exact ⟨F₀ * G₀, _root_.map_mul _ _ _⟩

/- English proof (translation)
Rewrite using `[intPol_iff]`. Conclude with `⟨X x, MvPolynomial.map_X _ _⟩`.
-/
theorem intPol_X (x : τ) : (X x : MvPolynomial τ ℚ_[p]) ∈ M.IntPol p τ := by
  rw [intPol_iff]
  exact ⟨X x, MvPolynomial.map_X _ _⟩

/- English proof (translation)
Rewrite `hF`, the goal using `[intPol_iff]`. Take `⟨F₀, rfl⟩` from `hF`. Conclude with `⟨F₀ ^ k, _root_.map_pow _ _ _⟩`.
-/
theorem intPol_pow {F : MvPolynomial τ ℚ_[p]} (hF : F ∈ M.IntPol p τ) (k : ℕ) :
    F ^ k ∈ M.IntPol p τ := by
  rw [intPol_iff] at hF ⊢
  obtain ⟨F₀, rfl⟩ := hF
  exact ⟨F₀ ^ k, _root_.map_pow _ _ _⟩

/- English proof (translation)
Rewrite `hf` using `[intPol_iff]`. Take `⟨f₀, rfl⟩` from `hf`. Proceed by induction on `f₀ using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[MvPolynomial.map_C, aeval_C, MvPolynomial.algebraMap_eq, intPol_iff]`.

Conclude with `⟨C a, MvPolynomial.map_C _ _⟩`. Consider the case `add f g hf hg`. Rewrite using `[_root_.map_add, _root_.map_add]`. Conclude with `Submodule.add_mem _ hf hg`. Consider the case `mul_X f x hf`.

Rewrite using `[_root_.map_mul, MvPolynomial.map_X, _root_.map_mul, aeval_X]`. Conclude with `intPol_mul p hf (hσ x)`.
-/
theorem intPol_aeval {υ : Type} (σ : υ → MvPolynomial τ ℚ_[p]) (hσ : ∀ x, σ x ∈ M.IntPol p τ)
    {f : MvPolynomial υ ℚ_[p]} (hf : f ∈ M.IntPol p υ) : aeval σ f ∈ M.IntPol p τ := by
  rw [intPol_iff] at hf
  obtain ⟨f₀, rfl⟩ := hf
  induction f₀ using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.map_C, aeval_C, MvPolynomial.algebraMap_eq, intPol_iff]
    exact ⟨C a, MvPolynomial.map_C _ _⟩
  | add f g hf hg =>
    rw [_root_.map_add, _root_.map_add]
    exact Submodule.add_mem _ hf hg
  | mul_X f x hf =>
    rw [_root_.map_mul, MvPolynomial.map_X, _root_.map_mul, aeval_X]
    exact intPol_mul p hf (hσ x)
end

/- English proof (translation)
Take `⟨i, c⟩` from `x`. Simplify using `only [M.freezeSub]`. Use `split_ifs`. Conclude with `Submodule.sum_mem _ (fun c' _ => intPol_mul p (intPol_X p _) (intPol_X p _))`. Conclude with `intPol_mul p (intPol_X p _) (intPol_X p _)`.

Conclude with `intPol_mul p (intPol_X p _) (intPol_X p _)`. Conclude with `Submodule.sub_mem _ (intPol_mul p (intPol_X p _) (intPol_X p _)) (intPol_mul p (intPol_X p _) (intPol_X p _))`.
-/
theorem freezeSub_int (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r)
    (x : Fin N × Fin r) : M.freezeSub p LL ρ x ∈ M.IntPol p (Fin (N + 1) × Fin r) := by
  obtain ⟨i, c⟩ := x
  simp only [M.freezeSub]
  split_ifs
  · exact Submodule.sum_mem _ (fun c' _ => intPol_mul p (intPol_X p _) (intPol_X p _))
  · exact intPol_mul p (intPol_X p _) (intPol_X p _)
  · exact intPol_mul p (intPol_X p _) (intPol_X p _)
  · exact Submodule.sub_mem _ (intPol_mul p (intPol_X p _) (intPol_X p _))
      (intPol_mul p (intPol_X p _) (intPol_X p _))

/- English proof (translation)
The claim follows from `intPol_mul p (intPol_pow p (intPol_X p _) _) (intPol_aeval p _ (freezeSub_int p LL ρ) hf)`.
-/
theorem freeze_int (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    {f : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hf : f ∈ M.IntPol p (Fin N × Fin r)) :
    M.freeze p LL ρ n f ∈ M.IntPol p (Fin (N + 1) × Fin r) :=
  intPol_mul p (intPol_pow p (intPol_X p _) _) (intPol_aeval p _ (freezeSub_int p LL ρ) hf)

end Formalism.GM.FrozenVariableLemmas

namespace Formalism.GM

/- English proof (translation)
Introduce `p _ N r LL ρ n hn f hf`. Conclude with `⟨FrozenVariableLemmas.freeze_mem_pol p LL ρ n hn hf, FrozenVariableLemmas.freeze_inv p LL ρ n f, fun h => FrozenVariableLemmas.freeze_int p LL ρ n h⟩`.
-/
theorem extendMapsTo : M.FreezeInto := by
  intro p _ N r LL ρ n hn f hf
  exact ⟨FrozenVariableLemmas.freeze_mem_pol p LL ρ n hn hf, FrozenVariableLemmas.freeze_inv p LL ρ n f,
    fun h => FrozenVariableLemmas.freeze_int p LL ρ n h⟩

/- English proof (translation)
Introduce `p _ N r LL ρ n hn f`. Unfold `M.freeze`. Rewrite using `[← mul_assoc, ← pow_succ', Nat.sub_add_comm hn]`.
-/
theorem extendSucc : M.FreezeStep := by
  intro p _ N r LL ρ n hn f
  unfold M.freeze
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_comm hn]

end Formalism.GM
