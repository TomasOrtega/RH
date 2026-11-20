import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent

open MvPowerSeries

variable {σ : Type}

def OnV {k : Type} [CommRing k] (V : Set σ) (f : MvPowerSeries σ k) : Prop :=
  ∀ e : σ →₀ ℕ, coeff e f ≠ 0 → ∀ i ∈ e.support, i ∈ V

def subV (k : Type) [CommRing k] (V : Set σ) : Subalgebra k (MvPowerSeries σ k) where
  carrier := {f | OnV V f}
  mul_mem' := by
    classical
    intro f g hf hg
    change OnV V f at hf
    change OnV V g at hg
    change OnV V (f * g)
    intro e he i hi
    rw [coeff_mul] at he
    obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [← hp] at hi
    rcases Finset.mem_union.1 (Finsupp.support_add hi) with h | h
    · exact hf _ (left_ne_zero_of_mul hne) i h
    · exact hg _ (right_ne_zero_of_mul hne) i h
  add_mem' := by
    intro f g hf hg
    change OnV V f at hf
    change OnV V g at hg
    change OnV V (f + g)
    intro e he i hi
    rw [map_add] at he
    by_cases h : coeff e f = 0
    · rw [h, zero_add] at he
      exact hg e he i hi
    · exact hf e h i hi
  algebraMap_mem' := by
    intro r
    change OnV V _
    intro e he i hi
    classical
    have e0 : e = 0 := by
      by_contra hne
      apply he
      simp [MvPowerSeries.algebraMap_apply, coeff_C, hne]
    subst e0
    simp at hi

variable {k : Type} [CommRing k]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_subV (V : Set σ) (f : MvPowerSeries σ k) : f ∈ subV k V ↔ OnV V f := Iff.rfl

/- English proof (translation)
Rewrite using `[mem_subV]`. Introduce `e he j hj`. Establish `e0 : e = 0`. Assume the negation of the conclusion as `h`. Conclude with `he (by simp [coeff_C, h])`.

Substitute `e0` using the available equality. Simplify using `at hj`.
-/
theorem C_mem (V : Set σ) (r : k) : (C r : MvPowerSeries σ k) ∈ subV k V := by
  classical
  rw [mem_subV]
  intro e he j hj
  have e0 : e = 0 := by
    by_contra h
    exact he (by simp [coeff_C, h])
  subst e0
  simp at hj

/- English proof (translation)
Rewrite using `[mem_subV]`. Introduce `e he j hj`. Rewrite `he` using `[coeff_subst ha]`. Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d : τ →₀ ℕ, coeff d f • coeff e (d.prod fun s n => a s ^ n) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `he (by simp only [hcon, finsum_zero])`. Establish `hP : (d.prod fun s n => a s ^ n) ∈ subV k V`. Unfold `Finsupp.prod`. Conclude with `Subalgebra.prod_mem _ (fun s _ => Subalgebra.pow_mem _ (haV s) _)`.

Rewrite `hd` using `[smul_eq_mul]`. Conclude with `(mem_subV V _).1 hP e (right_ne_zero_of_mul hd) j hj`.
-/
theorem subst_mem {τ : Type} {V : Set σ} (a : τ → MvPowerSeries σ k) (ha : HasSubst a)
    (haV : ∀ t, a t ∈ subV k V) (f : MvPowerSeries τ k) : subst a f ∈ subV k V := by
  rw [mem_subV]
  intro e he j hj
  rw [coeff_subst ha] at he
  obtain ⟨d, hd⟩ : ∃ d : τ →₀ ℕ, coeff d f • coeff e (d.prod fun s n => a s ^ n) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact he (by simp only [hcon, finsum_zero])
  have hP : (d.prod fun s n => a s ^ n) ∈ subV k V := by
    unfold Finsupp.prod
    exact Subalgebra.prod_mem _ (fun s _ => Subalgebra.pow_mem _ (haV s) _)
  rw [smul_eq_mul] at hd
  exact (mem_subV V _).1 hP e (right_ne_zero_of_mul hd) j hj

/- English proof (translation)
Rewrite `hf`, the goal using `[mem_subV]`. Introduce `e he j hj`. Rewrite `he` using `[coeff_pderiv]`. Establish `h1 : coeff (e + Finsupp.single i 1) f ≠ 0` using `left_ne_zero_of_mul he`. Apply `hf _ h1 j` to reduce the goal to its premises.

Rewrite `hj`, the goal using `[Finsupp.mem_support_iff]`. Simplify using `only [Finsupp.coe_add, Pi.add_apply]`. Use linear arithmetic over natural numbers and integers.
-/
theorem pderiv_mem {V : Set σ} (i : σ) {f : MvPowerSeries σ k} (hf : f ∈ subV k V) :
    pderiv k i f ∈ subV k V := by
  rw [mem_subV] at hf ⊢
  intro e he j hj
  rw [coeff_pderiv] at he
  have h1 : coeff (e + Finsupp.single i 1) f ≠ 0 := left_ne_zero_of_mul he
  apply hf _ h1 j
  rw [Finsupp.mem_support_iff] at hj ⊢
  simp only [Finsupp.coe_add, Pi.add_apply]
  omega

/- English proof (translation)
Rewrite `hf` using `[mem_subV]`. Use extensionality with `e`. Rewrite using `[coeff_pderiv, map_zero]`. Distinguish the cases in `h : coeff (e + Finsupp.single i 1) f = 0`. Rewrite using `[h, zero_mul]`.

It suffices to derive a contradiction. Apply `hi` to reduce the goal to its premises. Apply `hf _ h i` to reduce the goal to its premises. Rewrite using `[Finsupp.mem_support_iff]`. Simplify using the standard rewrite rules.
-/
theorem pderiv_kill {V : Set σ} {i : σ} (hi : i ∉ V) {f : MvPowerSeries σ k} (hf : f ∈ subV k V) :
    pderiv k i f = 0 := by
  rw [mem_subV] at hf
  ext e
  rw [coeff_pderiv, map_zero]
  by_cases h : coeff (e + Finsupp.single i 1) f = 0
  · rw [h, zero_mul]
  · exfalso
    apply hi
    apply hf _ h i
    rw [Finsupp.mem_support_iff]
    simp

variable [Algebra ℚ k]

/- English proof (translation)
Rewrite using `[add_pow, map_sum]`. Establish `key : ∀ m ∈ Finset.range (d + 1), coeff e ((X 0 : MvPowerSeries (Fin 2) k) ^ m * X 1 ^ (d - m) * (d.choose m : MvPowerSeries (Fin 2) k)) = if e 0 = m ∧ e 1 = d - m then (d.choose m : k) else 0`. Introduce `m _`. Rewrite using `[← map_natCast (C : k →+* MvPowerSeries (Fin 2) k), coeff_mul_C, X_pow_eq, X_pow_eq, monomial_mul_monomial, coeff_monomial]`. Establish `hiff : (e = Finsupp.single 0 m + Finsupp.single 1 (d - m)) ↔ (e 0 = m ∧ e 1 = d - m)`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Simplify using the standard rewrite rules. Introduce and unpack `⟨h0, h1⟩`. Use extensionality with `i`.

Apply the tactic sequence `fin_cases i <;> simp [h0, h1]`. Distinguish the cases in `h : e 0 = m ∧ e 1 = d - m`. Rewrite using `[if_pos (hiff.2 h), if_pos h]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun h' => h (hiff.1 h')), if_neg h, zero_mul]`.

Rewrite using `[Finset.sum_congr rfl key]`. Distinguish the cases in `hd : e 0 + e 1 = d`. Rewrite using `[if_pos hd, Finset.sum_eq_single (e 0)]`. Rewrite using `[if_pos ⟨rfl, by omega⟩]`. Introduce `m _ hm`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨h, _⟩`. Conclude with `hm h.symm`. Introduce `h`. It suffices to derive a contradiction.

Apply `h` to reduce the goal to its premises. Rewrite using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hd]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `m hm`. Rewrite `hm` using `[Finset.mem_range]`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h0, h1⟩`. Use linear arithmetic over natural numbers and integers.
-/
private lemma coeff_XX_pow_lemma (d : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e ((X 0 + X 1 : MvPowerSeries (Fin 2) k) ^ d) =
      if e 0 + e 1 = d then ((d.choose (e 0) : ℕ) : k) else 0 := by
  rw [add_pow, map_sum]
  have key : ∀ m ∈ Finset.range (d + 1),
      coeff e ((X 0 : MvPowerSeries (Fin 2) k) ^ m * X 1 ^ (d - m) * (d.choose m : MvPowerSeries (Fin 2) k)) =
        if e 0 = m ∧ e 1 = d - m then (d.choose m : k) else 0 := by
    intro m _
    rw [← map_natCast (C : k →+* MvPowerSeries (Fin 2) k), coeff_mul_C, X_pow_eq, X_pow_eq,
      monomial_mul_monomial, coeff_monomial]
    have hiff : (e = Finsupp.single 0 m + Finsupp.single 1 (d - m)) ↔ (e 0 = m ∧ e 1 = d - m) := by
      constructor
      · rintro rfl
        simp
      · rintro ⟨h0, h1⟩
        ext i
        fin_cases i <;> simp [h0, h1]
    by_cases h : e 0 = m ∧ e 1 = d - m
    · rw [if_pos (hiff.2 h), if_pos h]
      simp
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, zero_mul]
  rw [Finset.sum_congr rfl key]
  by_cases hd : e 0 + e 1 = d
  · rw [if_pos hd, Finset.sum_eq_single (e 0)]
    · rw [if_pos ⟨rfl, by omega⟩]
    · intro m _ hm
      rw [if_neg]
      rintro ⟨h, _⟩
      exact hm h.symm
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_range] at hm
    rw [if_neg]
    rintro ⟨h0, h1⟩
    omega

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]`. Repeatedly rewrite using `[coeff_X_pow]`. Distinguish the cases in `h : e = Finsupp.single i (e i)`. Rewrite using `[if_pos h, finsum_eq_single _ (e i)]`. Rewrite using `[if_pos h, smul_eq_mul, mul_one]`.

Introduce `d hd`. Rewrite using `[if_neg, smul_zero]`. Introduce `h'`. Apply `hd` to reduce the goal to its premises. Rewrite using `[h']`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg h]`. Establish `hz : ∀ d : ℕ, (PowerSeries.coeff d f • if e = Finsupp.single i d then (1 : k) else 0) = 0`. Introduce `d`. Rewrite using `[if_neg, smul_zero]`.

Introduce `h'`. Apply `h` to reduce the goal to its premises. Rewrite using `[h']`. Simplify using the standard rewrite rules. Simplify using `only [hz, finsum_zero]`.
-/
private lemma coeff_substX_lemma_2 (i : Fin 2) (f : PowerSeries k) (e : Fin 2 →₀ ℕ) :
    coeff e (PowerSeries.subst (X i : MvPowerSeries (Fin 2) k) f) =
      if e = Finsupp.single i (e i) then PowerSeries.coeff (e i) f else 0 := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  simp_rw [coeff_X_pow]
  by_cases h : e = Finsupp.single i (e i)
  · rw [if_pos h, finsum_eq_single _ (e i)]
    · rw [if_pos h, smul_eq_mul, mul_one]
    · intro d hd
      rw [if_neg, smul_zero]
      intro h'
      apply hd
      rw [h']
      simp
  · rw [if_neg h]
    have hz : ∀ d : ℕ, (PowerSeries.coeff d f • if e = Finsupp.single i d then (1 : k) else 0) = 0 := by
      intro d
      rw [if_neg, smul_zero]
      intro h'
      apply h
      rw [h']
      simp
    simp only [hz, finsum_zero]

/- English proof (translation)
Use extensionality with `e`. Establish `hsum : PowerSeries.HasSubst (X 0 + X 1 : MvPowerSeries (Fin 2) k)` using `PowerSeries.HasSubst.of_constantCoeff_zero (by simp)`. Establish `hL : coeff e (PowerSeries.subst (X (0 : Fin 2) + X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) = PowerSeries.coeff (e 0 + e 1) (PowerSeries.exp k) * ((e 0 + e 1).choose (e 0) : k)`. Rewrite using `[PowerSeries.coeff_subst hsum, finsum_eq_single _ (e 0 + e 1)]`. Rewrite using `[coeff_XX_pow_lemma, if_pos rfl, smul_eq_mul]`.

Introduce `d hd`. Rewrite using `[coeff_XX_pow_lemma, if_neg (fun h => hd h.symm), smul_zero]`. Establish `hR : coeff e (PowerSeries.subst (X (0 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) * PowerSeries.subst (X (1 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) = PowerSeries.coeff (e 0) (PowerSeries.exp k) * PowerSeries.coeff (e 1) (PowerSeries.exp k)`. Rewrite using `[coeff_mul, Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))]`. Rewrite using `[coeff_substX_lemma_2, coeff_substX_lemma_2, if_pos (by simp), if_pos (by simp)]`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨p, q⟩ hpq hne`. Rewrite `hpq` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[coeff_substX_lemma_2, coeff_substX_lemma_2]`. Distinguish the cases in `h1 : p = Finsupp.single 0 (p 0)`.

Distinguish the cases in `h2 : q = Finsupp.single 1 (q 1)`. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Establish `hq0 : q 0 = 0`. Rewrite using `[h2]`.

Simplify using the standard rewrite rules. Establish `hp1 : p 1 = 0`. Rewrite using `[h1]`. Simplify using the standard rewrite rules. Establish `c0` using `DFunLike.congr_fun hpq 0`.

Establish `c1` using `DFunLike.congr_fun hpq 1`. Simplify using `only [Finsupp.coe_add, Pi.add_apply] at c0 c1`. Rewrite using `[Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[h1]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h2]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_neg h2, mul_zero]`. Rewrite using `[if_neg h1, zero_mul]`. Introduce `h`. It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises.

Rewrite using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp`. Rewrite using `[hL, hR, PowerSeries.coeff_exp, PowerSeries.coeff_exp, PowerSeries.coeff_exp, ← map_natCast (algebraMap ℚ k), ← map_mul, ← map_mul]`. Use `congr 1`.

Establish `hle : e 0 ≤ e 0 + e 1` using `Nat.le_add_right _ _`. Establish `h` using `Nat.choose_mul_factorial_mul_factorial hle`. Rewrite `h` using `[Nat.add_sub_cancel_left]`. Establish `h' : ((e 0 + e 1).choose (e 0) : ℚ) * ((e 0).factorial : ℚ) * ((e 1).factorial : ℚ) = ((e 0 + e 1).factorial : ℚ)`. Conclude with `h` after adjusting the coercions.

Establish `hc : ((e 0 + e 1).choose (e 0) : ℚ) ≠ 0`. Conclude with `(Nat.choose_pos hle).ne'` after adjusting the coercions. Establish `hf0 : ((e 0).factorial : ℚ) ≠ 0`. Conclude with `(Nat.factorial_pos _).ne'` after adjusting the coercions. Establish `hf1 : ((e 1).factorial : ℚ) ≠ 0`.

Conclude with `(Nat.factorial_pos _).ne'` after adjusting the coercions. Rewrite using `[← h']`. Clear the denominators using the available nonvanishing facts.
-/
theorem exp_biv :
    PowerSeries.subst (X (0 : Fin 2) + X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) =
      PowerSeries.subst (X (0 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X (1 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) := by
  ext e
  have hsum : PowerSeries.HasSubst (X 0 + X 1 : MvPowerSeries (Fin 2) k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hL : coeff e (PowerSeries.subst (X (0 : Fin 2) + X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) =
      PowerSeries.coeff (e 0 + e 1) (PowerSeries.exp k) * ((e 0 + e 1).choose (e 0) : k) := by
    rw [PowerSeries.coeff_subst hsum, finsum_eq_single _ (e 0 + e 1)]
    · rw [coeff_XX_pow_lemma, if_pos rfl, smul_eq_mul]
    · intro d hd
      rw [coeff_XX_pow_lemma, if_neg (fun h => hd h.symm), smul_zero]
  have hR : coeff e (PowerSeries.subst (X (0 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X (1 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) =
      PowerSeries.coeff (e 0) (PowerSeries.exp k) * PowerSeries.coeff (e 1) (PowerSeries.exp k) := by
    rw [coeff_mul, Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))]
    · rw [coeff_substX_lemma_2, coeff_substX_lemma_2, if_pos (by simp), if_pos (by simp)]
      simp
    · rintro ⟨p, q⟩ hpq hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
      rw [coeff_substX_lemma_2, coeff_substX_lemma_2]
      by_cases h1 : p = Finsupp.single 0 (p 0)
      · by_cases h2 : q = Finsupp.single 1 (q 1)
        · exfalso
          apply hne
          have hq0 : q 0 = 0 := by
            rw [h2]
            simp
          have hp1 : p 1 = 0 := by
            rw [h1]
            simp
          have c0 := DFunLike.congr_fun hpq 0
          have c1 := DFunLike.congr_fun hpq 1
          simp only [Finsupp.coe_add, Pi.add_apply] at c0 c1
          rw [Prod.mk.injEq]
          constructor
          · rw [h1]
            congr 1
            omega
          · rw [h2]
            congr 1
            omega
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro h
      exfalso
      apply h
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      ext i
      fin_cases i <;> simp
  rw [hL, hR, PowerSeries.coeff_exp, PowerSeries.coeff_exp, PowerSeries.coeff_exp,
    ← map_natCast (algebraMap ℚ k), ← map_mul, ← map_mul]
  congr 1
  have hle : e 0 ≤ e 0 + e 1 := Nat.le_add_right _ _
  have h := Nat.choose_mul_factorial_mul_factorial hle
  rw [Nat.add_sub_cancel_left] at h
  have h' : ((e 0 + e 1).choose (e 0) : ℚ) * ((e 0).factorial : ℚ) * ((e 1).factorial : ℚ) =
      ((e 0 + e 1).factorial : ℚ) := by
    exact_mod_cast h
  have hc : ((e 0 + e 1).choose (e 0) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hle).ne'
  have hf0 : ((e 0).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hf1 : ((e 1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  rw [← h']
  field_simp

/- English proof (translation)
Establish `ha' : HasSubst (fun _ : Unit => a)` using `hasSubst_of_constantCoeff_zero (fun _ => ha)`. Simplify using `only [PowerSeries.subst]`. Rewrite using `[subst_comp_subst_apply ha' hb]`.
-/
theorem psubst_comp {τ υ : Type} (b : τ → MvPowerSeries υ k) (hb : HasSubst b)
    (a : MvPowerSeries τ k) (ha : constantCoeff a = 0) (f : PowerSeries k) :
    subst b (PowerSeries.subst a f) = PowerSeries.subst (subst b a) f := by
  have ha' : HasSubst (fun _ : Unit => a) := hasSubst_of_constantCoeff_zero (fun _ => ha)
  simp only [PowerSeries.subst]
  rw [subst_comp_subst_apply ha' hb]

/- English proof (translation)
Apply the tactic sequence `have hb : HasSubst (![x, y] : Fin 2 → MvPowerSeries τ k) := hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp [hx, hy])`. Establish `h` using `congrArg (subst (![x, y] : Fin 2 → MvPowerSeries τ k)) (exp_biv (k := k))`. Rewrite `h` using `[psubst_comp _ hb (X 0 + X 1) (by simp), subst_mul hb, psubst_comp _ hb (X 0) (by simp), psubst_comp _ hb (X 1) (by simp)]`. Simplify `h` using `[subst_add hb, subst_X hb]`.
-/
theorem expS_add {τ : Type} (x y : MvPowerSeries τ k) (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) :
    PowerSeries.subst (x + y) (PowerSeries.exp k) =
      PowerSeries.subst x (PowerSeries.exp k) * PowerSeries.subst y (PowerSeries.exp k) := by
  have hb : HasSubst (![x, y] : Fin 2 → MvPowerSeries τ k) :=
    hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp [hx, hy])
  have h := congrArg (subst (![x, y] : Fin 2 → MvPowerSeries τ k)) (exp_biv (k := k))
  rw [psubst_comp _ hb (X 0 + X 1) (by simp), subst_mul hb, psubst_comp _ hb (X 0) (by simp),
    psubst_comp _ hb (X 1) (by simp)] at h
  simpa [subst_add hb, subst_X hb] using h

/- English proof (translation)
Establish `hx'` using `PowerSeries.HasSubst.of_constantCoeff_zero hx`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst hx', finsum_eq_single _ 0]`. Simplify using `[PowerSeries.coeff_exp]`. Introduce `d hd`. Rewrite using `[coeff_zero_eq_constantCoeff_apply, map_pow, hx, zero_pow hd, smul_zero]`.
-/
theorem cc_exp {τ : Type} (x : MvPowerSeries τ k) (hx : constantCoeff x = 0) :
    constantCoeff (PowerSeries.subst x (PowerSeries.exp k)) = 1 := by
  have hx' := PowerSeries.HasSubst.of_constantCoeff_zero hx
  rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst hx', finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro d hd
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, hx, zero_pow hd, smul_zero]

end Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
