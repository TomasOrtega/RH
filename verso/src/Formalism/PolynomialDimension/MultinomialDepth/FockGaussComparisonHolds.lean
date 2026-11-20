import Formalism.PolynomialDimension.FrameSum

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

/- English proof (translation)
Use `Finset.induction_on s (by simp) ?_` and prove the remaining obligations. Introduce `a s ha ih`. Rewrite using `[Nat.multinomial_insert ha, Nat.factorization_mul (Nat.choose_pos (Nat.le_add_right _ _)).ne' (Nat.multinomial_pos _ _).ne', Finsupp.add_apply, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]`. Establish `h1` using `Nat.factorization_choose_le_log (p := p) (n := f a + ∑ i ∈ s, f i) (k := f a)`. Establish `h2 : Nat.log p (∑ i ∈ s, f i) ≤ Nat.log p (f a + ∑ i ∈ s, f i)` using `Nat.log_mono_right (Nat.le_add_left _ _)`.

Establish `h3` using `Nat.mul_le_mul_left s.card h2`. Rewrite using `[add_one_mul]`. Use linear arithmetic over natural numbers and integers.
-/
theorem fock_mult_fact_le {α : Type*} (p : ℕ) (f : α → ℕ) (s : Finset α) :
    (Nat.multinomial s f).factorization p ≤ s.card * Nat.log p (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Nat.multinomial_insert ha, Nat.factorization_mul (Nat.choose_pos (Nat.le_add_right _ _)).ne'
    (Nat.multinomial_pos _ _).ne', Finsupp.add_apply, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
  have h1 := Nat.factorization_choose_le_log (p := p) (n := f a + ∑ i ∈ s, f i) (k := f a)
  have h2 : Nat.log p (∑ i ∈ s, f i) ≤ Nat.log p (f a + ∑ i ∈ s, f i) :=
    Nat.log_mono_right (Nat.le_add_left _ _)
  have h3 := Nat.mul_le_mul_left s.card h2
  rw [add_one_mul]
  omega

/- English proof (translation)
Rewrite using `[← Nat.factorization_def _ hp.out]`. Conclude with `fock_mult_fact_le p f s`.
-/
theorem fock_mult_val_le {α : Type*} (p : ℕ) [hp : Fact p.Prime] (f : α → ℕ) (s : Finset α) :
    padicValNat p (Nat.multinomial s f) ≤ s.card * Nat.log p (∑ i ∈ s, f i) := by
  rw [← Nat.factorization_def _ hp.out]
  exact fock_mult_fact_le p f s

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Establish `h1 : f a ≠ 0` using `hf a (Finset.mem_insert_self a s)`.

Establish `h2 : ∏ i ∈ s, f i ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)`. Rewrite using `[padicValNat.mul h1 h2, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]`.
-/
theorem fock_val_prod {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h1 : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have h2 : ∏ i ∈ s, f i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [padicValNat.mul h1 h2, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.out.one_lt`. Establish `hx : (1 : ℝ) ≤ 2 * a + k`. Establish `: (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.logb_nonneg hp1 hx` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fock_L_nonneg (p : ℕ) [hp : Fact p.Prime] (k : ℕ) (a : ℝ) (ha : 0 ≤ a) (hk : 1 ≤ k) :
    0 ≤ Real.logb p (2 * a + k) + 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hx : (1 : ℝ) ≤ 2 * a + k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have := Real.logb_nonneg hp1 hx
  linarith

/- English proof (translation)
Establish `h0` using `fock_L_nonneg p k a ha hk`. Break down `Nat.eq_zero_or_pos D with hD0 | hD0` into its components or cases. Substitute `hD0` using the available equality. Simplify using `using h0`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.out.one_lt`.

Establish `hkR : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hpos : (0 : ℝ) < 2 * a + k` using `by linarith`. Establish `hle : (Nat.log p D : ℝ) ≤ Real.logb p (2 * a + k)`. Rewrite using `[Real.le_logb_iff_rpow_le hp1 hpos, Real.rpow_natCast]`. Establish `: p ^ Nat.log p D ≤ D` using `Nat.pow_log_le_self p hD0.ne'`.

Establish `: ((p ^ Nat.log p D : ℕ) : ℝ) ≤ D` using `by exact_mod_cast this`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fock_log_le (p : ℕ) [hp : Fact p.Prime] (k D : ℕ) (a : ℝ) (ha : 0 ≤ a) (hk : 1 ≤ k)
    (hD : (D : ℝ) ≤ 2 * a) : (Nat.log p D : ℝ) ≤ Real.logb p (2 * a + k) + 1 := by
  have h0 := fock_L_nonneg p k a ha hk
  rcases Nat.eq_zero_or_pos D with hD0 | hD0
  · subst hD0; simpa using h0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < 2 * a + k := by linarith
  have hle : (Nat.log p D : ℝ) ≤ Real.logb p (2 * a + k) := by
    rw [Real.le_logb_iff_rpow_le hp1 hpos, Real.rpow_natCast]
    have : p ^ Nat.log p D ≤ D := Nat.pow_log_le_self p hD0.ne'
    have : ((p ^ Nat.log p D : ℕ) : ℝ) ≤ D := by exact_mod_cast this
    push_cast at this
    linarith
  linarith

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _`.
-/
theorem factProd_ne_zero {σ : Type} [Fintype σ] (α : σ →₀ ℕ) : factProd α ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _

/- English proof (translation)
Unfold `factProd`. Rewrite using `[← Finset.prod_fiberwise Finset.univ letter (fun i => (α i).factorial), ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun z _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.multinomial_spec, h z]`.
-/
theorem fock_key {σ Z : Type} [Fintype σ] [Fintype Z] [DecidableEq Z] (letter : σ → Z)
    (d : Z → ℕ) (α : σ →₀ ℕ)
    (h : ∀ z, ∑ i ∈ univ.filter (fun i => letter i = z), α i = d z) :
    ∏ z, (d z).factorial =
      factProd α * ∏ z, Nat.multinomial (univ.filter (fun i => letter i = z)) α := by
  classical
  unfold factProd
  rw [← Finset.prod_fiberwise Finset.univ letter (fun i => (α i).factorial), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun z _ => ?_
  rw [Nat.multinomial_spec, h z]

/- English proof (translation)
Establish `hkey` using `fock_key letter d α hh`. Establish `hne : ∏ z, Nat.multinomial (univ.filter (fun i => letter i = z)) α ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun z _ => (Nat.multinomial_pos _ _).ne'`. Use `set S := ∑ z, padicValNat p (Nat.multinomial (univ.filter (fun i => letter i = z)) α) with hS`. Establish `hV : padicValNat p (∏ z, (d z).factorial) = padicValNat p (factProd α) + S`. Rewrite using `[hkey, padicValNat.mul (factProd_ne_zero α) hne, hS, fock_val_prod p univ _ (fun z _ => (Nat.multinomial_pos _ _).ne')]`.

Use `⟨by rw [hV]; omega, ?_⟩` and prove the remaining obligations. Use `set T := ∑ z, (univ.filter (fun i => letter i = z)).card * Nat.log p (d z) with hT`. Establish `hST : S ≤ T`. Use `Finset.sum_le_sum fun z _ => ?_` and prove the remaining obligations. Use `fock_mult_val_le p (⇑α) (univ.filter fun i => letter i = z)` as an intermediate fact.

Rewrite `this` using `[hh z]`. Then use the resulting hypothesis. Establish `hcardsum : ∑ z, (univ.filter (fun i => letter i = z)).card = Fintype.card σ`. Rewrite using `[← Finset.card_univ]`. Conclude with `(Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (letter x))).symm`. Establish `hTR : (T : ℝ) ≤ N * k * (Real.logb p (2 * a + k) + 1)`.

Break down `Nat.eq_zero_or_pos k with hk0 | hk0` into its components or cases. Establish `hc : ∀ z, (univ.filter (fun i => letter i = z)).card = 0`. Introduce `z`. Use `Finset.card_le_univ (univ.filter (fun i => letter i = z))` as an intermediate fact. Substitute `hk0` using the available equality.

Use linear arithmetic over natural numbers and integers. Establish `: T = 0` using `by rw [hT]; simp [hc]`. Rewrite using `[this, hk0]`. Simplify using the standard rewrite rules. Establish `hL0` using `fock_L_nonneg p k a ha hk0`.

Rewrite using `[hT]`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_mul, ← Nat.cast_sum, hcardsum]`. Use `_ ≤ N * k * (Real.logb p (2 * a + k) + 1) := by`.

Apply `mul_le_mul_of_nonneg_right _ hL0` to reduce the goal to its premises. Conclude with `hcard` after adjusting the coercions. Establish `e1 : (padicValNat p (∏ z, (d z).factorial) : ℝ) = padicValNat p (factProd α) + S`. Conclude with `hV` after adjusting the coercions. Establish `e2 : (S : ℝ) ≤ T` using `by exact_mod_cast hST`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fock_core (p : ℕ) [Fact p.Prime] {σ Z : Type} [Fintype σ] [Fintype Z] [DecidableEq Z]
    (letter : σ → Z) (d : Z → ℕ) (N k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hcard : Fintype.card σ ≤ N * k) (hd : ∀ z, (d z : ℝ) ≤ 2 * a) (α : σ →₀ ℕ)
    (hh : ∀ z, ∑ i ∈ univ.filter (fun i => letter i = z), α i = d z) :
    padicValNat p (factProd α) ≤ padicValNat p (∏ z, (d z).factorial) ∧
      (padicValNat p (∏ z, (d z).factorial) : ℝ) - N * k * (Real.logb p (2 * a + k) + 1) ≤
        padicValNat p (factProd α) := by
  classical
  have hkey := fock_key letter d α hh
  have hne : ∏ z, Nat.multinomial (univ.filter (fun i => letter i = z)) α ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun z _ => (Nat.multinomial_pos _ _).ne'
  set S := ∑ z, padicValNat p (Nat.multinomial (univ.filter (fun i => letter i = z)) α) with hS
  have hV : padicValNat p (∏ z, (d z).factorial) = padicValNat p (factProd α) + S := by
    rw [hkey, padicValNat.mul (factProd_ne_zero α) hne, hS,
      fock_val_prod p univ _ (fun z _ => (Nat.multinomial_pos _ _).ne')]
  refine ⟨by rw [hV]; omega, ?_⟩
  set T := ∑ z, (univ.filter (fun i => letter i = z)).card * Nat.log p (d z) with hT
  have hST : S ≤ T := by
    refine Finset.sum_le_sum fun z _ => ?_
    have := fock_mult_val_le p (⇑α) (univ.filter fun i => letter i = z)
    rwa [hh z] at this
  have hcardsum : ∑ z, (univ.filter (fun i => letter i = z)).card = Fintype.card σ := by
    rw [← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (letter x))).symm
  have hTR : (T : ℝ) ≤ N * k * (Real.logb p (2 * a + k) + 1) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · have hc : ∀ z, (univ.filter (fun i => letter i = z)).card = 0 := by
        intro z
        have := Finset.card_le_univ (univ.filter (fun i => letter i = z))
        subst hk0
        omega
      have : T = 0 := by rw [hT]; simp [hc]
      rw [this, hk0]; simp
    · have hL0 := fock_L_nonneg p k a ha hk0
      rw [hT]; push_cast
      calc ∑ z, ((univ.filter (fun i => letter i = z)).card : ℝ) * (Nat.log p (d z) : ℝ)
          ≤ ∑ z, ((univ.filter (fun i => letter i = z)).card : ℝ) * (Real.logb p (2 * a + k) + 1) :=
            Finset.sum_le_sum fun z _ =>
              mul_le_mul_of_nonneg_left (fock_log_le p k (d z) a ha hk0 (hd z)) (Nat.cast_nonneg _)
        _ = (Fintype.card σ : ℝ) * (Real.logb p (2 * a + k) + 1) := by
            rw [← Finset.sum_mul, ← Nat.cast_sum, hcardsum]
        _ ≤ N * k * (Real.logb p (2 * a + k) + 1) := by
            apply mul_le_mul_of_nonneg_right _ hL0
            exact_mod_cast hcard
  have e1 : (padicValNat p (∏ z, (d z).factorial) : ℝ) = padicValNat p (factProd α) + S := by
    exact_mod_cast hV
  have e2 : (S : ℝ) ≤ T := by exact_mod_cast hST
  linarith

/- English proof (translation)
Establish `hc : D.choose (∑ i, m i) ≠ 0` using `(Nat.choose_pos hm).ne'`. Establish `hm0 : Nat.multinomial univ m ≠ 0` using `(Nat.multinomial_pos _ _).ne'`. Rewrite using `[padicValNat.mul hc hm0]`. Establish `h1 : padicValNat p (D.choose (∑ i, m i)) ≤ Nat.log p D`. Rewrite using `[← Nat.factorization_def _ (Fact.out : p.Prime)]`.

Conclude with `Nat.factorization_choose_le_log`. Establish `h2` using `fock_mult_val_le p m univ`. Rewrite `h2` using `[Finset.card_univ, Fintype.card_fin]`. Establish `h3 : Nat.log p (∑ i, m i) ≤ Nat.log p D` using `Nat.log_mono_right hm`. Establish `h4` using `Nat.mul_le_mul_left r h3`.

Rewrite using `[add_mul, one_mul]`. Use linear arithmetic over natural numbers and integers.
-/
theorem frame_val (p : ℕ) [Fact p.Prime] (D : ℕ) {r : ℕ} (m : Fin r → ℕ) (hm : ∑ i, m i ≤ D) :
    padicValNat p (D.choose (∑ i, m i) * Nat.multinomial univ m) ≤ (r + 1) * Nat.log p D := by
  have hc : D.choose (∑ i, m i) ≠ 0 := (Nat.choose_pos hm).ne'
  have hm0 : Nat.multinomial univ m ≠ 0 := (Nat.multinomial_pos _ _).ne'
  rw [padicValNat.mul hc hm0]
  have h1 : padicValNat p (D.choose (∑ i, m i)) ≤ Nat.log p D := by
    rw [← Nat.factorization_def _ (Fact.out : p.Prime)]
    exact Nat.factorization_choose_le_log
  have h2 := fock_mult_val_le p m univ
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h3 : Nat.log p (∑ i, m i) ≤ Nat.log p D := Nat.log_mono_right hm
  have h4 := Nat.mul_le_mul_left r h3
  rw [add_mul, one_mul]
  omega

end Formalism.CountingSumsFrames
