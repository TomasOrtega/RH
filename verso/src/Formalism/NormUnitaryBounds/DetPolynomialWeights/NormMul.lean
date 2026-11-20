import Formalism.NormUnitaryBounds.Statement

open MvPolynomial Finset

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

namespace NMul

/- English proof (translation)
Establish `h1 : (∑ k, c k).choose m = PowerSeries.coeff m (((∏ k, (1 + Polynomial.X : Polynomial ℕ) ^ (c k) : Polynomial ℕ)) : PowerSeries ℕ)`. Rewrite using `[Polynomial.coeff_coe, Finset.prod_pow_eq_pow_sum, Polynomial.coeff_one_add_X_pow, Nat.cast_id]`. Establish `h2 : (((∏ k, (1 + Polynomial.X : Polynomial ℕ) ^ (c k) : Polynomial ℕ)) : PowerSeries ℕ) = ∏ k, (((1 + Polynomial.X : Polynomial ℕ) ^ (c k) : Polynomial ℕ) : PowerSeries ℕ)` using `map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℕ)) _ _`. Rewrite using `[h1, h2, PowerSeries.coeff_prod]`. Use `sum_congr rfl fun l _ => prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, Nat.cast_id]`.
-/
theorem vandermonde {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) (m : ℕ) :
    ∑ l ∈ finsuppAntidiag (univ : Finset ι) m, ∏ k, (c k).choose (l k) =
      (∑ k, c k).choose m := by
  have h1 : (∑ k, c k).choose m = PowerSeries.coeff m
      (((∏ k, (1 + Polynomial.X : Polynomial ℕ) ^ (c k) : Polynomial ℕ)) : PowerSeries ℕ) := by
    rw [Polynomial.coeff_coe, Finset.prod_pow_eq_pow_sum, Polynomial.coeff_one_add_X_pow,
      Nat.cast_id]
  have h2 : (((∏ k, (1 + Polynomial.X : Polynomial ℕ) ^ (c k) : Polynomial ℕ)) : PowerSeries ℕ)
      = ∏ k, (((1 + Polynomial.X : Polynomial ℕ) ^ (c k) : Polynomial ℕ) : PowerSeries ℕ) :=
    map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℕ)) _ _
  rw [h1, h2, PowerSeries.coeff_prod]
  refine sum_congr rfl fun l _ => prod_congr rfl fun k _ => ?_
  rw [Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, Nat.cast_id]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using `only [blockWt, blockDeg, Finset.sum_apply, Fintype.sum_prod_type, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem weight_blockWt {N n : ℕ} (a : Fin N × Fin n →₀ ℕ) (j : Fin N) :
    Finsupp.weight (blockWt N n) a j = blockDeg a j := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [blockWt, blockDeg, Finset.sum_apply, Fintype.sum_prod_type, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

/- English proof (translation)
Rewrite `hF` using `[mem_weightedHomogeneousSubmodule]`. Use `hF (mem_support_iff.1 ha)` as an intermediate fact. Rewrite using `[← weight_blockWt, this]`.
-/
theorem blockDeg_of_mem {N n : ℕ} {ν : Fin N → ℕ} {F : MvPolynomial (Fin N × Fin n) ℂ}
    (hF : F ∈ weightedHomogeneousSubmodule ℂ (blockWt N n) ν) {a : Fin N × Fin n →₀ ℕ}
    (ha : a ∈ F.support) (j : Fin N) : blockDeg a j = ν j := by
  rw [mem_weightedHomogeneousSubmodule] at hF
  have := hF (mem_support_iff.1 ha)
  rw [← weight_blockWt, this]

/- English proof (translation)
Simplify using `[blockDeg, sum_add_distrib]`.
-/
theorem blockDeg_add {N n : ℕ} (a b : Fin N × Fin n →₀ ℕ) (j : Fin N) :
    blockDeg (a + b) j = blockDeg a j + blockDeg b j := by
  simp [blockDeg, sum_add_distrib]

/- English proof (translation)
Unfold `bweight`. Check the signs of the components of the expression.
-/
theorem bweight_pos {N n : ℕ} (e : Fin N × Fin n →₀ ℕ) : 0 < bweight e := by
  unfold bweight
  positivity

/- English proof (translation)
Rewrite using `[Nat.choose_symm_add]`. Conclude with `(Nat.add_choose_mul_factorial_mul_factorial x y).symm` after adjusting the coercions.
-/
theorem fact_add (x y : ℕ) :
    ((x + y).factorial : ℝ) = ((x + y).choose x : ℝ) * x.factorial * y.factorial := by
  rw [Nat.choose_symm_add]
  exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial x y).symm

/- English proof (translation)
Unfold `bweight`. Rewrite using `[← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib]`. Use `prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[blockDeg_add]`. Simplify using `only [Finsupp.coe_add, Pi.add_apply]`.

Use `push_cast`. Rewrite using `[fact_add (blockDeg a j) (blockDeg b j), prod_congr rfl (fun k _ => fact_add (a (j, k)) (b (j, k))), prod_mul_distrib, prod_mul_distrib]`. Establish `h1 : (0 : ℝ) < ((blockDeg a j + blockDeg b j).choose (blockDeg a j) : ℝ)`. Conclude with `Nat.choose_pos (Nat.le_add_right _ _)` after adjusting the coercions. Establish `h2 : (0 : ℝ) < (blockDeg a j).factorial` using `by positivity`.

Establish `h3 : (0 : ℝ) < (blockDeg b j).factorial` using `by positivity`. Clear the denominators using the available nonvanishing facts.
-/
theorem bweight_add {N n : ℕ} (a b : Fin N × Fin n →₀ ℕ) :
    bweight (a + b) * ∏ j, ((blockDeg (a + b) j).choose (blockDeg a j) : ℝ) =
      bweight a * bweight b * ∏ j, ∏ k, (((a + b) (j, k)).choose (a (j, k)) : ℝ) := by
  unfold bweight
  rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [blockDeg_add]
  simp only [Finsupp.coe_add, Pi.add_apply]
  push_cast
  rw [fact_add (blockDeg a j) (blockDeg b j),
    prod_congr rfl (fun k _ => fact_add (a (j, k)) (b (j, k))), prod_mul_distrib,
    prod_mul_distrib]
  have h1 : (0 : ℝ) < ((blockDeg a j + blockDeg b j).choose (blockDeg a j) : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right _ _)
  have h2 : (0 : ℝ) < (blockDeg a j).factorial := by positivity
  have h3 : (0 : ℝ) < (blockDeg b j).factorial := by positivity
  field_simp

def Dc {N n : ℕ} (ν : Fin N → ℕ) (c : Fin N × Fin n →₀ ℕ) : ℝ :=
  ∏ j, ((blockDeg c j).choose (ν j) : ℝ)

def Pc {N n : ℕ} (c a : Fin N × Fin n →₀ ℕ) : ℝ :=
  ∏ j, ∏ k, ((c (j, k)).choose (a (j, k)) : ℝ)

/- English proof (translation)
Establish `hR : ∏ j, (blockDeg c j).choose (ν j) = ∑ x ∈ Fintype.piFinset (fun j => finsuppAntidiag (univ : Finset (Fin n)) (ν j)), ∏ j, ∏ k, (c (j, k)).choose (x j k)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hR]`. Set `ι : (Fin N × Fin n →₀ ℕ) × (Fin N × Fin n →₀ ℕ) → (Fin N → Fin n →₀ ℕ)` to `fun p j => Finsupp.equivFunOnFinite.symm (fun k => p.1 (j, k))`. Establish `hinj : Set.InjOn ι ((sF ×ˢ sG).filter (fun p => p.1 + p.2 = c))`.

Introduce `p hp q hq hpq`. Rewrite `hp`, `hq` using `[mem_coe, mem_filter]`. Establish `h1 : p.1 = q.1`. Use extensionality with `⟨j, k⟩`. Use `congrArg (fun x => x j k) hpq` as an intermediate fact.

Simplify `this` using `[ι]`. Establish `h2 : p.2 = q.2`. Use `hp.2.trans hq.2.symm` as an intermediate fact. Rewrite `this` using `[h1]`. Conclude with `add_left_cancel this`.

Conclude with `Prod.ext h1 h2`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[ι]`. Use `_ = ∑ x ∈ ((sF ×ˢ sG).filter (fun p => p.1 + p.2 = c)).image ι, ∏ j, ∏ k, (c (j, k)).choose (x j k) := (sum_image (f := fun x : Fin N → Fin n →₀ ℕ => ∏ j, ∏ k, (c (j, k)).choose (x j k)) hinj).symm`. Use `_ ≤ _ := by`.

Apply `sum_le_sum_of_subset` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[mem_image]`. Take `⟨p, hp, rfl⟩` from `hx`. Rewrite using `[Fintype.mem_piFinset]`.

Introduce `j`. Rewrite using `[mem_finsuppAntidiag]`. Use `⟨?_, subset_univ _⟩` and prove the remaining obligations. Rewrite `hp` using `[mem_filter, mem_product]`. Rewrite using `[← hF _ hp.1.1 j]`.

Simplify using `[ι, blockDeg]`.
-/
theorem comb {N n : ℕ} (ν : Fin N → ℕ) (sF sG : Finset (Fin N × Fin n →₀ ℕ))
    (hF : ∀ a ∈ sF, ∀ j, blockDeg a j = ν j) (c : Fin N × Fin n →₀ ℕ) :
    ∑ p ∈ (sF ×ˢ sG).filter (fun p => p.1 + p.2 = c), ∏ j, ∏ k, (c (j, k)).choose (p.1 (j, k)) ≤
      ∏ j, (blockDeg c j).choose (ν j) := by
  classical
  have hR : ∏ j, (blockDeg c j).choose (ν j) =
      ∑ x ∈ Fintype.piFinset (fun j => finsuppAntidiag (univ : Finset (Fin n)) (ν j)),
        ∏ j, ∏ k, (c (j, k)).choose (x j k) := by
    calc ∏ j, (blockDeg c j).choose (ν j)
        = ∏ j, ∑ l ∈ finsuppAntidiag (univ : Finset (Fin n)) (ν j), ∏ k, (c (j, k)).choose (l k) :=
          prod_congr rfl fun j _ => (vandermonde (fun k => c (j, k)) (ν j)).symm
      _ = _ := Finset.prod_univ_sum _ _
  rw [hR]
  let ι : (Fin N × Fin n →₀ ℕ) × (Fin N × Fin n →₀ ℕ) → (Fin N → Fin n →₀ ℕ) :=
    fun p j => Finsupp.equivFunOnFinite.symm (fun k => p.1 (j, k))
  have hinj : Set.InjOn ι ((sF ×ˢ sG).filter (fun p => p.1 + p.2 = c)) := by
    intro p hp q hq hpq
    rw [mem_coe, mem_filter] at hp hq
    have h1 : p.1 = q.1 := by
      ext ⟨j, k⟩
      have := congrArg (fun x => x j k) hpq
      simpa [ι] using this
    have h2 : p.2 = q.2 := by
      have := hp.2.trans hq.2.symm
      rw [h1] at this
      exact add_left_cancel this
    exact Prod.ext h1 h2
  calc ∑ p ∈ (sF ×ˢ sG).filter (fun p => p.1 + p.2 = c), ∏ j, ∏ k, (c (j, k)).choose (p.1 (j, k))
      = ∑ p ∈ (sF ×ˢ sG).filter (fun p => p.1 + p.2 = c),
          (fun x : Fin N → Fin n →₀ ℕ => ∏ j, ∏ k, (c (j, k)).choose (x j k)) (ι p) := by
        simp [ι]
    _ = ∑ x ∈ ((sF ×ˢ sG).filter (fun p => p.1 + p.2 = c)).image ι,
          ∏ j, ∏ k, (c (j, k)).choose (x j k) := (sum_image (f := fun x : Fin N → Fin n →₀ ℕ =>
          ∏ j, ∏ k, (c (j, k)).choose (x j k)) hinj).symm
    _ ≤ _ := by
        apply sum_le_sum_of_subset
        intro x hx
        rw [mem_image] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        rw [Fintype.mem_piFinset]
        intro j
        rw [mem_finsuppAntidiag]
        refine ⟨?_, subset_univ _⟩
        rw [mem_filter, mem_product] at hp
        rw [← hF _ hp.1.1 j]
        simp [ι, blockDeg]

/- English proof (translation)
Break down `((F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c)).eq_empty_or_nonempty with hA | hA` into its components or cases. Simplify using `[hA]`. Establish `hmem : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c), p.1 ∈ F.support ∧ p.2 ∈ G.support ∧ p.1 + p.2 = c`. Introduce `p hp`. Rewrite `hp` using `[mem_filter, mem_product]`.

Conclude with `⟨hp.1.1, hp.1.2, hp.2⟩`. Establish `hDpos : 0 < Dc ν c`. Take `⟨p0, hp0⟩` from `hA`. Take `⟨h1, _, h3⟩` from `hmem p0 hp0`. Use `prod_pos fun j _ => ?_` and prove the remaining obligations.

Establish `: ν j ≤ blockDeg c j`. Rewrite using `[← h3, ← hF _ h1 j, blockDeg_add]`. Conclude with `Nat.le_add_right _ _`. Conclude with `Nat.choose_pos this` after adjusting the coercions. Establish `hPpos : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c), 0 < Pc c p.1`.

Introduce `p hp`. Take `⟨_, _, h3⟩` from `hmem p hp`. Use `prod_pos fun j _ => prod_pos fun k _ => ?_` and prove the remaining obligations. Establish `: p.1 (j, k) ≤ c (j, k)`. Rewrite using `[← h3]`.

Simplify using the standard rewrite rules. Conclude with `Nat.choose_pos this` after adjusting the coercions. Establish `hW : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c), bweight c = bweight p.1 * bweight p.2 * Pc c p.1 / Dc ν c`. Introduce `p hp`. Take `⟨h1, _, h3⟩` from `hmem p hp`.

Use `bweight_add p.1 p.2` as an intermediate fact. Rewrite `this` using `[h3]`. Establish `e : ∏ j, ((blockDeg c j).choose (blockDeg p.1 j) : ℝ) = Dc ν c` using `prod_congr rfl fun j _ => by rw [hF _ h1 j]`. Rewrite `this` using `[e]`. Rewrite using `[eq_div_iff hDpos.ne']`.

Conclude with `this`. Establish `hsumP : ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c), Pc c p.1 ≤ Dc ν c`. Use `comb ν F.support G.support hF c` as an intermediate fact. Unfold `Pc Dc`. Conclude with `this` after adjusting the coercions.

Establish `hgpos : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c), 0 < Pc c p.1 / Dc ν c` using `fun p hp => div_pos (hPpos p hp) hDpos`. Establish `hsumg : ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c), Pc c p.1 / Dc ν c ≤ 1`. Rewrite using `[← sum_div, div_le_one hDpos]`. Conclude with `hsumP`. Establish `hsumgpos : 0 < ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c), Pc c p.1 / Dc ν c` using `sum_pos hgpos hA`.

Establish `hsed` using `sq_sum_div_le_sum_sq_div _ (fun p => ‖coeff p.1 F * coeff p.2 G‖) hgpos`. Establish `h1 : ‖∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c), coeff p.1 F * coeff p.2 G‖ ^ 2 ≤ ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c), ‖coeff p.1 F * coeff p.2 G‖ ^ 2 / (Pc c p.1 / Dc ν c)`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sum_mul]`.

Use `sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hP` using `hPpos p hp`. Rewrite using `[hW p hp, norm_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem key_c {N n : ℕ} {ν : Fin N → ℕ} {F G : MvPolynomial (Fin N × Fin n) ℂ}
    (hF : ∀ a ∈ F.support, ∀ j, blockDeg a j = ν j) (c : Fin N × Fin n →₀ ℕ) :
    ‖∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        coeff p.1 F * coeff p.2 G‖ ^ 2 * bweight c ≤
      ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) := by
  classical
  rcases ((F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c)).eq_empty_or_nonempty
    with hA | hA
  · simp [hA]
  have hmem : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      p.1 ∈ F.support ∧ p.2 ∈ G.support ∧ p.1 + p.2 = c := by
    intro p hp
    rw [mem_filter, mem_product] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩
  have hDpos : 0 < Dc ν c := by
    obtain ⟨p0, hp0⟩ := hA
    obtain ⟨h1, _, h3⟩ := hmem p0 hp0
    refine prod_pos fun j _ => ?_
    have : ν j ≤ blockDeg c j := by
      rw [← h3, ← hF _ h1 j, blockDeg_add]
      exact Nat.le_add_right _ _
    exact_mod_cast Nat.choose_pos this
  have hPpos : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      0 < Pc c p.1 := by
    intro p hp
    obtain ⟨_, _, h3⟩ := hmem p hp
    refine prod_pos fun j _ => prod_pos fun k _ => ?_
    have : p.1 (j, k) ≤ c (j, k) := by
      rw [← h3]
      simp
    exact_mod_cast Nat.choose_pos this
  have hW : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      bweight c = bweight p.1 * bweight p.2 * Pc c p.1 / Dc ν c := by
    intro p hp
    obtain ⟨h1, _, h3⟩ := hmem p hp
    have := bweight_add p.1 p.2
    rw [h3] at this
    have e : ∏ j, ((blockDeg c j).choose (blockDeg p.1 j) : ℝ) = Dc ν c :=
      prod_congr rfl fun j _ => by rw [hF _ h1 j]
    rw [e] at this
    rw [eq_div_iff hDpos.ne']
    exact this
  have hsumP : ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c), Pc c p.1 ≤
      Dc ν c := by
    have := comb ν F.support G.support hF c
    unfold Pc Dc
    exact_mod_cast this
  have hgpos : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      0 < Pc c p.1 / Dc ν c := fun p hp => div_pos (hPpos p hp) hDpos
  have hsumg : ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      Pc c p.1 / Dc ν c ≤ 1 := by
    rw [← sum_div, div_le_one hDpos]
    exact hsumP
  have hsumgpos : 0 < ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      Pc c p.1 / Dc ν c := sum_pos hgpos hA
  have hsed := sq_sum_div_le_sum_sq_div _ (fun p => ‖coeff p.1 F * coeff p.2 G‖) hgpos
  have h1 : ‖∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        coeff p.1 F * coeff p.2 G‖ ^ 2 ≤
      ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        ‖coeff p.1 F * coeff p.2 G‖ ^ 2 / (Pc c p.1 / Dc ν c) := by
    calc _ ≤ (∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
          ‖coeff p.1 F * coeff p.2 G‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := le_div_self (sq_nonneg _) hsumgpos hsumg
      _ ≤ _ := hsed
  calc _ ≤ (∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        ‖coeff p.1 F * coeff p.2 G‖ ^ 2 / (Pc c p.1 / Dc ν c)) * bweight c :=
        mul_le_mul_of_nonneg_right h1 (bweight_pos c).le
    _ = _ := by
      rw [sum_mul]
      refine sum_congr rfl fun p hp => ?_
      have hP := hPpos p hp
      rw [hW p hp, norm_mul]
      field_simp

/- English proof (translation)
Rewrite using `[coeff_mul]`. Use `symm`. Use `sum_subset (fun p hp => ?_) (fun p hp hnot => ?_)` and prove the remaining obligations. Rewrite `hp` using `[mem_filter]`. Conclude with `mem_antidiagonal.2 hp.2`.

Distinguish the cases in `h1 : coeff p.1 F = 0`. Simplify using `[h1]`. Distinguish the cases in `h2 : coeff p.2 G = 0`. Simplify using `[h2]`. Establish `h3 : p.1 + p.2 = c` using `mem_antidiagonal.1 hp`.

Conclude with `(hnot (mem_filter.2 ⟨mem_product.2 ⟨mem_support_iff.2 h1, mem_support_iff.2 h2⟩, h3⟩)).elim`.
-/
theorem coeff_mul_eq {N n : ℕ} (F G : MvPolynomial (Fin N × Fin n) ℂ)
    (c : Fin N × Fin n →₀ ℕ) :
    coeff c (F * G) = ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      coeff p.1 F * coeff p.2 G := by
  classical
  rw [coeff_mul]
  symm
  refine sum_subset (fun p hp => ?_) (fun p hp hnot => ?_)
  · rw [mem_filter] at hp
    exact mem_antidiagonal.2 hp.2
  · by_cases h1 : coeff p.1 F = 0
    · simp [h1]
    by_cases h2 : coeff p.2 G = 0
    · simp [h2]
    have h3 : p.1 + p.2 = c := mem_antidiagonal.1 hp
    exact (hnot (mem_filter.2 ⟨mem_product.2 ⟨mem_support_iff.2 h1, mem_support_iff.2 h2⟩,
      h3⟩)).elim

/- English proof (translation)
Establish `hF' : ∀ a ∈ F.support, ∀ j, blockDeg a j = ν j` using `fun a ha j => blockDeg_of_mem hF ha j`. Establish `hnn : ∀ p : (Fin N × Fin n →₀ ℕ) × (Fin N × Fin n →₀ ℕ), 0 ≤ (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2)` using `fun p => mul_nonneg (mul_nonneg (sq_nonneg _) (bweight_pos _).le) (mul_nonneg (sq_nonneg _) (bweight_pos _).le)`. Combine the equalities or inequalities in the displayed calculation. Use `sum_le_sum fun c _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_mul_eq]`.

Conclude with `key_c hF' c`. Use `_ = ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 ∈ (F * G).support), (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) := sum_fiberwise_eq_sum_filter _ _ _ _`. Use `_ ≤ ∑ p ∈ F.support ×ˢ G.support, (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => hnn p)`. Use `_ = bnormSq F * bnormSq G := by`. Rewrite using `[bnormSq, bnormSq, Finset.sum_mul_sum, Finset.sum_product]`.
-/
theorem normSq_mul {N n : ℕ} (ν : Fin N → ℕ) (F G : MvPolynomial (Fin N × Fin n) ℂ)
    (hF : F ∈ weightedHomogeneousSubmodule ℂ (blockWt N n) ν) :
    bnormSq (F * G) ≤ bnormSq F * bnormSq G := by
  classical
  have hF' : ∀ a ∈ F.support, ∀ j, blockDeg a j = ν j := fun a ha j => blockDeg_of_mem hF ha j
  have hnn : ∀ p : (Fin N × Fin n →₀ ℕ) × (Fin N × Fin n →₀ ℕ),
      0 ≤ (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) := fun p =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (bweight_pos _).le)
      (mul_nonneg (sq_nonneg _) (bweight_pos _).le)
  calc bnormSq (F * G) = ∑ c ∈ (F * G).support, ‖coeff c (F * G)‖ ^ 2 * bweight c := rfl
    _ ≤ ∑ c ∈ (F * G).support, ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
          (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) := by
        refine sum_le_sum fun c _ => ?_
        rw [coeff_mul_eq]
        exact key_c hF' c
    _ = ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 ∈ (F * G).support),
          (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) :=
        sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ p ∈ F.support ×ˢ G.support,
          (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => hnn p)
    _ = bnormSq F * bnormSq G := by
        rw [bnormSq, bnormSq, Finset.sum_mul_sum, Finset.sum_product]

end NMul

end Formalism.NormUnitaryCountingLemmas
