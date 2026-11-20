import Formalism.TowerValuationBounds.TowerValuationBoundIndexed
import Formalism.TowerValuationBounds.TowerValuationProofs.SumAdditiveCharacterEqZero

noncomputable section
namespace Formalism.ValuationGridEstimates
open Finset

/- English proof (translation)
Introduce `G _ v hv a a' d h p q e had hae hdh he ha' T Td Tdp ρ E N0 ε δ σ H1 H2 c0 c00 A A0 A0' hc0 hc00 hA ub ua hub hua r hr`. Substitute `hr` using the available equality. Establish `hv1 : v 1 = 0`. Establish `h11` using `hv 1 1`. Rewrite `h11` using `[one_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hvinv : ∀ x, v x⁻¹ = - v x` using `fun x => by`. Establish `h2` using `hv x x⁻¹`. Rewrite `h2` using `[mul_inv_cancel, hv1]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hvdiv : ∀ x y, v (x / y) = v x - v y` using `fun x y => by`. Rewrite using `[div_eq_mul_inv, hv, hvinv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hvprod : ∀ {ι : Type} (s : Finset ι) (f : ι → G), v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i)`. Introduce `ι s f`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hv1]`. Consider the case `insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, hv, ih]`. Establish `hvA` using `congrArg v hA`. Rewrite `hvA` using `[hvdiv, hvprod]`.

Simplify using `only [hv, hvinv, hvdiv, hvprod]`. Take `⟨U, hU⟩ : ∃ U : ℕ, U = h - (p + q)` from `⟨_, rfl⟩`. Take `⟨P, hP⟩ : ∃ P : ℕ, P = e + q - p` from `⟨_, rfl⟩`. Establish `hUz : (h : ℤ) - (p + q) = (U : ℤ)` using `by omega`. Establish `hPz : (e : ℤ) + q - p = (P : ℤ)` using `by omega`.

Rewrite `hvA` using `[hUz, hPz]`. Rewrite `H2` using `[hPz]`. Establish `I1 : ∑ s ∈ Finset.Icc (1 - (P : ℤ)) (U : ℤ), v (ρ s) = ∑ s ∈ Finset.Icc (1 - (P : ℤ)) 0, v (ρ s) + ∑ s ∈ Finset.Icc (1 : ℤ) U, v (ρ s)`. Rewrite using `[← Finset.sum_union]`. Use `Finset.sum_congr ?_ (fun _ _ => rfl)` and prove the remaining obligations.

Use extensionality with `x`. Simplify using `only [Finset.mem_union, Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.disjoint_left]`. Introduce `x hx hx'`.

Simplify using `only [Finset.mem_Icc] at hx hx'`. Use linear arithmetic over natural numbers and integers. Establish `I2 : ∑ s ∈ Finset.Icc (1 - (P : ℤ)) 0, v (ρ s) = ∑ s ∈ Finset.Icc (1 : ℤ) P, v (ρ s)`. Use `Finset.sum_nbij' (fun s => 1 - s) (fun t => 1 - t) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`.

Simplify using `only [Finset.mem_Icc, Finset.mem_coe] at *`. Use linear arithmetic over natural numbers and integers. Introduce `x hx`. Simplify using `only [Finset.mem_Icc, Finset.mem_coe] at *`. Use linear arithmetic over natural numbers and integers.

Introduce `x _`. Expand and normalize the polynomial expressions, which then agree. Introduce `x _`. Expand and normalize the polynomial expressions, which then agree. Introduce `s hs`.

Simplify using `only [Finset.mem_Icc] at hs`. Take `⟨h1, h2⟩` from `H2 s hs.1 hs.2`. Rewrite using `[h1, hv, h2, zero_add]`. Establish `I3 : ∑ k ∈ Finset.Icc 1 p, v (ρ ((e : ℤ) + q - k + 1)) = ∑ t ∈ Finset.Icc ((P : ℤ) + 1) ((e : ℤ) + q), v (ρ t)`. Use `Finset.sum_nbij' (fun k : ℕ => (e : ℤ) + q - k + 1) (fun t : ℤ => ((e : ℤ) + q + 1 - t).toNat) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `x hx`. Simplify using `only [Finset.mem_Icc, Finset.mem_coe] at *`. Use linear arithmetic over natural numbers and integers. Introduce `x hx`. Simplify using `only [Finset.mem_Icc, Finset.mem_coe] at *`.

Use linear arithmetic over natural numbers and integers. Introduce `x hx`. Simplify using `only [Finset.mem_Icc, Finset.mem_coe] at *`. Use linear arithmetic over natural numbers and integers. Introduce `x hx`.

Simplify using `only [Finset.mem_Icc, Finset.mem_coe] at *`. Use linear arithmetic over natural numbers and integers. Introduce `k _`. Both sides reduce to the same expression. Establish `I4 : ∑ k ∈ Finset.Icc 1 q, v (ρ ((e : ℤ) + k)) = ∑ t ∈ Finset.Icc ((e : ℤ) + 1) ((e : ℤ) + q), v (ρ t)`.

Use `Finset.sum_nbij' (fun k : ℕ => (e : ℤ) + k) (fun t : ℤ => (t - e).toNat) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Finset.mem_Icc, Finset.mem_coe] at *`. Use linear arithmetic over natural numbers and integers. Introduce `x hx`.

Simplify using `only [Finset.mem_Icc, Finset.mem_coe] at *`. Use linear arithmetic over natural numbers and integers. Introduce `x hx`. Simplify using `only [Finset.mem_Icc, Finset.mem_coe] at *`. Use linear arithmetic over natural numbers and integers.

Introduce `x hx`. Simplify using `only [Finset.mem_Icc, Finset.mem_coe] at *`. Use linear arithmetic over natural numbers and integers. Introduce `k _`. Both sides reduce to the same expression.

Establish `ShiftFormula : ∑ t ∈ Finset.Icc (1 : ℤ) P, v (ρ t) + ∑ t ∈ Finset.Icc ((P : ℤ) + 1) ((e : ℤ) + q), v (ρ t) = ∑ t ∈ Finset.Icc (1 : ℤ) ((e : ℤ) + q), v (ρ t)`. Rewrite using `[← Finset.sum_union]`. Use `Finset.sum_congr ?_ (fun _ _ => rfl)` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [Finset.mem_union, Finset.mem_Icc]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.disjoint_left]`. Introduce `x hx hx'`. Simplify using `only [Finset.mem_Icc] at hx hx'`. Use linear arithmetic over natural numbers and integers.

Establish `I5b : ∑ t ∈ Finset.Icc (1 : ℤ) e, v (ρ t) + ∑ t ∈ Finset.Icc ((e : ℤ) + 1) ((e : ℤ) + q), v (ρ t) = ∑ t ∈ Finset.Icc (1 : ℤ) ((e : ℤ) + q), v (ρ t)`. Rewrite using `[← Finset.sum_union]`. Use `Finset.sum_congr ?_ (fun _ _ => rfl)` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [Finset.mem_union, Finset.mem_Icc]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.disjoint_left]`. Introduce `x hx hx'`. Simplify using `only [Finset.mem_Icc] at hx hx'`. Use linear arithmetic over natural numbers and integers.

Establish `hF : ∀ s ∈ Finset.Icc (1 : ℤ) h, v (ρ s) ≤ |v (Td s)| + |v (T s)| + ε`. Introduce `s hs`. Simplify using `only [Finset.mem_Icc] at hs`. Take `⟨_, hρ, _, hup⟩` from `H1 s hs.1 hs.2`. Rewrite using `[hρ, hvdiv]`.

Use `le_abs_self (v (Td s))` as an intermediate fact. Use `neg_abs_le (v (T s))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hε : ∀ s ∈ Finset.Icc (1 : ℤ) h, -ε ≤ |v (Td s)| + N0 s`. Introduce `s hs`.

Simplify using `only [Finset.mem_Icc] at hs`. Take `⟨_, _, hlo, hup⟩` from `H1 s hs.1 hs.2`. Use `le_abs_self (v (Td s))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN : ∀ s ∈ Finset.Icc (1 : ℤ) h, 0 ≤ N0 s` using `fun s hs => by`.

Simplify using `only [Finset.mem_Icc] at hs`. Conclude with `(H1 s hs.1 hs.2).1`. Establish `hcard : ∀ (lo hi : ℤ) (n : ℕ), hi + 1 - lo = n → ((Finset.Icc lo hi).card : ℝ) = n`. Introduce `lo hi n hn`. Rewrite using `[Int.card_Icc, hn]`.

Simplify using the standard rewrite rules. Set `C : ℤ → ℝ` to `fun s => |v (Td s)| + |v (T s)| + N0 s`. Establish `hsub : ∀ {lo hi : ℤ}, 1 ≤ lo → hi ≤ h → Finset.Icc lo hi ⊆ Finset.Icc (1 : ℤ) h`. Introduce `lo hi h1 h2 x hx`. Simplify using `only [Finset.mem_Icc] at hx ⊢`.

Use linear arithmetic over natural numbers and integers. Establish `hCnn : ∀ s ∈ Finset.Icc (1 : ℤ) h, 0 ≤ C s` using `fun s hs => by`. Use `hN s hs` as an intermediate fact. Use `abs_nonneg (v (Td s))` as an intermediate fact. Use `abs_nonneg (v (T s))` as an intermediate fact.

Simplify using `only [C]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `Be : ∑ s ∈ Finset.Icc (1 : ℤ) e, v (ρ s) ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, C s + e * ε`. Establish `hs1 : Finset.Icc (1 : ℤ) e ⊆ Finset.Icc (1 : ℤ) h` using `hsub le_rfl (by omega)`. Combine the equalities or inequalities in the displayed calculation.

Use `hF s (hs1 hs)` as an intermediate fact. Use `hN s (hs1 hs)` as an intermediate fact. Simplify using `only [C]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = ∑ s ∈ Finset.Icc (1 : ℤ) e, C s + e * ε := by`.

Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard 1 e e (by ring)]`. Use `_ ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, C s + e * ε := add_le_add (Finset.sum_le_sum_of_subset_of_nonneg hs1 (fun s hs _ => hCnn s hs)) le_rfl`. Establish `BU : ∑ s ∈ Finset.Icc (1 : ℤ) U, v (ρ s) ≤ ∑ s ∈ Finset.Icc (1 : ℤ) U, C s + U * ε`. Establish `hs1 : Finset.Icc (1 : ℤ) U ⊆ Finset.Icc (1 : ℤ) h` using `hsub le_rfl (by omega)`. Combine the equalities or inequalities in the displayed calculation.

Use `hF s (hs1 hs)` as an intermediate fact. Use `hN s (hs1 hs)` as an intermediate fact. Simplify using `only [C]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = ∑ s ∈ Finset.Icc (1 : ℤ) U, C s + U * ε := by`.

Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard 1 U U (by ring)]`. Establish `Bq : -(q * ε) ≤ ∑ s ∈ Finset.Icc ((U : ℤ) + 1) ((U : ℤ) + q), C s`. Establish `hs1 : Finset.Icc ((U : ℤ) + 1) ((U : ℤ) + q) ⊆ Finset.Icc (1 : ℤ) h` using `hsub (by omega) (by omega)`. Establish `h3` using `Finset.sum_le_sum (s := Finset.Icc ((U : ℤ) + 1) ((U : ℤ) + q)) (f := fun _ => -ε) (g := C) (fun s hs => by`. Use `hε s (hs1 hs)` as an intermediate fact.

Use `abs_nonneg (v (T s))` as an intermediate fact. Simplify using `only [C]`. Use the proof step `linarith)`. Rewrite `h3` using `[Finset.sum_const, nsmul_eq_mul, hcard _ _ q (by ring)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hUq : ∑ s ∈ Finset.Icc (1 : ℤ) U, C s + ∑ s ∈ Finset.Icc ((U : ℤ) + 1) ((U : ℤ) + q), C s ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, C s`. Rewrite using `[← Finset.sum_union]`. Use `Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun s hs _ => hCnn s hs)` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Finset.mem_union, Finset.mem_Icc] at hx ⊢`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.disjoint_left]`. Introduce `x hx hx'`. Simplify using `only [Finset.mem_Icc] at hx hx'`. Use linear arithmetic over natural numbers and integers.

Establish `hCsum : ∑ s ∈ Finset.Icc (1 : ℤ) h, C s = ∑ s ∈ Finset.Icc (1 : ℤ) h, |v (Td s)| + ∑ s ∈ Finset.Icc (1 : ℤ) h, |v (T s)| + ∑ s ∈ Finset.Icc (1 : ℤ) h, N0 s`. Simplify using `only [C, Finset.sum_add_distrib]`. Establish `hTnn : 0 ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, |v (T s)|` using `Finset.sum_nonneg fun s _ => abs_nonneg _`. Establish `hNnn : 0 ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, N0 s` using `Finset.sum_nonneg hN`. Establish `hσq : ∑ j ∈ Finset.range q, v (ub j) ≤ q * σ`.

Establish `h3` using `Finset.sum_le_sum (s := Finset.range q) (f := fun j => v (ub j)) (g := fun _ => σ) (fun j hj => hub j (Finset.mem_range.1 hj))`. Simplify using `using h3`. Establish `hσp : ∑ i ∈ Finset.range p, v (ua i) ≤ p * σ`. Establish `h3` using `Finset.sum_le_sum (s := Finset.range p) (f := fun i => v (ua i)) (g := fun _ => σ) (fun i hi => hua i (Finset.mem_range.1 hi))`. Simplify using `using h3`.

Establish `hε2 : ((a : ℝ) - p) * ε = e * ε + U * ε + q * ε`. Establish `ha : a = e + U + q + p` using `by omega`. Rewrite using `[ha]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hpq : ((p + q : ℕ) : ℝ) * σ = p * σ + q * σ`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Combine the linear relations using `[hvA, I1, I2, I3, I4, ShiftFormula, I5b, Be, BU, Bq, hUq, hσq, hσp, hc0, hc00, hCsum, hTnn, hNnn, hε2, hpq]`.
-/
theorem valuation_ratio_index : TowerValuationBoundIndexed := by
  intro G _ v hv a a' d h p q e had hae hdh he ha' T Td Tdp ρ E N0 ε δ σ H1 H2 c0 c00 A A0 A0'
    hc0 hc00 hA ub ua hub hua r hr
  classical
  subst hr
  have hv1 : v 1 = 0 := by
    have h11 := hv 1 1
    rw [one_mul] at h11
    linarith
  have hvinv : ∀ x, v x⁻¹ = - v x := fun x => by
    have h2 := hv x x⁻¹
    rw [mul_inv_cancel, hv1] at h2
    linarith
  have hvdiv : ∀ x y, v (x / y) = v x - v y := fun x y => by
    rw [div_eq_mul_inv, hv, hvinv]; ring
  have hvprod : ∀ {ι : Type} (s : Finset ι) (f : ι → G),
      v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
    intro ι s f
    induction s using Finset.induction_on with
    | empty => simp [hv1]
    | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, hv, ih]
  have hvA := congrArg v hA
  rw [hvdiv, hvprod] at hvA
  simp only [hv, hvinv, hvdiv, hvprod]
  obtain ⟨U, hU⟩ : ∃ U : ℕ, U = h - (p + q) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = e + q - p := ⟨_, rfl⟩
  have hUz : (h : ℤ) - (p + q) = (U : ℤ) := by omega
  have hPz : (e : ℤ) + q - p = (P : ℤ) := by omega
  rw [hUz, hPz] at hvA
  rw [hPz] at H2
  have I1 : ∑ s ∈ Finset.Icc (1 - (P : ℤ)) (U : ℤ), v (ρ s) =
      ∑ s ∈ Finset.Icc (1 - (P : ℤ)) 0, v (ρ s) + ∑ s ∈ Finset.Icc (1 : ℤ) U, v (ρ s) := by
    rw [← Finset.sum_union]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    · rw [Finset.disjoint_left]; intro x hx hx'; simp only [Finset.mem_Icc] at hx hx'; omega
  have I2 : ∑ s ∈ Finset.Icc (1 - (P : ℤ)) 0, v (ρ s) = ∑ s ∈ Finset.Icc (1 : ℤ) P, v (ρ s) := by
    refine Finset.sum_nbij' (fun s => 1 - s) (fun t => 1 - t) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x _; ring
    · intro x _; ring
    · intro s hs
      simp only [Finset.mem_Icc] at hs
      obtain ⟨h1, h2⟩ := H2 s hs.1 hs.2
      rw [h1, hv, h2, zero_add]
  have I3 : ∑ k ∈ Finset.Icc 1 p, v (ρ ((e : ℤ) + q - k + 1)) =
      ∑ t ∈ Finset.Icc ((P : ℤ) + 1) ((e : ℤ) + q), v (ρ t) := by
    refine Finset.sum_nbij' (fun k : ℕ => (e : ℤ) + q - k + 1)
      (fun t : ℤ => ((e : ℤ) + q + 1 - t).toNat) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro k _; rfl
  have I4 : ∑ k ∈ Finset.Icc 1 q, v (ρ ((e : ℤ) + k)) =
      ∑ t ∈ Finset.Icc ((e : ℤ) + 1) ((e : ℤ) + q), v (ρ t) := by
    refine Finset.sum_nbij' (fun k : ℕ => (e : ℤ) + k) (fun t : ℤ => (t - e).toNat) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro k _; rfl
  have ShiftFormula : ∑ t ∈ Finset.Icc (1 : ℤ) P, v (ρ t) +
      ∑ t ∈ Finset.Icc ((P : ℤ) + 1) ((e : ℤ) + q), v (ρ t) =
      ∑ t ∈ Finset.Icc (1 : ℤ) ((e : ℤ) + q), v (ρ t) := by
    rw [← Finset.sum_union]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    · rw [Finset.disjoint_left]; intro x hx hx'; simp only [Finset.mem_Icc] at hx hx'; omega
  have I5b : ∑ t ∈ Finset.Icc (1 : ℤ) e, v (ρ t) +
      ∑ t ∈ Finset.Icc ((e : ℤ) + 1) ((e : ℤ) + q), v (ρ t) =
      ∑ t ∈ Finset.Icc (1 : ℤ) ((e : ℤ) + q), v (ρ t) := by
    rw [← Finset.sum_union]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    · rw [Finset.disjoint_left]; intro x hx hx'; simp only [Finset.mem_Icc] at hx hx'; omega
  have hF : ∀ s ∈ Finset.Icc (1 : ℤ) h, v (ρ s) ≤ |v (Td s)| + |v (T s)| + ε := by
    intro s hs
    simp only [Finset.mem_Icc] at hs
    obtain ⟨_, hρ, _, hup⟩ := H1 s hs.1 hs.2
    rw [hρ, hvdiv]
    have := le_abs_self (v (Td s))
    have := neg_abs_le (v (T s))
    linarith
  have hε : ∀ s ∈ Finset.Icc (1 : ℤ) h, -ε ≤ |v (Td s)| + N0 s := by
    intro s hs
    simp only [Finset.mem_Icc] at hs
    obtain ⟨_, _, hlo, hup⟩ := H1 s hs.1 hs.2
    have := le_abs_self (v (Td s))
    linarith
  have hN : ∀ s ∈ Finset.Icc (1 : ℤ) h, 0 ≤ N0 s := fun s hs => by
    simp only [Finset.mem_Icc] at hs
    exact (H1 s hs.1 hs.2).1
  have hcard : ∀ (lo hi : ℤ) (n : ℕ), hi + 1 - lo = n → ((Finset.Icc lo hi).card : ℝ) = n := by
    intro lo hi n hn
    rw [Int.card_Icc, hn]
    simp
  let C : ℤ → ℝ := fun s => |v (Td s)| + |v (T s)| + N0 s
  have hsub : ∀ {lo hi : ℤ}, 1 ≤ lo → hi ≤ h → Finset.Icc lo hi ⊆ Finset.Icc (1 : ℤ) h := by
    intro lo hi h1 h2 x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  have hCnn : ∀ s ∈ Finset.Icc (1 : ℤ) h, 0 ≤ C s := fun s hs => by
    have := hN s hs
    have := abs_nonneg (v (Td s))
    have := abs_nonneg (v (T s))
    simp only [C]
    linarith
  have Be : ∑ s ∈ Finset.Icc (1 : ℤ) e, v (ρ s) ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, C s + e * ε := by
    have hs1 : Finset.Icc (1 : ℤ) e ⊆ Finset.Icc (1 : ℤ) h := hsub le_rfl (by omega)
    calc ∑ s ∈ Finset.Icc (1 : ℤ) e, v (ρ s) ≤ ∑ s ∈ Finset.Icc (1 : ℤ) e, (C s + ε) :=
          Finset.sum_le_sum fun s hs => by
            have := hF s (hs1 hs)
            have := hN s (hs1 hs)
            simp only [C]
            linarith
      _ = ∑ s ∈ Finset.Icc (1 : ℤ) e, C s + e * ε := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard 1 e e (by ring)]
      _ ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, C s + e * ε :=
          add_le_add (Finset.sum_le_sum_of_subset_of_nonneg hs1 (fun s hs _ => hCnn s hs)) le_rfl
  have BU : ∑ s ∈ Finset.Icc (1 : ℤ) U, v (ρ s) ≤ ∑ s ∈ Finset.Icc (1 : ℤ) U, C s + U * ε := by
    have hs1 : Finset.Icc (1 : ℤ) U ⊆ Finset.Icc (1 : ℤ) h := hsub le_rfl (by omega)
    calc ∑ s ∈ Finset.Icc (1 : ℤ) U, v (ρ s) ≤ ∑ s ∈ Finset.Icc (1 : ℤ) U, (C s + ε) :=
          Finset.sum_le_sum fun s hs => by
            have := hF s (hs1 hs)
            have := hN s (hs1 hs)
            simp only [C]
            linarith
      _ = ∑ s ∈ Finset.Icc (1 : ℤ) U, C s + U * ε := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard 1 U U (by ring)]
  have Bq : -(q * ε) ≤ ∑ s ∈ Finset.Icc ((U : ℤ) + 1) ((U : ℤ) + q), C s := by
    have hs1 : Finset.Icc ((U : ℤ) + 1) ((U : ℤ) + q) ⊆ Finset.Icc (1 : ℤ) h :=
      hsub (by omega) (by omega)
    have h3 := Finset.sum_le_sum (s := Finset.Icc ((U : ℤ) + 1) ((U : ℤ) + q))
      (f := fun _ => -ε) (g := C) (fun s hs => by
        have := hε s (hs1 hs)
        have := abs_nonneg (v (T s))
        simp only [C]
        linarith)
    rw [Finset.sum_const, nsmul_eq_mul, hcard _ _ q (by ring)] at h3
    linarith
  have hUq : ∑ s ∈ Finset.Icc (1 : ℤ) U, C s +
      ∑ s ∈ Finset.Icc ((U : ℤ) + 1) ((U : ℤ) + q), C s ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, C s := by
    rw [← Finset.sum_union]
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun s hs _ => hCnn s hs)
      intro x hx
      simp only [Finset.mem_union, Finset.mem_Icc] at hx ⊢
      omega
    · rw [Finset.disjoint_left]; intro x hx hx'; simp only [Finset.mem_Icc] at hx hx'; omega
  have hCsum : ∑ s ∈ Finset.Icc (1 : ℤ) h, C s = ∑ s ∈ Finset.Icc (1 : ℤ) h, |v (Td s)| +
      ∑ s ∈ Finset.Icc (1 : ℤ) h, |v (T s)| + ∑ s ∈ Finset.Icc (1 : ℤ) h, N0 s := by
    simp only [C, Finset.sum_add_distrib]
  have hTnn : 0 ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, |v (T s)| :=
    Finset.sum_nonneg fun s _ => abs_nonneg _
  have hNnn : 0 ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, N0 s := Finset.sum_nonneg hN
  have hσq : ∑ j ∈ Finset.range q, v (ub j) ≤ q * σ := by
    have h3 := Finset.sum_le_sum (s := Finset.range q) (f := fun j => v (ub j)) (g := fun _ => σ)
      (fun j hj => hub j (Finset.mem_range.1 hj))
    simpa using h3
  have hσp : ∑ i ∈ Finset.range p, v (ua i) ≤ p * σ := by
    have h3 := Finset.sum_le_sum (s := Finset.range p) (f := fun i => v (ua i)) (g := fun _ => σ)
      (fun i hi => hua i (Finset.mem_range.1 hi))
    simpa using h3
  have hε2 : ((a : ℝ) - p) * ε = e * ε + U * ε + q * ε := by
    have ha : a = e + U + q + p := by omega
    rw [ha]
    push_cast
    ring
  have hpq : ((p + q : ℕ) : ℝ) * σ = p * σ + q * σ := by
    push_cast
    ring
  linarith [hvA, I1, I2, I3, I4, ShiftFormula, I5b, Be, BU, Bq, hUq, hσq, hσp, hc0, hc00, hCsum, hTnn, hNnn,
    hε2, hpq]

/- English proof (translation)
Simplify using `only [Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun w _ => by ring`.
-/
private theorem sum_mul_add_smul_five_eq_add_sums {W : Type} (W0 : Finset W) (lam a b c d f : W → ℝ)
    (k1 k2 k3 k4 : ℝ) :
    ∑ w ∈ W0, lam w * (a w + k1 * b w + k2 * c w + k3 * d w + k4 * f w) =
      ∑ w ∈ W0, lam w * a w + k1 * ∑ w ∈ W0, lam w * b w + k2 * ∑ w ∈ W0, lam w * c w +
        k3 * ∑ w ∈ W0, lam w * d w + k4 * ∑ w ∈ W0, lam w * f w := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => by ring

/- English proof (translation)
Introduce `W X S m N lam δ ell N0 vr vx XX ch dd hh yy S0 cc ee qq vq H BN Bδ W0 hlam hδ hN0 hvq hprime hlamL hdd hddN hyy hcc hvr hH hBN hBδ hqq`. Establish `group : ∀ φ : ℕ → ℝ, (∀ l, 0 ≤ φ l) → ∑ w ∈ W0, lam w * φ (ell w) ≤ ∑ l ∈ W0.image ell, φ l * Real.log l`. Introduce `φ hφ`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := ell) (t := W0.image ell) (fun w hw => Finset.mem_image_of_mem ell hw)]`. Use `Finset.sum_le_sum fun l _ => ?_` and prove the remaining obligations.

Establish `h1 : ∑ w ∈ W0 with ell w = l, lam w * φ (ell w) = φ l * ∑ w ∈ W0 with ell w = l, lam w`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w hw => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.1 hw).2]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1]`. Conclude with `mul_le_mul_of_nonneg_left (hlamL l _ (fun w hw => (Finset.mem_filter.1 hw).2)) (hφ l)`. Establish `hprimes : ∀ l ∈ W0.image ell, l.Prime`. Introduce `l hl`. Take `⟨w, _, rfl⟩` from `Finset.mem_image.1 hl`.

Conclude with `hprime w`. Establish `hBN0 : ∀ ij : Fin m × Fin m, 0 ≤ BN` using `fun ij => by`. Simplify using `using hBN ij 0 ∅ (by simp)`. Establish `hlog : ∀ s ∈ S0, 0 ≤ Real.log (qq s)` using `fun s hs => by`. Simplify using `using hqq s hs ∅`.

Establish `hT1 : ∀ ij, ∑ w ∈ W0, lam w * (∑ x ∈ XX ij (ch w), |vx w x|) ≤ ∑ b, ∑ x ∈ XX ij b, H x`. Introduce `ij`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := ch) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]`. Use `Finset.sum_le_sum fun b _ => ?_` and prove the remaining obligations. Establish `h1 : ∑ w ∈ W0 with ch w = b, lam w * (∑ x ∈ XX ij (ch w), |vx w x|) = ∑ x ∈ XX ij b, ∑ w ∈ W0 with ch w = b, lam w * |vx w x|`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun w hw => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.1 hw).2, Finset.mul_sum]`. Rewrite using `[h1]`. Conclude with `Finset.sum_le_sum fun x _ => hH x _`.

Establish `hT2 : ∀ ij, ∑ w ∈ W0, lam w * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) ≤ N * BN`. Introduce `ij`. Establish `h1 : ∑ w ∈ W0, lam w * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) = ∑ s ∈ Icc (1 : ℤ) (hh ij), ∑ w ∈ W0, lam w * N0 ij s (ell w)`. Simplify using `only [Finset.mul_sum]`. Conclude with `Finset.sum_comm`.

Rewrite using `[h1]`. Establish `h2 : ∀ s ∈ Icc (1 : ℤ) (hh ij), ∑ w ∈ W0, lam w * N0 ij s (ell w) ≤ BN`. Introduce `s _`. Conclude with `(group (N0 ij s) (hN0 ij s)).trans (hBN ij s _ hprimes)`. Establish `h3` using `Finset.sum_le_sum h2`.

Rewrite `h3` using `[Finset.sum_const, nsmul_eq_mul, Int.card_Icc]`. Establish `h4 : ((hh ij : ℤ) + 1 - 1).toNat = hh ij` using `by omega`. Rewrite `h3` using `[h4]`. Establish `h5 : (hh ij : ℝ) ≤ N`. Use `hdd ij` as an intermediate fact.

Use `hddN ij` as an intermediate fact. Conclude with `(by omega : hh ij ≤ N)` after adjusting the coercions. Use `hBN0 ij` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hT3 : ∑ w ∈ W0, lam w * ((ell w : ℝ) ^ 2)⁻¹ ≤ 1`.

Use `(group (fun l => ((l : ℝ) ^ 2)⁻¹) (fun l => by positivity)).trans ?_` and prove the remaining obligations. Establish `h1` using `prime_budget_bound (fun _ => 0) 0 (fun P _ => by simp) (W0.image ell) hprimes`. Simplify using `using h1`. Establish `hT4 : ∑ w ∈ W0, lam w * δ w ≤ Bδ` using `hBδ W0`. Establish `hT5 : ∑ w ∈ W0, lam w * (∑ s ∈ S0, (cc s : ℝ) * vq w s) ≤ ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)`.

Establish `h1 : ∑ w ∈ W0, lam w * (∑ s ∈ S0, (cc s : ℝ) * vq w s) = ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ W0, lam w * vq w s`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun w _ => by ring`. Rewrite using `[h1]`.

Use `Finset.sum_le_sum fun s hs => ?_` and prove the remaining obligations. Establish `h2` using `hqq s hs W0`. Establish `h3 : (cc s : ℝ) ≤ ee s` using `by exact_mod_cast hcc s hs`. Establish `h4` using `hlog s hs`. Combine the equalities or inequalities in the displayed calculation.

Establish `hT5nn : 0 ≤ ∑ w ∈ W0, lam w * (∑ s ∈ S0, (cc s : ℝ) * vq w s)` using `Finset.sum_nonneg fun w _ => mul_nonneg (hlam w) (Finset.sum_nonneg fun s _ => mul_nonneg (by positivity) (hvq w s))`. Establish `hSnn : 0 ≤ ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)` using `Finset.sum_nonneg fun s hs => mul_nonneg (by positivity) (hlog s hs)`. Use `set K : ℝ := 5 * (N * BN) + 2 * N + 6 * Bδ + 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) with hK`. Establish `hper : ∀ ij, ∑ w ∈ W0, lam w * ((∑ x ∈ XX ij (ch w), |vx w x|) + 5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) + dd ij * ((ell w : ℝ) ^ 2)⁻¹ + 6 * δ w + 2 * yy ij * (∑ s ∈ S0, (cc s : ℝ) * vq w s)) ≤ (∑ b, ∑ x ∈ XX ij b, H x) + K`. Introduce `ij`.

Rewrite using `[sum_mul_add_smul_five_eq_add_sums W0 lam (fun w => ∑ x ∈ XX ij (ch w), |vx w x|) (fun w => ∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) (fun w => ((ell w : ℝ) ^ 2)⁻¹) δ (fun w => ∑ s ∈ S0, (cc s : ℝ) * vq w s) 5 (dd ij) 6 (2 * yy ij)]`. Establish `e1` using `hT1 ij`. Establish `e2` using `hT2 ij`. Establish `e3 : (dd ij : ℝ) * ∑ w ∈ W0, lam w * ((ell w : ℝ) ^ 2)⁻¹ ≤ 2 * N`. Establish `h1 : (dd ij : ℝ) ≤ 2 * N` using `by exact_mod_cast hddN ij`.

Combine the equalities or inequalities in the displayed calculation. Establish `e5 : 2 * (yy ij : ℝ) * ∑ w ∈ W0, lam w * (∑ s ∈ S0, (cc s : ℝ) * vq w s) ≤ 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)`. Establish `h1 : (yy ij : ℝ) ≤ m` using `by exact_mod_cast hyy ij`. Establish `h2 : 0 ≤ (yy ij : ℝ)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hK]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.mul_sum]`. Conclude with `Finset.sum_comm`.

Use `_ ≤ ∑ ij : Fin m × Fin m, ((∑ b, ∑ x ∈ XX ij b, H x) + K) := Finset.sum_le_sum fun ij _ => hper ij`. Use `_ = (∑ ij, ∑ b, ∑ x ∈ XX ij b, H x) + (m : ℝ) ^ 2 * K := by`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ (∑ ij, ∑ b, ∑ x ∈ XX ij b, H x) + (m : ℝ) ^ 2 * (10 * N * BN + 2 * N + 6 * Bδ + 4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) := by`. Break down `Nat.eq_zero_or_pos m with hm | hm` into its components or cases. Substitute `hm` using the available equality. Simplify using the standard rewrite rules. Establish `hBN : 0 ≤ BN` using `hBN0 (⟨0, hm⟩, ⟨0, hm⟩)`.

Establish `h1 : K ≤ 10 * N * BN + 2 * N + 6 * Bδ + 4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)`. Rewrite using `[hK]`. Establish `: 0 ≤ (N : ℝ) * BN` using `mul_nonneg (by positivity) hBN`. Establish `: 0 ≤ (m : ℝ) * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)` using `mul_nonneg (by positivity) hSnn`. Use the polynomial consequences of the given equalities and inequalities.

Use `mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem grid_index_bound : GridValuationBoundIndexed := by
  intro W X S m N lam δ ell N0 vr vx XX ch dd hh yy S0 cc ee qq vq H BN Bδ W0
    hlam hδ hN0 hvq hprime hlamL hdd hddN hyy hcc hvr hH hBN hBδ hqq
  classical

  have group : ∀ φ : ℕ → ℝ, (∀ l, 0 ≤ φ l) →
      ∑ w ∈ W0, lam w * φ (ell w) ≤ ∑ l ∈ W0.image ell, φ l * Real.log l := by
    intro φ hφ
    rw [← Finset.sum_fiberwise_of_maps_to (g := ell) (t := W0.image ell)
      (fun w hw => Finset.mem_image_of_mem ell hw)]
    refine Finset.sum_le_sum fun l _ => ?_
    have h1 : ∑ w ∈ W0 with ell w = l, lam w * φ (ell w) =
        φ l * ∑ w ∈ W0 with ell w = l, lam w := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [(Finset.mem_filter.1 hw).2]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left
      (hlamL l _ (fun w hw => (Finset.mem_filter.1 hw).2)) (hφ l)
  have hprimes : ∀ l ∈ W0.image ell, l.Prime := by
    intro l hl
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.1 hl
    exact hprime w
  have hBN0 : ∀ ij : Fin m × Fin m, 0 ≤ BN := fun ij => by
    simpa using hBN ij 0 ∅ (by simp)
  have hlog : ∀ s ∈ S0, 0 ≤ Real.log (qq s) := fun s hs => by
    simpa using hqq s hs ∅
  have hT1 : ∀ ij, ∑ w ∈ W0, lam w * (∑ x ∈ XX ij (ch w), |vx w x|) ≤
      ∑ b, ∑ x ∈ XX ij b, H x := by
    intro ij
    rw [← Finset.sum_fiberwise_of_maps_to (g := ch) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_le_sum fun b _ => ?_
    have h1 : ∑ w ∈ W0 with ch w = b, lam w * (∑ x ∈ XX ij (ch w), |vx w x|) =
        ∑ x ∈ XX ij b, ∑ w ∈ W0 with ch w = b, lam w * |vx w x| := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [(Finset.mem_filter.1 hw).2, Finset.mul_sum]
    rw [h1]
    exact Finset.sum_le_sum fun x _ => hH x _
  have hT2 : ∀ ij, ∑ w ∈ W0, lam w * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) ≤ N * BN := by
    intro ij
    have h1 : ∑ w ∈ W0, lam w * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) =
        ∑ s ∈ Icc (1 : ℤ) (hh ij), ∑ w ∈ W0, lam w * N0 ij s (ell w) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    rw [h1]
    have h2 : ∀ s ∈ Icc (1 : ℤ) (hh ij), ∑ w ∈ W0, lam w * N0 ij s (ell w) ≤ BN := by
      intro s _
      exact (group (N0 ij s) (hN0 ij s)).trans (hBN ij s _ hprimes)
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_const, nsmul_eq_mul, Int.card_Icc] at h3
    have h4 : ((hh ij : ℤ) + 1 - 1).toNat = hh ij := by omega
    rw [h4] at h3
    have h5 : (hh ij : ℝ) ≤ N := by
      have := hdd ij
      have := hddN ij
      exact_mod_cast (by omega : hh ij ≤ N)
    have := hBN0 ij
    nlinarith
  have hT3 : ∑ w ∈ W0, lam w * ((ell w : ℝ) ^ 2)⁻¹ ≤ 1 := by
    refine (group (fun l => ((l : ℝ) ^ 2)⁻¹) (fun l => by positivity)).trans ?_
    have h1 := prime_budget_bound (fun _ => 0) 0 (fun P _ => by simp) (W0.image ell) hprimes
    simpa using h1
  have hT4 : ∑ w ∈ W0, lam w * δ w ≤ Bδ := hBδ W0
  have hT5 : ∑ w ∈ W0, lam w * (∑ s ∈ S0, (cc s : ℝ) * vq w s) ≤
      ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) := by
    have h1 : ∑ w ∈ W0, lam w * (∑ s ∈ S0, (cc s : ℝ) * vq w s) =
        ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ W0, lam w * vq w s := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun w _ => by ring
    rw [h1]
    refine Finset.sum_le_sum fun s hs => ?_
    have h2 := hqq s hs W0
    have h3 : (cc s : ℝ) ≤ ee s := by exact_mod_cast hcc s hs
    have h4 := hlog s hs
    calc (cc s : ℝ) * ∑ w ∈ W0, lam w * vq w s ≤ (cc s : ℝ) * Real.log (qq s) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (ee s : ℝ) * Real.log (qq s) := mul_le_mul_of_nonneg_right h3 h4
  have hT5nn : 0 ≤ ∑ w ∈ W0, lam w * (∑ s ∈ S0, (cc s : ℝ) * vq w s) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (hlam w)
      (Finset.sum_nonneg fun s _ => mul_nonneg (by positivity) (hvq w s))
  have hSnn : 0 ≤ ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) :=
    Finset.sum_nonneg fun s hs => mul_nonneg (by positivity) (hlog s hs)
  set K : ℝ := 5 * (N * BN) + 2 * N + 6 * Bδ + 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)
    with hK
  have hper : ∀ ij, ∑ w ∈ W0, lam w * ((∑ x ∈ XX ij (ch w), |vx w x|) +
      5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) + dd ij * ((ell w : ℝ) ^ 2)⁻¹ +
      6 * δ w + 2 * yy ij * (∑ s ∈ S0, (cc s : ℝ) * vq w s)) ≤
      (∑ b, ∑ x ∈ XX ij b, H x) + K := by
    intro ij
    rw [sum_mul_add_smul_five_eq_add_sums W0 lam (fun w => ∑ x ∈ XX ij (ch w), |vx w x|)
      (fun w => ∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) (fun w => ((ell w : ℝ) ^ 2)⁻¹)
      δ (fun w => ∑ s ∈ S0, (cc s : ℝ) * vq w s) 5 (dd ij) 6 (2 * yy ij)]
    have e1 := hT1 ij
    have e2 := hT2 ij
    have e3 : (dd ij : ℝ) * ∑ w ∈ W0, lam w * ((ell w : ℝ) ^ 2)⁻¹ ≤ 2 * N := by
      have h1 : (dd ij : ℝ) ≤ 2 * N := by exact_mod_cast hddN ij
      calc (dd ij : ℝ) * ∑ w ∈ W0, lam w * ((ell w : ℝ) ^ 2)⁻¹ ≤ (dd ij : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hT3 (by positivity)
        _ ≤ 2 * N := by linarith
    have e5 : 2 * (yy ij : ℝ) * ∑ w ∈ W0, lam w * (∑ s ∈ S0, (cc s : ℝ) * vq w s) ≤
        2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) := by
      have h1 : (yy ij : ℝ) ≤ m := by exact_mod_cast hyy ij
      have h2 : 0 ≤ (yy ij : ℝ) := by positivity
      calc 2 * (yy ij : ℝ) * ∑ w ∈ W0, lam w * (∑ s ∈ S0, (cc s : ℝ) * vq w s)
          ≤ 2 * (yy ij : ℝ) * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) :=
            mul_le_mul_of_nonneg_left hT5 (by positivity)
        _ ≤ 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) :=
            mul_le_mul_of_nonneg_right (by linarith) hSnn
    rw [hK]
    linarith
  calc ∑ w ∈ W0, lam w * ∑ ij, vr w ij
      ≤ ∑ w ∈ W0, lam w * ∑ ij, ((∑ x ∈ XX ij (ch w), |vx w x|) +
        5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) + dd ij * ((ell w : ℝ) ^ 2)⁻¹ +
        6 * δ w + 2 * yy ij * (∑ s ∈ S0, (cc s : ℝ) * vq w s)) :=
        Finset.sum_le_sum fun w hw =>
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ij _ => hvr w hw ij) (hlam w)
    _ = ∑ ij, ∑ w ∈ W0, lam w * ((∑ x ∈ XX ij (ch w), |vx w x|) +
        5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) + dd ij * ((ell w : ℝ) ^ 2)⁻¹ +
        6 * δ w + 2 * yy ij * (∑ s ∈ S0, (cc s : ℝ) * vq w s)) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ ij : Fin m × Fin m, ((∑ b, ∑ x ∈ XX ij b, H x) + K) := Finset.sum_le_sum fun ij _ => hper ij
    _ = (∑ ij, ∑ b, ∑ x ∈ XX ij b, H x) + (m : ℝ) ^ 2 * K := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_prod, Fintype.card_fin]
        push_cast
        ring
    _ ≤ (∑ ij, ∑ b, ∑ x ∈ XX ij b, H x) +
        (m : ℝ) ^ 2 * (10 * N * BN + 2 * N + 6 * Bδ + 4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) := by
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm
          simp
        · have hBN : 0 ≤ BN := hBN0 (⟨0, hm⟩, ⟨0, hm⟩)
          have h1 : K ≤ 10 * N * BN + 2 * N + 6 * Bδ +
              4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) := by
            rw [hK]
            have : 0 ≤ (N : ℝ) * BN := mul_nonneg (by positivity) hBN
            have : 0 ≤ (m : ℝ) * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) :=
              mul_nonneg (by positivity) hSnn
            nlinarith
          have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)
          linarith

end Formalism.ValuationGridEstimates
