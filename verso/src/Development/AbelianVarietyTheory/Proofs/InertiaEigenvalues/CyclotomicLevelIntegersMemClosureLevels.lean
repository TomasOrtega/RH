import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersEqSumZetaPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersLevelOneEqSumZetaPowStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.Cyc.LevelGen

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_succ', pow_mul, ← add_assoc]`.

Use `_ = ζ j := by rw [h, ih]`.
-/
theorem chain_pow {l : ℕ} {M : Type} [Monoid M] (ζ : ℕ → M) (h : ∀ j, ζ (j + 1) ^ l = ζ j)
    (j k : ℕ) : ζ (j + k) ^ (l ^ k) = ζ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc ζ (j + (k + 1)) ^ (l ^ (k + 1)) = (ζ (j + k + 1) ^ l) ^ (l ^ k) := by
          rw [pow_succ', pow_mul, ← add_assoc]
      _ = ζ j := by rw [h, ih]

/- English proof (translation)
Establish `hfin : ζ (j + 1) ^ l ^ (j + 1) = 1`. Use `chain_pow ζ h 0 (j + 1)` as an intermediate fact. Rewrite `this` using `[zero_add]`. Rewrite using `[this, h0]`. Establish `hnot : ¬ ζ (j + 1) ^ l ^ j = 1`.

Use `chain_pow ζ h 1 j` as an intermediate fact. Rewrite `this` using `[add_comm 1 j]`. Rewrite using `[this]`. Conclude with `h1`. Rewrite using `[← orderOf_eq_prime_pow hnot hfin]`.

Conclude with `IsPrimitiveRoot.orderOf _`.
-/
theorem chain_primitive {l : ℕ} [Fact l.Prime] {M : Type} [CommMonoid M] (ζ : ℕ → M)
    (h0 : ζ 0 = 1) (h1 : ζ 1 ≠ 1) (h : ∀ j, ζ (j + 1) ^ l = ζ j) (j : ℕ) :
    IsPrimitiveRoot (ζ (j + 1)) (l ^ (j + 1)) := by
  have hfin : ζ (j + 1) ^ l ^ (j + 1) = 1 := by
    have := chain_pow ζ h 0 (j + 1)
    rw [zero_add] at this
    rw [this, h0]
  have hnot : ¬ ζ (j + 1) ^ l ^ j = 1 := by
    have := chain_pow ζ h 1 j
    rw [add_comm 1 j] at this
    rw [this]
    exact h1
  rw [← orderOf_eq_prime_pow hnot hfin]
  exact IsPrimitiveRoot.orderOf _

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero`. Introduce `α hα hn`. Establish `hp : IsPrimitiveRoot (ζ (0 + 1)) l`. Simplify using `using chain_primitive ζ h0 h1 h 0`.

Take `⟨y, hy, rfl⟩` from `GlobalTheory.T.exists_integral_eq_sum_zeta_pow_level_one l K (ζ (0 + 1)) hp α hα hn`. Use `AddSubgroup.sum_mem _ (fun a _ => AddSubgroup.subset_closure ?_)` and prove the remaining obligations. Conclude with `⟨a, y a, (hy a).1, (hy a).2, mul_comm _ _⟩`. Consider the case `succ s ih`. Introduce `α hα hn`.

Establish `hp : IsPrimitiveRoot (ζ (s + 1 + 1)) (l ^ (s + 1 + 1))` using `chain_primitive ζ h0 h1 h (s + 1)`. Establish `hα' : α ∈ Ks K (s + 1 + 1)` using `hα`. Take `⟨y, hy, rfl⟩` from `(GlobalTheory.Cyc.integers_eq_sum_zeta_pow l K (s + 1 + 1) (by omega) (ζ (s + 1 + 1)) hp).1 α hα' hn`. Use `AddSubgroup.sum_mem _ (fun a _ => ?_)` and prove the remaining obligations. Establish `hya : y a ∈ Ks K (s + 1)` using `by simpa using (hy a).1`.

Establish `hmem` using `ih (y a) hya (hy a).2`. Establish `hle : AddSubgroup.closure {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (s + 1) ^ n} ≤ (AddSubgroup.closure {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (s + 1 + 1) ^ n}).comap (AddMonoidHom.mulLeft (ζ (s + 1 + 1) ^ (a : ℕ)))`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `x ⟨n, c, hc, hcn, rfl⟩`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises.

Use `⟨(a : ℕ) + l * n, c, hc, hcn, ?_⟩` and prove the remaining obligations. Simplify using `only [AddMonoidHom.coe_mulLeft]`. Rewrite using `[← h (s + 1), pow_add, pow_mul]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `hle hmem`.
-/
theorem mem_closure_all (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : ℕ → Om l) (h0 : ζ 0 = 1)
    (h1 : ζ 1 ≠ 1) (h : ∀ j, ζ (j + 1) ^ l = ζ j) (s : ℕ) :
    ∀ α : Om l, α ∈ Ks K (s + 1) → ‖α‖ ≤ 1 → α ∈ AddSubgroup.closure
      {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (s + 1) ^ n} := by
  induction s with
  | zero =>
    intro α hα hn
    have hp : IsPrimitiveRoot (ζ (0 + 1)) l := by
      simpa using chain_primitive ζ h0 h1 h 0
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.T.exists_integral_eq_sum_zeta_pow_level_one l K (ζ (0 + 1)) hp α hα hn
    refine AddSubgroup.sum_mem _ (fun a _ => AddSubgroup.subset_closure ?_)
    exact ⟨a, y a, (hy a).1, (hy a).2, mul_comm _ _⟩
  | succ s ih =>
    intro α hα hn
    have hp : IsPrimitiveRoot (ζ (s + 1 + 1)) (l ^ (s + 1 + 1)) := chain_primitive ζ h0 h1 h (s + 1)
    have hα' : α ∈ Ks K (s + 1 + 1) := hα
    obtain ⟨y, hy, rfl⟩ := (GlobalTheory.Cyc.integers_eq_sum_zeta_pow l K (s + 1 + 1) (by omega)
      (ζ (s + 1 + 1)) hp).1 α hα' hn
    refine AddSubgroup.sum_mem _ (fun a _ => ?_)
    have hya : y a ∈ Ks K (s + 1) := by simpa using (hy a).1
    have hmem := ih (y a) hya (hy a).2
    have hle : AddSubgroup.closure
        {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (s + 1) ^ n} ≤
        (AddSubgroup.closure
          {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (s + 1 + 1) ^ n}).comap
          (AddMonoidHom.mulLeft (ζ (s + 1 + 1) ^ (a : ℕ))) := by
      rw [AddSubgroup.closure_le]
      rintro x ⟨n, c, hc, hcn, rfl⟩
      apply AddSubgroup.subset_closure
      refine ⟨(a : ℕ) + l * n, c, hc, hcn, ?_⟩
      simp only [AddMonoidHom.coe_mulLeft]
      rw [← h (s + 1), pow_add, pow_mul]
      ring
    exact hle hmem

end GlobalTheory.Cyc.LevelGen

open GlobalTheory.Cyc.LevelGen in

/- English proof (translation)
Introduce `l _ K ζ h0 h1 h s hs α hα hn`. Use `set S : AddSubgroup (Om l) := AddSubgroup.closure {x : Om l | ∃ (j n : ℕ) (c : Om l), 1 ≤ j ∧ j ≤ s ∧ ¬ l ∣ n ∧ c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ j ^ n} with hS`. Establish `hl : 1 < l` using `(Fact.out : l.Prime).one_lt`. Establish `hconst : ∀ c : Om l, c ∈ K0 K → ‖c‖ ≤ 1 → c ∈ S`. Introduce `c hc hcn`.

Establish `hp : IsPrimitiveRoot (ζ 1) l` using `by simpa using chain_primitive ζ h0 h1 h 0`. Establish `hsum` using `hp.geom_sum_eq_zero hl`. Take `⟨m, hm⟩ : ∃ m, l = m + 1` from `⟨l - 1, by omega⟩`. Establish `hr : Finset.range l = Finset.range (m + 1)` using `by rw [hm]`. Rewrite `hsum` using `[hr, Finset.sum_range_succ', pow_zero]`.

Establish `hc' : c = ∑ i ∈ Finset.range m, (-c) * ζ 1 ^ (i + 1)`. Rewrite using `[← Finset.mul_sum, eq_neg_of_add_eq_zero_left hsum]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc']`. Use `AddSubgroup.sum_mem _ (fun i hi => AddSubgroup.subset_closure ?_)` and prove the remaining obligations.

Establish `hi'` using `Finset.mem_range.1 hi`. Use `⟨1, i + 1, -c, le_rfl, hs, ?_, neg_mem hc, by rwa [norm_neg], rfl⟩` and prove the remaining obligations. Introduce `hdvd`. Use `Nat.le_of_dvd (by omega) hdvd` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hlev : ∀ j, j ≤ s → ∀ (n : ℕ) (c : Om l), c ∈ K0 K → ‖c‖ ≤ 1 → c * ζ j ^ n ∈ S`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_ n c hc hcn`.

Rewrite using `[h0, one_pow, mul_one]`. Conclude with `hconst c hc hcn`. Consider the case `succ j ih`. Introduce `hj n c hc hcn`. Distinguish the cases in `hd : l ∣ n`.

Take `⟨m, rfl⟩` from `hd`. Rewrite using `[pow_mul, h j]`. Conclude with `ih (by omega) m c hc hcn`. Conclude with `AddSubgroup.subset_closure ⟨j + 1, n, c, by omega, hj, hd, hc, hcn, rfl⟩`. Take `⟨t, rfl⟩ : ∃ t, s = t + 1` from `⟨s - 1, by omega⟩`.

Establish `hmem` using `mem_closure_all l K ζ h0 h1 h t α hα hn`. Establish `hle : AddSubgroup.closure {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (t + 1) ^ n} ≤ S`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `x ⟨n, c, hc, hcn, rfl⟩`. Conclude with `hlev (t + 1) le_rfl n c hc hcn`.

Conclude with `hle hmem`.
-/
theorem GlobalTheory.Cyc.integers_mem_closure_levels : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : ℕ → Om l), ζ 0 = 1 → ζ 1 ≠ 1 → (∀ j, ζ (j + 1) ^ l = ζ j) → ∀ s : ℕ, 1 ≤ s → ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → α ∈ AddSubgroup.closure {x : Om l | ∃ (j n : ℕ) (c : Om l), 1 ≤ j ∧ j ≤ s ∧ ¬ l ∣ n ∧ c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ j ^ n} := by
  intro l _ K ζ h0 h1 h s hs α hα hn
  set S : AddSubgroup (Om l) := AddSubgroup.closure
    {x : Om l | ∃ (j n : ℕ) (c : Om l), 1 ≤ j ∧ j ≤ s ∧ ¬ l ∣ n ∧ c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧
      x = c * ζ j ^ n} with hS
  have hl : 1 < l := (Fact.out : l.Prime).one_lt

  have hconst : ∀ c : Om l, c ∈ K0 K → ‖c‖ ≤ 1 → c ∈ S := by
    intro c hc hcn
    have hp : IsPrimitiveRoot (ζ 1) l := by simpa using chain_primitive ζ h0 h1 h 0
    have hsum := hp.geom_sum_eq_zero hl
    obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    have hr : Finset.range l = Finset.range (m + 1) := by rw [hm]
    rw [hr, Finset.sum_range_succ', pow_zero] at hsum
    have hc' : c = ∑ i ∈ Finset.range m, (-c) * ζ 1 ^ (i + 1) := by
      rw [← Finset.mul_sum, eq_neg_of_add_eq_zero_left hsum]
      ring
    rw [hc']
    refine AddSubgroup.sum_mem _ (fun i hi => AddSubgroup.subset_closure ?_)
    have hi' := Finset.mem_range.1 hi
    refine ⟨1, i + 1, -c, le_rfl, hs, ?_, neg_mem hc, by rwa [norm_neg], rfl⟩
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hlev : ∀ j, j ≤ s → ∀ (n : ℕ) (c : Om l), c ∈ K0 K → ‖c‖ ≤ 1 → c * ζ j ^ n ∈ S := by
    intro j
    induction j with
    | zero =>
      intro _ n c hc hcn
      rw [h0, one_pow, mul_one]
      exact hconst c hc hcn
    | succ j ih =>
      intro hj n c hc hcn
      by_cases hd : l ∣ n
      · obtain ⟨m, rfl⟩ := hd
        rw [pow_mul, h j]
        exact ih (by omega) m c hc hcn
      · exact AddSubgroup.subset_closure ⟨j + 1, n, c, by omega, hj, hd, hc, hcn, rfl⟩
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hmem := mem_closure_all l K ζ h0 h1 h t α hα hn
  have hle : AddSubgroup.closure
      {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (t + 1) ^ n} ≤ S := by
    rw [AddSubgroup.closure_le]
    rintro x ⟨n, c, hc, hcn, rfl⟩
    exact hlev (t + 1) le_rfl n c hc hcn
  exact hle hmem
