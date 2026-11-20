import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Polynomial

/- English proof (translation)
Establish `hinj : Set.InjOn (fun j : ℤ => j₀ - j) (T : Set ℤ)`. Introduce `x _ y _ h`. Simplify using `only at h`. Use linear arithmetic over natural numbers and integers. Establish `hre : ∑ j ∈ T, padicValInt ℓ (j₀ - j) = ∑ i ∈ T.image (fun j : ℤ => j₀ - j), padicValInt ℓ i` using `(Finset.sum_image hinj).symm`.

Rewrite using `[hre]`. Apply `Formalism.WindowSums.arc_WindowSum ℓ lo L D` to reduce the goal to its premises. Introduce `i hi`. Take `⟨j, hj, rfl⟩` from `Finset.mem_image.1 hi`. Use `hT j hj` as an intermediate fact.

Rewrite using `[Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Introduce `hi`. Take `⟨j, hj, hj0⟩` from `Finset.mem_image.1 hi`. Establish `: j = j₀` using `by omega`.

Conclude with `h0 (this ▸ hj)`. Introduce `i hi`. Take `⟨j, hj, rfl⟩` from `Finset.mem_image.1 hi`. Conclude with `hD j hj`.
-/
private theorem winDiff (ℓ : ℕ) [Fact ℓ.Prime] (j₀ lo : ℤ) (L D : ℕ) (T : Finset ℤ)
    (hT : ∀ j ∈ T, lo ≤ j₀ - j ∧ j₀ - j < lo + L) (h0 : j₀ ∉ T)
    (hD : ∀ j ∈ T, |j₀ - j| ≤ (D : ℤ)) :
    ((∑ j ∈ T, padicValInt ℓ (j₀ - j) : ℕ) : ℝ) ≤
      (L : ℝ) / ((ℓ : ℝ) - 1) + Real.logb (ℓ : ℝ) (D : ℝ) := by
  have hinj : Set.InjOn (fun j : ℤ => j₀ - j) (T : Set ℤ) := by
    intro x _ y _ h
    simp only at h
    omega
  have hre : ∑ j ∈ T, padicValInt ℓ (j₀ - j) =
      ∑ i ∈ T.image (fun j : ℤ => j₀ - j), padicValInt ℓ i :=
    (Finset.sum_image hinj).symm
  rw [hre]
  apply Formalism.WindowSums.arc_WindowSum ℓ lo L D
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    have := hT j hj
    rw [Finset.mem_Ico]
    omega
  · intro hi
    obtain ⟨j, hj, hj0⟩ := Finset.mem_image.1 hi
    have : j = j₀ := by omega
    exact h0 (this ▸ hj)
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    exact hD j hj

/- English proof (translation)
Introduce `ℓ _ R _ _ c hc h η S b a S₂ hb hbS hS₂`. Establish `hℓ2 : (2 : ℝ) ≤ (ℓ : ℝ)` using `by exact_mod_cast (Fact.out : ℓ.Prime).two_le`. Use `set S₁ := Finset.Icc ((b : ℤ) - a + 1) (b : ℤ) with hS₁def`. Establish `m2 : ∀ r ∈ S₂, ((b : ℤ) + 1 ≤ r ∧ r ≤ b + S + a) ∨ (1 - (η : ℤ) ≤ r ∧ r ≤ η + a)`. Introduce `r hr`.

Simplify `hS₂ hr` using `only [Finset.mem_union, Finset.mem_Icc]`. Establish `hdisj : Disjoint S₁ S₂`. Rewrite using `[Finset.disjoint_left]`. Introduce `r hr1 hr2`. Rewrite `hr1` using `[hS₁def, Finset.mem_Icc]`.

Use `m2 r hr2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hlag` using `Formalism.LIFT.lift_LagrangeIdealInt ℓ R S₁ S₂ c hdisj (fun x _ y _ hxy => hc x y hxy)`. Use `⟨S₁.sup fun j₀ => (∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) + ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j), ?_, hlag⟩` and prove the remaining obligations. Establish `hH1 : (1 : ℝ) ≤ ((h + η : ℕ) : ℝ)`.

Establish `: 1 ≤ h + η` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hlog : Real.logb (ℓ : ℝ) ((h + η : ℕ) : ℝ) ≤ lam ℓ (h + η)`. Unfold `lam`. Use `Real.logb_le_logb_of_le (b := (ℓ : ℝ)) (by linarith) (by linarith) (show ((h + η : ℕ) : ℝ) ≤ 2 * ((h + η : ℕ) : ℝ) by linarith)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlam0 : 0 ≤ lam ℓ (h + η)`. Unfold `lam`. Use `Real.logb_nonneg (b := (ℓ : ℝ)) (by linarith) (show (1 : ℝ) ≤ 2 * ((h + η : ℕ) : ℝ) by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hden : 0 < (ℓ : ℝ) - 1` using `by linarith`. Establish `key : ∀ j₀ ∈ S₁, ((((∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) + ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j) : ℕ)) : ℝ) ≤ (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) + 3 * lam ℓ (h + η)`. Introduce `j₀ hj₀`. Rewrite `hj₀` using `[hS₁def, Finset.mem_Icc]`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not S₂ (fun j => (b : ℤ) + 1 ≤ j)]`.

Use `push_cast`. Establish `w1` using `winDiff ℓ j₀ (j₀ - b) a (h + η) (S₁.erase j₀) (by`. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_erase, hS₁def, Finset.mem_Icc]`. Use the proof step `omega)`.

Use the proof step `(by simp)`. Use the proof step `(by`. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_erase, hS₁def, Finset.mem_Icc]`. Rewrite using `[abs_le]`.

Use `push_cast`. Apply the tactic sequence `constructor <;> omega)`. Establish `w2` using `winDiff ℓ j₀ (j₀ - b - S - a) (S + a) (h + η) (S₂.filter (fun j => (b : ℤ) + 1 ≤ j)) (by`. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_filter]`.

Use `m2 j hj.1` as an intermediate fact. Use `push_cast`. Use the proof step `omega)`. Use the proof step `(by`. Rewrite using `[Finset.mem_filter]`.

Use the proof step `omega)`. Use the proof step `(by`. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_filter]`. Use `m2 j hj.1` as an intermediate fact.

Rewrite using `[abs_le]`. Use `push_cast`. Apply the tactic sequence `constructor <;> omega)`. Establish `w3` using `winDiff ℓ j₀ (j₀ - η - a) (2 * η + a) (h + η) (S₂.filter (fun j => ¬ (b : ℤ) + 1 ≤ j)) (by`. Introduce `j hj`.

Rewrite `hj` using `[Finset.mem_filter]`. Use `m2 j hj.1` as an intermediate fact. Use `push_cast`. Use the proof step `omega)`. Use the proof step `(by`.

Rewrite using `[Finset.mem_filter]`. Introduce `hh`. Use `m2 j₀ hh.1` as an intermediate fact. Use the proof step `omega)`. Use the proof step `(by`.

Introduce `j hj`. Rewrite `hj` using `[Finset.mem_filter]`. Use `m2 j hj.1` as an intermediate fact. Rewrite using `[abs_le]`. Use `push_cast`.

Apply the tactic sequence `constructor <;> omega)`. Move the coercions through the operations in `at w1 w2 w3`. Establish `hsum : (a : ℝ) / ((ℓ : ℝ) - 1) + ((S : ℝ) + (a : ℝ)) / ((ℓ : ℝ) - 1) + (2 * (η : ℝ) + (a : ℝ)) / ((ℓ : ℝ) - 1) = (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1)` using `by ring`. Move the coercions through the operations in `at hlog`. Combine the linear equalities and inequalities to obtain the conclusion.

Break down `S₁.eq_empty_or_nonempty with he | hne` into its components or cases. Rewrite using `[he, Finset.sup_empty]`. Simplify using `only [Nat.bot_eq_zero, Nat.cast_zero]`. Establish `: 0 ≤ (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨j, hj, hjeq⟩` from `Finset.exists_mem_eq_sup S₁ hne (fun j₀ => (∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) + ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j))`. Rewrite using `[hjeq]`. Conclude with `key j hj`.
-/
theorem g_ideal_valuation_statement : LemmaGIdeal := by
  intro ℓ _ R _ _ c hc h η S b a S₂ hb hbS hS₂
  have hℓ2 : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (Fact.out : ℓ.Prime).two_le
  set S₁ := Finset.Icc ((b : ℤ) - a + 1) (b : ℤ) with hS₁def
  have m2 : ∀ r ∈ S₂, ((b : ℤ) + 1 ≤ r ∧ r ≤ b + S + a) ∨ (1 - (η : ℤ) ≤ r ∧ r ≤ η + a) := by
    intro r hr
    simpa only [Finset.mem_union, Finset.mem_Icc] using hS₂ hr
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    rw [hS₁def, Finset.mem_Icc] at hr1
    have := m2 r hr2
    omega
  have hlag := Formalism.LIFT.lift_LagrangeIdealInt ℓ R S₁ S₂ c hdisj
    (fun x _ y _ hxy => hc x y hxy)
  refine ⟨S₁.sup fun j₀ => (∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) +
      ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j), ?_, hlag⟩

  have hH1 : (1 : ℝ) ≤ ((h + η : ℕ) : ℝ) := by
    have : 1 ≤ h + η := by omega
    exact_mod_cast this
  have hlog : Real.logb (ℓ : ℝ) ((h + η : ℕ) : ℝ) ≤ lam ℓ (h + η) := by
    unfold lam
    have := Real.logb_le_logb_of_le (b := (ℓ : ℝ)) (by linarith) (by linarith)
      (show ((h + η : ℕ) : ℝ) ≤ 2 * ((h + η : ℕ) : ℝ) by linarith)
    linarith
  have hlam0 : 0 ≤ lam ℓ (h + η) := by
    unfold lam
    have := Real.logb_nonneg (b := (ℓ : ℝ)) (by linarith)
      (show (1 : ℝ) ≤ 2 * ((h + η : ℕ) : ℝ) by linarith)
    linarith
  have hden : 0 < (ℓ : ℝ) - 1 := by linarith
  have key : ∀ j₀ ∈ S₁, ((((∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) +
      ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j) : ℕ)) : ℝ) ≤
      (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) + 3 * lam ℓ (h + η) := by
    intro j₀ hj₀
    rw [hS₁def, Finset.mem_Icc] at hj₀
    rw [← Finset.sum_filter_add_sum_filter_not S₂ (fun j => (b : ℤ) + 1 ≤ j)]
    push_cast
    have w1 := winDiff ℓ j₀ (j₀ - b) a (h + η) (S₁.erase j₀)
      (by
        intro j hj
        rw [Finset.mem_erase, hS₁def, Finset.mem_Icc] at hj
        omega)
      (by simp)
      (by
        intro j hj
        rw [Finset.mem_erase, hS₁def, Finset.mem_Icc] at hj
        rw [abs_le]
        push_cast
        constructor <;> omega)
    have w2 := winDiff ℓ j₀ (j₀ - b - S - a) (S + a) (h + η)
      (S₂.filter (fun j => (b : ℤ) + 1 ≤ j))
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        push_cast
        omega)
      (by
        rw [Finset.mem_filter]
        omega)
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        rw [abs_le]
        push_cast
        constructor <;> omega)
    have w3 := winDiff ℓ j₀ (j₀ - η - a) (2 * η + a) (h + η)
      (S₂.filter (fun j => ¬ (b : ℤ) + 1 ≤ j))
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        push_cast
        omega)
      (by
        rw [Finset.mem_filter]
        intro hh
        have := m2 j₀ hh.1
        omega)
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        rw [abs_le]
        push_cast
        constructor <;> omega)
    push_cast at w1 w2 w3
    have hsum : (a : ℝ) / ((ℓ : ℝ) - 1) + ((S : ℝ) + (a : ℝ)) / ((ℓ : ℝ) - 1) +
        (2 * (η : ℝ) + (a : ℝ)) / ((ℓ : ℝ) - 1) =
        (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) := by ring
    push_cast at hlog
    linarith
  rcases S₁.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sup_empty]
    simp only [Nat.bot_eq_zero, Nat.cast_zero]
    have : 0 ≤ (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) := by positivity
    linarith
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup S₁ hne
      (fun j₀ => (∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) + ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j))
    rw [hjeq]
    exact key j hj

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
