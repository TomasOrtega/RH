import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.FinSupp

section
variable {K : Type} [CommRing K]

def Bd (M : ℕ) (F : K⟦X⟧⟦X⟧) : Prop := ∀ i n, M < i ∨ M < n → coeff n (coeff i F) = 0

/- English proof (translation)
Introduce `i n hin` and use `h i n (by omega)`.
-/
theorem Bd.mono {M M' : ℕ} {F : K⟦X⟧⟦X⟧} (h : Bd M F) (hM : M ≤ M') : Bd M' F :=
  fun i n hin => h i n (by omega)

/- English proof (translation)
Introduce `i n hin`. Rewrite using `[coeff_mul, map_sum]`. Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations. Rewrite using `[coeff_mul]`. Use `Finset.sum_eq_zero fun q hq => ?_` and prove the remaining obligations.

Rewrite `hp`, `hq` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Distinguish the cases in `h1 : M < p.1 ∨ M < q.1`. Rewrite using `[h _ _ h1, zero_mul]`. Rewrite using `[h' _ _ (by omega), mul_zero]`.
-/
theorem Bd.mul {M M' : ℕ} {F G : K⟦X⟧⟦X⟧} (h : Bd M F) (h' : Bd M' G) : Bd (M + M') (F * G) := by
  intro i n hin
  rw [coeff_mul, map_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hq
  by_cases h1 : M < p.1 ∨ M < q.1
  · rw [h _ _ h1, zero_mul]
  · rw [h' _ _ (by omega), mul_zero]

/- English proof (translation)
Introduce `i n hin`. Rewrite using `[coeff_C]`. Use `split_ifs with h`. Rewrite using `[coeff_C, if_neg (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem bd_CC (c : K) : Bd 0 (C (C c) : K⟦X⟧⟦X⟧) := by
  intro i n hin
  rw [coeff_C]
  split_ifs with h
  · rw [coeff_C, if_neg (by omega)]
  · simp

/- English proof (translation)
Introduce `i n hin`. Rewrite using `[coeff_C]`. Use `split_ifs with h`. Rewrite using `[coeff_X, if_neg (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem bd_CX : Bd 1 (C X : K⟦X⟧⟦X⟧) := by
  intro i n hin
  rw [coeff_C]
  split_ifs with h
  · rw [coeff_X, if_neg (by omega)]
  · simp

/- English proof (translation)
Introduce `i n hin`. Rewrite using `[coeff_X]`. Use `split_ifs with h`. Rewrite using `[coeff_one, if_neg (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem bd_X : Bd 1 (X : K⟦X⟧⟦X⟧) := by
  intro i n hin
  rw [coeff_X]
  split_ifs with h
  · rw [coeff_one, if_neg (by omega)]
  · simp

variable (K) in

def fin : Subring K⟦X⟧⟦X⟧ where
  carrier := {F | ∃ M, Bd M F}
  mul_mem' := by
    rintro F G ⟨M, h⟩ ⟨M', h'⟩
    exact ⟨_, h.mul h'⟩
  one_mem' := ⟨0, by simpa using bd_CC (1 : K)⟩
  add_mem' := by
    rintro F G ⟨M, h⟩ ⟨M', h'⟩
    exact ⟨M + M', fun i n hin => by
      rw [map_add, map_add, h i n (by omega), h' i n (by omega), add_zero]⟩
  zero_mem' := ⟨0, fun i n _ => by simp⟩
  neg_mem' := by
    rintro F ⟨M, h⟩
    exact ⟨M, fun i n hin => by rw [map_neg, map_neg, h i n hin, neg_zero]⟩

/- English proof (translation)
Use extensionality with `i n`. Simplify using `only [map_sum (coeff i), coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]`. Use `split_ifs with hi`. Simplify using `only [map_sum (coeff n), coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range] split_ifs with hn`. Both sides reduce to the same expression.

Conclude with `h i n (by omega)`. Rewrite using `[h i n (by omega), map_zero]`.
-/
theorem Bd.eq_sum {M : ℕ} {F : K⟦X⟧⟦X⟧} (h : Bd M F) :
    F = ∑ i ∈ Finset.range (M + 1), C (∑ n ∈ Finset.range (M + 1),
      C (coeff n (coeff i F)) * X ^ n) * X ^ i := by
  ext i n
  simp only [map_sum (coeff i), coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with hi
  · simp only [map_sum (coeff n), coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hn
    · rfl
    · exact h i n (by omega)
  · rw [h i n (by omega), map_zero]

/- English proof (translation)
Take `⟨M, h⟩` from `hF`. Rewrite using `[h.eq_sum]`. Simplify using `only [map_sum, map_mul, map_pow]`. Use `sum_mem fun i _ => mul_mem (sum_mem fun n _ => mul_mem (h1 _) (pow_mem h2 _)) (pow_mem h3 _)` and prove the remaining obligations.
-/
theorem map_mem (φ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧) (h1 : ∀ c : K, φ (C (C c)) ∈ fin K)
    (h2 : φ (C X) ∈ fin K) (h3 : φ X ∈ fin K) {F : K⟦X⟧⟦X⟧} (hF : F ∈ fin K) : φ F ∈ fin K := by
  obtain ⟨M, h⟩ := hF
  rw [h.eq_sum]
  simp only [map_sum, map_mul, map_pow]
  refine sum_mem fun i _ => mul_mem (sum_mem fun n _ => mul_mem (h1 _) (pow_mem h2 _)) (pow_mem h3 _)

/- English proof (translation)
Use `choose M hM using h`. Take `⟨B, hB⟩` from `(Set.finite_range M).bddAbove`. Conclude with `⟨B, fun τ => (hM τ).mono (hB ⟨τ, rfl⟩)⟩`.
-/
theorem unif {ι : Type} [Finite ι] (F : ι → K⟦X⟧⟦X⟧) (h : ∀ τ, F τ ∈ fin K) : ∃ M, ∀ τ, Bd M (F τ) := by
  choose M hM using h
  obtain ⟨B, hB⟩ := (Set.finite_range M).bddAbove
  exact ⟨B, fun τ => (hM τ).mono (hB ⟨τ, rfl⟩)⟩

end

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC hX N w hw`. Establish `hF : ∀ τ, ofW t K e w τ ∈ fin K` using `fun τ => ⟨N, fun i n hin => by`. Rewrite using `[coeff_ofW, hw i n hin]`. Use the proof step `simp⟩`. Establish `hCX : (C X : K⟦X⟧⟦X⟧) ∈ fin K` using `⟨_, bd_CX⟩`.

Establish `hX' : (X : K⟦X⟧⟦X⟧) ∈ fin K` using `⟨_, bd_X⟩`. Take `⟨M, hM⟩` from `unif (frob2 φ₂ (ofW t K e w)) fun τ => by`. Express the relevant statement in the definitionally equal form `φ₂ (ofW t K e w (τ - 1)) ∈ _`. Use `map_mem φ₂ (fun c => ?_) ?_ ?_ (hF _)` and prove the remaining obligations. Establish `: frob K l (C c) = C c` using `(frob K l).commutes c`.

Rewrite using `[hC, this]`. Conclude with `⟨_, bd_CC c⟩`. Rewrite using `[hC, frob_X, map_pow]`. Conclude with `pow_mem hCX _`. Rewrite using `[hX, map_pow]`.

Conclude with `sub_mem (pow_mem (add_mem hCX hX') _) (pow_mem hCX _)`. Take `⟨M', hM'⟩` from `unif (ofW t K e w ^ l) fun τ => pow_mem (hF τ) l`. Conclude with `⟨M + M', fun τ i n hin => ⟨hM τ i n (by omega), hM' τ i n (by omega)⟩⟩`.
-/
theorem exists_coeff_frob2_ofW_and_pow_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) → ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n → coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0 := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC hX N w hw
  have hF : ∀ τ, ofW t K e w τ ∈ fin K := fun τ => ⟨N, fun i n hin => by
    rw [coeff_ofW, hw i n hin]; simp⟩
  have hCX : (C X : K⟦X⟧⟦X⟧) ∈ fin K := ⟨_, bd_CX⟩
  have hX' : (X : K⟦X⟧⟦X⟧) ∈ fin K := ⟨_, bd_X⟩
  obtain ⟨M, hM⟩ := unif (frob2 φ₂ (ofW t K e w)) fun τ => by
    change φ₂ (ofW t K e w (τ - 1)) ∈ _
    refine map_mem φ₂ (fun c => ?_) ?_ ?_ (hF _)
    · have : frob K l (C c) = C c := (frob K l).commutes c
      rw [hC, this]; exact ⟨_, bd_CC c⟩
    · rw [hC, frob_X, map_pow]; exact pow_mem hCX _
    · rw [hX, map_pow]; exact sub_mem (pow_mem (add_mem hCX hX') _) (pow_mem hCX _)
  obtain ⟨M', hM'⟩ := unif (ofW t K e w ^ l) fun τ => pow_mem (hF τ) l
  exact ⟨M + M', fun τ i n hin => ⟨hM τ i n (by omega), hM' τ i n (by omega)⟩⟩

end GlobalTheory.CrysPrism.FinSupp
