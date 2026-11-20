import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsInSpanOfRankNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.CountTranslates
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Take `⟨l₁, -, hl₁⟩` from `Finset.exists_max_image Finset.univ (fun j => valuation k (s j)) ⟨l, Finset.mem_univ _⟩`. Establish `hM : t < valuation k (s l₁)` using `hlt.trans_le (hl₁ l (Finset.mem_univ _))`. Establish `hM0 : 0 < valuation k (s l₁)` using `lt_of_le_of_lt zero_le' hM`.

Establish `h1 : valuation k ((s ᵥ* E) l₁) ≤ valuation k (s l₁) * u`. Simplify using `only [Matrix.vecMul, dotProduct]`. Use `Valuation.map_sum_le _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_mul' (hl₁ j (Finset.mem_univ _)) (hE j l₁)`.

Establish `h3` using `Valuation.map_sub_le (valuation k) ((hw l₁).trans (le_max_left t (valuation k (s l₁) * u))) (h1.trans (le_max_right _ _))`. Rewrite `h3` using `[Pi.add_apply, add_sub_cancel_right]`. Establish `h4 : valuation k (s l₁) * u < valuation k (s l₁)` using `mul_lt_of_lt_one_right hM0 hu`. Break down `le_max_iff.1 h3 with h | h` into its components or cases. Conclude with `absurd h (not_le.2 hM)`.

Conclude with `absurd h (not_le.2 h4)`.
-/
theorem val_le_of_add_vecMul {r : ℕ} {u t : ValueGroupWithZero k} (hu : u < 1) (s : Fin r → k)
    (E : Matrix (Fin r) (Fin r) k) (hE : ∀ l j, valuation k (E l j) ≤ u)
    (hw : ∀ l, valuation k ((s + s ᵥ* E) l) ≤ t) (l : Fin r) : valuation k (s l) ≤ t := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨l₁, -, hl₁⟩ := Finset.exists_max_image Finset.univ (fun j => valuation k (s j)) ⟨l, Finset.mem_univ _⟩
  have hM : t < valuation k (s l₁) := hlt.trans_le (hl₁ l (Finset.mem_univ _))
  have hM0 : 0 < valuation k (s l₁) := lt_of_le_of_lt zero_le' hM
  have h1 : valuation k ((s ᵥ* E) l₁) ≤ valuation k (s l₁) * u := by
    simp only [Matrix.vecMul, dotProduct]
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hl₁ j (Finset.mem_univ _)) (hE j l₁)
  have h3 := Valuation.map_sub_le (valuation k) ((hw l₁).trans (le_max_left t (valuation k (s l₁) * u)))
    (h1.trans (le_max_right _ _))
  rw [Pi.add_apply, add_sub_cancel_right] at h3
  have h4 : valuation k (s l₁) * u < valuation k (s l₁) := mul_lt_of_lt_one_right hM0 hu
  rcases le_max_iff.1 h3 with h | h
  · exact absurd h (not_le.2 hM)
  · exact absurd h (not_le.2 h4)

/- English proof (translation)
Simplify using `[Units.val_pow_eq_pow_val, map_pow]`.
-/
theorem val_pow (ϖ : kˣ) (n : ℕ) : valuation k ((ϖ ^ n : kˣ) : k) = valuation k (ϖ : k) ^ n := by
  simp [Units.val_pow_eq_pow_val, map_pow]

/- English proof (translation)
Rewrite using `[pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton, ← (Valuation.integer.integers (valuation k)).le_iff_dvd]`. Conclude with `Iff.rfl`.
-/
theorem mem_max_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (x : 𝒪[k]) :
    x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ 1 ↔ valuation k (x : k) ≤ valuation k (ϖ : k) := by
  rw [pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton, ← (Valuation.integer.integers (valuation k)).le_iff_dvd]
  exact Iff.rfl

variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

omit [Fintype A] [Fintype D] [DecidableEq D] in

/- English proof (translation)
Simplify using `only [box, Set.mem_setOf_eq, val_pow]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨fun i hi j => by simpa [Function.update_of_ne hi] using h i j, fun j => by simpa [hC] using h i₀ j⟩`. Introduce and unpack `⟨h1, h2⟩ i j`.

Distinguish the cases in `hi : i = i₀`. Substitute `hi` using the available equality. Simplify `h2 j` using `[hC]`. Simplify `h1 i hi j` using `[Function.update_of_ne hi]`.
-/
theorem mem_box_update {ϖ : kˣ} {C X : Matrix A D k} {i₀ : A} {m : ℕ} (hC : ∀ j, C i₀ j = 0) :
    X ∈ box ϖ C (Function.update (fun _ => m) i₀ (m - 1)) ↔
      (∀ i, i ≠ i₀ → ∀ j, valuation k (X i j - C i j) ≤ valuation k (ϖ : k) ^ m) ∧
        ∀ j, valuation k (X i₀ j) ≤ valuation k (ϖ : k) ^ (m - 1) := by
  simp only [box, Set.mem_setOf_eq, val_pow]
  constructor
  · intro h
    exact ⟨fun i hi j => by simpa [Function.update_of_ne hi] using h i j, fun j => by simpa [hC] using h i₀ j⟩
  · rintro ⟨h1, h2⟩ i j
    by_cases hi : i = i₀
    · subst hi; simpa [hC] using h2 j
    · simpa [Function.update_of_ne hi] using h1 i hi j

omit [Fintype A] [Fintype D] [DecidableEq D] in

/- English proof (translation)
Simplify using `only [box, Set.mem_setOf_eq, val_pow]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨fun i hi j => by simpa [updateRow_ne hi] using h i j, fun j => by simpa using h i₀ j⟩`. Introduce and unpack `⟨h1, h2⟩ i j`.

Distinguish the cases in `hi : i = i₀`. Substitute `hi` using the available equality. Simplify using `using h2 j`. Simplify `h1 i hi j` using `[updateRow_ne hi]`.
-/
theorem mem_box_updateRow {ϖ : kˣ} {C X : Matrix A D k} {i₀ : A} {m : ℕ} (R : D → k) :
    X ∈ box ϖ (C.updateRow i₀ R) (fun _ => m) ↔
      (∀ i, i ≠ i₀ → ∀ j, valuation k (X i j - C i j) ≤ valuation k (ϖ : k) ^ m) ∧
        ∀ j, valuation k (X i₀ j - R j) ≤ valuation k (ϖ : k) ^ m := by
  simp only [box, Set.mem_setOf_eq, val_pow]
  constructor
  · intro h
    exact ⟨fun i hi j => by simpa [updateRow_ne hi] using h i j, fun j => by simpa using h i₀ j⟩
  · rintro ⟨h1, h2⟩ i j
    by_cases hi : i = i₀
    · subst hi; simpa using h2 j
    · simpa [updateRow_ne hi] using h1 i hi j

end GlobalTheory.CountTranslates

namespace GlobalTheory.CountTranslates
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {D : Type} [Fintype D] [DecidableEq D]

def shiftRow (ϖ : kˣ) (m : ℕ) {r : ℕ} (b : Fin r → Res k 1) : Fin r → k :=
  fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, m = c + 1 + n` from `⟨m - (c + 1), by omega⟩`. Rewrite using `[pow_add, pow_succ, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hu0)]`. Conclude with `mul_le_of_le_one_right' (pow_le_one' hu.le n)`.
-/
theorem inv_pow_mul_pow_le {u : ValueGroupWithZero k} (hu : u < 1) (hu0 : u ≠ 0) {c m : ℕ} (hcm : c + 1 ≤ m) :
    (u ^ c)⁻¹ * u ^ m ≤ u := by
  obtain ⟨n, rfl⟩ : ∃ n, m = c + 1 + n := ⟨m - (c + 1), by omega⟩
  rw [pow_add, pow_succ, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hu0)]
  exact mul_le_of_le_one_right' (pow_le_one' hu.le n)

omit [DecidableEq D] in

/- English proof (translation)
Simplify using `only [Matrix.vecMul, dotProduct, shiftRow]`. Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem val_shiftRow_le (ϖ : kˣ) {r m : ℕ} (Y : Matrix (Fin r) D k) (hY : ∀ l j, Y l j ∈ 𝒪[k])
    (b : Fin r → Res k 1) (j : D) :
    valuation k ((shiftRow ϖ m b ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ (m - 1) := by
  simp only [Matrix.vecMul, dotProduct, shiftRow]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul, map_mul, map_pow]
  calc _ ≤ valuation k (ϖ : k) ^ (m - 1) * 1 * 1 :=
        mul_le_mul' (mul_le_mul' le_rfl ((Valuation.mem_integer_iff _ _).1 (Quotient.out (b l)).2))
          ((Valuation.mem_integer_iff _ _).1 (hY l j))
    _ = _ := by rw [mul_one, mul_one]

omit [DecidableEq D] in

/- English proof (translation)
Establish `hu0 : valuation k (ϖ : k) ≠ 0` using `by simp`. Set `δ : Fin r → k` to `fun l => (ϖ : k) ^ (m - 1) * (((Quotient.out (b l) : 𝒪[k]) : k) - ((Quotient.out (b' l) : 𝒪[k]) : k))`. Establish `hδ : δ ᵥ* Y = shiftRow ϖ m b ᵥ* Y - shiftRow ϖ m b' ᵥ* Y`. Rewrite using `[← Matrix.sub_vecMul]`. Use `congr 1`.

Use function extensionality and compare the values at `l`. Simplify using `[δ, shiftRow, mul_sub]`. Establish `h1 : ∀ j, valuation k ((δ ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ m` using `fun j => by`. Use `Valuation.map_sub_le (valuation k) (hb' j) (hb j)` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_left, ← Pi.sub_apply, ← hδ]`. Then use the resulting hypothesis.

Establish `h2 : δ = (δ ᵥ* Y) ᵥ* Q` using `by rw [Matrix.vecMul_vecMul, hYQ, Matrix.vecMul_one]`. Establish `h3 : ∀ l, valuation k (δ l) ≤ valuation k (ϖ : k) ^ m` using `fun l => by`. Rewrite using `[h2]`. Use `show valuation k (∑ j, (δ ᵥ* Y) j * Q j l) ≤ _`. Use `Valuation.map_sum_le _ fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Conclude with `(mul_le_mul' (h1 j) ((Valuation.mem_integer_iff _ _).1 (hQ j l))).trans (by rw [mul_one])`. Use function extensionality and compare the values at `l`. Establish `h4 : valuation k (((Quotient.out (b l) : 𝒪[k]) : k) - ((Quotient.out (b' l) : 𝒪[k]) : k)) ≤ valuation k (ϖ : k)`. Establish `h5` using `h3 l`.

Establish `hm' : valuation k (ϖ : k) ^ m = valuation k (ϖ : k) ^ (m - 1) * valuation k (ϖ : k)`. Rewrite using `[← pow_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Simplify using `only [δ, map_mul, map_pow] at h5`.

Rewrite `h5` using `[hm']`. Conclude with `(mul_le_mul_iff_right₀ (zero_lt_iff.2 (pow_ne_zero _ hu0))).1 h5`. Rewrite using `[← Ideal.Quotient.mk_out (b l), ← Ideal.Quotient.mk_out (b' l)]`. Conclude with `Ideal.Quotient.eq.2 ((mem_max_iff hϖ _).2 h4)`.
-/
theorem shiftRow_unique {ϖ : kˣ} (hϖ : IsUnif ϖ) {r m : ℕ} (hm : 1 ≤ m) (Y : Matrix (Fin r) D k)
    (Q : Matrix D (Fin r) k) (hQ : ∀ j l, Q j l ∈ 𝒪[k]) (hYQ : Y * Q = 1) (x : D → k)
    (b b' : Fin r → Res k 1)
    (hb : ∀ j, valuation k (x j - (shiftRow ϖ m b ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ m)
    (hb' : ∀ j, valuation k (x j - (shiftRow ϖ m b' ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ m) :
    b = b' := by
  have hu0 : valuation k (ϖ : k) ≠ 0 := by simp
  let δ : Fin r → k := fun l =>
    (ϖ : k) ^ (m - 1) * (((Quotient.out (b l) : 𝒪[k]) : k) - ((Quotient.out (b' l) : 𝒪[k]) : k))
  have hδ : δ ᵥ* Y = shiftRow ϖ m b ᵥ* Y - shiftRow ϖ m b' ᵥ* Y := by
    rw [← Matrix.sub_vecMul]; congr 1; funext l; simp [δ, shiftRow, mul_sub]
  have h1 : ∀ j, valuation k ((δ ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ m := fun j => by
    have := Valuation.map_sub_le (valuation k) (hb' j) (hb j)
    rwa [sub_sub_sub_cancel_left, ← Pi.sub_apply, ← hδ] at this
  have h2 : δ = (δ ᵥ* Y) ᵥ* Q := by rw [Matrix.vecMul_vecMul, hYQ, Matrix.vecMul_one]
  have h3 : ∀ l, valuation k (δ l) ≤ valuation k (ϖ : k) ^ m := fun l => by
    rw [h2]
    show valuation k (∑ j, (δ ᵥ* Y) j * Q j l) ≤ _
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact (mul_le_mul' (h1 j) ((Valuation.mem_integer_iff _ _).1 (hQ j l))).trans (by rw [mul_one])
  funext l
  have h4 : valuation k (((Quotient.out (b l) : 𝒪[k]) : k) - ((Quotient.out (b' l) : 𝒪[k]) : k)) ≤
      valuation k (ϖ : k) := by
    have h5 := h3 l
    have hm' : valuation k (ϖ : k) ^ m = valuation k (ϖ : k) ^ (m - 1) * valuation k (ϖ : k) := by
      rw [← pow_succ]; congr 1; omega
    simp only [δ, map_mul, map_pow] at h5
    rw [hm'] at h5
    exact (mul_le_mul_iff_right₀ (zero_lt_iff.2 (pow_ne_zero _ hu0))).1 h5
  rw [← Ideal.Quotient.mk_out (b l), ← Ideal.Quotient.mk_out (b' l)]
  exact Ideal.Quotient.eq.2 ((mem_max_iff hϖ _).2 h4)

omit [DecidableEq D] in

/- English proof (translation)
Establish `hu : valuation k (ϖ : k) < 1` using `hϖ ▸ uniformizer_lt_one`. Establish `hu0 : valuation k (ϖ : k) ≠ 0` using `by simp`. Establish `hp0 : (ϖ : k) ^ (m - 1) ≠ 0` using `pow_ne_zero _ ϖ.ne_zero`. Establish `hvp : 0 < valuation k (ϖ : k) ^ (m - 1)` using `zero_lt_iff.2 (pow_ne_zero _ hu0)`. Establish `hm' : valuation k (ϖ : k) ^ m = valuation k (ϖ : k) ^ (m - 1) * valuation k (ϖ : k)`.

Rewrite using `[← pow_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `htt : ∀ l, ((ϖ : k) ^ (m - 1))⁻¹ * s l ∈ 𝒪[k]` using `fun l => by`. Rewrite using `[Valuation.mem_integer_iff, map_mul, map_inv₀, map_pow, inv_mul_le_iff₀ hvp, mul_one]`.

Conclude with `hs l`. Set `b₀ : Fin r → Res k 1` to `fun l => Ideal.Quotient.mk _ ⟨_, htt l⟩`. Establish `hb : ∀ l, valuation k (((Quotient.out (b₀ l) : 𝒪[k]) : k) - ((ϖ : k) ^ (m - 1))⁻¹ * s l) ≤ valuation k (ϖ : k)` using `fun l => (mem_max_iff hϖ _).1 (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out (b₀ l)))`. Use `⟨b₀, fun j => ?_⟩` and prove the remaining obligations. Establish `e : (s ᵥ* (Y + Z)) j - (shiftRow ϖ m b₀ ᵥ* Y) j = ((s - shiftRow ϖ m b₀) ᵥ* Y) j + (s ᵥ* Z) j`.

Rewrite using `[Matrix.vecMul_add, Matrix.sub_vecMul]`. Simplify using `only [Pi.add_apply, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `Valuation.map_add_le _ ?_ ?_` and prove the remaining obligations.

Use `show valuation k (∑ l, (s - shiftRow ϖ m b₀) l * Y l j) ≤ _`. Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations. Establish `e2 : (s - shiftRow ϖ m b₀) l = -((ϖ : k) ^ (m - 1) * (((Quotient.out (b₀ l) : 𝒪[k]) : k) - ((ϖ : k) ^ (m - 1))⁻¹ * s l))`. Simplify using `only [Pi.sub_apply, shiftRow]`. Rewrite using `[mul_sub, mul_inv_cancel_left₀ hp0]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, map_mul, Valuation.map_neg, map_mul, map_pow, hm']`. Conclude with `(mul_le_mul' (mul_le_mul' le_rfl (hb l)) ((Valuation.mem_integer_iff _ _).1 (hY l j))).trans (by rw [mul_one])`. Use `show valuation k (∑ l, s l * Z l j) ≤ _`. Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, hm']`. Conclude with `mul_le_mul' (hs l) ((hZ l j).trans (inv_pow_mul_pow_le hu hu0 hcm))`.
-/
theorem shiftRow_exists {ϖ : kˣ} (hϖ : IsUnif ϖ) {r c m : ℕ} (hcm : c + 1 ≤ m) (Y Z : Matrix (Fin r) D k)
    (hY : ∀ l j, Y l j ∈ 𝒪[k])
    (hZ : ∀ l j, valuation k (Z l j) ≤ (valuation k (ϖ : k) ^ c)⁻¹ * valuation k (ϖ : k) ^ m)
    (s : Fin r → k) (hs : ∀ l, valuation k (s l) ≤ valuation k (ϖ : k) ^ (m - 1)) :
    ∃ b : Fin r → Res k 1, ∀ j,
      valuation k ((s ᵥ* (Y + Z)) j - (shiftRow ϖ m b ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ m := by
  have hu : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hu0 : valuation k (ϖ : k) ≠ 0 := by simp
  have hp0 : (ϖ : k) ^ (m - 1) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have hvp : 0 < valuation k (ϖ : k) ^ (m - 1) := zero_lt_iff.2 (pow_ne_zero _ hu0)
  have hm' : valuation k (ϖ : k) ^ m = valuation k (ϖ : k) ^ (m - 1) * valuation k (ϖ : k) := by
    rw [← pow_succ]; congr 1; omega
  have htt : ∀ l, ((ϖ : k) ^ (m - 1))⁻¹ * s l ∈ 𝒪[k] := fun l => by
    rw [Valuation.mem_integer_iff, map_mul, map_inv₀, map_pow, inv_mul_le_iff₀ hvp, mul_one]; exact hs l
  let b₀ : Fin r → Res k 1 := fun l => Ideal.Quotient.mk _ ⟨_, htt l⟩
  have hb : ∀ l, valuation k (((Quotient.out (b₀ l) : 𝒪[k]) : k) - ((ϖ : k) ^ (m - 1))⁻¹ * s l) ≤
      valuation k (ϖ : k) :=
    fun l => (mem_max_iff hϖ _).1 (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out (b₀ l)))
  refine ⟨b₀, fun j => ?_⟩
  have e : (s ᵥ* (Y + Z)) j - (shiftRow ϖ m b₀ ᵥ* Y) j = ((s - shiftRow ϖ m b₀) ᵥ* Y) j + (s ᵥ* Z) j := by
    rw [Matrix.vecMul_add, Matrix.sub_vecMul]; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [e]
  refine Valuation.map_add_le _ ?_ ?_
  · show valuation k (∑ l, (s - shiftRow ϖ m b₀) l * Y l j) ≤ _
    refine Valuation.map_sum_le _ fun l _ => ?_
    have e2 : (s - shiftRow ϖ m b₀) l = -((ϖ : k) ^ (m - 1) *
        (((Quotient.out (b₀ l) : 𝒪[k]) : k) - ((ϖ : k) ^ (m - 1))⁻¹ * s l)) := by
      simp only [Pi.sub_apply, shiftRow]; rw [mul_sub, mul_inv_cancel_left₀ hp0]; ring
    rw [e2, map_mul, Valuation.map_neg, map_mul, map_pow, hm']
    exact (mul_le_mul' (mul_le_mul' le_rfl (hb l)) ((Valuation.mem_integer_iff _ _).1 (hY l j))).trans
      (by rw [mul_one])
  · show valuation k (∑ l, s l * Z l j) ≤ _
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul, hm']
    exact mul_le_mul' (hs l) ((hZ l j).trans (inv_pow_mul_pow_le hu hu0 hcm))

end GlobalTheory.CountTranslates

namespace GlobalTheory.CountTranslates
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv

/- English proof (translation)
Introduce `k _ _ _ _ A D _ _ _ _ ϖ hϖ i₀ r c m C H Q hH0 hHv hcm hY hQ hYQ hC0`. Establish `hu : valuation k (ϖ : k) < 1` using `hϖ ▸ uniformizer_lt_one`. Establish `hu0 : valuation k (ϖ : k) ≠ 0` using `by simp`. Establish `hm' : valuation k (ϖ : k) ^ m = valuation k (ϖ : k) ^ (m - 1) * valuation k (ϖ : k)`. Rewrite using `[← pow_succ]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hmm : valuation k (ϖ : k) ^ m ≤ valuation k (ϖ : k) ^ (m - 1)`. Rewrite using `[hm']`. Conclude with `mul_le_of_le_one_right' hu.le`.

Establish `hHv' : ∀ l i, valuation k (H l i) ≤ (valuation k (ϖ : k) ^ c)⁻¹` using `fun l i => by`. Use `hHv l i` as an intermediate fact. Rewrite `this` using `[Units.val_inv_eq_inv_val, map_inv₀, val_pow]`. Then use the resulting hypothesis. Rewrite using `[mem_lowRank]`. Use `⟨sub_mem (boxFn_mem_SB _ _ _) (Submodule.sum_mem _ fun b _ => boxFn_mem_SB _ _ _), fun X hX => ?_⟩` and prove the remaining obligations.

Establish `hXr : X.rank ≤ r` using `Nat.lt_succ_iff.1 hX`. Simplify using `only [Pi.sub_apply, Finset.sum_apply, boxFn]`. Rewrite using `[sub_eq_zero]`. Express the relevant statement in the definitionally equal form `_ = ∑ b : Fin r → Res k 1, (box ϖ (C.updateRow i₀ (shiftRow ϖ m b ᵥ* (H * C))) fun _ => m).indicator 1 X`. Distinguish the cases in `hrows : ∀ i, i ≠ i₀ → ∀ j, valuation k (X i j - C i j) ≤ valuation k (ϖ : k) ^ m`.

Distinguish the cases in `hi0 : ∀ j, valuation k (X i₀ j) ≤ valuation k (ϖ : k) ^ (m - 1)`. Set `E : Matrix (Fin r) (Fin r) k` to `H * (X - C) * Q`. Establish `hHXC : ∀ l j, valuation k ((H * (X - C)) l j) ≤ (valuation k (ϖ : k) ^ c)⁻¹ * valuation k (ϖ : k) ^ m`. Introduce `l j`. Rewrite using `[Matrix.mul_apply]`.

Use `Valuation.map_sum_le _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = i₀`. Substitute `hi` using the available equality. Simplify using `[hH0]`. Rewrite using `[map_mul]; exact mul_le_mul' (hHv' l i) (by simpa [Matrix.sub_apply] using hrows i hi j)`.

Establish `hE : ∀ l j, valuation k (E l j) ≤ valuation k (ϖ : k)`. Introduce `l j`. Use `(?_ : _ ≤ (valuation k (ϖ : k) ^ c)⁻¹ * valuation k (ϖ : k) ^ m).trans (inv_pow_mul_pow_le hu hu0 hcm)` and prove the remaining obligations. Use `show valuation k (∑ a, (H * (X - C)) l a * Q a j) ≤ _`. Use `Valuation.map_sum_le _ fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Conclude with `(mul_le_mul' (hHXC l a) ((Valuation.mem_integer_iff _ _).1 (hQ a j))).trans (by rw [mul_one])`. Establish `hHXQ : H * X * Q = 1 + E`. Simplify using `only [E, Matrix.mul_sub, Matrix.sub_mul, hYQ]`. Normalize the expressions using the abelian group laws.

Establish `hunit : IsUnit (H * X * Q)`. Rewrite using `[← vecMul_injective_iff_isUnit]`. Introduce `s s' hss`. Establish `h0 : (s - s') + (s - s') ᵥ* E = 0`. Establish `: (s - s') ᵥ* (H * X * Q) = 0` using `by rw [Matrix.sub_vecMul]; exact sub_eq_zero.2 hss`.

Rewrite `this` using `[hHXQ, Matrix.vecMul_add, Matrix.vecMul_one]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `l`. Use `val_le_of_add_vecMul hu (s - s') E hE (t := 0) (fun l => by rw [h0]; simp) l` as an intermediate fact. Conclude with `sub_eq_zero.1 ((Valuation.zero_iff _).1 (le_zero_iff.1 this))`. Take `⟨s, hs⟩` from `GlobalTheory.T.rows_in_span_of_rank_normal_form k A D r X H Q hXr hunit i₀`.

Establish `hsv : ∀ l, valuation k (s l) ≤ valuation k (ϖ : k) ^ (m - 1)`. Use `val_le_of_add_vecMul hu s E hE fun l => ?_` and prove the remaining obligations. Establish `e : s + s ᵥ* E = X i₀ ᵥ* Q`. Rewrite using `[hs, Matrix.vecMul_vecMul, hHXQ, Matrix.vecMul_add, Matrix.vecMul_one]`. Rewrite using `[e]`.

Use `show valuation k (∑ j, X i₀ j * Q j l) ≤ _`. Use `Valuation.map_sum_le _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `(mul_le_mul' (hi0 j) ((Valuation.mem_integer_iff _ _).1 (hQ j l))).trans (by rw [mul_one])`. Establish `hXs : X i₀ = s ᵥ* (H * C + H * (X - C))`.

Rewrite using `[hs]`. Use `congr 1`. Rewrite using `[Matrix.mul_sub]`. Normalize the expressions using the abelian group laws. Take `⟨b₀, hb₀⟩` from `shiftRow_exists hϖ hcm (H * C) (H * (X - C)) hY hHXC s hsv`.

Rewrite `hb₀` using `[← hXs]`. Establish `hmem : ∀ b, X ∈ box ϖ (C.updateRow i₀ (shiftRow ϖ m b ᵥ* (H * C))) (fun _ => m) ↔ b = b₀` using `fun b => ⟨fun h => shiftRow_unique hϖ (by omega) (H * C) Q hQ hYQ (X i₀) b b₀ ((mem_box_updateRow _).1 h).2 hb₀, fun h => h ▸ (mem_box_updateRow _).2 ⟨hrows, hb₀⟩⟩`. Rewrite using `[Set.indicator_of_mem ((mem_box_update hC0).2 ⟨hrows, hi0⟩), Finset.sum_eq_single b₀ (fun b _ hb => Set.indicator_of_notMem (fun h => hb ((hmem b).1 h)) _) (by simp), Set.indicator_of_mem ((hmem b₀).2 rfl)]`. Rewrite using `[Set.indicator_of_notMem (fun h => hi0 ((mem_box_update hC0).1 h).2)]`. Use `(Finset.sum_eq_zero fun b _ => Set.indicator_of_notMem (fun h => hi0 fun j => ?_) _).symm` and prove the remaining obligations.

Establish `h2` using `((mem_box_updateRow _).1 h).2 j`. Rewrite using `[← sub_add_cancel (X i₀ j) ((shiftRow ϖ m b ᵥ* (H * C)) j)]`. Conclude with `Valuation.map_add_le _ (h2.trans hmm) (val_shiftRow_le ϖ (H * C) hY b j)`. Rewrite using `[Set.indicator_of_notMem (fun h => hrows ((mem_box_update hC0).1 h).1)]`. Conclude with `(Finset.sum_eq_zero fun b _ => Set.indicator_of_notMem (fun h => hrows ((mem_box_updateRow _).1 h).1) _).symm`.
-/
theorem boxFn_sub_sum_mem_lowRank : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ (m - 1)) - ∑ b : Fin r → GlobalTheory.SplitFlip.Res k 1, GlobalTheory.RankCoinv.boxFn ϖ (Matrix.updateRow C i₀ ((fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ᵥ* (H * C))) (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ i₀ r c m C H Q hH0 hHv hcm hY hQ hYQ hC0
  have hu : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hu0 : valuation k (ϖ : k) ≠ 0 := by simp
  have hm' : valuation k (ϖ : k) ^ m = valuation k (ϖ : k) ^ (m - 1) * valuation k (ϖ : k) := by
    rw [← pow_succ]; congr 1; omega
  have hmm : valuation k (ϖ : k) ^ m ≤ valuation k (ϖ : k) ^ (m - 1) := by
    rw [hm']; exact mul_le_of_le_one_right' hu.le
  have hHv' : ∀ l i, valuation k (H l i) ≤ (valuation k (ϖ : k) ^ c)⁻¹ := fun l i => by
    have := hHv l i
    rwa [Units.val_inv_eq_inv_val, map_inv₀, val_pow] at this
  rw [mem_lowRank]
  refine ⟨sub_mem (boxFn_mem_SB _ _ _) (Submodule.sum_mem _ fun b _ => boxFn_mem_SB _ _ _), fun X hX => ?_⟩
  have hXr : X.rank ≤ r := Nat.lt_succ_iff.1 hX
  simp only [Pi.sub_apply, Finset.sum_apply, boxFn]
  rw [sub_eq_zero]
  change _ = ∑ b : Fin r → Res k 1, (box ϖ (C.updateRow i₀ (shiftRow ϖ m b ᵥ* (H * C))) fun _ => m).indicator 1 X
  by_cases hrows : ∀ i, i ≠ i₀ → ∀ j, valuation k (X i j - C i j) ≤ valuation k (ϖ : k) ^ m
  · by_cases hi0 : ∀ j, valuation k (X i₀ j) ≤ valuation k (ϖ : k) ^ (m - 1)
    · let E : Matrix (Fin r) (Fin r) k := H * (X - C) * Q
      have hHXC : ∀ l j, valuation k ((H * (X - C)) l j) ≤
          (valuation k (ϖ : k) ^ c)⁻¹ * valuation k (ϖ : k) ^ m := by
        intro l j
        rw [Matrix.mul_apply]
        refine Valuation.map_sum_le _ fun i _ => ?_
        by_cases hi : i = i₀
        · subst hi; simp [hH0]
        · rw [map_mul]; exact mul_le_mul' (hHv' l i) (by simpa [Matrix.sub_apply] using hrows i hi j)
      have hE : ∀ l j, valuation k (E l j) ≤ valuation k (ϖ : k) := by
        intro l j
        refine (?_ : _ ≤ (valuation k (ϖ : k) ^ c)⁻¹ * valuation k (ϖ : k) ^ m).trans
          (inv_pow_mul_pow_le hu hu0 hcm)
        show valuation k (∑ a, (H * (X - C)) l a * Q a j) ≤ _
        refine Valuation.map_sum_le _ fun a _ => ?_
        rw [map_mul]
        exact (mul_le_mul' (hHXC l a) ((Valuation.mem_integer_iff _ _).1 (hQ a j))).trans (by rw [mul_one])
      have hHXQ : H * X * Q = 1 + E := by
        simp only [E, Matrix.mul_sub, Matrix.sub_mul, hYQ]; abel
      have hunit : IsUnit (H * X * Q) := by
        rw [← vecMul_injective_iff_isUnit]
        intro s s' hss
        have h0 : (s - s') + (s - s') ᵥ* E = 0 := by
          have : (s - s') ᵥ* (H * X * Q) = 0 := by rw [Matrix.sub_vecMul]; exact sub_eq_zero.2 hss
          rwa [hHXQ, Matrix.vecMul_add, Matrix.vecMul_one] at this
        funext l
        have := val_le_of_add_vecMul hu (s - s') E hE (t := 0) (fun l => by rw [h0]; simp) l
        exact sub_eq_zero.1 ((Valuation.zero_iff _).1 (le_zero_iff.1 this))
      obtain ⟨s, hs⟩ := GlobalTheory.T.rows_in_span_of_rank_normal_form k A D r X H Q hXr hunit i₀
      have hsv : ∀ l, valuation k (s l) ≤ valuation k (ϖ : k) ^ (m - 1) := by
        refine val_le_of_add_vecMul hu s E hE fun l => ?_
        have e : s + s ᵥ* E = X i₀ ᵥ* Q := by
          rw [hs, Matrix.vecMul_vecMul, hHXQ, Matrix.vecMul_add, Matrix.vecMul_one]
        rw [e]
        show valuation k (∑ j, X i₀ j * Q j l) ≤ _
        refine Valuation.map_sum_le _ fun j _ => ?_
        rw [map_mul]
        exact (mul_le_mul' (hi0 j) ((Valuation.mem_integer_iff _ _).1 (hQ j l))).trans (by rw [mul_one])
      have hXs : X i₀ = s ᵥ* (H * C + H * (X - C)) := by
        rw [hs]; congr 1; rw [Matrix.mul_sub]; abel
      obtain ⟨b₀, hb₀⟩ := shiftRow_exists hϖ hcm (H * C) (H * (X - C)) hY hHXC s hsv
      rw [← hXs] at hb₀
      have hmem : ∀ b, X ∈ box ϖ (C.updateRow i₀ (shiftRow ϖ m b ᵥ* (H * C))) (fun _ => m) ↔ b = b₀ := fun b =>
        ⟨fun h => shiftRow_unique hϖ (by omega) (H * C) Q hQ hYQ (X i₀) b b₀ ((mem_box_updateRow _).1 h).2 hb₀,
          fun h => h ▸ (mem_box_updateRow _).2 ⟨hrows, hb₀⟩⟩
      rw [Set.indicator_of_mem ((mem_box_update hC0).2 ⟨hrows, hi0⟩), Finset.sum_eq_single b₀
        (fun b _ hb => Set.indicator_of_notMem (fun h => hb ((hmem b).1 h)) _) (by simp),
        Set.indicator_of_mem ((hmem b₀).2 rfl)]
    · rw [Set.indicator_of_notMem (fun h => hi0 ((mem_box_update hC0).1 h).2)]
      refine (Finset.sum_eq_zero fun b _ => Set.indicator_of_notMem (fun h => hi0 fun j => ?_) _).symm
      have h2 := ((mem_box_updateRow _).1 h).2 j
      rw [← sub_add_cancel (X i₀ j) ((shiftRow ϖ m b ᵥ* (H * C)) j)]
      exact Valuation.map_add_le _ (h2.trans hmm) (val_shiftRow_le ϖ (H * C) hY b j)
  · rw [Set.indicator_of_notMem (fun h => hrows ((mem_box_update hC0).1 h).1)]
    exact (Finset.sum_eq_zero fun b _ =>
      Set.indicator_of_notMem (fun h => hrows ((mem_box_updateRow _).1 h).1) _).symm

end GlobalTheory.CountTranslates
