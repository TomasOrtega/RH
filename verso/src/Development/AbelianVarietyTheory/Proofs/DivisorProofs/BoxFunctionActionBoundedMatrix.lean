import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv
open GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def rowOpMat (i₀ : A) (w : A → k) : Matrix A A k :=
  replicateCol Unit (Pi.single i₀ (1 : k)) * replicateRow Unit w

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Distinguish the cases in `h : i = i₀`. Substitute `h` using the available equality. Simplify using `[rowOpMat, Matrix.mul_apply]`. Simplify using `[rowOpMat, Matrix.mul_apply, h]`.
-/
theorem rowOpMat_apply (i₀ : A) (w : A → k) (i a : A) : rowOpMat i₀ w i a = if i = i₀ then w a else 0 := by
  by_cases h : i = i₀
  · subst h; simp [rowOpMat, Matrix.mul_apply]
  · simp [rowOpMat, Matrix.mul_apply, h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, rowOpMat_apply, hw]`.
-/
theorem rowOpMat_mul_self (i₀ : A) (w : A → k) (hw : w i₀ = 0) : rowOpMat i₀ w * rowOpMat i₀ w = 0 := by
  ext i j
  simp [Matrix.mul_apply, rowOpMat_apply, hw]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq D] in
/- English proof (translation)
Distinguish the cases in `h : i = i₀`. Simplify using `[Matrix.mul_apply, rowOpMat_apply, h]`. Simplify using `[Matrix.mul_apply, rowOpMat_apply, h]`.
-/
theorem rowOpMat_mul_apply (i₀ : A) (w : A → k) (X : Matrix A D k) (i : A) (j : D) :
    (rowOpMat i₀ w * X) i j = if i = i₀ then ∑ a, w a * X a j else 0 := by
  by_cases h : i = i₀
  · simp [Matrix.mul_apply, rowOpMat_apply, h]
  · simp [Matrix.mul_apply, rowOpMat_apply, h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Rewrite using `[rowOpMat, det_one_add_replicateCol_mul_replicateRow]`. Simplify using `[hw]`.
-/
theorem det_one_add_rowOpMat (i₀ : A) (w : A → k) (hw : w i₀ = 0) : (1 + rowOpMat i₀ w).det = 1 := by
  rw [rowOpMat, det_one_add_replicateCol_mul_replicateRow]
  simp [hw]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def unipRowGL (i₀ : A) (w : A → k) (hw : w i₀ = 0) : GL A k :=
  ⟨1 + rowOpMat i₀ w, 1 - rowOpMat i₀ w,
    by simp [add_mul, mul_sub, rowOpMat_mul_self i₀ w hw],
    by simp [sub_mul, mul_add, rowOpMat_mul_self i₀ w hw]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
The claim follows from `Units.ext (det_one_add_rowOpMat i₀ w hw)`.
-/
theorem gdet_unipRowGL (i₀ : A) (w : A → k) (hw : w i₀ = 0) : gdet (unipRowGL i₀ w hw) = 1 :=
  Units.ext (det_one_add_rowOpMat i₀ w hw)

/- English proof (translation)
Use `Valuation.map_sum_le _ fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `ha : a = i₀`. Substitute `ha` using the available equality. Simplify using `[hw0]`. Rewrite using `[map_mul]`.

Conclude with `(mul_le_mul' (hw a) (hZ a ha)).trans (by rw [one_mul])`.
-/
theorem valuation_rowSum_le (i₀ : A) (w : A → k) (hw0 : w i₀ = 0) (hw : ∀ a, valuation k (w a) ≤ 1)
    (Z : A → k) (b : ValueGroupWithZero k) (hZ : ∀ a, a ≠ i₀ → valuation k (Z a) ≤ b) :
    valuation k (∑ a, w a * Z a) ≤ b := by
  refine Valuation.map_sum_le _ fun a _ => ?_
  by_cases ha : a = i₀
  · subst ha; simp [hw0]
  · rw [map_mul]
    exact (mul_le_mul' (hw a) (hZ a ha)).trans (by rw [one_mul])

/- English proof (translation)
Use function extensionality and compare the values at `X`. Rewrite using `[omA_one_apply, gdet_unipRowGL]`. Simplify using `only [map_one, inv_one, Units.val_one, apow_one, one_mul]`. Establish `hinv : ((unipRowGL i₀ w hw0)⁻¹).val = 1 - rowOpMat i₀ w` using `rfl`. Rewrite using `[hinv]`.

Use `set C' := updateRow C i₀ (C i₀ + w ᵥ* C)`. Establish `hT : ∀ i j, ((1 - rowOpMat i₀ w : Matrix A A k) * X : Matrix A D k) i j - C i j = (X i j - C' i j) - (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0)`. Introduce `i j`. Rewrite using `[Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, rowOpMat_mul_apply]`. Distinguish the cases in `hi : i = i₀`.

Substitute `hi` using the available equality. Simplify using `only [C', updateRow_self, if_true, Pi.add_apply, vecMul, dotProduct, mul_sub, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[C', hi]`. Establish `hrow : ∀ a, a ≠ i₀ → ∀ j, X a j - C' a j = X a j - C a j` using `fun a ha j => by simp [C', ha]`.

Establish `hbox : (1 - rowOpMat i₀ w) * X ∈ box ϖ C (fun _ => m) ↔ X ∈ box ϖ C' (fun _ => m)`. Simplify using `only [box, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Establish `hS : valuation k (∑ a, w a * (X a j - C a j)) ≤ valuation k ((ϖ ^ m : kˣ) : k)` using `valuation_rowSum_le i₀ w hw0 hw _ _ fun a ha => by`.

Use `h a j` as an intermediate fact. Rewrite `this` using `[hT, if_neg ha, sub_zero, hrow a ha]`. Then use the resulting hypothesis. Use `h i j` as an intermediate fact. Rewrite `this` using `[hT]`. Rewrite using `[show X i j - C' i j = ((X i j - C' i j) - (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0)) + (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0) by ring]`.

Use `Valuation.map_add_le _ this ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `hS`. Simplify using the standard rewrite rules. Introduce `h i j`.

Establish `hS : valuation k (∑ a, w a * (X a j - C a j)) ≤ valuation k ((ϖ ^ m : kˣ) : k)` using `valuation_rowSum_le i₀ w hw0 hw _ _ fun a ha => by`. Use `h a j` as an intermediate fact. Rewrite `this` using `[hrow a ha]`. Then use the resulting hypothesis. Rewrite using `[hT]`. Use `Valuation.map_sub_le _ (h i j) ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `hS`. Simplify using the standard rewrite rules. Unfold `boxFn`. Distinguish the cases in `hX : X ∈ box ϖ C' (fun _ => m)`.

Rewrite using `[Set.indicator_of_mem hX, Set.indicator_of_mem (hbox.2 hX)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hX, Set.indicator_of_notMem (fun h => hX (hbox.1 h))]`.
-/
theorem omA_unipRowGL_boxFn (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (i₀ : A) (w : A → k) (hw0 : w i₀ = 0)
    (hw : ∀ a, valuation k (w a) ≤ 1) (C : Matrix A D k) (m : ℕ) :
    omA ν β (unipRowGL i₀ w hw0) 1 (boxFn ϖ C (fun _ => m)) =
      boxFn ϖ (updateRow C i₀ (C i₀ + w ᵥ* C)) (fun _ => m) := by
  funext X
  rw [omA_one_apply, gdet_unipRowGL]
  simp only [map_one, inv_one, Units.val_one, apow_one, one_mul]
  have hinv : ((unipRowGL i₀ w hw0)⁻¹).val = 1 - rowOpMat i₀ w := rfl
  rw [hinv]
  set C' := updateRow C i₀ (C i₀ + w ᵥ* C)
  have hT : ∀ i j, ((1 - rowOpMat i₀ w : Matrix A A k) * X : Matrix A D k) i j - C i j =
      (X i j - C' i j) - (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0) := by
    intro i j
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, rowOpMat_mul_apply]
    by_cases hi : i = i₀
    · subst hi
      simp only [C', updateRow_self, if_true, Pi.add_apply, vecMul, dotProduct, mul_sub, Finset.sum_sub_distrib]
      ring
    · simp [C', hi]
  have hrow : ∀ a, a ≠ i₀ → ∀ j, X a j - C' a j = X a j - C a j := fun a ha j => by simp [C', ha]
  have hbox : (1 - rowOpMat i₀ w) * X ∈ box ϖ C (fun _ => m) ↔ X ∈ box ϖ C' (fun _ => m) := by
    simp only [box, Set.mem_setOf_eq]
    constructor
    · intro h i j
      have hS : valuation k (∑ a, w a * (X a j - C a j)) ≤ valuation k ((ϖ ^ m : kˣ) : k) :=
        valuation_rowSum_le i₀ w hw0 hw _ _ fun a ha => by
          have := h a j
          rwa [hT, if_neg ha, sub_zero, hrow a ha] at this
      have := h i j
      rw [hT] at this
      rw [show X i j - C' i j = ((X i j - C' i j) - (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0)) +
        (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0) by ring]
      refine Valuation.map_add_le _ this ?_
      split_ifs
      · exact hS
      · simp
    · intro h i j
      have hS : valuation k (∑ a, w a * (X a j - C a j)) ≤ valuation k ((ϖ ^ m : kˣ) : k) :=
        valuation_rowSum_le i₀ w hw0 hw _ _ fun a ha => by
          have := h a j
          rwa [hrow a ha] at this
      rw [hT]
      refine Valuation.map_sub_le _ (h i j) ?_
      split_ifs
      · exact hS
      · simp
  unfold boxFn
  by_cases hX : X ∈ box ϖ C' (fun _ => m)
  · rw [Set.indicator_of_mem hX, Set.indicator_of_mem (hbox.2 hX)]; rfl
  · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem (fun h => hX (hbox.1 h))]
end GlobalTheory.RankCoinv

/- English proof (translation)
Introduce `k _ _ _ _ A D _ _ _ _ ϖ ν β i₀ r c m C H t hH0 hH ht`. Establish `hw0 : (t ᵥ* H) i₀ = 0` using `by simp [vecMul, dotProduct, hH0]`. Establish `hw : ∀ a, valuation k ((t ᵥ* H) a) ≤ 1` using `fun a => by show valuation k (∑ l, t l * H l a) ≤ 1`. Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Use `(mul_le_mul' (ht l) (hH l a)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Rewrite using `[← vecMul_vecMul, ← GlobalTheory.RankCoinv.omA_unipRowGL_boxFn ν β ϖ i₀ (t ᵥ* H) hw0 hw C m]`. Conclude with `GlobalTheory.RankCoinv.sub_mem_twistSpan ν β _ (GlobalTheory.RankCoinv.boxFn_mem_SB ϖ C _)`.
-/
theorem GlobalTheory.RankCoinv.boxFn_unip_row_sub_mem_twistSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (t : Fin r → k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → (∀ l, valuation k (t l) ≤ valuation k ((ϖ ^ c : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ (Matrix.updateRow C i₀ (C i₀ + t ᵥ* (H * C))) (fun _ => m) - GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ ν β i₀ r c m C H t hH0 hH ht
  have hw0 : (t ᵥ* H) i₀ = 0 := by simp [vecMul, dotProduct, hH0]
  have hw : ∀ a, valuation k ((t ᵥ* H) a) ≤ 1 := fun a => by
    show valuation k (∑ l, t l * H l a) ≤ 1
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    refine (mul_le_mul' (ht l) (hH l a)).trans (le_of_eq ?_)
    rw [← map_mul, Units.mul_inv, map_one]
  rw [← vecMul_vecMul, ← GlobalTheory.RankCoinv.omA_unipRowGL_boxFn ν β ϖ i₀ (t ᵥ* H) hw0 hw C m]
  exact GlobalTheory.RankCoinv.sub_mem_twistSpan ν β _ (GlobalTheory.RankCoinv.boxFn_mem_SB ϖ C _)
