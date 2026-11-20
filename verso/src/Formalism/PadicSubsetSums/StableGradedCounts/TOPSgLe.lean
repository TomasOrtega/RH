import Formalism.PadicSubsetSums.CentralIdempotents.ResidueAvoidanceOfPrimes

namespace Formalism.IrreducibleCountingLemmas.TOP

/- English proof (translation)
Establish `hr0 : 0 ≤ (ℓ : ℝ)⁻¹` using `by positivity`. Establish `hr1 : (ℓ : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by linarith)`. Establish `hl0 : (ℓ : ℝ) ≠ 0` using `by positivity`. Establish `hl1 : (ℓ : ℝ) - 1 ≠ 0` using `by intro h; linarith`. Establish `e : ∀ j : ℕ, H * ((ℓ : ℝ)⁻¹) ^ (j + 1) = (H * (ℓ : ℝ)⁻¹) * ((ℓ : ℝ)⁻¹) ^ j`.

Introduce `j`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e]`. Rewrite using `[tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]`. Establish `e2 : (1 : ℝ) - (ℓ : ℝ)⁻¹ = ((ℓ : ℝ) - 1) / ℓ` using `by field_simp`.

Rewrite using `[e2]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem tsum_mul_inv_pow_succ_eq_div_sub_one (ℓ : ℕ) (H : ℝ) (hℓ : (2 : ℝ) ≤ ℓ) :
    ∑' j : ℕ, H * ((ℓ : ℝ)⁻¹) ^ (j + 1) = H / ((ℓ : ℝ) - 1) := by
  have hr0 : 0 ≤ (ℓ : ℝ)⁻¹ := by positivity
  have hr1 : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hl0 : (ℓ : ℝ) ≠ 0 := by positivity
  have hl1 : (ℓ : ℝ) - 1 ≠ 0 := by intro h; linarith
  have e : ∀ j : ℕ, H * ((ℓ : ℝ)⁻¹) ^ (j + 1) = (H * (ℓ : ℝ)⁻¹) * ((ℓ : ℝ)⁻¹) ^ j := by
    intro j; ring
  simp_rw [e]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have e2 : (1 : ℝ) - (ℓ : ℝ)⁻¹ = ((ℓ : ℝ) - 1) / ℓ := by field_simp
  rw [e2]
  field_simp

/- English proof (translation)
Introduce `f _ ℓ h H hℓ hH i`. Unfold `sg`. Establish `hℓ' : (2 : ℝ) ≤ ℓ` using `by exact_mod_cast hℓ`. Establish `hr0 : 0 ≤ (ℓ : ℝ)⁻¹` using `by positivity`. Establish `hr1 : (ℓ : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by linarith)`.

Establish `hgeom : Summable (fun j : ℕ => (H : ℝ) * ((ℓ : ℝ)⁻¹) ^ (j + 1))`. Use `(summable_geometric_of_lt_one hr0 hr1).mul_left ((H : ℝ) * (ℓ : ℝ)⁻¹)` as an intermediate fact. Use `this.congr ?_` and prove the remaining obligations. Introduce `j`. Expand and normalize the polynomial expressions, which then agree.

Establish `hle : ∀ j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1) ≤ (H : ℝ) * ((ℓ : ℝ)⁻¹) ^ (j + 1)`. Introduce `j`. Rewrite using `[inv_pow, ← div_eq_mul_inv]`. Conclude with `div_le_div_of_nonneg_right (by exact_mod_cast hH _) (by positivity)`. Establish `hnn : ∀ j : ℕ, 0 ≤ (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)` using `fun j => by positivity`.

Establish `hs : Summable (fun j : ℕ => (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1))` using `hgeom.of_nonneg_of_le hnn hle`. Establish `h1` using `hs.tsum_le_tsum hle hgeom`. Rewrite `h1` using `[tsum_mul_inv_pow_succ_eq_div_sub_one ℓ H hℓ']`. Conclude with `(Int.floor_le _).trans h1`.
-/
theorem carryFloorLeGeom : SgLe := by
  intro f _ ℓ h H hℓ hH i
  unfold sg
  have hℓ' : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hr0 : 0 ≤ (ℓ : ℝ)⁻¹ := by positivity
  have hr1 : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hgeom : Summable (fun j : ℕ => (H : ℝ) * ((ℓ : ℝ)⁻¹) ^ (j + 1)) := by
    have := (summable_geometric_of_lt_one hr0 hr1).mul_left ((H : ℝ) * (ℓ : ℝ)⁻¹)
    refine this.congr ?_
    intro j; ring
  have hle : ∀ j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1) ≤
      (H : ℝ) * ((ℓ : ℝ)⁻¹) ^ (j + 1) := by
    intro j
    rw [inv_pow, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hH _) (by positivity)
  have hnn : ∀ j : ℕ, 0 ≤ (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1) :=
    fun j => by positivity
  have hs : Summable (fun j : ℕ => (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)) :=
    hgeom.of_nonneg_of_le hnn hle
  have h1 := hs.tsum_le_tsum hle hgeom
  rw [tsum_mul_inv_pow_succ_eq_div_sub_one ℓ H hℓ'] at h1
  exact (Int.floor_le _).trans h1

end Formalism.IrreducibleCountingLemmas.TOP
