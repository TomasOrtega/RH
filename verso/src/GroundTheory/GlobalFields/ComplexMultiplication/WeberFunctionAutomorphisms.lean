import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.WeberFunction
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open WeierstrassCurve OnePoint ShortWeierstrass

variable {F : Type*} [Field F]

open scoped Classical in

noncomputable def automorphismOrder (W : WeierstrassCurve F) : ℕ :=
  if W.a₆ = 0 then 4 else if W.a₄ = 0 then 6 else 2

/- English proof (translation)
Simplify using `[automorphismOrder, hb]`.
-/
theorem automorphismOrder_of_a₆_eq_zero {W : WeierstrassCurve F} (hb : W.a₆ = 0) : automorphismOrder W = 4 := by
  simp [automorphismOrder, hb]

/- English proof (translation)
Simplify using `[automorphismOrder, ha, hb]`.
-/
theorem automorphismOrder_of_a₄_eq_zero {W : WeierstrassCurve F} (ha : W.a₄ = 0) (hb : W.a₆ ≠ 0) :
    automorphismOrder W = 6 := by
  simp [automorphismOrder, ha, hb]

def automorphismScale (W : WeierstrassCurve F) :
    MulAction.stabilizer (VariableChange F) W →* Fˣ where
  toFun ξ := ξ.1.u
  map_one' := rfl
  map_mul' _ _ := rfl

def automorphismPoint {W : WeierstrassCurve F} (ξ : MulAction.stabilizer (VariableChange F) W) :
    W.toAffine.Point → W.toAffine.Point :=
  variableChangePoint ξ.1 (MulAction.mem_stabilizer_iff.mp ξ.2)

section CharZero

variable [CharZero F] {W : WeierstrassCurve F}

/- English proof (translation)
The claim follows from `variableChange_rst_eq_zero hW ((MulAction.mem_stabilizer_iff.mp ξ.2).symm ▸ hW)`.
-/
theorem automorphism_rst_eq_zero (hW : IsShortForm W)
    (ξ : MulAction.stabilizer (VariableChange F) W) : ξ.1.r = 0 ∧ ξ.1.s = 0 ∧ ξ.1.t = 0 :=
  variableChange_rst_eq_zero hW ((MulAction.mem_stabilizer_iff.mp ξ.2).symm ▸ hW)

/- English proof (translation)
Introduce `ξ η h`. Take `⟨hr, hs, ht⟩` from `automorphism_rst_eq_zero hW ξ`. Take `⟨hr', hs', ht'⟩` from `automorphism_rst_eq_zero hW η`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `VariableChange.ext h (hr.trans hr'.symm) (hs.trans hs'.symm) (ht.trans ht'.symm)`.
-/
theorem automorphismScale_injective (hW : IsShortForm W) :
    Function.Injective (automorphismScale W) := by
  intro ξ η h
  obtain ⟨hr, hs, ht⟩ := automorphism_rst_eq_zero hW ξ
  obtain ⟨hr', hs', ht'⟩ := automorphism_rst_eq_zero hW η
  apply Subtype.ext
  exact VariableChange.ext h (hr.trans hr'.symm) (hs.trans hs'.symm) (ht.trans ht'.symm)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ξ, rfl⟩`. Establish `hξ : ξ.1 • W = W` using `MulAction.mem_stabilizer_iff.mp ξ.2`. Establish `hCW : IsShortForm (ξ.1 • W)` using `hξ.symm ▸ hW`. Establish `h4` using `variableChange_a₄_of_isShortForm hW hCW`.

Establish `h6` using `variableChange_a₆_of_isShortForm hW hCW`. Rewrite `h4`, `h6` using `[hξ]`. Conclude with `⟨h4.symm, h6.symm⟩`. Introduce and unpack `⟨h4, h6⟩`. Establish `hC : (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W`.

Use `ext`. Simplify using `[variableChange_a₁, hW.a₁_eq]`. Simplify using `[variableChange_a₂, hW.a₂_eq, hW.a₁_eq]`. Simplify using `[variableChange_a₃, hW.a₃_eq, hW.a₁_eq]`. Simplify `h4` using `[variableChange_a₄, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq]`.

Simplify `h6` using `[variableChange_a₆, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq]`. Conclude with `⟨⟨_, MulAction.mem_stabilizer_iff.mpr hC⟩, rfl⟩`.
-/
theorem mem_range_automorphismScale (hW : IsShortForm W) (u : Fˣ) :
    u ∈ (automorphismScale W).range ↔
      (↑u⁻¹ : F) ^ 4 * W.a₄ = W.a₄ ∧ (↑u⁻¹ : F) ^ 6 * W.a₆ = W.a₆ := by
  constructor
  · rintro ⟨ξ, rfl⟩
    have hξ : ξ.1 • W = W := MulAction.mem_stabilizer_iff.mp ξ.2
    have hCW : IsShortForm (ξ.1 • W) := hξ.symm ▸ hW
    have h4 := variableChange_a₄_of_isShortForm hW hCW
    have h6 := variableChange_a₆_of_isShortForm hW hCW
    rw [hξ] at h4 h6
    exact ⟨h4.symm, h6.symm⟩
  · rintro ⟨h4, h6⟩
    have hC : (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W := by
      ext
      · simp [variableChange_a₁, hW.a₁_eq]
      · simp [variableChange_a₂, hW.a₂_eq, hW.a₁_eq]
      · simp [variableChange_a₃, hW.a₃_eq, hW.a₁_eq]
      · simpa [variableChange_a₄, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using h4
      · simpa [variableChange_a₆, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using h6
    exact ⟨⟨_, MulAction.mem_stabilizer_iff.mpr hC⟩, rfl⟩

variable [W.IsElliptic]

omit [CharZero F] in

/- English proof (translation)
Establish `key : ∀ (k : ℕ) (c : F), c ≠ 0 → (w⁻¹ ^ k * c = c ↔ w ^ k = 1)`. Introduce `k c hc`. Rewrite using `[inv_pow]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `inv_eq_one.mp (mul_right_cancel₀ hc (h.trans (one_mul c).symm))`. Introduce `h`. Rewrite using `[h, inv_one, one_mul]`. Unfold `automorphismOrder`. Distinguish the cases in `h6 : W.a₆ = 0`.

Establish `h4 : W.a₄ ≠ 0`. Break down `hW.a₄_ne_zero_or_a₆_ne_zero with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h6 h`. Simplify using `only [h6, mul_zero, and_true, if_true]`.

Conclude with `key 4 _ h4`. Distinguish the cases in `h4 : W.a₄ = 0`. Simplify using `only [h4, h6, mul_zero, true_and, if_false, if_true]`. Conclude with `key 6 _ h6`. Simplify using `only [h4, h6, if_false, key 4 _ h4, key 6 _ h6]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b⟩`. Establish `: w ^ 6 = w ^ 4 * w ^ 2` using `by ring`. Rewrite `b` using `[this, a, one_mul]`. Conclude with `b`.

Introduce `h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show w ^ 4 = (w ^ 2) ^ 2 by ring, h, one_pow]`. Rewrite using `[show w ^ 6 = (w ^ 2) ^ 3 by ring, h, one_pow]`.
-/
theorem scale_conditions_iff (hW : IsShortForm W) (w : F) :
    (w⁻¹ ^ 4 * W.a₄ = W.a₄ ∧ w⁻¹ ^ 6 * W.a₆ = W.a₆) ↔ w ^ automorphismOrder W = 1 := by
  have key : ∀ (k : ℕ) (c : F), c ≠ 0 → (w⁻¹ ^ k * c = c ↔ w ^ k = 1) := by
    intro k c hc
    rw [inv_pow]
    constructor
    · intro h
      exact inv_eq_one.mp (mul_right_cancel₀ hc (h.trans (one_mul c).symm))
    · intro h
      rw [h, inv_one, one_mul]
  unfold automorphismOrder
  by_cases h6 : W.a₆ = 0
  · have h4 : W.a₄ ≠ 0 := by
      rcases hW.a₄_ne_zero_or_a₆_ne_zero with h | h
      · exact h
      · exact absurd h6 h
    simp only [h6, mul_zero, and_true, if_true]
    exact key 4 _ h4
  by_cases h4 : W.a₄ = 0
  · simp only [h4, h6, mul_zero, true_and, if_false, if_true]
    exact key 6 _ h6
  · simp only [h4, h6, if_false, key 4 _ h4, key 6 _ h6]
    constructor
    · rintro ⟨a, b⟩
      have : w ^ 6 = w ^ 4 * w ^ 2 := by ring
      rw [this, a, one_mul] at b
      exact b
    · intro h
      refine ⟨?_, ?_⟩
      · rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, h, one_pow]
      · rw [show w ^ 6 = (w ^ 2) ^ 3 by ring, h, one_pow]

/- English proof (translation)
Use extensionality with `u`. Rewrite using `[mem_range_automorphismScale hW, mem_rootsOfUnity', Units.val_inv_eq_inv_val]`. Conclude with `scale_conditions_iff hW _`.
-/
theorem range_automorphismScale (hW : IsShortForm W) :
    (automorphismScale W).range = rootsOfUnity (automorphismOrder W) F := by
  ext u
  rw [mem_range_automorphismScale hW, mem_rootsOfUnity', Units.val_inv_eq_inv_val]
  exact scale_conditions_iff hW _

noncomputable def automorphismEquivRootsOfUnity (hW : IsShortForm W) :
    MulAction.stabilizer (VariableChange F) W ≃* rootsOfUnity (automorphismOrder W) F :=
  (MonoidHom.ofInjective (automorphismScale_injective hW)).trans
    (MulEquiv.subgroupCongr (range_automorphismScale hW))

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem automorphismEquivRootsOfUnity_apply (hW : IsShortForm W)
    (ξ : MulAction.stabilizer (VariableChange F) W) :
    ((automorphismEquivRootsOfUnity hW ξ : Fˣ)) = ξ.1.u := rfl

/- English proof (translation)
The claim follows from `weberFunction_variableChangePoint ξ.1 _ hW hW P`.
-/
theorem weberFunction_automorphismPoint (hW : IsShortForm W)
    (ξ : MulAction.stabilizer (VariableChange F) W) (P : W.toAffine.Point) :
    weberFunction W (automorphismPoint ξ P) = weberFunction W P :=
  weberFunction_variableChangePoint ξ.1 _ hW hW P

end CharZero

section Fibres

variable [CharZero F] {W : WeierstrassCurve F} [W.IsElliptic]

omit [CharZero F] [W.IsElliptic] in

/- English proof (translation)
Use `h.1` as an intermediate fact. Rewrite `this` using `[Affine.equation_iff]`. Simplify `this` using `[hW.a₁_eq, hW.a₂_eq, hW.a₃_eq]`.
-/
theorem IsShortForm.sq_eq (hW : IsShortForm W) {x y : F} (h : W.toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 + W.a₄ * x + W.a₆ := by
  have := h.1
  rw [Affine.equation_iff] at this
  simpa [hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using this

/- English proof (translation)
Establish `hΔ : W.Δ ≠ 0` using `W.isUnit_Δ.ne_zero`. Distinguish the cases in `h6 : W.a₆ = 0`. Establish `h4 : W.a₄ ≠ 0`. Break down `hW.a₄_ne_zero_or_a₆_ne_zero with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd h6 h`. Rewrite `hx` using `[weberValue_of_a₆_eq_zero h6, weberValue_of_a₆_eq_zero h6]`. Establish `hc : g₂ W ^ 2 / W.Δ ≠ 0` using `by simp [g₂, h4, hΔ]`. Establish `hsq : x₁ ^ 2 = x₂ ^ 2` using `mul_left_cancel₀ hc hx`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h` into its components or cases.

Conclude with `⟨1, one_ne_zero, by simp, by simp, by simp [h]⟩`. Take `⟨i, hi⟩` from `IsAlgClosed.exists_eq_mul_self (-1 : F)`. Establish `hi4 : i ^ 4 = 1` using `by linear_combination (1 - i * i) * hi`. Use `⟨i, ?_, by rw [hi4, one_mul], by rw [h6, mul_zero], ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Simplify using `at hi`. Take the linear combination `(-x₁) * hi - h`. Distinguish the cases in `h4 : W.a₄ = 0`. Rewrite `hx` using `[weberValue_of_a₄_eq_zero h4 h6, weberValue_of_a₄_eq_zero h4 h6]`. Establish `hc : g₃ W / W.Δ ≠ 0` using `by simp [g₃, h6, hΔ]`.

Establish `hcube : x₁ ^ 3 = x₂ ^ 3` using `mul_left_cancel₀ hc hx`. Distinguish the cases in `hx1 : x₁ = 0`. Establish `hx2 : x₂ = 0`. Rewrite `hcube` using `[hx1, zero_pow (by norm_num)]`. Conclude with `pow_eq_zero_iff (n := 3) (by norm_num) |>.mp hcube.symm`.

Conclude with `⟨1, one_ne_zero, by simp, by simp, by simp [hx1, hx2]⟩`. Take `⟨w, hw⟩ : ∃ w, w = x₂ / x₁` from `⟨_, rfl⟩`. Establish `hw3 : w ^ 3 = 1`. Rewrite using `[hw, div_pow, ← hcube, div_self (pow_ne_zero 3 hx1)]`. Establish `hw0 : w ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hw3`. Use `⟨w ^ 2, pow_ne_zero 2 hw0, by simp [h4], ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show (w ^ 2) ^ 6 = (w ^ 3) ^ 4 by ring, hw3, one_pow, one_mul]`. Rewrite using `[show (w ^ 2) ^ 2 = w ^ 3 * w by ring, hw3, one_mul, hw, div_mul_cancel₀ _ hx1]`.

Rewrite `hx` using `[weberValue_of_ne_zero h4 h6, weberValue_of_ne_zero h4 h6]`. Establish `hc : g₂ W * g₃ W / W.Δ ≠ 0` using `by simp [g₂, g₃, h4, h6, hΔ]`. Establish `h : x₁ = x₂` using `mul_left_cancel₀ hc hx`. Conclude with `⟨1, one_ne_zero, by simp, by simp, by simp [h]⟩`.
-/
theorem exists_scale_of_weberValue_eq [IsAlgClosed F] (hW : IsShortForm W) {x₁ x₂ : F}
    (hx : weberValue W x₁ = weberValue W x₂) :
    ∃ v : F, v ≠ 0 ∧ v ^ 4 * W.a₄ = W.a₄ ∧ v ^ 6 * W.a₆ = W.a₆ ∧ v ^ 2 * x₁ = x₂ := by
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  by_cases h6 : W.a₆ = 0
  · have h4 : W.a₄ ≠ 0 := by
      rcases hW.a₄_ne_zero_or_a₆_ne_zero with h | h
      · exact h
      · exact absurd h6 h
    rw [weberValue_of_a₆_eq_zero h6, weberValue_of_a₆_eq_zero h6] at hx
    have hc : g₂ W ^ 2 / W.Δ ≠ 0 := by simp [g₂, h4, hΔ]
    have hsq : x₁ ^ 2 = x₂ ^ 2 := mul_left_cancel₀ hc hx
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨1, one_ne_zero, by simp, by simp, by simp [h]⟩
    · obtain ⟨i, hi⟩ := IsAlgClosed.exists_eq_mul_self (-1 : F)
      have hi4 : i ^ 4 = 1 := by linear_combination (1 - i * i) * hi
      refine ⟨i, ?_, by rw [hi4, one_mul], by rw [h6, mul_zero], ?_⟩
      · rintro rfl
        simp at hi
      · linear_combination (-x₁) * hi - h
  by_cases h4 : W.a₄ = 0
  · rw [weberValue_of_a₄_eq_zero h4 h6, weberValue_of_a₄_eq_zero h4 h6] at hx
    have hc : g₃ W / W.Δ ≠ 0 := by simp [g₃, h6, hΔ]
    have hcube : x₁ ^ 3 = x₂ ^ 3 := mul_left_cancel₀ hc hx
    by_cases hx1 : x₁ = 0
    · have hx2 : x₂ = 0 := by
        rw [hx1, zero_pow (by norm_num)] at hcube
        exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp hcube.symm
      exact ⟨1, one_ne_zero, by simp, by simp, by simp [hx1, hx2]⟩
    · obtain ⟨w, hw⟩ : ∃ w, w = x₂ / x₁ := ⟨_, rfl⟩
      have hw3 : w ^ 3 = 1 := by
        rw [hw, div_pow, ← hcube, div_self (pow_ne_zero 3 hx1)]
      have hw0 : w ≠ 0 := by
        rintro rfl
        simp at hw3
      refine ⟨w ^ 2, pow_ne_zero 2 hw0, by simp [h4], ?_, ?_⟩
      · rw [show (w ^ 2) ^ 6 = (w ^ 3) ^ 4 by ring, hw3, one_pow, one_mul]
      · rw [show (w ^ 2) ^ 2 = w ^ 3 * w by ring, hw3, one_mul, hw, div_mul_cancel₀ _ hx1]
  · rw [weberValue_of_ne_zero h4 h6, weberValue_of_ne_zero h4 h6] at hx
    have hc : g₂ W * g₃ W / W.Δ ≠ 0 := by simp [g₂, g₃, h4, h6, hΔ]
    have h : x₁ = x₂ := mul_left_cancel₀ hc hx
    exact ⟨1, one_ne_zero, by simp, by simp, by simp [h]⟩

omit [W.IsElliptic] in

/- English proof (translation)
Take `⟨ξ, hξ⟩` from `(mem_range_automorphismScale hW ((Units.mk0 v hv)⁻¹)).mpr ⟨by simpa using h4, by simpa using h6⟩`. Use `⟨ξ, ?_⟩` and prove the remaining obligations. Take `⟨hr, hs, ht⟩` from `automorphism_rst_eq_zero hW ξ`. Establish `hu : (↑ξ.1.u⁻¹ : F) = v`. Establish `: ξ.1.u = (Units.mk0 v hv)⁻¹` using `hξ`.

Rewrite using `[this, inv_inv, Units.val_mk0]`. Simplify using `only [automorphismPoint, variableChangePoint_some, hr, hs, ht, hu, sub_zero, zero_mul, Affine.Point.some.injEq]`. Conclude with `⟨hx, hy⟩`.
-/
theorem exists_automorphismPoint_of_scale (hW : IsShortForm W) {v x₁ y₁ x₂ y₂ : F} (hv : v ≠ 0)
    (h4 : v ^ 4 * W.a₄ = W.a₄) (h6 : v ^ 6 * W.a₆ = W.a₆) (hx : v ^ 2 * x₁ = x₂)
    (hy : v ^ 3 * y₁ = y₂) (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    ∃ ξ : MulAction.stabilizer (VariableChange F) W,
      automorphismPoint ξ (.some x₁ y₁ h₁) = .some x₂ y₂ h₂ := by
  obtain ⟨ξ, hξ⟩ := (mem_range_automorphismScale hW ((Units.mk0 v hv)⁻¹)).mpr
    ⟨by simpa using h4, by simpa using h6⟩
  refine ⟨ξ, ?_⟩
  obtain ⟨hr, hs, ht⟩ := automorphism_rst_eq_zero hW ξ
  have hu : (↑ξ.1.u⁻¹ : F) = v := by
    have : ξ.1.u = (Units.mk0 v hv)⁻¹ := hξ
    rw [this, inv_inv, Units.val_mk0]
  simp only [automorphismPoint, variableChangePoint_some, hr, hs, ht, hu, sub_zero, zero_mul,
    Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hPQ`. Consider the cases of `P with`. Consider the case `zero`. Consider the cases of `Q with`.

Consider the case `zero => exact ⟨1, rfl⟩`. Consider the case `some x y h => simp at hPQ`. Consider the case `some x₁ y₁ h₁`. Consider the cases of `Q with`. Consider the case `zero => simp at hPQ`.

Consider the case `some x₂ y₂ h₂`. Simplify using `only [weberFunction_some] at hPQ`. Establish `hx : weberValue W x₁ = weberValue W x₂` using `Option.some_injective _ hPQ`. Take `⟨v, hv, h4, h6, hx2⟩` from `exists_scale_of_weberValue_eq hW hx`. Establish `hy : y₂ ^ 2 = (v ^ 3 * y₁) ^ 2`.

Rewrite using `[hW.sq_eq h₂, ← hx2]`. Take the linear combination `(-(v ^ 6)) * hW.sq_eq h₁ - v ^ 2 * x₁ * h4 - h6`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hy with hy | hy` into its components or cases. Conclude with `exists_automorphismPoint_of_scale hW hv h4 h6 hx2 hy.symm h₁ h₂`. Use `exists_automorphismPoint_of_scale (v := -v) hW (neg_ne_zero.mpr hv) ?_ ?_ ?_ ?_ h₁ h₂` and prove the remaining obligations.

Rewrite using `[show (-v) ^ 4 = v ^ 4 by ring, h4]`. Rewrite using `[show (-v) ^ 6 = v ^ 6 by ring, h6]`. Rewrite using `[show (-v) ^ 2 = v ^ 2 by ring, hx2]`. Rewrite using `[hy]`. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `⟨ξ, rfl⟩`. Conclude with `(weberFunction_automorphismPoint hW ξ P).symm`.
-/
theorem weberFunction_eq_iff [IsAlgClosed F] (hW : IsShortForm W) (P Q : W.toAffine.Point) :
    weberFunction W P = weberFunction W Q ↔
      ∃ ξ : MulAction.stabilizer (VariableChange F) W, automorphismPoint ξ P = Q := by
  constructor
  · intro hPQ
    cases P with
    | zero =>
      cases Q with
      | zero => exact ⟨1, rfl⟩
      | some x y h => simp at hPQ
    | some x₁ y₁ h₁ =>
      cases Q with
      | zero => simp at hPQ
      | some x₂ y₂ h₂ =>
        simp only [weberFunction_some] at hPQ
        have hx : weberValue W x₁ = weberValue W x₂ := Option.some_injective _ hPQ
        obtain ⟨v, hv, h4, h6, hx2⟩ := exists_scale_of_weberValue_eq hW hx
        have hy : y₂ ^ 2 = (v ^ 3 * y₁) ^ 2 := by
          rw [hW.sq_eq h₂, ← hx2]
          linear_combination (-(v ^ 6)) * hW.sq_eq h₁ - v ^ 2 * x₁ * h4 - h6
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with hy | hy
        · exact exists_automorphismPoint_of_scale hW hv h4 h6 hx2 hy.symm h₁ h₂
        · refine exists_automorphismPoint_of_scale (v := -v) hW (neg_ne_zero.mpr hv) ?_ ?_ ?_ ?_
            h₁ h₂
          · rw [show (-v) ^ 4 = v ^ 4 by ring, h4]
          · rw [show (-v) ^ 6 = v ^ 6 by ring, h6]
          · rw [show (-v) ^ 2 = v ^ 2 by ring, hx2]
          · rw [hy]
            ring
  · rintro ⟨ξ, rfl⟩
    exact (weberFunction_automorphismPoint hW ξ P).symm

end Fibres

end GroundTheory.Global
