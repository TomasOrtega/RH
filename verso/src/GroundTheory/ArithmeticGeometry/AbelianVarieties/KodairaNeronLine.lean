import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeron
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

section Line

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

/- English proof (translation)
Establish `hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)`. Introduce `hxy`. Rewrite `hs` using `[Point.add_of_Y_eq hxy.1 hxy.2, zero_add]`. Conclude with `Point.some_ne_zero _ hs`. Use `set ℓ := W.toAffine.slope x₁ x₂ y₁ y₂ with hℓ`.

Rewrite `hs` using `[Point.add_some hxy, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq]`. Take `⟨hx3, hy3⟩` from `hs`. Rewrite `hx3`, `hy3` using `[← hℓ]`. Use `⟨ℓ, y₁ - ℓ * x₁, by ring, ?_, ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x₁ = x₂`.

Substitute `hx` using the available equality. Establish `hy` using `Y_eq_of_Y_ne h₁.1 h₂.1 rfl (fun h => hxy ⟨rfl, h⟩)`. Rewrite using `[← hy]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hℓ, slope_of_X_ne hx]`.

Establish `hd : x₁ - x₂ ≠ 0` using `sub_ne_zero.2 hx`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← W.toAffine.negY_negY x₃ y₃, ← hy3, ← hx3]`. Simplify using `only [addY, negY_negY, negAddY]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e` using `W.toAffine.addPolynomial_slope h₁.1 h₂.1 hxy`. Rewrite `e` using `[addPolynomial_eq, Cubic.prod_X_sub_C_eq, neg_inj, Cubic.toPoly_injective, Cubic.mk.injEq, hx3]`. Take `⟨-, e2, e3, e4⟩` from `e`. Rewrite `e2`, `e3`, `e4` using `[← hℓ]`.

Use `⟨by linear_combination e2, by linear_combination -e3, by linear_combination e4⟩` and prove the remaining obligations.
-/
theorem exists_line_of_add_eq_zero {x₁ y₁ x₂ y₂ x₃ y₃ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) (h₃ : W.toAffine.Nonsingular x₃ y₃)
    (hs : Point.some _ _ h₁ + Point.some _ _ h₂ + Point.some _ _ h₃ = 0) :
    ∃ ℓ ν : F, y₁ = ℓ * x₁ + ν ∧ y₂ = ℓ * x₂ + ν ∧ y₃ = ℓ * x₃ + ν ∧
      x₁ + x₂ + x₃ = ℓ ^ 2 + W.a₁ * ℓ - W.a₂ ∧
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = W.a₄ - 2 * ℓ * ν - W.a₁ * ν - W.a₃ * ℓ ∧
      x₁ * x₂ * x₃ = ν ^ 2 + W.a₃ * ν - W.a₆ := by
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := by
    intro hxy
    rw [Point.add_of_Y_eq hxy.1 hxy.2, zero_add] at hs
    exact Point.some_ne_zero _ hs
  set ℓ := W.toAffine.slope x₁ x₂ y₁ y₂ with hℓ
  rw [Point.add_some hxy, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq] at hs
  obtain ⟨hx3, hy3⟩ := hs
  rw [← hℓ] at hx3 hy3
  refine ⟨ℓ, y₁ - ℓ * x₁, by ring, ?_, ?_, ?_⟩
  · by_cases hx : x₁ = x₂
    · subst hx
      have hy := Y_eq_of_Y_ne h₁.1 h₂.1 rfl (fun h => hxy ⟨rfl, h⟩)
      rw [← hy]; ring
    · rw [hℓ, slope_of_X_ne hx]
      have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
      field_simp
      ring
  · rw [← W.toAffine.negY_negY x₃ y₃, ← hy3, ← hx3]
    simp only [addY, negY_negY, negAddY]
    ring
  have e := W.toAffine.addPolynomial_slope h₁.1 h₂.1 hxy
  rw [addPolynomial_eq, Cubic.prod_X_sub_C_eq, neg_inj, Cubic.toPoly_injective,
    Cubic.mk.injEq, hx3] at e
  obtain ⟨-, e2, e3, e4⟩ := e
  rw [← hℓ] at e2 e3 e4
  refine ⟨by linear_combination e2, by linear_combination -e3, by linear_combination e4⟩

end Line

section Counting

variable {G : Type*} [AddCommGroup G] (H : AddSubgroup G)

/- English proof (translation)
Set `f : G ⧸ H → Option s` to `fun q => if h : q.out ∈ H then none else some ⟨(hex _ h).choose, (hex _ h).choose_spec.1⟩`. Establish `hf : Function.Injective f`. Introduce `q₁ q₂ e`. Apply the tactic sequence `by_cases h₁ : q₁.out ∈ H <;> by_cases h₂ : q₂.out ∈ H <;> simp only [f, h₁, h₂, dif_pos, dif_neg, not_false_eq_true, reduceCtorEq, Option.some.injEq, Subtype.mk.injEq] at e`. Rewrite using `[← QuotientAddGroup.out_eq' q₁, ← QuotientAddGroup.out_eq' q₂, (QuotientAddGroup.eq_zero_iff _).2 h₁, (QuotientAddGroup.eq_zero_iff _).2 h₂]`.

Establish `hR₁` using `(hex _ h₁).choose_spec.2`. Establish `hR₂` using `(hex _ h₂).choose_spec.2`. Rewrite `hR₁` using `[e]`. Use `hinj _ _ _ h₁ h₂ hR₁ hR₂` as an intermediate fact. Rewrite using `[← QuotientAddGroup.out_eq' q₁, ← QuotientAddGroup.out_eq' q₂, QuotientAddGroup.eq]`.

Establish `h'` using `H.neg_mem this`. Rewrite `h'` using `[neg_sub, sub_eq_neg_add]`. Then use the resulting hypothesis. Establish `: Finite (G ⧸ H)` using `Finite.of_injective f hf`. Use `⟨this, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_quotient_le_of_rel {T : Type*} (s : Finset T) (R : G → T → Prop)
    (hex : ∀ P, P ∉ H → ∃ t ∈ s, R P t)
    (hinj : ∀ P Q t, P ∉ H → Q ∉ H → R P t → R Q t → P - Q ∈ H) :
    Finite (G ⧸ H) ∧ Nat.card (G ⧸ H) ≤ s.card + 1 := by
  classical
  let f : G ⧸ H → Option s := fun q =>
    if h : q.out ∈ H then none else some ⟨(hex _ h).choose, (hex _ h).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro q₁ q₂ e
    by_cases h₁ : q₁.out ∈ H <;> by_cases h₂ : q₂.out ∈ H <;> simp only [f, h₁, h₂, dif_pos,
      dif_neg, not_false_eq_true, reduceCtorEq, Option.some.injEq, Subtype.mk.injEq] at e
    · rw [← QuotientAddGroup.out_eq' q₁, ← QuotientAddGroup.out_eq' q₂,
        (QuotientAddGroup.eq_zero_iff _).2 h₁, (QuotientAddGroup.eq_zero_iff _).2 h₂]
    · have hR₁ := (hex _ h₁).choose_spec.2
      have hR₂ := (hex _ h₂).choose_spec.2
      rw [e] at hR₁
      have := hinj _ _ _ h₁ h₂ hR₁ hR₂
      rw [← QuotientAddGroup.out_eq' q₁, ← QuotientAddGroup.out_eq' q₂, QuotientAddGroup.eq]
      have h' := H.neg_mem this
      rwa [neg_sub, sub_eq_neg_add] at h'
  have : Finite (G ⧸ H) := Finite.of_injective f hf
  refine ⟨this, ?_⟩
  calc Nat.card (G ⧸ H) ≤ Nat.card (Option s) := Nat.card_le_card_of_injective f hf
    _ = s.card + 1 := by simp

/- English proof (translation)
Use `card_quotient_le_of_rel H ({()} : Finset Unit) (fun _ _ => True) (fun _ _ => ⟨(), Finset.mem_singleton_self _, trivial⟩) (fun P Q _ hP hQ _ _ => by` as an intermediate fact. Assume the negation of the conclusion as `hPQ`. Establish `hQ' : -Q ∉ H` using `fun h => hQ (by simpa using H.neg_mem h)`. Establish `hR : Q - P ∉ H` using `fun h => hPQ (by simpa using H.neg_mem h)`. Conclude with `hno P (-Q) (Q - P) hP hQ' hR (by abel))`.

Simplify using `using this`.
-/
theorem card_quotient_le_two (hno : ∀ P Q R, P ∉ H → Q ∉ H → R ∉ H → P + Q + R ≠ 0) :
    Finite (G ⧸ H) ∧ Nat.card (G ⧸ H) ≤ 2 := by
  have := card_quotient_le_of_rel H ({()} : Finset Unit) (fun _ _ => True)
    (fun _ _ => ⟨(), Finset.mem_singleton_self _, trivial⟩)
    (fun P Q _ hP hQ _ _ => by
      by_contra hPQ
      have hQ' : -Q ∉ H := fun h => hQ (by simpa using H.neg_mem h)
      have hR : Q - P ∉ H := fun h => hPQ (by simpa using H.neg_mem h)
      exact hno P (-Q) (Q - P) hP hQ' hR (by abel))
  simpa using this

end Counting

section DVR

open IsLocalRing

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

local notation "ι" => algebraMap 𝒪 K

omit [IsFractionRing 𝒪 K] in
/- English proof (translation)
Simplify using `only [E0Set, Set.mem_ofPred_eq, not_forall, exists_prop]`.
-/
theorem notMem_E0Set_iff (P : (curveK K W).Point) :
    P ∉ E0Set K W ↔ ∃ (x y : 𝒪) (h : (curveK K W).Nonsingular (ι x) (ι y)),
      P = .some _ _ h ∧ ¬(curveRed W).Nonsingular (residue 𝒪 x) (residue 𝒪 y) := by
  simp only [E0Set, Set.mem_ofPred_eq, not_forall, exists_prop]

/- English proof (translation)
Take `⟨L, N, e1, e2, e3, v1, v2, v3⟩` from `exists_line_of_add_eq_zero h₁ h₂ h₃ hs`. Establish `hinj` using `IsFractionRing.injective 𝒪 K`. Establish `hL : ∃ ℓ : 𝒪, ι ℓ = L`. Distinguish the cases in `hL0 : L = 0`. Conclude with `⟨0, by rw [hL0, map_zero]⟩`.

Break down `ValuationRing.isInteger_or_isInteger 𝒪 L with ⟨ℓ, hℓ⟩ | ⟨t, ht⟩` into its components or cases. Conclude with `⟨ℓ, hℓ⟩`. Establish `hLt : L * ι t = 1` using `by rw [ht, mul_inv_cancel₀ hL0]`. Distinguish the cases in `hu : IsUnit t`. Use `⟨↑hu.unit⁻¹, ?_⟩` and prove the remaining obligations.

Establish `h1 : ι t * ι ↑hu.unit⁻¹ = 1` using `by rw [← map_mul, hu.mul_val_inv, map_one]`. Combine the equalities or inequalities in the displayed calculation. It suffices to derive a contradiction. Establish `key : ι (1 : 𝒪) = ι ((x₁ + x₂ + x₃) * t ^ 2 - W.a₁ * t + W.a₂ * t ^ 2)`. Simplify using `only [map_add, map_sub, map_mul, map_pow, map_one]`.

Rewrite using `[v1]`. Simplify using `only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂]`. Take the linear combination `(-(L * ι t + 1) - ι W.a₁ * ι t) * hLt`. Establish `h1` using `hinj key`. Establish `ht' : t ∈ maximalIdeal 𝒪` using `(mem_maximalIdeal t).2 hu`.

Establish `hm : (1 : 𝒪) ∈ maximalIdeal 𝒪`. Rewrite using `[h1]`. Use `Ideal.add_mem _ (Ideal.sub_mem _ ?_ ?_) ?_` and prove the remaining obligations. Conclude with `Ideal.mul_mem_left _ _ (by rw [pow_two]; exact Ideal.mul_mem_left _ _ ht')`. Conclude with `Ideal.mul_mem_left _ _ ht'`.

Conclude with `Ideal.mul_mem_left _ _ (by rw [pow_two]; exact Ideal.mul_mem_left _ _ ht')`. Conclude with `(maximalIdeal.isMaximal 𝒪).ne_top ((Ideal.eq_top_iff_one _).2 hm)`. Take `⟨ℓ, rfl⟩` from `hL`. Use `⟨ℓ, y₁ - ℓ * x₁, by ring, hinj ?_, hinj ?_, hinj ?_, hinj ?_, hinj ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_sub, map_mul]`.

Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_add, map_sub, map_mul]`. Rewrite using `[e1, e3]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [map_add, map_sub, map_mul, map_pow]`. Rewrite using `[v1]`. Simplify using the standard rewrite rules. Establish `hN : N = ι y₁ - ι ℓ * ι x₁` using `by rw [e1]; ring`. Simplify using `only [map_add, map_sub, map_mul, map_pow, map_ofNat]`.

Rewrite using `[v2, hN]`. Simplify using the standard rewrite rules. Establish `hN : N = ι y₁ - ι ℓ * ι x₁` using `by rw [e1]; ring`. Simplify using `only [map_add, map_sub, map_mul, map_pow]`. Rewrite using `[v3, hN]`.

Simplify using the standard rewrite rules.
-/
theorem exists_integral_line [DecidableEq K] {x₁ y₁ x₂ y₂ x₃ y₃ : 𝒪}
    (h₁ : (curveK K W).Nonsingular (ι x₁) (ι y₁)) (h₂ : (curveK K W).Nonsingular (ι x₂) (ι y₂))
    (h₃ : (curveK K W).Nonsingular (ι x₃) (ι y₃))
    (hs : Point.some _ _ h₁ + Point.some _ _ h₂ + Point.some _ _ h₃ = 0) :
    ∃ ℓ ν : 𝒪, y₁ = ℓ * x₁ + ν ∧ y₂ = ℓ * x₂ + ν ∧ y₃ = ℓ * x₃ + ν ∧
      x₁ + x₂ + x₃ = ℓ ^ 2 + W.a₁ * ℓ - W.a₂ ∧
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = W.a₄ - 2 * ℓ * ν - W.a₁ * ν - W.a₃ * ℓ ∧
      x₁ * x₂ * x₃ = ν ^ 2 + W.a₃ * ν - W.a₆ := by
  obtain ⟨L, N, e1, e2, e3, v1, v2, v3⟩ := exists_line_of_add_eq_zero h₁ h₂ h₃ hs
  have hinj := IsFractionRing.injective 𝒪 K

  have hL : ∃ ℓ : 𝒪, ι ℓ = L := by
    by_cases hL0 : L = 0
    · exact ⟨0, by rw [hL0, map_zero]⟩
    rcases ValuationRing.isInteger_or_isInteger 𝒪 L with ⟨ℓ, hℓ⟩ | ⟨t, ht⟩
    · exact ⟨ℓ, hℓ⟩
    have hLt : L * ι t = 1 := by rw [ht, mul_inv_cancel₀ hL0]
    by_cases hu : IsUnit t
    · refine ⟨↑hu.unit⁻¹, ?_⟩
      have h1 : ι t * ι ↑hu.unit⁻¹ = 1 := by rw [← map_mul, hu.mul_val_inv, map_one]
      calc ι ↑hu.unit⁻¹ = ι ↑hu.unit⁻¹ * (L * ι t) := by rw [hLt, mul_one]
        _ = L * (ι t * ι ↑hu.unit⁻¹) := by ring
        _ = L := by rw [h1, mul_one]
    · exfalso
      have key : ι (1 : 𝒪) = ι ((x₁ + x₂ + x₃) * t ^ 2 - W.a₁ * t + W.a₂ * t ^ 2) := by
        simp only [map_add, map_sub, map_mul, map_pow, map_one]
        rw [v1]
        simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂]
        linear_combination (-(L * ι t + 1) - ι W.a₁ * ι t) * hLt
      have h1 := hinj key
      have ht' : t ∈ maximalIdeal 𝒪 := (mem_maximalIdeal t).2 hu
      have hm : (1 : 𝒪) ∈ maximalIdeal 𝒪 := by
        rw [h1]
        refine Ideal.add_mem _ (Ideal.sub_mem _ ?_ ?_) ?_
        · exact Ideal.mul_mem_left _ _ (by rw [pow_two]; exact Ideal.mul_mem_left _ _ ht')
        · exact Ideal.mul_mem_left _ _ ht'
        · exact Ideal.mul_mem_left _ _ (by rw [pow_two]; exact Ideal.mul_mem_left _ _ ht')
      exact (maximalIdeal.isMaximal 𝒪).ne_top ((Ideal.eq_top_iff_one _).2 hm)
  obtain ⟨ℓ, rfl⟩ := hL
  refine ⟨ℓ, y₁ - ℓ * x₁, by ring, hinj ?_, hinj ?_, hinj ?_, hinj ?_, hinj ?_⟩
  · simp only [map_add, map_sub, map_mul]; rw [e1, e2]; ring
  · simp only [map_add, map_sub, map_mul]; rw [e1, e3]; ring
  · simp only [map_add, map_sub, map_mul, map_pow]; rw [v1]; simp
  · have hN : N = ι y₁ - ι ℓ * ι x₁ := by rw [e1]; ring
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]; rw [v2, hN]; simp
  · have hN : N = ι y₁ - ι ℓ * ι x₁ := by rw [e1]; ring
    simp only [map_add, map_sub, map_mul, map_pow]; rw [v3, hN]; simp

section Origin

variable {π : 𝒪} (hπ : Irreducible π)
include hπ

omit [IsFractionRing 𝒪 K] in
/- English proof (translation)
Rewrite using `[residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]`.
-/
theorem dvd_iff_residue_eq_zero {a : 𝒪} : π ∣ a ↔ residue 𝒪 a = 0 := by
  rw [residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]

omit [IsFractionRing 𝒪 K] in

/- English proof (translation)
Rewrite `hs` using `[WeierstrassCurve.Affine.nonsingular_iff']`. Use `push Not at hs`. Take `⟨hA, hB⟩` from `hs (equation_residue W h)`. Rewrite using `[dvd_iff_residue_eq_zero hπ, dvd_iff_residue_eq_zero hπ]`. Simplify using `only [map_sub, map_add, map_mul, map_pow, map_ofNat, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄] at hA hB ⊢`.

Conclude with `⟨hA, hB⟩`.
-/
theorem dvd_partials_of_singular {x y : 𝒪} (h : W.toAffine.Equation x y)
    (hs : ¬(curveRed W).Nonsingular (residue 𝒪 x) (residue 𝒪 y)) :
    π ∣ W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ∧ π ∣ 2 * y + W.a₁ * x + W.a₃ := by
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at hs
  push Not at hs
  obtain ⟨hA, hB⟩ := hs (equation_residue W h)
  rw [dvd_iff_residue_eq_zero hπ, dvd_iff_residue_eq_zero hπ]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄] at hA hB ⊢
  exact ⟨hA, hB⟩

omit [IsFractionRing 𝒪 K] in

/- English proof (translation)
Take `⟨hA, hB⟩` from `dvd_partials_of_singular W hπ h hs`. Rewrite `h3`, `h4`, `h6`, `hA`, `hB`, the goal using `[dvd_iff_residue_eq_zero hπ]`. Rewrite using `[dvd_iff_residue_eq_zero hπ]`. Establish `he` using `equation_residue W h`. Rewrite `he` using `[WeierstrassCurve.Affine.equation_iff]`.

Simplify using `only [map_sub, map_add, map_mul, map_pow, map_ofNat, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hA hB he`. Use `set X := residue 𝒪 x`. Use `set Y := residue 𝒪 y`. Establish `hX3 : X ^ 3 = 0`. Take the linear combination `(-X) * hA + (-Y) * hB + 2 * he + X * h4 - Y * h3 + 2 * h6`.

Establish `hX : X = 0` using `pow_eq_zero_iff (by norm_num) |>.1 hX3`. Use `⟨hX, ?_⟩` and prove the remaining obligations. Establish `hY2 : Y ^ 2 = 0`. Rewrite `he` using `[hX]`. Take the linear combination `he - Y * h3 + h6`.

Conclude with `pow_eq_zero_iff (by norm_num) |>.1 hY2`.
-/
theorem dvd_of_singular_origin (h3 : π ∣ W.a₃) (h4 : π ∣ W.a₄) (h6 : π ∣ W.a₆) {x y : 𝒪}
    (h : W.toAffine.Equation x y) (hs : ¬(curveRed W).Nonsingular (residue 𝒪 x) (residue 𝒪 y)) :
    π ∣ x ∧ π ∣ y := by
  obtain ⟨hA, hB⟩ := dvd_partials_of_singular W hπ h hs
  rw [dvd_iff_residue_eq_zero hπ] at h3 h4 h6 hA hB ⊢
  rw [dvd_iff_residue_eq_zero hπ]
  have he := equation_residue W h
  rw [WeierstrassCurve.Affine.equation_iff] at he
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆] at hA hB he
  set X := residue 𝒪 x
  set Y := residue 𝒪 y
  have hX3 : X ^ 3 = 0 := by
    linear_combination (-X) * hA + (-Y) * hB + 2 * he + X * h4 - Y * h3 + 2 * h6
  have hX : X = 0 := pow_eq_zero_iff (by norm_num) |>.1 hX3
  refine ⟨hX, ?_⟩
  have hY2 : Y ^ 2 = 0 := by
    rw [hX] at he
    linear_combination he - Y * h3 + h6
  exact pow_eq_zero_iff (by norm_num) |>.1 hY2

omit [IsFractionRing 𝒪 K] in

/- English proof (translation)
Rewrite using `[WeierstrassCurve.Affine.nonsingular_iff']`. Rewrite `h3`, `h4`, `hx`, `hy` using `[dvd_iff_residue_eq_zero hπ]`. Introduce and unpack `⟨-, hn⟩`. Simplify using `only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, hx, hy, h3, h4] at hn`. Simplify using `at hn`.
-/
theorem singular_of_dvd_origin (h3 : π ∣ W.a₃) (h4 : π ∣ W.a₄) {x y : 𝒪} (hx : π ∣ x)
    (hy : π ∣ y) : ¬(curveRed W).Nonsingular (residue 𝒪 x) (residue 𝒪 y) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  rw [dvd_iff_residue_eq_zero hπ] at h3 h4 hx hy
  rintro ⟨-, hn⟩
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, hx, hy, h3, h4] at hn
  simp at hn

/- English proof (translation)
Rewrite using `[notMem_E0Set_iff]`. Conclude with `⟨x, y, h, rfl, singular_of_dvd_origin W hπ h3 h4 hx hy⟩`.
-/
theorem notMem_E0Set_of_dvd (h3 : π ∣ W.a₃) (h4 : π ∣ W.a₄) {x y : 𝒪}
    (h : (curveK K W).Nonsingular (ι x) (ι y)) (hx : π ∣ x) (hy : π ∣ y) :
    Point.some _ _ h ∉ E0Set K W := by
  rw [notMem_E0Set_iff]
  exact ⟨x, y, h, rfl, singular_of_dvd_origin W hπ h3 h4 hx hy⟩

/- English proof (translation)
Take `⟨x, y, h, rfl, hs⟩` from `(notMem_E0Set_iff K W P).1 hP`. Establish `he` using `equation_of_map K W h.1`. Conclude with `⟨x, y, h, rfl, he, dvd_of_singular_origin W hπ h3 h4 h6 he hs⟩`.
-/
theorem exists_of_notMem_E0Set (h3 : π ∣ W.a₃) (h4 : π ∣ W.a₄) (h6 : π ∣ W.a₆)
    {P : (curveK K W).Point} (hP : P ∉ E0Set K W) :
    ∃ (x y : 𝒪) (h : (curveK K W).Nonsingular (ι x) (ι y)), P = .some _ _ h ∧
      W.toAffine.Equation x y ∧ π ∣ x ∧ π ∣ y := by
  obtain ⟨x, y, h, rfl, hs⟩ := (notMem_E0Set_iff K W P).1 hP
  have he := equation_of_map K W h.1
  exact ⟨x, y, h, rfl, he, dvd_of_singular_origin W hπ h3 h4 h6 he hs⟩

/- English proof (translation)
Take `⟨hA, hB⟩` from `dvd_partials_of_singular W hπ h hs`. Rewrite `h` using `[WeierstrassCurve.Affine.equation_iff]`. Simplify using `only [variableChange_a₃, variableChange_a₄, variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul]`. Use `⟨by linear_combination -h, ?_, ?_⟩` and prove the remaining obligations. Use `hB using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Use `hA.neg_right` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem origin_vc {x₀ y₀ : 𝒪} (h : W.toAffine.Equation x₀ y₀)
    (hs : ¬(curveRed W).Nonsingular (residue 𝒪 x₀) (residue 𝒪 y₀)) :
    (((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₆ = 0 ∧
      π ∣ ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₃ ∧
      π ∣ ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₄) := by
  obtain ⟨hA, hB⟩ := dvd_partials_of_singular W hπ h hs
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [variableChange_a₃, variableChange_a₄, variableChange_a₆, inv_one, Units.val_one,
    one_pow, one_mul]
  refine ⟨by linear_combination -h, ?_, ?_⟩
  · convert hB using 1; ring
  · have := hA.neg_right
    convert this using 1; ring

/- English proof (translation)
Take `⟨x₁, y₁, h₁, rfl, e₁, dx₁, dy₁⟩` from `exists_of_notMem_E0Set K W hπ h3 h4 h6 hP₁`. Take `⟨x₂, y₂, h₂, rfl, e₂, dx₂, dy₂⟩` from `exists_of_notMem_E0Set K W hπ h3 h4 h6 hP₂`. Take `⟨x₃, y₃, h₃, rfl, e₃, dx₃, dy₃⟩` from `exists_of_notMem_E0Set K W hπ h3 h4 h6 hP₃`. Take `⟨ℓ, ν, l1, l2, l3, v1, v2, v3⟩` from `exists_integral_line K W h₁ h₂ h₃ hs`. Conclude with `⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, ⟨h₁, rfl⟩, ⟨h₂, rfl⟩, ⟨h₃, rfl⟩, e₁, e₂, e₃, dx₁, dy₁, dx₂, dy₂, dx₃, dy₃, l1, l2, l3, v1, v2, v3⟩`.
-/
theorem triple_origin [DecidableEq K] (h3 : π ∣ W.a₃) (h4 : π ∣ W.a₄) (h6 : π ∣ W.a₆)
    {P₁ P₂ P₃ : (curveK K W).Point} (hP₁ : P₁ ∉ E0Set K W) (hP₂ : P₂ ∉ E0Set K W)
    (hP₃ : P₃ ∉ E0Set K W) (hs : P₁ + P₂ + P₃ = 0) :
    ∃ x₁ y₁ x₂ y₂ x₃ y₃ ℓ ν : 𝒪,
      (∃ h, P₁ = Point.some (ι x₁) (ι y₁) h) ∧ (∃ h, P₂ = Point.some (ι x₂) (ι y₂) h) ∧
      (∃ h, P₃ = Point.some (ι x₃) (ι y₃) h) ∧
      W.toAffine.Equation x₁ y₁ ∧ W.toAffine.Equation x₂ y₂ ∧ W.toAffine.Equation x₃ y₃ ∧
      π ∣ x₁ ∧ π ∣ y₁ ∧ π ∣ x₂ ∧ π ∣ y₂ ∧ π ∣ x₃ ∧ π ∣ y₃ ∧
      y₁ = ℓ * x₁ + ν ∧ y₂ = ℓ * x₂ + ν ∧ y₃ = ℓ * x₃ + ν ∧
      x₁ + x₂ + x₃ = ℓ ^ 2 + W.a₁ * ℓ - W.a₂ ∧
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = W.a₄ - 2 * ℓ * ν - W.a₁ * ν - W.a₃ * ℓ ∧
      x₁ * x₂ * x₃ = ν ^ 2 + W.a₃ * ν - W.a₆ := by
  obtain ⟨x₁, y₁, h₁, rfl, e₁, dx₁, dy₁⟩ := exists_of_notMem_E0Set K W hπ h3 h4 h6 hP₁
  obtain ⟨x₂, y₂, h₂, rfl, e₂, dx₂, dy₂⟩ := exists_of_notMem_E0Set K W hπ h3 h4 h6 hP₂
  obtain ⟨x₃, y₃, h₃, rfl, e₃, dx₃, dy₃⟩ := exists_of_notMem_E0Set K W hπ h3 h4 h6 hP₃
  obtain ⟨ℓ, ν, l1, l2, l3, v1, v2, v3⟩ := exists_integral_line K W h₁ h₂ h₃ hs
  exact ⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, ⟨h₁, rfl⟩, ⟨h₂, rfl⟩, ⟨h₃, rfl⟩, e₁, e₂, e₃, dx₁, dy₁,
    dx₂, dy₂, dx₃, dy₃, l1, l2, l3, v1, v2, v3⟩

end Origin

omit [IsFractionRing 𝒪 K] in

/- English proof (translation)
Establish `e : (curveK K W).negY (ι x) (ι y) = ι (-y - W.a₁ * x - W.a₃)`. Simplify using `[negY]`. Use `⟨e ▸ (nonsingular_neg _ _).2 h, ?_⟩` and prove the remaining obligations. Rewrite using `[Point.neg_some, Point.some.injEq]`. Conclude with `⟨rfl, e⟩`.
-/
theorem neg_some_integral [DecidableEq K] {x y : 𝒪} (h : (curveK K W).Nonsingular (ι x) (ι y)) :
    ∃ h', -(Point.some _ _ h : (curveK K W).Point) =
      Point.some (ι x) (ι (-y - W.a₁ * x - W.a₃)) h' := by
  have e : (curveK K W).negY (ι x) (ι y) = ι (-y - W.a₁ * x - W.a₃) := by
    simp [negY]
  refine ⟨e ▸ (nonsingular_neg _ _).2 h, ?_⟩
  rw [Point.neg_some, Point.some.injEq]
  exact ⟨rfl, e⟩

omit [IsFractionRing 𝒪 K] in

/- English proof (translation)
Rewrite `e` using `[Point.some.injEq]`. Conclude with `⟨IsFractionRing.injective 𝒪 K e.1, IsFractionRing.injective 𝒪 K e.2⟩`.
-/
theorem coords_eq_of_some_eq {x y x' y' : 𝒪} {h : (curveK K W).Nonsingular (ι x) (ι y)}
    {h' : (curveK K W).Nonsingular (ι x') (ι y')} [IsFractionRing 𝒪 K]
    (e : (Point.some _ _ h : (curveK K W).Point) = Point.some _ _ h') : x = x' ∧ y = y' := by
  rw [Point.some.injEq] at e
  exact ⟨IsFractionRing.injective 𝒪 K e.1, IsFractionRing.injective 𝒪 K e.2⟩

end DVR

end

end GroundTheory.Arith.Abelian
