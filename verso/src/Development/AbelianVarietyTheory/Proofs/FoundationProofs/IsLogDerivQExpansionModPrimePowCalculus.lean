import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulOfIsPrimitiveIntegralHahnGaussStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaDerivationHahnSeriesLeibnizAddConstStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue

section Calc

variable {Ω : Type} [Field Ω]

def DvA (A : ValuationSubring Ω) (l n : ℕ) (D : HahnSeries ℚ Ω) : Prop :=
  ∀ r, ∃ z ∈ A, D.coeff r = (l : Ω) ^ n * z

/- English proof (translation)
Rewrite using `[HahnSeries.coeff_mul]`. Conclude with `Finset.sum_induction _ (fun x => x ∈ A) (fun x y hx hy => add_mem hx hy) (zero_mem A) (fun ij _ => mul_mem (hP _) (hQ _))`.
-/
theorem coeffA_mul (A : ValuationSubring Ω) (P Q : HahnSeries ℚ Ω) (hP : ∀ r, P.coeff r ∈ A)
    (hQ : ∀ r, Q.coeff r ∈ A) (r : ℚ) : (P * Q).coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact Finset.sum_induction _ (fun x => x ∈ A) (fun x y hx hy => add_mem hx hy) (zero_mem A)
    (fun ij _ => mul_mem (hP _) (hQ _))

/- English proof (translation)
Introduce `r`. Rewrite using `[HahnSeries.coeff_mul]`. Use `Finset.sum_induction _ (fun x => ∃ z ∈ A, x = (l : Ω) ^ n * z) ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `x y ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩`. Conclude with `⟨z + w, add_mem hz hw, by ring⟩`.

Conclude with `⟨0, (zero_mem A), by ring⟩`. Introduce `ij _`. Take `⟨z, hz, e⟩` from `hD ij.2`. Conclude with `⟨P.coeff ij.1 * z, mul_mem (hP _) hz, by rw [e]; ring⟩`.
-/
theorem dvA_mul (A : ValuationSubring Ω) (l n : ℕ) (P D : HahnSeries ℚ Ω) (hP : ∀ r, P.coeff r ∈ A)
    (hD : DvA A l n D) : DvA A l n (P * D) := by
  intro r
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_induction _ (fun x => ∃ z ∈ A, x = (l : Ω) ^ n * z) ?_ ?_ ?_
  · rintro x y ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨z + w, add_mem hz hw, by ring⟩
  · exact ⟨0, (zero_mem A), by ring⟩
  · intro ij _
    obtain ⟨z, hz, e⟩ := hD ij.2
    exact ⟨P.coeff ij.1 * z, mul_mem (hP _) hz, by rw [e]; ring⟩

/- English proof (translation)
Introduce `r`. Take `⟨z, hz, e⟩` from `hD r`. Take `⟨w, hw, e'⟩` from `hE r`. Conclude with `⟨z + w, add_mem hz hw, by rw [HahnSeries.coeff_add, e, e']; ring⟩`.
-/
theorem dvA_add (A : ValuationSubring Ω) (l n : ℕ) (D E : HahnSeries ℚ Ω) (hD : DvA A l n D)
    (hE : DvA A l n E) : DvA A l n (D + E) := by
  intro r
  obtain ⟨z, hz, e⟩ := hD r
  obtain ⟨w, hw, e'⟩ := hE r
  exact ⟨z + w, add_mem hz hw, by rw [HahnSeries.coeff_add, e, e']; ring⟩

/- English proof (translation)
Simplify using `only [CgA, DvA, HahnSeries.coeff_sub]`.
-/
theorem cgA_iff (A : ValuationSubring Ω) (l n : ℕ) (P Q : HahnSeries ℚ Ω) :
    (∀ r, CgA A l n (P.coeff r) (Q.coeff r)) ↔ DvA A l n (P - Q) := by
  simp only [CgA, DvA, HahnSeries.coeff_sub]

end Calc

/- English proof (translation)
Introduce `Ω _ _ _ ε X _ l _ A _ n s f g φ ψ`. Establish `lei` using `fun P Q => (GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const (Ω := Ω) s P Q).1`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩ ⟨hψ, a2, b2, κ2, hκ2, hgb, hpa2, hpb2, hc2⟩`. Use `⟨fun r => by rw [HahnSeries.coeff_add]; exact add_mem (hφ r) (hψ r), a * a2, b * b2, κ * κ2, mul_ne_zero hκ hκ2, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul]`. Conclude with `GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hpa hpa2`. Rewrite using `[map_mul]`. Conclude with `GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hpb hpb2`.

Rewrite `hc`, `hc2`, the goal using `[cgA_iff]`. Rewrite using `[map_mul, map_mul, lei, lei]`. Establish `key : (φ + ψ) * (X.exp a * X.exp a2) * (X.exp b * X.exp b2) - ((theta s (X.exp a) * X.exp a2 + X.exp a * theta s (X.exp a2)) * (X.exp b * X.exp b2) - X.exp a * X.exp a2 * (theta s (X.exp b) * X.exp b2 + X.exp b * theta s (X.exp b2))) = (X.exp a2 * X.exp b2) * (φ * X.exp a * X.exp …`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Conclude with `dvA_add A l n _ _ (dvA_mul A l n _ _ (coeffA_mul A _ _ hpa2.1 hpb2.1) hc) (dvA_mul A l n _ _ (coeffA_mul A _ _ hpa.1 hpb.1) hc2)`. Introduce and unpack `⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩`. Establish `hf : f ≠ 0`. Introduce and unpack `rfl`. Establish `ha : a = 0`.

Establish `: algebraMap Ω X.K κ * a = 0` using `by rw [← hfb, zero_mul]`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `absurd ((map_eq_zero_iff _ (algebraMap Ω X.K).injective).mp h) hκ`. Conclude with `h`. Take `⟨r, hr, _⟩` from `hpa.2`.

Conclude with `hr (by rw [ha, map_zero, HahnSeries.coeff_zero])`. Use `⟨fun r => by rw [HahnSeries.coeff_neg]; exact neg_mem (hφ r), b, a, κ⁻¹, inv_ne_zero hκ, ?_, hpb, hpa, ?_⟩` and prove the remaining obligations. Establish `hk : algebraMap Ω X.K κ ≠ 0` using `(map_ne_zero _).mpr hκ`. Rewrite using `[map_inv₀]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[mul_comm, hfb]`. Rewrite `hc`, the goal using `[cgA_iff]`. Establish `key : -φ * X.exp b * X.exp a - (theta s (X.exp b) * X.exp a - X.exp b * theta s (X.exp a)) = -(φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)))` using `by ring`. Rewrite using `[key]`. Introduce `r`.

Take `⟨z, hz, e⟩` from `hc r`. Conclude with `⟨-z, neg_mem hz, by rw [HahnSeries.coeff_neg, e]; ring⟩`. Introduce and unpack `⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩ hψ hcg`. Use `⟨hψ, a, b, κ, hκ, hfb, hpa, hpb, ?_⟩` and prove the remaining obligations. Rewrite `hc`, `hcg`, the goal using `[cgA_iff]`.

Establish `key : ψ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)) = (-(X.exp a * X.exp b)) * (φ - ψ) + (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)))`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Use `dvA_add A l n _ _ (dvA_mul A l n _ _ ?_ hcg) hc` and prove the remaining obligations. Introduce `r`.

Rewrite using `[HahnSeries.coeff_neg]`. Conclude with `neg_mem (coeffA_mul A _ _ hpa.1 hpb.1 r)`. Introduce `κ hκ`. Establish `hp1 : Prim A (X.exp 1)`. Rewrite using `[map_one]`.

Use `⟨fun r => ?_, 0, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [HahnSeries.coeff_one]; split_ifs <;> simp`. Simplify using `[HahnSeries.coeff_one]`. Simplify using `[HahnSeries.coeff_one]`. Use `⟨fun r => by simp, 1, 1, κ, hκ, by simp, hp1, hp1, fun r => ⟨0, (zero_mem A), ?_⟩⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Introduce and unpack `n' hn ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩`. Use `⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, fun r => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, e⟩` from `hc r`. Use `⟨(l : Ω) ^ (n - n') * z, mul_mem (pow_mem (natCast_mem A l) _) hz, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hn]`.
-/
theorem isDl_calc : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (f g : X.K) (φ ψ : HahnSeries ℚ Ω), (IsDl X A l n s f φ → IsDl X A l n s g ψ → IsDl X A l n s (f * g) (φ + ψ)) ∧ (IsDl X A l n s f φ → IsDl X A l n s f⁻¹ (-φ)) ∧ (IsDl X A l n s f φ → (∀ r, ψ.coeff r ∈ A) → (∀ r, CgA A l n (φ.coeff r) (ψ.coeff r)) → IsDl X A l n s f ψ) ∧ (∀ κ : Ω, κ ≠ 0 → IsDl X A l n s (algebraMap Ω X.K κ) 0) ∧ (∀ n', n' ≤ n → IsDl X A l n s f φ → IsDl X A l n' s f φ) := by
  intro Ω _ _ _ ε X _ l _ A _ n s f g φ ψ
  have lei := fun P Q => (GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const (Ω := Ω) s P Q).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩ ⟨hψ, a2, b2, κ2, hκ2, hgb, hpa2, hpb2, hc2⟩
    refine ⟨fun r => by rw [HahnSeries.coeff_add]; exact add_mem (hφ r) (hψ r),
      a * a2, b * b2, κ * κ2, mul_ne_zero hκ hκ2, ?_, ?_, ?_, ?_⟩
    · calc f * g * (b * b2) = (f * b) * (g * b2) := by ring
        _ = _ := by rw [hfb, hgb, map_mul]; ring
    · rw [map_mul]; exact GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hpa hpa2
    · rw [map_mul]; exact GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hpb hpb2
    · rw [cgA_iff] at hc hc2 ⊢
      rw [map_mul, map_mul, lei, lei]
      have key : (φ + ψ) * (X.exp a * X.exp a2) * (X.exp b * X.exp b2) -
          ((theta s (X.exp a) * X.exp a2 + X.exp a * theta s (X.exp a2)) * (X.exp b * X.exp b2) -
            X.exp a * X.exp a2 * (theta s (X.exp b) * X.exp b2 + X.exp b * theta s (X.exp b2))) =
          (X.exp a2 * X.exp b2) * (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) +
          (X.exp a * X.exp b) * (ψ * X.exp a2 * X.exp b2 - (theta s (X.exp a2) * X.exp b2 - X.exp a2 * theta s (X.exp b2))) := by
        ring
      rw [key]
      exact dvA_add A l n _ _ (dvA_mul A l n _ _ (coeffA_mul A _ _ hpa2.1 hpb2.1) hc)
        (dvA_mul A l n _ _ (coeffA_mul A _ _ hpa.1 hpb.1) hc2)
  · rintro ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩
    have hf : f ≠ 0 := by
      rintro rfl
      have ha : a = 0 := by
        have : algebraMap Ω X.K κ * a = 0 := by rw [← hfb, zero_mul]
        rcases mul_eq_zero.mp this with h | h
        · exact absurd ((map_eq_zero_iff _ (algebraMap Ω X.K).injective).mp h) hκ
        · exact h
      obtain ⟨r, hr, _⟩ := hpa.2
      exact hr (by rw [ha, map_zero, HahnSeries.coeff_zero])
    refine ⟨fun r => by rw [HahnSeries.coeff_neg]; exact neg_mem (hφ r), b, a, κ⁻¹, inv_ne_zero hκ, ?_, hpb, hpa, ?_⟩
    · have hk : algebraMap Ω X.K κ ≠ 0 := (map_ne_zero _).mpr hκ
      rw [map_inv₀]
      field_simp
      rw [mul_comm, hfb]
    · rw [cgA_iff] at hc ⊢
      have key : -φ * X.exp b * X.exp a - (theta s (X.exp b) * X.exp a - X.exp b * theta s (X.exp a)) =
          -(φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) := by ring
      rw [key]
      intro r
      obtain ⟨z, hz, e⟩ := hc r
      exact ⟨-z, neg_mem hz, by rw [HahnSeries.coeff_neg, e]; ring⟩
  · rintro ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩ hψ hcg
    refine ⟨hψ, a, b, κ, hκ, hfb, hpa, hpb, ?_⟩
    rw [cgA_iff] at hc hcg ⊢
    have key : ψ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)) =
        (-(X.exp a * X.exp b)) * (φ - ψ) + (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) := by
      ring
    rw [key]
    refine dvA_add A l n _ _ (dvA_mul A l n _ _ ?_ hcg) hc
    intro r
    rw [HahnSeries.coeff_neg]
    exact neg_mem (coeffA_mul A _ _ hpa.1 hpb.1 r)
  · intro κ hκ
    have hp1 : Prim A (X.exp 1) := by
      rw [map_one]
      refine ⟨fun r => ?_, 0, ?_, ?_⟩
      · rw [HahnSeries.coeff_one]; split_ifs <;> simp
      · simp [HahnSeries.coeff_one]
      · simp [HahnSeries.coeff_one]
    refine ⟨fun r => by simp, 1, 1, κ, hκ, by simp, hp1, hp1, fun r => ⟨0, (zero_mem A), ?_⟩⟩
    simp
  · rintro n' hn ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩
    refine ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, fun r => ?_⟩
    obtain ⟨z, hz, e⟩ := hc r
    refine ⟨(l : Ω) ^ (n - n') * z, mul_mem (pow_mem (natCast_mem A l) _) hz, ?_⟩
    rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hn]

end GlobalTheory.Glue
