import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

/- English proof (translation)
Introduce `O _ bar X _ _ m n p δ γ γ' h₂ h₁ hδb hδp hγ' h2δ h2γ hf2 h1γ h1γ' hf1`. Use `set K : ℤ := 1 + ∑ i, |h₁ (δ i)| with hK`. Establish `hKi : ∀ i, |h₁ (δ i)| < K` using `fun i => by`. Use `Finset.single_le_sum (f := fun i => |h₁ (δ i)|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hK0 : 0 ≤ K`. Use `Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (h₁ (δ i)))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `happ : ∀ x, (K • h₂ + h₁) x = K * h₂ x + h₁ x` using `fun x => by simp`. Establish `hpos : ∀ i, 0 < h₂ (δ i) → 0 < (K • h₂ + h₁) (δ i)` using `fun i hi => by`.

Rewrite using `[happ]`. Establish `h1 : K ≤ K * h₂ (δ i)` using `by nlinarith`. Use `neg_abs_le (h₁ (δ i))` as an intermediate fact. Combine the linear relations using `[hKi i]`. Establish `hnn : ∀ i, 0 ≤ (K • h₂ + h₁) (δ i)` using `fun i => by`.

Break down `(h2δ i).lt_or_eq with hi | hi` into its components or cases. Conclude with `(hpos i hi).le`. Rewrite using `[happ, ← hi, mul_zero, zero_add]`. Conclude with `InRCone.apply_nonneg (hf2 _ (hδb i) (hδp i) (inRCone_self δ i) hi.symm) h₁ h1γ`. Establish `h2γ' : ∀ j, h₂ (γ' j) = 0` using `fun j => le_antisymm (by`.

Use `InRCone.apply_nonneg (hγ' j) (-h₂) (fun k => by simp [h2γ k])` as an intermediate fact. Simplify using `using this)`. Use the proof step `(InRCone.apply_nonneg (hγ' j) h₂ (fun k => (h2γ k).ge))`. Use `⟨K • h₂ + h₁, hnn, fun j => by rw [happ, h2γ' j, h1γ' j]; ring, ?_⟩` and prove the remaining obligations. Introduce `β hb hp hc hz`.

Establish `h2β : h₂ β = 0`. Take `⟨c, hc0, e⟩` from `hc`. Establish `eh` using `apply_eq_of_toReal_eq e (K • h₂ + h₁)`. Establish `e2` using `apply_eq_of_toReal_eq e h₂`. Rewrite `eh` using `[hz, Int.cast_zero]`.

Establish `hterm : ∀ i ∈ Finset.univ, 0 ≤ c i * ((K • h₂ + h₁) (δ i) : ℝ)` using `fun i _ => mul_nonneg (hc0 i) (by exact_mod_cast hnn i)`. Establish `hall` using `(Finset.sum_eq_zero_iff_of_nonneg hterm).1 eh.symm`. Establish `hs : ∑ i, c i * (h₂ (δ i) : ℝ) = 0` using `Finset.sum_eq_zero fun i _ => by`. Break down `(h2δ i).lt_or_eq with hi | hi` into its components or cases. Establish `h0` using `hall i (Finset.mem_univ _)`.

Establish `hp' : (0 : ℝ) < (K • h₂ + h₁) (δ i)` using `by exact_mod_cast hpos i hi`. Rewrite using `[(mul_eq_zero.1 h0).resolve_right hp'.ne', zero_mul]`. Rewrite using `[← hi]`. Simplify using the standard rewrite rules. Conclude with `e2.trans hs` after adjusting the coercions.

Establish `hγβ` using `hf2 β hb hp hc h2β`. Use `hf1 β hb hp hγβ ?_` and prove the remaining obligations. Use `happ β` as an intermediate fact. Rewrite `this` using `[hz, h2β]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_linForm_cut_face_of_face : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n p : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (γ' : Fin p → LinearMap.BilinForm ℤ X)
    (h₂ h₁ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    (∀ i, δ i ∈ balForms bar X) → (∀ i y, 0 ≤ δ i y y) → (∀ j, InRCone γ (γ' j)) →
    (∀ i, 0 ≤ h₂ (δ i)) → (∀ k, h₂ (γ k) = 0) →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → h₂ β = 0 → InRCone γ β) →
    (∀ k, 0 ≤ h₁ (γ k)) → (∀ j, h₁ (γ' j) = 0) →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h₁ β = 0 → InRCone γ' β) →
    ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ i, 0 ≤ h (δ i)) ∧ (∀ j, h (γ' j) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → h β = 0 → InRCone γ' β := by
  intro O _ bar X _ _ m n p δ γ γ' h₂ h₁ hδb hδp hγ' h2δ h2γ hf2 h1γ h1γ' hf1
  set K : ℤ := 1 + ∑ i, |h₁ (δ i)| with hK
  have hKi : ∀ i, |h₁ (δ i)| < K := fun i => by
    have := Finset.single_le_sum (f := fun i => |h₁ (δ i)|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  have hK0 : 0 ≤ K := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (h₁ (δ i)))
    linarith
  have happ : ∀ x, (K • h₂ + h₁) x = K * h₂ x + h₁ x := fun x => by simp
  have hpos : ∀ i, 0 < h₂ (δ i) → 0 < (K • h₂ + h₁) (δ i) := fun i hi => by
    rw [happ]
    have h1 : K ≤ K * h₂ (δ i) := by nlinarith
    have := neg_abs_le (h₁ (δ i))
    linarith [hKi i]
  have hnn : ∀ i, 0 ≤ (K • h₂ + h₁) (δ i) := fun i => by
    rcases (h2δ i).lt_or_eq with hi | hi
    · exact (hpos i hi).le
    · rw [happ, ← hi, mul_zero, zero_add]
      exact InRCone.apply_nonneg (hf2 _ (hδb i) (hδp i) (inRCone_self δ i) hi.symm) h₁ h1γ
  have h2γ' : ∀ j, h₂ (γ' j) = 0 := fun j => le_antisymm (by
      have := InRCone.apply_nonneg (hγ' j) (-h₂) (fun k => by simp [h2γ k])
      simpa using this)
    (InRCone.apply_nonneg (hγ' j) h₂ (fun k => (h2γ k).ge))
  refine ⟨K • h₂ + h₁, hnn, fun j => by rw [happ, h2γ' j, h1γ' j]; ring, ?_⟩
  intro β hb hp hc hz
  have h2β : h₂ β = 0 := by
    obtain ⟨c, hc0, e⟩ := hc
    have eh := apply_eq_of_toReal_eq e (K • h₂ + h₁)
    have e2 := apply_eq_of_toReal_eq e h₂
    rw [hz, Int.cast_zero] at eh
    have hterm : ∀ i ∈ Finset.univ, 0 ≤ c i * ((K • h₂ + h₁) (δ i) : ℝ) := fun i _ =>
      mul_nonneg (hc0 i) (by exact_mod_cast hnn i)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 eh.symm
    have hs : ∑ i, c i * (h₂ (δ i) : ℝ) = 0 := Finset.sum_eq_zero fun i _ => by
      rcases (h2δ i).lt_or_eq with hi | hi
      · have h0 := hall i (Finset.mem_univ _)
        have hp' : (0 : ℝ) < (K • h₂ + h₁) (δ i) := by exact_mod_cast hpos i hi
        rw [(mul_eq_zero.1 h0).resolve_right hp'.ne', zero_mul]
      · rw [← hi]; simp
    exact_mod_cast e2.trans hs
  have hγβ := hf2 β hb hp hc h2β
  refine hf1 β hb hp hγβ ?_
  have := happ β
  rw [hz, h2β] at this
  linarith

end GlobalTheory.PolFan
