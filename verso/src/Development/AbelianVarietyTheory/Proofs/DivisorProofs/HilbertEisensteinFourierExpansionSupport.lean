import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumNatCastEq

set_option autoImplicit false

noncomputable section

open NumberField
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion qClass qRel)
open GlobalTheory.PairFourier (pairPt pairCoef qClass_eq tsum_natCast_eq pairPt_ne_zero)

namespace GlobalTheory.HilbFam

/- English proof (translation)
Introduce `F _ _ _ k 𝔞 𝔟 G hG`. Take `⟨Z, hZ, hE⟩` from `hG`. Use `set C : ℂ := (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) with hC`. Set `p : Quotient (qRel 𝔞 𝔟) → F` to `fun c ↦ (pairPt 𝔞 𝔟 c : F)`. Set `a' : F → ℂ` to `fun ξ ↦ ∑' c : p ⁻¹' {ξ}, (pairCoef 𝔞 𝔟 k c : ℂ)`.

Establish `ha' : ∀ ξ, a' ξ = ∑' c : p ⁻¹' {ξ}, (pairCoef 𝔞 𝔟 k c : ℂ)` using `fun _ ↦ rfl`. Establish `hfib : ∀ (z : Emb F → ℂ) (ξ : F) (c : p ⁻¹' {ξ}), qClass 𝔞 𝔟 k z c = (pairCoef 𝔞 𝔟 k c : ℂ) * qPow ξ z`. Introduce and unpack `z ξ ⟨c, hc⟩`. Rewrite `hc` using `[Set.mem_preimage, Set.mem_singleton_iff]`. Substitute `hc` using the available equality.

Conclude with `qClass_eq 𝔞 𝔟 k z c`. Use `⟨Z, fun ξ ↦ a' ξ + if ξ = 0 then C else 0, hZ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show a' 0 + (if (0 : F) = 0 then C else 0) = C`. Rewrite using `[if_pos rfl]`. Establish `: IsEmpty (p ⁻¹' {0})` using `⟨fun ⟨c, hc⟩ ↦ pairPt_ne_zero 𝔞 𝔟 c (Subtype.ext (Set.mem_singleton_iff.1 (Set.mem_preimage.1 hc)))⟩`.

Rewrite using `[ha']`. Simplify using `only [tsum_empty, zero_add]`. Introduce `ξ hξ set z₀ : Emb F → ℂ := fun _ ↦ Complex.I`. Establish `hz₀ : z₀ ∈ upperHalf F` using `fun _ ↦ by simp [z₀]`. Establish `hq : qPow ξ z₀ ≠ 0` using `Complex.exp_ne_zero _`.

Establish `hsum : Summable (fun c : p ⁻¹' {ξ} ↦ (pairCoef 𝔞 𝔟 k c : ℂ))`. Use `((hE z₀ hz₀).1.subtype (p ⁻¹' {ξ})).mul_right (qPow ξ z₀)⁻¹` as an intermediate fact. Use `this.congr fun c ↦ ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[hfib z₀ ξ c, mul_assoc, mul_inv_cancel₀ hq, mul_one]`.

Take `⟨m, hm⟩` from `tsum_natCast_eq _ hsum`. Use `⟨m, ?_⟩` and prove the remaining obligations. Use `show a' ξ + (if ξ = 0 then C else 0) = _`. Rewrite using `[if_neg hξ, add_zero, ha']`. Simplify using `only [hm]`.

Simplify using the standard rewrite rules. Introduce `ξ hξ hne`. Establish `hne' : a' ξ ≠ 0`. Introduce `h`. Apply `hne` to reduce the goal to its premises.

Use `show a' ξ + (if ξ = 0 then C else 0) = 0`. Rewrite using `[if_neg hξ, h, add_zero]`. Distinguish the cases in `hem : IsEmpty (p ⁻¹' {ξ})`. Conclude with `absurd (by rw [ha']; exact tsum_empty) hne'`. Take `⟨c, hc⟩` from `not_isEmpty_iff.1 hem`.

Rewrite `hc` using `[Set.mem_preimage, Set.mem_singleton_iff]`. Substitute `hc` using the available equality. Conclude with `⟨(pairPt 𝔞 𝔟 c).2, c.out.2.2.2⟩`. Introduce `z hz`. Take `⟨hs, heq⟩` from `hE z hz`.

Establish `h1` using `hs.hasSum.tsum_fiberwise p`. Establish `h2 : (fun ξ ↦ ∑' c : p ⁻¹' {ξ}, qClass 𝔞 𝔟 k z c) = fun ξ ↦ a' ξ * qPow ξ z`. Use function extensionality and compare the values at `ξ`. Rewrite using `[ha', ← tsum_mul_right]`. Conclude with `tsum_congr (hfib z ξ)`.

Rewrite `h1` using `[h2]`. Establish `h3 : HasSum (fun ξ : F ↦ (if ξ = 0 then C else 0) * qPow ξ z) C`. Use `hasSum_ite_eq (0 : F) C using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `ξ`. Use `split_ifs with h`.

Substitute `h` using the available equality. Simplify using `[qPow]`. Simplify using the standard rewrite rules. Establish `hv : (cK F k : ℂ) * G z / (omegaFactor 𝔞 : ℂ) ^ k = (∑' c, qClass 𝔞 𝔟 k z c) + C` using `by rw [heq]; ring`. Use `show HasSum (fun ξ : F ↦ (a' ξ + if ξ = 0 then C else 0) * qPow ξ z) ((cK F k : ℂ) * G z / (omegaFactor 𝔞 : ℂ) ^ k)`.

Rewrite using `[hv]`. Simplify using `only [add_mul]`. Conclude with `h1.add h3`.
-/
theorem fourier_with_support :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (G : (Emb F → ℂ) → ℂ),
      HasExpansion 𝔞 𝔟 k G → ∃ (Z : ℂ → ℂ) (a : F → ℂ), IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧
        a 0 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) ∧ (∀ ξ, ξ ≠ 0 → ∃ n : ℤ, a ξ = n) ∧
        (∀ ξ, ξ ≠ 0 → a ξ ≠ 0 → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ i : Emb F, 0 < i ξ) ∧
        ∀ w ∈ upperHalf F, HasSum (fun ξ : F ↦ a ξ * qPow ξ w)
          ((cK F k : ℂ) * G w / (omegaFactor 𝔞 : ℂ) ^ k) := by
  classical
  intro F _ _ _ k 𝔞 𝔟 G hG
  obtain ⟨Z, hZ, hE⟩ := hG
  set C : ℂ := (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) with hC
  let p : Quotient (qRel 𝔞 𝔟) → F := fun c ↦ (pairPt 𝔞 𝔟 c : F)
  let a' : F → ℂ := fun ξ ↦ ∑' c : p ⁻¹' {ξ}, (pairCoef 𝔞 𝔟 k c : ℂ)
  have ha' : ∀ ξ, a' ξ = ∑' c : p ⁻¹' {ξ}, (pairCoef 𝔞 𝔟 k c : ℂ) := fun _ ↦ rfl
  have hfib : ∀ (z : Emb F → ℂ) (ξ : F) (c : p ⁻¹' {ξ}),
      qClass 𝔞 𝔟 k z c = (pairCoef 𝔞 𝔟 k c : ℂ) * qPow ξ z := by
    rintro z ξ ⟨c, hc⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hc
    subst hc
    exact qClass_eq 𝔞 𝔟 k z c
  refine ⟨Z, fun ξ ↦ a' ξ + if ξ = 0 then C else 0, hZ, ?_, ?_, ?_, ?_⟩
  · show a' 0 + (if (0 : F) = 0 then C else 0) = C
    rw [if_pos rfl]
    have : IsEmpty (p ⁻¹' {0}) :=
      ⟨fun ⟨c, hc⟩ ↦ pairPt_ne_zero 𝔞 𝔟 c
        (Subtype.ext (Set.mem_singleton_iff.1 (Set.mem_preimage.1 hc)))⟩
    rw [ha']
    simp only [tsum_empty, zero_add]
  · intro ξ hξ
    set z₀ : Emb F → ℂ := fun _ ↦ Complex.I
    have hz₀ : z₀ ∈ upperHalf F := fun _ ↦ by simp [z₀]
    have hq : qPow ξ z₀ ≠ 0 := Complex.exp_ne_zero _
    have hsum : Summable (fun c : p ⁻¹' {ξ} ↦ (pairCoef 𝔞 𝔟 k c : ℂ)) := by
      have := ((hE z₀ hz₀).1.subtype (p ⁻¹' {ξ})).mul_right (qPow ξ z₀)⁻¹
      refine this.congr fun c ↦ ?_
      simp only [Function.comp_apply]
      rw [hfib z₀ ξ c, mul_assoc, mul_inv_cancel₀ hq, mul_one]
    obtain ⟨m, hm⟩ := tsum_natCast_eq _ hsum
    refine ⟨m, ?_⟩
    show a' ξ + (if ξ = 0 then C else 0) = _
    rw [if_neg hξ, add_zero, ha']
    simp only [hm]
    simp
  · intro ξ hξ hne
    have hne' : a' ξ ≠ 0 := by
      intro h
      apply hne
      show a' ξ + (if ξ = 0 then C else 0) = 0
      rw [if_neg hξ, h, add_zero]
    by_cases hem : IsEmpty (p ⁻¹' {ξ})
    · exact absurd (by rw [ha']; exact tsum_empty) hne'
    obtain ⟨c, hc⟩ := not_isEmpty_iff.1 hem
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hc
    subst hc
    exact ⟨(pairPt 𝔞 𝔟 c).2, c.out.2.2.2⟩
  · intro z hz
    obtain ⟨hs, heq⟩ := hE z hz
    have h1 := hs.hasSum.tsum_fiberwise p
    have h2 : (fun ξ ↦ ∑' c : p ⁻¹' {ξ}, qClass 𝔞 𝔟 k z c) = fun ξ ↦ a' ξ * qPow ξ z := by
      funext ξ
      rw [ha', ← tsum_mul_right]
      exact tsum_congr (hfib z ξ)
    rw [h2] at h1
    have h3 : HasSum (fun ξ : F ↦ (if ξ = 0 then C else 0) * qPow ξ z) C := by
      convert hasSum_ite_eq (0 : F) C using 1
      funext ξ
      split_ifs with h
      · subst h; simp [qPow]
      · simp
    have hv : (cK F k : ℂ) * G z / (omegaFactor 𝔞 : ℂ) ^ k =
        (∑' c, qClass 𝔞 𝔟 k z c) + C := by rw [heq]; ring
    show HasSum (fun ξ : F ↦ (a' ξ + if ξ = 0 then C else 0) * qPow ξ z)
      ((cK F k : ℂ) * G z / (omegaFactor 𝔞 : ℂ) ^ k)
    rw [hv]
    simp only [add_mul]
    exact h1.add h3

end GlobalTheory.HilbFam
