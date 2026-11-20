import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinB
import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts ComplexConjugate
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def etil (ν : Y →ₗ[ℤ] ℤ) (a : Y) : E :=
  ∑ k, ((ν (RingOfIntegers.basis E k • a) : ℤ) : E) * ed E k

/- English proof (translation)
Unfold `comp etil`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[map_mul, map_intCast]`.
-/
theorem comp_int (ν : Y →ₗ[ℤ] ℤ) (σ : E →+* ℂ) (a : Y) :
    comp (Algebra.linearMap ℤ ℝ ∘ₗ ν) σ a = σ (etil ν a) := by
  unfold comp etil
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [map_mul, map_intCast]

/- English proof (translation)
Use `show etil ν a ∈ ((Dinv E : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)`. Unfold `etil`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zsmul_eq_mul]`. Conclude with `zsmul_mem (FractionalIdeal.mem_coe.mpr (ed_mem k)) _`.
-/
theorem etil_mem (ν : Y →ₗ[ℤ] ℤ) (a : Y) : etil ν a ∈ Dinv E := by
  show etil ν a ∈ ((Dinv E : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)
  unfold etil
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [← zsmul_eq_mul]
  exact zsmul_mem (FractionalIdeal.mem_coe.mpr (ed_mem k)) _

/- English proof (translation)
Establish `hcj' : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = conj (φ z)` using `fun φ z => hcj φ z`. Establish `hadd1 : ∀ a a' b : Y, (comp η σ (a + a') * conj (comp η σ b)).re = (comp η σ a * conj (comp η σ b)).re + (comp η σ a' * conj (comp η σ b)).re`. Introduce `a a' b`. Rewrite using `[comp_add, add_mul, Complex.add_re]`. Establish `hadd2 : ∀ a b b' : Y, (comp η σ a * conj (comp η σ (b + b'))).re = (comp η σ a * conj (comp η σ b)).re + (comp η σ a * conj (comp η σ b')).re`.

Introduce `a b b'`. Rewrite using `[comp_add, map_add, mul_add, Complex.add_re]`. Set `β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ` to `(AddMonoidHom.mk' (fun a => (AddMonoidHom.mk' (fun b => (comp η σ a * conj (comp η σ b)).re) (hadd2 a)).toIntLinearMap) (fun a a' => LinearMap.ext fun b => hadd1 a a' b)).toIntLinearMap`. Establish `hβ : ∀ a b, β a b = (comp η σ a * conj (comp η σ b)).re` using `fun a b => rfl`. Establish `hsq : ∀ a, (comp η σ a * conj (comp η σ a)).re = Complex.normSq (comp η σ a)`.

Introduce `a`. Use `first`. Consider the case `(rw [Complex.mul_conj, Complex.ofReal_re])`. Consider the case `(simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]; ring)`. Establish `hmem : β ∈ SymB cj Y` using `by show _ ∧ _`.

Use `⟨fun a b => ?_, fun c c' hc a b => ?_⟩` and prove the remaining obligations. Rewrite using `[hβ, hβ]`. Simplify using `only [Complex.mul_re, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hβ, hβ, comp_smul, comp_smul, map_mul, hc, hcj', Complex.conj_conj]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hpsd : ∀ a, 0 ≤ ((⟨β, hmem⟩ : SymB cj Y) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a`. Introduce `a`. Use `show 0 ≤ β a a`.

Rewrite using `[hβ, hsq]`. Conclude with `Complex.normSq_nonneg _`. Establish `hne : (⟨β, hmem⟩ : SymB cj Y) ≠ 0`. Introduce `h`. Establish `h2 : β a₀ a₀ = 0` using `by first`.

Consider the case `exact congrArg (fun γ : SymB cj Y => (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a₀ a₀) h`. Consider the case `simpa using congrArg (fun γ : SymB cj Y => (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a₀ a₀) h`. Rewrite `h2` using `[hβ, hsq]`. Conclude with `ha₀ (Complex.normSq_eq_zero.mp h2)`. Establish `hl : l ⟨β, hmem⟩ = ∑ i, (comp η σ (x i) * conj (comp η σ (x' i))).re` using `(htie _).trans (Finset.sum_congr rfl fun i _ => hβ _ _)`.

Rewrite using `[← hl]`. Conclude with `hpos _ hpsd hne`.
-/
private theorem pos_lemma {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
    (l : SymB cj Y →ₗ[ℝ] ℝ)
    (hpos : ∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β)
    {m : ℕ} (x x' : Fin m → Y)
    (htie : ∀ β : SymB cj Y, l β = ∑ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x' i))
    (η : Y →ₗ[ℤ] ℝ) (σ : E →+* ℂ) (a₀ : Y) (ha₀ : comp η σ a₀ ≠ 0) :
    0 < ∑ i, (comp η σ (x i) * conj (comp η σ (x' i))).re := by
  have hcj' : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = conj (φ z) := fun φ z => hcj φ z
  have hadd1 : ∀ a a' b : Y, (comp η σ (a + a') * conj (comp η σ b)).re =
      (comp η σ a * conj (comp η σ b)).re + (comp η σ a' * conj (comp η σ b)).re := by
    intro a a' b
    rw [comp_add, add_mul, Complex.add_re]
  have hadd2 : ∀ a b b' : Y, (comp η σ a * conj (comp η σ (b + b'))).re =
      (comp η σ a * conj (comp η σ b)).re + (comp η σ a * conj (comp η σ b')).re := by
    intro a b b'
    rw [comp_add, map_add, mul_add, Complex.add_re]
  let β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ :=
    (AddMonoidHom.mk' (fun a => (AddMonoidHom.mk' (fun b => (comp η σ a * conj (comp η σ b)).re)
      (hadd2 a)).toIntLinearMap) (fun a a' => LinearMap.ext fun b => hadd1 a a' b)).toIntLinearMap
  have hβ : ∀ a b, β a b = (comp η σ a * conj (comp η σ b)).re := fun a b => rfl
  have hsq : ∀ a, (comp η σ a * conj (comp η σ a)).re = Complex.normSq (comp η σ a) := by
    intro a
    first
      | (rw [Complex.mul_conj, Complex.ofReal_re])
      | (simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]; ring)
  have hmem : β ∈ SymB cj Y := by
    show _ ∧ _
    refine ⟨fun a b => ?_, fun c c' hc a b => ?_⟩
    · rw [hβ, hβ]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    · rw [hβ, hβ, comp_smul, comp_smul, map_mul, hc, hcj', Complex.conj_conj]
      congr 1
      ring
  have hpsd : ∀ a, 0 ≤ ((⟨β, hmem⟩ : SymB cj Y) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a := by
    intro a
    show 0 ≤ β a a
    rw [hβ, hsq]
    exact Complex.normSq_nonneg _
  have hne : (⟨β, hmem⟩ : SymB cj Y) ≠ 0 := by
    intro h
    have h2 : β a₀ a₀ = 0 := by
      first
        | exact congrArg (fun γ : SymB cj Y => (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a₀ a₀) h
        | simpa using congrArg (fun γ : SymB cj Y => (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a₀ a₀) h
    rw [hβ, hsq] at h2
    exact ha₀ (Complex.normSq_eq_zero.mp h2)
  have hl : l ⟨β, hmem⟩ = ∑ i, (comp η σ (x i) * conj (comp η σ (x' i))).re :=
    (htie _).trans (Finset.sum_congr rfl fun i _ => hβ _ _)
  rw [← hl]
  exact hpos _ hpsd hne

/- English proof (translation)
Establish `h : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = (Dinv E)⁻¹` using `by first`. Consider the case `exact coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E)`. Consider the case `exact coeIdeal_differentIdeal ℤ ℚ`. Consider the case `exact coeIdeal_differentIdeal ℤ ℚ (𝓞 E) E`. Establish `h3 : FractionalIdeal.absNorm ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = ((discr E).natAbs : ℚ)` using `by first`.

Consider the case `(rw [FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal])`. Consider the case `(rw [FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal (K := E)])`. Consider the case `(rw [FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal E])`. Consider the case `(rw [FractionalIdeal.coeIdeal_absNorm]; exact_mod_cast NumberField.absNorm_differentIdeal)`. Rewrite `h3` using `[h, map_inv₀]`.

Establish `hdinv : FractionalIdeal.absNorm (Dinv E) = ((discr E).natAbs : ℚ)⁻¹`. Rewrite using `[← h3, inv_inv]`. Apply the tactic sequence `have hd : discr E ≠ 0 := by first | exact NumberField.discr_ne_zero E | exact NumberField.discr_ne_zero`. Establish `hd' : ((discr E).natAbs : ℚ) ≠ 0`. Conclude with `Int.natAbs_ne_zero.mpr hd` after adjusting the coercions.

Establish `hD : Dinv E ≠ 0`. Introduce `h0`. Rewrite `hdinv` using `[h0, map_zero]`. Conclude with `hd' (inv_eq_zero.mp hdinv.symm)`. Establish `hD2 : Dinv E * Dinv E ≠ 0` using `mul_ne_zero hD hD`.

Establish `hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ t ≤ Dinv E * Dinv E` using `FractionalIdeal.spanSingleton_le_iff_mem.mpr ht`. Take `⟨J, hJ⟩ : ∃ J, J = (Dinv E * Dinv E)⁻¹ * FractionalIdeal.spanSingleton (𝓞 E)⁰ t` from `⟨_, rfl⟩`. Establish `hspan : FractionalIdeal.spanSingleton (𝓞 E)⁰ t = (Dinv E * Dinv E) * J`. Rewrite using `[hJ, mul_inv_cancel_left₀ hD2]`. Establish `hJ1 : J ≤ 1`.

Rewrite using `[hJ]`. Combine the equalities or inequalities in the displayed calculation. Consider the case `exact mul_le_mul_left' hle _`. Consider the case `exact FractionalIdeal.mul_le_mul_left hle _`. Consider the case `exact mul_right_mono hle`.

Consider the case `exact mul_le_mul_left hle _`. Consider the case `(rw [mul_comm _ (FractionalIdeal.spanSingleton (𝓞 E)⁰ t), mul_comm _ (Dinv E * Dinv E)];`. Conclude with `mul_left_mono hle)`. Use `_ = 1 := inv_mul_cancel₀ hD2`. Take `⟨I, hI⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ1`.

Establish `hJ0 : J ≠ 0`. Introduce `h0`. Rewrite `hspan` using `[h0, mul_zero]`. Conclude with `ht0 (FractionalIdeal.spanSingleton_eq_zero_iff.mp hspan)`. Establish `hI0 : I ≠ ⊥`.

Introduce and unpack `rfl`. Apply `hJ0` to reduce the goal to its premises. Rewrite using `[← hI]`. Apply the tactic sequence `first | exact FractionalIdeal.coeIdeal_bot | simp`. Establish `hJn : (1 : ℚ) ≤ FractionalIdeal.absNorm J`.

Rewrite using `[← hI]`. Establish `hI1 : 1 ≤ Ideal.absNorm I` using `Nat.one_le_iff_ne_zero.mpr (fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h))`. Use `first`. Consider the case `(rw [FractionalIdeal.coeIdeal_absNorm]; exact_mod_cast hI1)`. Consider the case `(rw [FractionalIdeal.absNorm_eq' 1 I (by first | (rw [one_smul]; rfl) | simp [IsLocalization.coeSubmodule] | rfl)]; simp; exact_mod_cast hI1)`.

Establish `h1 : |Algebra.norm ℚ t| = FractionalIdeal.absNorm (Dinv E * Dinv E) * FractionalIdeal.absNorm J`. Rewrite using `[← map_mul, ← hspan]`. Use `first`. Consider the case `exact (FractionalIdeal.absNorm_span_singleton (R := 𝓞 E) t).symm`. Consider the case `exact (FractionalIdeal.absNorm_span_singleton t).symm`.

Establish `h2 : FractionalIdeal.absNorm (Dinv E * Dinv E) = (((discr E).natAbs : ℚ) ^ 2)⁻¹`. Rewrite using `[map_mul, hdinv, sq, mul_inv]`. Rewrite using `[h1, h2]`. Establish `h4 : (0 : ℚ) ≤ (((discr E).natAbs : ℚ) ^ 2)⁻¹` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem normb_lemma_2 {t : E} (ht : t ∈ Dinv E * Dinv E) (ht0 : t ≠ 0) :
    (((discr E).natAbs : ℚ) ^ 2)⁻¹ ≤ |Algebra.norm ℚ t| := by
  have h : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = (Dinv E)⁻¹ := by
    first
      | exact coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E)
      | exact coeIdeal_differentIdeal ℤ ℚ
      | exact coeIdeal_differentIdeal ℤ ℚ (𝓞 E) E
  have h3 : FractionalIdeal.absNorm ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (𝓞 E)⁰ E) = ((discr E).natAbs : ℚ) := by
    first
      | (rw [FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal])
      | (rw [FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal (K := E)])
      | (rw [FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal E])
      | (rw [FractionalIdeal.coeIdeal_absNorm]; exact_mod_cast NumberField.absNorm_differentIdeal)
  rw [h, map_inv₀] at h3
  have hdinv : FractionalIdeal.absNorm (Dinv E) = ((discr E).natAbs : ℚ)⁻¹ := by
    rw [← h3, inv_inv]
  have hd : discr E ≠ 0 := by
    first | exact NumberField.discr_ne_zero E | exact NumberField.discr_ne_zero
  have hd' : ((discr E).natAbs : ℚ) ≠ 0 := by
    exact_mod_cast Int.natAbs_ne_zero.mpr hd
  have hD : Dinv E ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hdinv
    exact hd' (inv_eq_zero.mp hdinv.symm)
  have hD2 : Dinv E * Dinv E ≠ 0 := mul_ne_zero hD hD
  have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ t ≤ Dinv E * Dinv E :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr ht
  obtain ⟨J, hJ⟩ : ∃ J, J = (Dinv E * Dinv E)⁻¹ * FractionalIdeal.spanSingleton (𝓞 E)⁰ t :=
    ⟨_, rfl⟩
  have hspan : FractionalIdeal.spanSingleton (𝓞 E)⁰ t = (Dinv E * Dinv E) * J := by
    rw [hJ, mul_inv_cancel_left₀ hD2]
  have hJ1 : J ≤ 1 := by
    rw [hJ]
    calc (Dinv E * Dinv E)⁻¹ * FractionalIdeal.spanSingleton (𝓞 E)⁰ t
        ≤ (Dinv E * Dinv E)⁻¹ * (Dinv E * Dinv E) := by
          first
            | exact mul_le_mul_left' hle _
            | exact FractionalIdeal.mul_le_mul_left hle _
            | exact mul_right_mono hle
            | exact mul_le_mul_left hle _
            | (rw [mul_comm _ (FractionalIdeal.spanSingleton (𝓞 E)⁰ t), mul_comm _ (Dinv E * Dinv E)];
               exact mul_left_mono hle)
      _ = 1 := inv_mul_cancel₀ hD2
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ1
  have hJ0 : J ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hspan
    exact ht0 (FractionalIdeal.spanSingleton_eq_zero_iff.mp hspan)
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hJ0
    rw [← hI]
    first | exact FractionalIdeal.coeIdeal_bot | simp
  have hJn : (1 : ℚ) ≤ FractionalIdeal.absNorm J := by
    rw [← hI]
    have hI1 : 1 ≤ Ideal.absNorm I :=
      Nat.one_le_iff_ne_zero.mpr (fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h))
    first
      | (rw [FractionalIdeal.coeIdeal_absNorm]; exact_mod_cast hI1)
      | (rw [FractionalIdeal.absNorm_eq' 1 I (by first | (rw [one_smul]; rfl) | simp [IsLocalization.coeSubmodule] | rfl)]; simp; exact_mod_cast hI1)
  have h1 : |Algebra.norm ℚ t| =
      FractionalIdeal.absNorm (Dinv E * Dinv E) * FractionalIdeal.absNorm J := by
    rw [← map_mul, ← hspan]
    first
      | exact (FractionalIdeal.absNorm_span_singleton (R := 𝓞 E) t).symm
      | exact (FractionalIdeal.absNorm_span_singleton t).symm
  have h2 : FractionalIdeal.absNorm (Dinv E * Dinv E) = (((discr E).natAbs : ℚ) ^ 2)⁻¹ := by
    rw [map_mul, hdinv, sq, mul_inv]
  rw [h1, h2]
  have h4 : (0 : ℚ) ≤ (((discr E).natAbs : ℚ) ^ 2)⁻¹ := by positivity
  calc (((discr E).natAbs : ℚ) ^ 2)⁻¹ = (((discr E).natAbs : ℚ) ^ 2)⁻¹ * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hJn h4

/- English proof (translation)
Establish `hcard : (Fintype.card (E →+* ℂ) : ℝ) = finrank ℚ E`. Rewrite using `[NumberField.Embeddings.card]`. Apply the tactic sequence `have hn : (0 : ℝ) < finrank ℚ E := by first | exact_mod_cast Module.finrank_pos | exact_mod_cast FiniteDimensional.finrank_pos`. Establish `hn' : (finrank ℚ E : ℝ) ≠ 0` using `hn.ne'`. Establish `hsum : ∑ _σ : E →+* ℂ, (1 : ℝ) / finrank ℚ E = 1`.

Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, mul_one_div_cancel hn']`. Establish `h : ∏ σ, w σ ^ ((1 : ℝ) / finrank ℚ E) ≤ ∑ σ, (1 : ℝ) / finrank ℚ E * w σ` using `Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (1 : ℝ) / finrank ℚ E) w (fun _ _ => by positivity) hsum (fun σ _ => hw σ)`. Rewrite `h` using `[Real.finset_prod_rpow _ _ (fun σ _ => hw σ), ← Finset.mul_sum]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem amgm_lemma_3 (w : (E →+* ℂ) → ℝ) (hw : ∀ σ, 0 ≤ w σ) :
    (finrank ℚ E : ℝ) * (∏ σ, w σ) ^ ((1 : ℝ) / finrank ℚ E) ≤ ∑ σ, w σ := by
  have hcard : (Fintype.card (E →+* ℂ) : ℝ) = finrank ℚ E := by
    rw [NumberField.Embeddings.card]
  have hn : (0 : ℝ) < finrank ℚ E := by
    first | exact_mod_cast Module.finrank_pos | exact_mod_cast FiniteDimensional.finrank_pos
  have hn' : (finrank ℚ E : ℝ) ≠ 0 := hn.ne'
  have hsum : ∑ _σ : E →+* ℂ, (1 : ℝ) / finrank ℚ E = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, mul_one_div_cancel hn']
  have h : ∏ σ, w σ ^ ((1 : ℝ) / finrank ℚ E) ≤ ∑ σ, (1 : ℝ) / finrank ℚ E * w σ :=
    Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (1 : ℝ) / finrank ℚ E) w
      (fun _ _ => by positivity) hsum (fun σ _ => hw σ)
  rw [Real.finset_prod_rpow _ _ (fun σ _ => hw σ), ← Finset.mul_sum] at h
  calc (finrank ℚ E : ℝ) * (∏ σ, w σ) ^ ((1 : ℝ) / finrank ℚ E)
      ≤ (finrank ℚ E : ℝ) * ((1 : ℝ) / finrank ℚ E * ∑ σ, w σ) :=
        mul_le_mul_of_nonneg_left h hn.le
    _ = ∑ σ, w σ := by rw [← mul_assoc, mul_one_div_cancel hn', one_mul]

/- English proof (translation)
Establish `h : algebraMap ℚ ℂ (Algebra.norm ℚ t) = ∏ σ : E →ₐ[ℚ] ℂ, σ t` using `by first`. Consider the case `exact Algebra.norm_eq_prod_embeddings ℚ ℂ t`. Consider the case `exact Algebra.norm_eq_prod_embeddings (K := ℚ) (E := ℂ) t`. Consider the case `exact Algebra.norm_eq_prod_embeddings t`. Establish `h2 : (∏ σ : E →ₐ[ℚ] ℂ, σ t) = ∏ σ : E →+* ℂ, σ t` using `Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)`.

Rewrite `h` using `[h2, Finset.prod_congr rfl (fun σ _ => hw σ), ← Complex.ofReal_prod]`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[← h]`. Apply the tactic sequence `first | simp | (rw [eq_ratCast]; simp) | norm_cast`.
-/
private theorem normprod_lemma_4 (t : E) (w : (E →+* ℂ) → ℝ) (hw : ∀ σ : E →+* ℂ, σ t = (w σ : ℂ)) :
    ((Algebra.norm ℚ t : ℚ) : ℝ) = ∏ σ, w σ := by
  have h : algebraMap ℚ ℂ (Algebra.norm ℚ t) = ∏ σ : E →ₐ[ℚ] ℂ, σ t := by
    first
      | exact Algebra.norm_eq_prod_embeddings ℚ ℂ t
      | exact Algebra.norm_eq_prod_embeddings (K := ℚ) (E := ℂ) t
      | exact Algebra.norm_eq_prod_embeddings t
  have h2 : (∏ σ : E →ₐ[ℚ] ℂ, σ t) = ∏ σ : E →+* ℂ, σ t :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)
  rw [h2, Finset.prod_congr rfl (fun σ _ => hw σ), ← Complex.ofReal_prod] at h
  apply Complex.ofReal_injective
  rw [← h]
  first | simp | (rw [eq_ratCast]; simp) | norm_cast

/- English proof (translation)
Establish `hv : ∀ (σ : E →+* ℂ) (a : Y), comp (Algebra.linearMap ℤ ℝ ∘ₗ ν) σ a = σ (etil ν a)` using `fun σ a => comp_int ν σ a`. Establish `hcj' : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = conj (φ z)` using `fun φ z => hcj φ z`. Establish `hη : (Algebra.linearMap ℤ ℝ ∘ₗ ν) ≠ 0`. Introduce `h`. Apply `hν` to reduce the goal to its premises.

Use extensionality with `a`. Simplify using `using LinearMap.congr_fun h a`. Choose the witnesses or unpack the hypotheses as in `⟨a₀, ha₀⟩ : ∃ a, (etil ν a : E) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Apply the tactic sequence `have hP : Pm hcj (Algebra.linearMap ℤ ℝ ∘ₗ ν) (Algebra.linearMap ℤ ℝ ∘ₗ ν) ≠ 0 := by first | exact Pm_ne_zero hcj hη | exact Pm_ne_zero hη`. Apply `hP` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearMap.ext₂` to reduce the goal to its premises. Introduce `a c`.

Simplify using `[Pm_apply, Pf, hv, hcon]`. Establish `hne : Nonempty (E →+* ℂ)`. Rewrite using `[← Fintype.card_pos_iff, NumberField.Embeddings.card]`. Apply the tactic sequence `first | exact Module.finrank_pos | exact FiniteDimensional.finrank_pos`. Take `⟨L, hL⟩ : ∃ L : (E →+* ℂ) → ℝ, ∀ σ, L σ = ∑ i, (comp (Algebra.linearMap ℤ ℝ ∘ₗ ν) σ (x i) * conj (comp (Algebra.linearMap ℤ ℝ ∘ₗ ν) σ (x' i))).re` from `⟨_, fun _ => rfl⟩`.

Establish `hLpos : ∀ σ, 0 < L σ`. Introduce `σ`. Rewrite using `[hL]`. Conclude with `pos_lemma hcj l hpos x x' htie _ σ a₀ (by rw [hv]; exact (map_ne_zero σ).mpr ha₀)`. Establish `hlP : l (Pm hcj (Algebra.linearMap ℤ ℝ ∘ₗ ν) (Algebra.linearMap ℤ ℝ ∘ₗ ν)) = ∑ σ, 2 * L σ`.

Rewrite using `[htie]`. Simplify using `only [Pm_apply, Pf, Complex.re_sum, Complex.add_re]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[hL, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Take `⟨t, ht⟩ : ∃ t : E, t = ∑ i, (etil ν (x i) * cj (etil ν (x' i)) + cj (etil ν (x i)) * etil ν (x' i))` from `⟨_, rfl⟩`. Establish `htσ : ∀ σ : E →+* ℂ, σ t = ((2 * L σ : ℝ) : ℂ)`. Introduce `σ`.

Rewrite using `[ht, hL, Finset.mul_sum, Complex.ofReal_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, hcj', hcj', hv, hv]`. Apply the tactic sequence `apply Complex.ext <;>`. Apply the tactic sequence `simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring`.

Establish `htmem : t ∈ Dinv E * Dinv E`. Rewrite using `[ht]`. Use `FractionalIdeal.mem_coe.mp (Submodule.sum_mem _ fun i _ => Submodule.add_mem _ ?_ ?_)` and prove the remaining obligations. Conclude with `FractionalIdeal.mem_coe.mpr (FractionalIdeal.mul_mem_mul (etil_mem ν (x i)) (cj_mem_Dinv hcj (etil_mem ν (x' i))))`. Conclude with `FractionalIdeal.mem_coe.mpr (FractionalIdeal.mul_mem_mul (cj_mem_Dinv hcj (etil_mem ν (x i))) (etil_mem ν (x' i)))`.

Establish `ht0 : t ≠ 0`. Introduce `h0`. Take `⟨φ⟩` from `hne`. Establish `h1` using `htσ φ`. Rewrite `h1` using `[h0, map_zero]`.

Establish `h2 : (2 * L φ : ℝ) = 0` using `by exact_mod_cast h1.symm`. Combine the linear relations using `[hLpos φ]`. Establish `hN : ((Algebra.norm ℚ t : ℚ) : ℝ) = ∏ σ, 2 * L σ` using `normprod_lemma_4 t (fun σ => 2 * L σ) htσ`. Establish `hprod : 0 < ∏ σ, 2 * L σ` using `Finset.prod_pos (fun σ _ => by linarith [hLpos σ])`. Establish `hB : ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ≤ ∏ σ, 2 * L σ`.

Establish `h1` using `(Rat.cast_le (K := ℝ)).mpr (normb_lemma_2 htmem ht0)`. Rewrite `h1` using `[Rat.cast_abs, hN, abs_of_pos hprod]`. Simplify using `using h1`. Rewrite using `[hlP]`. Establish `hn : (0 : ℝ) ≤ finrank ℚ E` using `Nat.cast_nonneg _`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ hn` to reduce the goal to its premises. Conclude with `Real.rpow_le_rpow (by positivity) hB (by positivity)`. Use `_ ≤ ∑ σ, 2 * L σ := amgm_lemma_3 (fun σ => 2 * L σ) (fun σ => by linarith [hLpos σ])`.
-/
theorem lower_bound {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
    (l : SymB cj Y →ₗ[ℝ] ℝ)
    (hpos : ∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β)
    {m : ℕ} (x x' : Fin m → Y)
    (htie : ∀ β : SymB cj Y, l β = ∑ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x' i))
    (ν : Y →ₗ[ℤ] ℤ) (hν : ν ≠ 0) :
    (finrank ℚ E : ℝ) * ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E) ≤
      l (Pm hcj (Algebra.linearMap ℤ ℝ ∘ₗ ν) (Algebra.linearMap ℤ ℝ ∘ₗ ν)) := by
  have hv : ∀ (σ : E →+* ℂ) (a : Y), comp (Algebra.linearMap ℤ ℝ ∘ₗ ν) σ a = σ (etil ν a) :=
    fun σ a => comp_int ν σ a
  have hcj' : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = conj (φ z) := fun φ z => hcj φ z
  have hη : (Algebra.linearMap ℤ ℝ ∘ₗ ν) ≠ 0 := by
    intro h
    apply hν
    ext a
    simpa using LinearMap.congr_fun h a
  obtain ⟨a₀, ha₀⟩ : ∃ a, (etil ν a : E) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hP : Pm hcj (Algebra.linearMap ℤ ℝ ∘ₗ ν) (Algebra.linearMap ℤ ℝ ∘ₗ ν) ≠ 0 := by
      first | exact Pm_ne_zero hcj hη | exact Pm_ne_zero hη
    apply hP
    apply Subtype.ext
    apply LinearMap.ext₂
    intro a c
    simp [Pm_apply, Pf, hv, hcon]
  have hne : Nonempty (E →+* ℂ) := by
    rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]
    first | exact Module.finrank_pos | exact FiniteDimensional.finrank_pos
  obtain ⟨L, hL⟩ : ∃ L : (E →+* ℂ) → ℝ, ∀ σ, L σ = ∑ i, (comp (Algebra.linearMap ℤ ℝ ∘ₗ ν) σ (x i) *
      conj (comp (Algebra.linearMap ℤ ℝ ∘ₗ ν) σ (x' i))).re := ⟨_, fun _ => rfl⟩
  have hLpos : ∀ σ, 0 < L σ := by
    intro σ
    rw [hL]
    exact pos_lemma hcj l hpos x x' htie _ σ a₀ (by rw [hv]; exact (map_ne_zero σ).mpr ha₀)
  have hlP : l (Pm hcj (Algebra.linearMap ℤ ℝ ∘ₗ ν) (Algebra.linearMap ℤ ℝ ∘ₗ ν)) =
      ∑ σ, 2 * L σ := by
    rw [htie]
    simp only [Pm_apply, Pf, Complex.re_sum, Complex.add_re]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hL, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  obtain ⟨t, ht⟩ : ∃ t : E, t = ∑ i, (etil ν (x i) * cj (etil ν (x' i)) +
      cj (etil ν (x i)) * etil ν (x' i)) := ⟨_, rfl⟩
  have htσ : ∀ σ : E →+* ℂ, σ t = ((2 * L σ : ℝ) : ℂ) := by
    intro σ
    rw [ht, hL, Finset.mul_sum, Complex.ofReal_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, map_mul, map_mul, hcj', hcj', hv, hv]
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring
  have htmem : t ∈ Dinv E * Dinv E := by
    rw [ht]
    refine FractionalIdeal.mem_coe.mp (Submodule.sum_mem _ fun i _ => Submodule.add_mem _ ?_ ?_)
    · exact FractionalIdeal.mem_coe.mpr (FractionalIdeal.mul_mem_mul (etil_mem ν (x i))
        (cj_mem_Dinv hcj (etil_mem ν (x' i))))
    · exact FractionalIdeal.mem_coe.mpr (FractionalIdeal.mul_mem_mul
        (cj_mem_Dinv hcj (etil_mem ν (x i))) (etil_mem ν (x' i)))
  have ht0 : t ≠ 0 := by
    intro h0
    obtain ⟨φ⟩ := hne
    have h1 := htσ φ
    rw [h0, map_zero] at h1
    have h2 : (2 * L φ : ℝ) = 0 := by exact_mod_cast h1.symm
    linarith [hLpos φ]
  have hN : ((Algebra.norm ℚ t : ℚ) : ℝ) = ∏ σ, 2 * L σ := normprod_lemma_4 t (fun σ => 2 * L σ) htσ
  have hprod : 0 < ∏ σ, 2 * L σ := Finset.prod_pos (fun σ _ => by linarith [hLpos σ])
  have hB : ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ≤ ∏ σ, 2 * L σ := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr (normb_lemma_2 htmem ht0)
    rw [Rat.cast_abs, hN, abs_of_pos hprod] at h1
    simpa using h1
  rw [hlP]
  have hn : (0 : ℝ) ≤ finrank ℚ E := Nat.cast_nonneg _
  calc (finrank ℚ E : ℝ) * ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E)
      ≤ (finrank ℚ E : ℝ) * (∏ σ, 2 * L σ) ^ ((1 : ℝ) / finrank ℚ E) := by
        apply mul_le_mul_of_nonneg_left _ hn
        exact Real.rpow_le_rpow (by positivity) hB (by positivity)
    _ ≤ ∑ σ, 2 * L σ := amgm_lemma_3 (fun σ => 2 * L σ) (fun σ => by linarith [hLpos σ])

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
