import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PointsPropertyOfD7
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightOfPolarisation

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition Ideal
open scoped Pointwise
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices Formalism.FrobeniusOrbits.OrdUnimod

def DiffK (D : D7) : Prop :=
  ∃ β : 𝓞 D.host.E, (β : D.host.E) = D.host.sqrtMinusD ∧
    (differentIdeal ℤ (𝓞 D.host.K)).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = Ideal.span {β}

def NormK (D : D7) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ →
    Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc *
      (D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc) =
    Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 D.host.E)}

namespace PolarisationData

variable (D : D7)

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

/- English proof (translation)
Use `show D.host.gal (D.host.gal.symm _) = _`. Conclude with `MulEquiv.apply_symm_apply _ _`.
-/
theorem galE_conj : D.host.galE D.host.conj = D.R.cc := by
  show D.host.gal (D.host.gal.symm _) = _
  exact MulEquiv.apply_symm_apply _ _

/- English proof (translation)
Use `show D.host.conj D.host.sqd = - D.host.sqd`. Rewrite using `[D.host.gal_sqd, show D.host.gal D.host.conj = D.R.cc from galE_conj D]`. Simplify using `[Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]`.
-/
theorem conj_b : D.host.conj D.host.sqrtMinusD = - D.host.sqrtMinusD := by
  show D.host.conj D.host.sqd = - D.host.sqd
  rw [D.host.gal_sqd, show D.host.gal D.host.conj = D.R.cc from galE_conj D]
  simp [Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]

/- English proof (translation)
Introduce `h`. Apply `hI` to reduce the goal to its premises. Establish `k : σ⁻¹ • σ • I = I` using `inv_smul_smul σ I`. Rewrite using `[← k, h]`. Use `first`.

Consider the case `simp`. Consider the case `(rw [Ideal.pointwise_smul_def]; exact Ideal.map_bot)`.
-/
private theorem smul_ne_bot' (σ : D.host.E ≃ₐ[ℚ] D.host.E) (I : Ideal (𝓞 D.host.E)) (hI : I ≠ ⊥) :
    σ • I ≠ ⊥ := by
  intro h
  apply hI
  have k : σ⁻¹ • σ • I = I := inv_smul_smul σ I
  rw [← k, h]
  first
    | simp
    | (rw [Ideal.pointwise_smul_def]; exact Ideal.map_bot)

/- English proof (translation)
Conclude with `Real.sqrt_pos.mpr (by exact_mod_cast D.host.hyp.2.1.pos)`.
-/
theorem sqrt_d_pos : 0 < Real.sqrt D.host.d := by
  exact Real.sqrt_pos.mpr (by exact_mod_cast D.host.hyp.2.1.pos)

/- English proof (translation)
Introduce `h`. Establish `k` using `D.host.sqd_sq`. Establish `hd : (D.host.d : D.host.E) ≠ 0` using `by exact_mod_cast D.host.hyp.2.1.ne_zero`. Rewrite `k` using `[show D.host.sqd = D.host.sqrtMinusD from rfl, h]`. Apply `hd` to reduce the goal to its premises.

Take the linear combination `k`.
-/
theorem b_ne_zero : D.host.sqrtMinusD ≠ 0 := by
  intro h
  have k := D.host.sqd_sq
  have hd : (D.host.d : D.host.E) ≠ 0 := by exact_mod_cast D.host.hyp.2.1.ne_zero
  rw [show D.host.sqd = D.host.sqrtMinusD from rfl, h] at k
  apply hd
  linear_combination k

/- English proof (translation)
Simplify using `only [FractionalIdeal.mem_coeIdeal]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, hz⟩`. Use `⟨σ⁻¹ • a, (Ideal.mem_pointwise_smul_iff_inv_smul_mem).1 ha, ?_⟩` and prove the remaining obligations. Establish `e1 : algebraMap (𝓞 D.host.E) D.host.E (σ⁻¹ • a) = σ⁻¹ (algebraMap (𝓞 D.host.E) D.host.E a)` using `rfl`.

Rewrite using `[e1, hz]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨σ • a, Ideal.smul_mem_pointwise_smul σ a A ha, rfl⟩`.
-/
theorem mem_coe_smul (σ : D.host.E ≃ₐ[ℚ] D.host.E) (A : Ideal (𝓞 D.host.E)) (z : D.host.E) :
    σ z ∈ ((σ • A : Ideal (𝓞 D.host.E)) : FI) ↔ z ∈ (A : FI) := by
  simp only [FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨a, ha, hz⟩
    refine ⟨σ⁻¹ • a, (Ideal.mem_pointwise_smul_iff_inv_smul_mem).1 ha, ?_⟩
    have e1 : algebraMap (𝓞 D.host.E) D.host.E (σ⁻¹ • a) =
        σ⁻¹ (algebraMap (𝓞 D.host.E) D.host.E a) := rfl
    rw [e1, hz]
    simp
  · rintro ⟨a, ha, rfl⟩
    exact ⟨σ • a, Ideal.smul_mem_pointwise_smul σ a A ha, rfl⟩

/- English proof (translation)
Establish `hB0 : ((Bd : Ideal (𝓞 D.host.E)) : FI) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr hB`. Establish `hB1 : ((σ • Bd : Ideal (𝓞 D.host.E)) : FI) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr (smul_ne_bot' D σ Bd hB)`. Rewrite using `[← div_eq_mul_inv, ← div_eq_mul_inv]`. Use `first`. Consider the case `rw [FractionalIdeal.mem_div_iff_of_ne_zero hB0, FractionalIdeal.mem_div_iff_of_ne_zero hB1]`.

Consider the case `rw [FractionalIdeal.mem_div_iff_of_nonzero hB0, FractionalIdeal.mem_div_iff_of_nonzero hB1]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Establish `k` using `h (σ y) ((mem_coe_smul D σ Bd y).2 hy)`. Rewrite `k` using `[← map_mul]`.

Conclude with `(mem_coe_smul D σ A (x * y)).1 k`. Introduce `h y hy`. Establish `hy' : σ (σ.symm y) ∈ ((σ • Bd : Ideal (𝓞 D.host.E)) : FI)`. Rewrite using `[AlgEquiv.apply_symm_apply]`. Conclude with `hy`.

Establish `k` using `(mem_coe_smul D σ A _).2 (h _ ((mem_coe_smul D σ Bd _).1 hy'))`. Rewrite `k` using `[map_mul, AlgEquiv.apply_symm_apply]`. Conclude with `k`.
-/
theorem mem_quot_smul (σ : D.host.E ≃ₐ[ℚ] D.host.E) (A Bd : Ideal (𝓞 D.host.E)) (hB : Bd ≠ ⊥)
    (x : D.host.E) :
    σ x ∈ ((σ • A : Ideal (𝓞 D.host.E)) : FI) * ((σ • Bd : Ideal (𝓞 D.host.E)) : FI)⁻¹ ↔
      x ∈ (A : FI) * (Bd : FI)⁻¹ := by
  have hB0 : ((Bd : Ideal (𝓞 D.host.E)) : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hB
  have hB1 : ((σ • Bd : Ideal (𝓞 D.host.E)) : FI) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (smul_ne_bot' D σ Bd hB)
  rw [← div_eq_mul_inv, ← div_eq_mul_inv]
  first
    | rw [FractionalIdeal.mem_div_iff_of_ne_zero hB0, FractionalIdeal.mem_div_iff_of_ne_zero hB1]
    | rw [FractionalIdeal.mem_div_iff_of_nonzero hB0, FractionalIdeal.mem_div_iff_of_nonzero hB1]
  constructor
  · intro h y hy
    have k := h (σ y) ((mem_coe_smul D σ Bd y).2 hy)
    rw [← map_mul] at k
    exact (mem_coe_smul D σ A (x * y)).1 k
  · intro h y hy
    have hy' : σ (σ.symm y) ∈ ((σ • Bd : Ideal (𝓞 D.host.E)) : FI) := by
      rw [AlgEquiv.apply_symm_apply]; exact hy
    have k := (mem_coe_smul D σ A _).2 (h _ ((mem_coe_smul D σ Bd _).1 hy'))
    rw [map_mul, AlgEquiv.apply_symm_apply] at k
    exact k

/- English proof (translation)
Use extensionality with `z`. Rewrite using `[FractionalIdeal.mem_spanSingleton, FractionalIdeal.mem_one_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨-a, by simp [Algebra.smul_def]⟩`.

Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨-a, by simp [Algebra.smul_def]⟩`.
-/
theorem spanSingleton_neg_one :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (-1 : D.host.E) = 1 := by
  ext z
  rw [FractionalIdeal.mem_spanSingleton, FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨-a, by simp [Algebra.smul_def]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨-a, by simp [Algebra.smul_def]⟩

/- English proof (translation)
Conclude with `D.host.𝔟_spec.1`.
-/
theorem diffEK : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) =
    D.host.𝔟 * (D.host.conj • D.host.𝔟) := by
  exact D.host.𝔟_spec.1

attribute [local instance] FractionRing.liftAlgebra in
/- English proof (translation)
Conclude with `differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ _ _`.
-/
theorem diffE : differentIdeal ℤ (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) *
    (differentIdeal ℤ (𝓞 D.host.K)).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  exact differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ _ _

/- English proof (translation)
Establish `hs : φ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)` using `(SlopeTestRemainingChoices.mem_PhiEmb_iff D φ).1 hφ`. Establish `hpos` using `sqrt_d_pos D`. Rewrite using `[map_div₀, map_neg, map_one, map_mul, map_natCast, hs]`. Establish `hN' : (N : ℂ) ≠ 0` using `by exact_mod_cast hN`. Establish `hs0 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hpos.ne'`.

Establish `key : (-1 : ℂ) / ((N : ℂ) * (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))) = Complex.I * ((((N : ℝ) * Real.sqrt D.host.d)⁻¹ : ℝ) : ℂ)`. Rewrite using `[div_eq_iff (mul_ne_zero hN' (mul_ne_zero Complex.I_ne_zero hs0))]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Put the polynomial expressions in normal form.

Rewrite using `[Complex.I_sq]`. Rewrite using `[key]`. Simplify using `only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, add_zero, mul_zero, zero_add]`. Conclude with `inv_pos.mpr (mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hN) hpos)`.
-/
theorem im_pos (N : ℕ) (hN : N ≠ 0) (φ : D.host.E →+* ℂ) (hφ : φ ∈ PhiEmb D) :
    0 < (φ (-1 / ((N : D.host.E) * D.host.sqrtMinusD))).im := by
  have hs : φ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) :=
    (SlopeTestRemainingChoices.mem_PhiEmb_iff D φ).1 hφ
  have hpos := sqrt_d_pos D
  rw [map_div₀, map_neg, map_one, map_mul, map_natCast, hs]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hs0 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have key : (-1 : ℂ) / ((N : ℂ) * (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))) =
      Complex.I * ((((N : ℝ) * Real.sqrt D.host.d)⁻¹ : ℝ) : ℂ) := by
    rw [div_eq_iff (mul_ne_zero hN' (mul_ne_zero Complex.I_ne_zero hs0))]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
  rw [key]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, add_zero, mul_zero, zero_add]
  exact inv_pos.mpr (mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hN) hpos)

/- English proof (translation)
Introduce `cc hcc`. Take `⟨β, hβ, hβspan⟩` from `hA`. Establish `hN0 : Ideal.absNorm cc ≠ 0` using `fun h => hcc (Ideal.absNorm_eq_zero_iff.mp h)`. Establish `hNE : ((Ideal.absNorm cc : ℕ) : D.host.E) ≠ 0` using `by exact_mod_cast hN0`. Establish `hb0` using `b_ne_zero D`.

Establish `hNcc` using `hB cc hcc`. Establish `hb𝔟 : D.host.𝔟 ≠ ⊥`. Introduce `h`. Establish `k` using `D.host.𝔟_spec.2`. Rewrite `k` using `[h]`.

Simplify using `at k`. Establish `hAbot : Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc ≠ ⊥`. Introduce `h`. Rewrite `hNcc` using `[h, bot_mul, eq_comm, Ideal.span_singleton_eq_bot]`. Conclude with `hN0 (by exact_mod_cast hNcc)`.

Use `⟨-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD), ?_, ?_, fun φ hφ => im_pos D (Ideal.absNorm cc) hN0 φ hφ, ?_⟩` and prove the remaining obligations. Establish `hs : D.host.sqrtMinusD ∈ D.host.K` using `IntermediateField.mem_adjoin_simple_self ℚ D.host.sqd`. Conclude with `div_mem (neg_mem (one_mem _)) (mul_mem (natCast_mem _ _) hs)`. Rewrite using `[map_div₀, map_neg, map_one, map_mul, map_natCast, conj_b, mul_neg, div_neg]`. Introduce `y`.

Establish `hprod : ((differentIdeal ℤ (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) : FI) * (FractionalIdeal.spanSingleton _ (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD)) * (((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) * ((D.host.co …`. Establish `h1 : (D.host.𝔟 : FI) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr hb𝔟`. Establish `h2 : ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr (smul_ne_bot' D _ _ hb𝔟)`. Establish `hN2 : ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) * ((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) = FractionalIdeal.spanSingleton _ ((Ideal.absNorm cc : ℕ) : D.host.E)`. Rewrite using `[← FractionalIdeal.coeIdeal_mul, hNcc, FractionalIdeal.coeIdeal_span_singleton, map_natCast]`.

Establish `hsp : ((Ideal.span {β} : Ideal (𝓞 D.host.E)) : FI) = FractionalIdeal.spanSingleton _ D.host.sqrtMinusD`. Rewrite using `[FractionalIdeal.coeIdeal_span_singleton]`. Use `congr 1`. Rewrite using `[diffE, diffEK, hβspan, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, hsp]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_inv_cancel₀ h1, mul_inv_cancel₀ h2, hN2, FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.spanSingleton_mul_spanSingleton, one_mul, one_mul]`. Establish `e : ((Ideal.absNorm cc : ℕ) : D.host.E) * (D.host.sqrtMinusD * (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD))) = -1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, spanSingleton_neg_one]`. Establish `hM0 : FractionalIdeal.spanSingleton _ (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD)) * (((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) * ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI)⁻¹) ≠ 0`.

Introduce `h`. Rewrite `hprod` using `[h, mul_zero, zero_mul]`. Conclude with `zero_ne_one hprod`. Establish `hdual : FractionalIdeal.dual ℤ ℚ (FractionalIdeal.spanSingleton _ (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD)) * (((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) * ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : …`. Rewrite using `[FractionalIdeal.dual_eq_mul_inv ℤ ℚ, ← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FI)), ← coeIdeal_differentIdeal ℤ ℚ D.host.E (𝓞 D.host.E), ← mul_inv]`.

Conclude with `inv_eq_of_mul_eq_one_right hprod`. Use `show y ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) * (D.host.𝔟 : FI)⁻¹ ↔ ∀ x ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) * (D.host.𝔟 : FI)⁻¹, _`. Use `conv_lhs => rw [← hdual]`. Rewrite using `[FractionalIdeal.mem_dual hM0]`. Prove the components needed by the constructor for the conclusion.

Introduce `h x hx`. Establish `hw` using `(mem_quot_smul D D.host.conj _ _ hb𝔟 x).2 hx`. Establish `k` using `h _ (FractionalIdeal.mem_singleton_mul.2 ⟨_, hw, rfl⟩)`. Rewrite `k` using `[Algebra.traceForm_apply]`. Rewrite using `[show -1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * D.host.conj x * y = y * (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * D.host.conj x) by ring]`.

Conclude with `k`. Introduce `h u hu`. Take `⟨w, hw, hweq⟩` from `FractionalIdeal.mem_singleton_mul.1 hu`. Establish `hw' : D.host.conj (D.host.conj.symm w) ∈ ((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) * ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI)⁻¹`. Rewrite using `[AlgEquiv.apply_symm_apply]`.

Conclude with `hw`. Establish `k` using `h _ ((mem_quot_smul D D.host.conj _ _ hb𝔟 _).1 hw')`. Rewrite `k` using `[AlgEquiv.apply_symm_apply]`. Rewrite using `[Algebra.traceForm_apply]`. Use `first`.

Consider the case `(rw [← hweq]; rw [show y * (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * w) = -1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * w * y by ring]; exact k)`. Consider the case `(rw [hweq]; rw [show y * (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * w) = -1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * w * y by ring]; exact k)`.
-/
theorem pol (hA : DiffK D) (hB : NormK D) : PolPart D := by
  intro cc hcc
  obtain ⟨β, hβ, hβspan⟩ := hA
  have hN0 : Ideal.absNorm cc ≠ 0 := fun h => hcc (Ideal.absNorm_eq_zero_iff.mp h)
  have hNE : ((Ideal.absNorm cc : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hN0
  have hb0 := b_ne_zero D
  have hNcc := hB cc hcc

  have hb𝔟 : D.host.𝔟 ≠ ⊥ := by
    intro h
    have k := D.host.𝔟_spec.2
    rw [h] at k
    simp at k
  have hAbot : Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc ≠ ⊥ := by
    intro h
    rw [h, bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hNcc
    exact hN0 (by exact_mod_cast hNcc)
  refine ⟨-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD), ?_, ?_,
    fun φ hφ => im_pos D (Ideal.absNorm cc) hN0 φ hφ, ?_⟩
  · have hs : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ D.host.sqd
    exact div_mem (neg_mem (one_mem _)) (mul_mem (natCast_mem _ _) hs)
  · rw [map_div₀, map_neg, map_one, map_mul, map_natCast, conj_b, mul_neg, div_neg]
  · intro y

    have hprod : ((differentIdeal ℤ (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) : FI) *
        (FractionalIdeal.spanSingleton _ (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD)) *
          (((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
            ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI)⁻¹)) *
        (((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
          (D.host.𝔟 : FI)⁻¹) = 1 := by
      have h1 : (D.host.𝔟 : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hb𝔟
      have h2 : ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI) ≠ 0 :=
        FractionalIdeal.coeIdeal_ne_zero.mpr (smul_ne_bot' D _ _ hb𝔟)
      have hN2 : ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
          ((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) =
          FractionalIdeal.spanSingleton _ ((Ideal.absNorm cc : ℕ) : D.host.E) := by
        rw [← FractionalIdeal.coeIdeal_mul, hNcc, FractionalIdeal.coeIdeal_span_singleton, map_natCast]
      have hsp : ((Ideal.span {β} : Ideal (𝓞 D.host.E)) : FI) =
          FractionalIdeal.spanSingleton _ D.host.sqrtMinusD := by
        rw [FractionalIdeal.coeIdeal_span_singleton]
        congr 1
      rw [diffE, diffEK, hβspan, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, hsp]
      calc _ = ((D.host.𝔟 : FI) * (D.host.𝔟 : FI)⁻¹) *
            (((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI) *
              ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI)⁻¹) *
            ((((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
              ((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI)) *
            (FractionalIdeal.spanSingleton _ D.host.sqrtMinusD *
              FractionalIdeal.spanSingleton _
                (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD)))) := by ring
        _ = 1 := by
          rw [mul_inv_cancel₀ h1, mul_inv_cancel₀ h2, hN2, FractionalIdeal.spanSingleton_mul_spanSingleton,
            FractionalIdeal.spanSingleton_mul_spanSingleton, one_mul, one_mul]
          have e : ((Ideal.absNorm cc : ℕ) : D.host.E) * (D.host.sqrtMinusD *
              (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD))) = -1 := by
            field_simp
          rw [e, spanSingleton_neg_one]
    have hM0 : FractionalIdeal.spanSingleton _ (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD)) *
          (((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
            ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI)⁻¹) ≠ 0 := by
      intro h
      rw [h, mul_zero, zero_mul] at hprod
      exact zero_ne_one hprod

    have hdual : FractionalIdeal.dual ℤ ℚ (FractionalIdeal.spanSingleton _
          (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD)) *
          (((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
            ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI)⁻¹)) =
        ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
          (D.host.𝔟 : FI)⁻¹ := by
      rw [FractionalIdeal.dual_eq_mul_inv ℤ ℚ, ← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FI)),
        ← coeIdeal_differentIdeal ℤ ℚ D.host.E (𝓞 D.host.E), ← mul_inv]
      exact inv_eq_of_mul_eq_one_right hprod
    show y ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
          (D.host.𝔟 : FI)⁻¹ ↔ ∀ x ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
          (D.host.𝔟 : FI)⁻¹, _
    conv_lhs => rw [← hdual]
    rw [FractionalIdeal.mem_dual hM0]
    constructor
    · intro h x hx
      have hw := (mem_quot_smul D D.host.conj _ _ hb𝔟 x).2 hx
      have k := h _ (FractionalIdeal.mem_singleton_mul.2 ⟨_, hw, rfl⟩)
      rw [Algebra.traceForm_apply] at k
      rw [show -1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * D.host.conj x * y =
        y * (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * D.host.conj x) by ring]
      exact k
    · intro h u hu
      obtain ⟨w, hw, hweq⟩ := FractionalIdeal.mem_singleton_mul.1 hu
      have hw' : D.host.conj (D.host.conj.symm w) ∈
          ((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
            ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI)⁻¹ := by
        rw [AlgEquiv.apply_symm_apply]; exact hw
      have k := h _ ((mem_quot_smul D D.host.conj _ _ hb𝔟 _).1 hw')
      rw [AlgEquiv.apply_symm_apply] at k
      rw [Algebra.traceForm_apply]
      first
        | (rw [← hweq]; rw [show y * (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * w) =
            -1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * w * y by ring]; exact k)
        | (rw [hweq]; rw [show y * (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * w) =
            -1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * w * y by ring]; exact k)

end PolarisationData

/- English proof (translation)
Conclude with `lemma_one_eight_of_polarisation D (PolarisationData.pol D hA hB)`.
-/
theorem lemma_one_eight_of_different (D : D7) (hA : DiffK D) (hB : NormK D) : Conclusion8 D := by
  exact lemma_one_eight_of_polarisation D (PolarisationData.pol D hA hB)

end Formalism.MainNotions.UnusedSlot33

end
