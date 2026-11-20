import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardDivisorsLeAbsNormNumberFieldStatement
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

noncomputable section

namespace GlobalTheory.QFiber

open FractionalIdeal

variable {F : Type} [Field F] [NumberField F]

def toIdeal (K : FractionalIdeal (𝓞 F)⁰ F) : Ideal (𝓞 F) :=
  open Classical in if h : K ≤ 1 then (le_one_iff_exists_coeIdeal.mp h).choose else ⊥

/- English proof (translation)
Unfold `toIdeal`. Rewrite using `[dif_pos h]`. Conclude with `(le_one_iff_exists_coeIdeal.mp h).choose_spec`.
-/
theorem coe_toIdeal {K : FractionalIdeal (𝓞 F)⁰ F} (h : K ≤ 1) :
    ((toIdeal K : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = K := by
  unfold toIdeal
  rw [dif_pos h]
  exact (le_one_iff_exists_coeIdeal.mp h).choose_spec

/- English proof (translation)
Unfold `nrm`. Conclude with `absNorm_nonneg _` after adjusting the coercions.
-/
theorem nrm_nonneg (𝔞 : Frac F) : 0 ≤ nrm 𝔞 := by
  unfold nrm; exact_mod_cast absNorm_nonneg _

/- English proof (translation)
Take `⟨φ⟩ : Nonempty (F →+* ℂ)` from `inferInstance`. Conclude with `⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩`.
-/
theorem emb_nonempty [IsTotallyReal F] : Nonempty (Emb F) := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩

/- English proof (translation)
Introduce `F _ _ _ 𝔞 𝔟 ξ s hs`. Break down `s.eq_empty_or_nonempty with rfl | ⟨c0, hc0⟩` into its components or cases. Simplify using `only [Finset.card_empty, Nat.cast_zero]`. Conclude with `div_nonneg (abs_nonneg _) (mul_nonneg (nrm_nonneg 𝔞) (nrm_nonneg 𝔟))`. Establish `hA : ((𝔞 : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0` using `𝔞.ne_zero`.

Establish `hB : ((𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0` using `𝔟.ne_zero`. Establish `hξ : ξ ≠ 0`. Take `⟨τ⟩` from `emb_nonempty (F := F)`. Establish `h` using `c0.out.2.2.2 τ`. Rewrite `h` using `[hs c0 hc0]`.

Introduce `h0`. Rewrite `h` using `[h0, map_zero]`. Conclude with `lt_irrefl _ h`. Establish `hle : ∀ c : Quotient (qRel 𝔞 𝔟), spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1` using `fun c => by`. Combine the equalities or inequalities in the displayed calculation.

Establish `hIle : ∀ c ∈ s, spanSingleton (𝓞 F)⁰ ξ * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹`. Introduce `c hc`. Establish `hb : spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hs c hc, ← spanSingleton_mul_spanSingleton]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hI1` using `(hIle c0 hc0).trans (hle c0)`. Use `set I := toIdeal (spanSingleton (𝓞 F)⁰ ξ * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) with hIdef`. Set `f : Quotient (qRel 𝔞 𝔟) → Ideal (𝓞 F)` to `fun c => toIdeal (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹)`. Establish `hIJ : ∀ c ∈ s, I ≤ f c`.

Introduce `c hc`. Rewrite using `[← coeIdeal_le_coeIdeal F, coe_toIdeal hI1, coe_toIdeal (hle c)]`. Conclude with `hIle c hc`. Establish `hI0 : I ≠ ⊥`. Introduce `h`.

Establish `h'` using `coe_toIdeal hI1`. Rewrite `h'` using `[← hIdef, h, coeIdeal_bot]`. Use `h'.symm` as an intermediate fact. Simplify using `only [mul_eq_zero, spanSingleton_eq_zero_iff, inv_eq_zero] at this`. The claim follows by propositional logic.

Establish `hinj : Set.InjOn f s`. Introduce `c hc c' hc' hcc`. Establish `h1 : spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ = spanSingleton (𝓞 F)⁰ c'.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹`. Rewrite using `[← coe_toIdeal (hle c), ← coe_toIdeal (hle c')]`. Conclude with `congrArg _ hcc`.

Establish `h2` using `mul_right_cancel₀ (inv_ne_zero hA) h1`. Take `⟨u, hu⟩` from `spanSingleton_eq_spanSingleton.mp h2`. Rewrite `hu` using `[Units.smul_def, Algebra.smul_def]`. Establish `hν : c.out.1.1 ≠ 0` using `left_ne_zero_of_mul (by rw [hs c hc]; exact hξ)`. Establish `hu0 : algebraMap (𝓞 F) F (u : 𝓞 F) ≠ 0`.

Rewrite using `[ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]`. Conclude with `u.ne_zero`. Establish `h4 : algebraMap (𝓞 F) F (u : 𝓞 F) * (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1`. Rewrite using `[mul_comm]`. Conclude with `unit_inv_mul u`.

Establish `e1` using `hs c hc`. Establish `e2` using `hs c' hc'`. Rewrite `e2` using `[← hu]`. Establish `hb : c'.out.1.2 = (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * c.out.1.2`. Apply `mul_left_cancel₀ (mul_ne_zero hu0 hν)` to reduce the goal to its premises.

Take the linear combination `e2 - e1 - c.out.1.1 * c.out.1.2 * h4`. Rewrite using `[← Quotient.out_eq c, ← Quotient.out_eq c']`. Apply `Quotient.sound` to reduce the goal to its premises. Use `⟨u⁻¹, ?_, hb⟩` and prove the remaining obligations. Rewrite using `[inv_inv, ← hu]`.

Establish `key : (FractionalIdeal.absNorm ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) : ℚ) = |Algebra.norm ℚ ξ| / (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F))`. Rewrite using `[coe_toIdeal hI1, map_mul, map_mul, map_inv₀, map_inv₀, absNorm_span_singleton]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[coeIdeal_absNorm]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `GlobalTheory.T.card_divisors_le_absNorm_numberField F I hI0 (s.image f) (by` after adjusting the coercions. Introduce `J hJ`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.mp hJ`. Conclude with `hIJ c hc)`. Use `_ = _ := by`.

Unfold `nrm`. Use `congrArg (Rat.cast : ℚ → ℝ) key` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.
-/
theorem card_le_norm : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (ξ : F)
    (s : Finset (Quotient (qRel 𝔞 𝔟))), (∀ c ∈ s, c.out.1.1 * c.out.1.2 = ξ) →
    (s.card : ℝ) ≤ |(Algebra.norm ℚ ξ : ℝ)| / (nrm 𝔞 * nrm 𝔟) := by
  intro F _ _ _ 𝔞 𝔟 ξ s hs
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨c0, hc0⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (abs_nonneg _) (mul_nonneg (nrm_nonneg 𝔞) (nrm_nonneg 𝔟))
  have hA : ((𝔞 : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := 𝔞.ne_zero
  have hB : ((𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := 𝔟.ne_zero
  have hξ : ξ ≠ 0 := by
    obtain ⟨τ⟩ := emb_nonempty (F := F)
    have h := c0.out.2.2.2 τ
    rw [hs c0 hc0] at h
    intro h0
    rw [h0, map_zero] at h
    exact lt_irrefl _ h
  have hle : ∀ c : Quotient (qRel 𝔞 𝔟),
      spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1 := fun c => by
    calc _ ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ :=
          by gcongr; exact spanSingleton_le_iff_mem.mpr c.out.2.1
      _ = 1 := mul_inv_cancel₀ hA
  have hIle : ∀ c ∈ s, spanSingleton (𝓞 F)⁰ ξ * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤
      spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    intro c hc
    have hb : spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1 := by
      calc _ ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ :=
            by gcongr; exact spanSingleton_le_iff_mem.mpr c.out.2.2.1
        _ = 1 := mul_inv_cancel₀ hB
    rw [← hs c hc, ← spanSingleton_mul_spanSingleton]
    calc spanSingleton (𝓞 F)⁰ c.out.1.1 * spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ *
          (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ =
          (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) *
          (spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) := by ring
      _ ≤ (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) * 1 := by gcongr
      _ = _ := mul_one _
  have hI1 := (hIle c0 hc0).trans (hle c0)
  set I := toIdeal (spanSingleton (𝓞 F)⁰ ξ * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) with hIdef
  let f : Quotient (qRel 𝔞 𝔟) → Ideal (𝓞 F) := fun c =>
    toIdeal (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹)
  have hIJ : ∀ c ∈ s, I ≤ f c := by
    intro c hc
    rw [← coeIdeal_le_coeIdeal F, coe_toIdeal hI1, coe_toIdeal (hle c)]
    exact hIle c hc
  have hI0 : I ≠ ⊥ := by
    intro h
    have h' := coe_toIdeal hI1
    rw [← hIdef, h, coeIdeal_bot] at h'
    have := h'.symm
    simp only [mul_eq_zero, spanSingleton_eq_zero_iff, inv_eq_zero] at this
    tauto
  have hinj : Set.InjOn f s := by
    intro c hc c' hc' hcc
    have h1 : spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ =
        spanSingleton (𝓞 F)⁰ c'.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
      rw [← coe_toIdeal (hle c), ← coe_toIdeal (hle c')]
      exact congrArg _ hcc
    have h2 := mul_right_cancel₀ (inv_ne_zero hA) h1
    obtain ⟨u, hu⟩ := spanSingleton_eq_spanSingleton.mp h2
    rw [Units.smul_def, Algebra.smul_def] at hu
    have hν : c.out.1.1 ≠ 0 := left_ne_zero_of_mul (by rw [hs c hc]; exact hξ)
    have hu0 : algebraMap (𝓞 F) F (u : 𝓞 F) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]; exact u.ne_zero
    have h4 : algebraMap (𝓞 F) F (u : 𝓞 F) * (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
      rw [mul_comm]; exact unit_inv_mul u
    have e1 := hs c hc
    have e2 := hs c' hc'
    rw [← hu] at e2
    have hb : c'.out.1.2 = (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * c.out.1.2 := by
      apply mul_left_cancel₀ (mul_ne_zero hu0 hν)
      linear_combination e2 - e1 - c.out.1.1 * c.out.1.2 * h4
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    apply Quotient.sound
    refine ⟨u⁻¹, ?_, hb⟩
    rw [inv_inv, ← hu]
  have key : (FractionalIdeal.absNorm ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) : ℚ) =
      |Algebra.norm ℚ ξ| / (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) *
        FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) := by
    rw [coe_toIdeal hI1, map_mul, map_mul, map_inv₀, map_inv₀, absNorm_span_singleton]
    ring
  rw [coeIdeal_absNorm] at key
  calc (s.card : ℝ) = ((s.image f).card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ (Ideal.absNorm I : ℝ) := by
      exact_mod_cast GlobalTheory.T.card_divisors_le_absNorm_numberField F I hI0 (s.image f) (by
        intro J hJ
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hJ
        exact hIJ c hc)
    _ = _ := by
      unfold nrm
      have := congrArg (Rat.cast : ℚ → ℝ) key
      push_cast at this
      exact this

end GlobalTheory.QFiber
