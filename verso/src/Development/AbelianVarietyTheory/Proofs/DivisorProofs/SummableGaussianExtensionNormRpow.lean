import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinConstantTermPartDifferentiableOn
import ReciprocityTheory.Chebotarev.EulerSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.GaussSum

open GlobalTheory.GaussExt

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
Establish `hy : y = 0`. Assume the negation of the conclusion as `hy`. Establish `hy' : algebraMap F (Ext F) y ≠ 0` using `(_root_.map_ne_zero _).2 hy`. Establish `hi : ii F = algebraMap F (Ext F) (-x / y)`. Rewrite using `[map_div₀, map_neg, eq_div_iff hy']`.

Take the linear combination `h`. Establish `h2 : algebraMap F (Ext F) ((-x / y) ^ 2 + 1) = 0`. Rewrite using `[map_add, map_pow, ← hi, ii_sq, map_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : (-x / y) ^ 2 + 1 = 0` using `(map_eq_zero _).1 h2`.

Choose the witnesses or unpack the hypotheses as in `⟨τ⟩ : Nonempty (F →+* ℝ) := by`. Take `⟨φ⟩` from `(inferInstance : Nonempty (F →+* ℂ))`. Conclude with `⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩`. Establish `h4` using `congrArg τ h3`. Rewrite `h4` using `[map_add, map_pow, map_one, map_zero]`.

Use polynomial arithmetic with `[sq_nonneg (τ (-x / y))]`. Use `⟨?_, hy⟩` and prove the remaining obligations. Rewrite `h` using `[hy, map_zero, zero_mul, add_zero]`. Conclude with `(map_eq_zero _).1 h`.
-/
theorem eq_zero_of_add_mul_ii {x y : F}
    (h : algebraMap F (Ext F) x + algebraMap F (Ext F) y * ii F = 0) : x = 0 ∧ y = 0 := by
  have hy : y = 0 := by
    by_contra hy
    have hy' : algebraMap F (Ext F) y ≠ 0 := (_root_.map_ne_zero _).2 hy
    have hi : ii F = algebraMap F (Ext F) (-x / y) := by
      rw [map_div₀, map_neg, eq_div_iff hy']
      linear_combination h
    have h2 : algebraMap F (Ext F) ((-x / y) ^ 2 + 1) = 0 := by
      rw [map_add, map_pow, ← hi, ii_sq, map_one]; ring
    have h3 : (-x / y) ^ 2 + 1 = 0 := (map_eq_zero _).1 h2
    obtain ⟨τ⟩ : Nonempty (F →+* ℝ) := by
      obtain ⟨φ⟩ := (inferInstance : Nonempty (F →+* ℂ))
      exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩
    have h4 := congrArg τ h3
    rw [map_add, map_pow, map_one, map_zero] at h4
    nlinarith [sq_nonneg (τ (-x / y))]
  refine ⟨?_, hy⟩
  rw [hy, map_zero, zero_mul, add_zero] at h
  exact (map_eq_zero _).1 h

/- English proof (translation)
Assemble the required witnesses or components as `⟨X ^ 2 + 1, by monicity!, by simp [ii_sq]⟩`.
-/
theorem isIntegral_ii : IsIntegral ℤ (ii F) :=
  ⟨X ^ 2 + 1, by monicity!, by simp [ii_sq]⟩

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨d₁, hd₁, h₁⟩` from `APart.exists_den (latM 𝔞)`. Take `⟨d₂, hd₂, h₂⟩` from `APart.exists_den (𝔟 : FractionalIdeal (𝓞 F)⁰ F)`. Establish `hd : ((d₁ : F) * (d₂ : F)) ≠ 0` using `mul_ne_zero (by exact_mod_cast hd₁) (by exact_mod_cast hd₂)`. Use `choose ga hga using fun c : Quotient (latRel 𝔞 𝔟) => h₁ c.out.1.1 c.out.2.1`. Use `choose gb hgb using fun c : Quotient (latRel 𝔞 𝔟) => h₂ c.out.1.2 c.out.2.2.1`.

Set `iO : 𝓞 (Ext F)` to `⟨ii F, isIntegral_ii⟩`. Set `y : Quotient (latRel 𝔞 𝔟) → 𝓞 (Ext F)` to `fun c => algebraMap (𝓞 F) (𝓞 (Ext F)) (d₂ * ga c) + algebraMap (𝓞 F) (𝓞 (Ext F)) (d₁ * gb c) * iO`. Establish `hy : ∀ c, ((y c : 𝓞 (Ext F)) : Ext F) = algebraMap F (Ext F) ((d₁ : F) * (d₂ : F)) * gEmb F c.out.1`. Introduce `c`. Establish `e : ((y c : 𝓞 (Ext F)) : Ext F) = algebraMap F (Ext F) ((d₂ * ga c : 𝓞 F) : F) + algebraMap F (Ext F) ((d₁ * gb c : 𝓞 F) : F) * ii F` using `rfl`.

Establish `ea : ((d₂ * ga c : 𝓞 F) : F) = (d₂ : F) * (ga c : F)` using `rfl`. Establish `eb : ((d₁ * gb c : 𝓞 F) : F) = (d₁ : F) * (gb c : F)` using `rfl`. Rewrite using `[e, ea, eb, hga, hgb, gEmb]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Set `rep : Ideal (𝓞 (Ext F)) → 𝓞 (Ext F)` to `fun J => if h : ∃ x, J = Ideal.span {x} then h.choose else 0`. Establish `hrep : ∀ c, Associated (rep (Ideal.span {y c})) (y c)`. Introduce `c`. Establish `hex : ∃ x, Ideal.span {y c} = Ideal.span {x}` using `⟨y c, rfl⟩`. Use `Ideal.span_singleton_eq_span_singleton.1 ?_` and prove the remaining obligations.

Simplify using `only [rep, dif_pos hex]`. Conclude with `hex.choose_spec.symm`. Use `choose u hu using hrep`. Set `Q` to `(𝓞 (Ext F))ˣ ⧸ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range`. Set `φ : Quotient (latRel 𝔞 𝔟) → Ideal (𝓞 (Ext F)) × Q` to `fun c => (Ideal.span {y c}, (QuotientGroup.mk (u c) : Q))`.

Establish `hinj : Function.Injective φ`. Introduce `c c' h`. Simplify using `only [φ, Prod.mk.injEq] at h`. Take `⟨hJ, hq⟩` from `h`. Take `⟨η, hη⟩` from `QuotientGroup.eq.1 hq`.

Establish `hu' : ((u c' : (𝓞 (Ext F))ˣ) : 𝓞 (Ext F)) = (u c : 𝓞 (Ext F)) * algebraMap (𝓞 F) (𝓞 (Ext F)) (η : 𝓞 F)`. Establish `: u c' = u c * Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom η`. Rewrite using `[hη]`. Use `group`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Establish `key : y c' = y c * algebraMap (𝓞 F) (𝓞 (Ext F)) (η : 𝓞 F)`. Rewrite using `[← hu c', ← hu c, ← hJ, hu']`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ((y c' : 𝓞 (Ext F)) : Ext F) = (y c : Ext F) * algebraMap F (Ext F) ((η : 𝓞 F) : F)`.

Rewrite using `[key]`. Both sides reduce to the same expression. Rewrite `h3` using `[hy, hy]`. Establish `h4 : gEmb F c'.out.1 = gEmb F c.out.1 * algebraMap F (Ext F) ((η : 𝓞 F) : F)` using `mul_left_cancel₀ ((_root_.map_ne_zero _).2 hd) (by rw [h3]; ring)`. Unfold `gEmb at h4`.

Establish `h5 : algebraMap F (Ext F) (c'.out.1.1 - ((η : 𝓞 F) : F) * c.out.1.1) + algebraMap F (Ext F) (c'.out.1.2 - ((η : 𝓞 F) : F) * c.out.1.2) * ii F = 0`. Simplify using `only [map_sub, map_mul]`. Take the linear combination `h4`. Take `⟨e1, e2⟩` from `eq_zero_of_add_mul_ii h5`. Conclude with `(Quotient.out_equiv_out.1 ⟨η, by linear_combination e1, by linear_combination e2⟩)`.

Use `haveI := hQ`. Establish `hS : Summable (fun p : Ideal (𝓞 (Ext F)) × Q => ((Ideal.absNorm p.1 : ℕ) : ℝ) ^ (-t) * (fun _ : Q => (1 : ℝ)) p.2)` using `(ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal (Ext F) ht).mul_of_nonneg (Summable.of_finite) (fun J => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun _ => zero_le_one)`. Establish `hS'` using `hS.comp_injective hinj`. Use `set K : ℝ := |((Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) : ℚ) : ℝ)| with hK`. Establish `hK0 : 0 < K`.

Rewrite using `[hK]`. Establish `h0 : algebraMap F (Ext F) ((d₁ : F) * (d₂ : F)) ≠ 0` using `(_root_.map_ne_zero _).2 hd`. Establish `h1 : Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) ≠ 0` using `Algebra.norm_ne_zero_iff.2 h0`. Conclude with `abs_pos.2 (by exact_mod_cast h1)`. Use `(hS'.mul_left (K ^ t)).congr fun c => ?_` and prove the remaining obligations.

Establish `e1 : ((Algebra.norm ℤ (y c) : ℤ) : ℚ) = Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) * Algebra.norm ℚ (gEmb F c.out.1)`. Rewrite using `[Algebra.coe_norm_int, hy, map_mul]`. Establish `e2 : ((Algebra.norm ℤ (y c) : ℤ) : ℝ) = ((Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) : ℚ) : ℝ) * ((Algebra.norm ℚ (gEmb F c.out.1) : ℚ) : ℝ)`. Conclude with `congrArg (fun q : ℚ => (q : ℝ)) e1` after adjusting the coercions. Establish `hN : ((Ideal.absNorm (Ideal.span ({y c} : Set (𝓞 (Ext F)))) : ℕ) : ℝ) = K * |((Algebra.norm ℚ (gEmb F c.out.1) : ℚ) : ℝ)|`.

Rewrite using `[Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, e2, abs_mul]`. Simplify using `only [Function.comp_apply, φ, mul_one]`. Rewrite using `[hN, Real.mul_rpow hK0.le (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hK0, add_neg_cancel, Real.rpow_zero, one_mul]`.
-/
theorem summable_norm_rpow (𝔞 𝔟 : Frac F) {t : ℝ} (ht : 1 < t)
    (hQ : Finite ((𝓞 (Ext F))ˣ ⧸ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range)) :
    Summable (fun c : Quotient (latRel 𝔞 𝔟) => |((Algebra.norm ℚ (gEmb F c.out.1) : ℚ) : ℝ)| ^ (-t)) := by
  classical
  obtain ⟨d₁, hd₁, h₁⟩ := APart.exists_den (latM 𝔞)
  obtain ⟨d₂, hd₂, h₂⟩ := APart.exists_den (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
  have hd : ((d₁ : F) * (d₂ : F)) ≠ 0 := mul_ne_zero (by exact_mod_cast hd₁) (by exact_mod_cast hd₂)
  choose ga hga using fun c : Quotient (latRel 𝔞 𝔟) => h₁ c.out.1.1 c.out.2.1
  choose gb hgb using fun c : Quotient (latRel 𝔞 𝔟) => h₂ c.out.1.2 c.out.2.2.1
  let iO : 𝓞 (Ext F) := ⟨ii F, isIntegral_ii⟩
  let y : Quotient (latRel 𝔞 𝔟) → 𝓞 (Ext F) := fun c =>
    algebraMap (𝓞 F) (𝓞 (Ext F)) (d₂ * ga c) + algebraMap (𝓞 F) (𝓞 (Ext F)) (d₁ * gb c) * iO
  have hy : ∀ c, ((y c : 𝓞 (Ext F)) : Ext F) = algebraMap F (Ext F) ((d₁ : F) * (d₂ : F)) * gEmb F c.out.1 := by
    intro c
    have e : ((y c : 𝓞 (Ext F)) : Ext F) =
        algebraMap F (Ext F) ((d₂ * ga c : 𝓞 F) : F) + algebraMap F (Ext F) ((d₁ * gb c : 𝓞 F) : F) * ii F := rfl
    have ea : ((d₂ * ga c : 𝓞 F) : F) = (d₂ : F) * (ga c : F) := rfl
    have eb : ((d₁ * gb c : 𝓞 F) : F) = (d₁ : F) * (gb c : F) := rfl
    rw [e, ea, eb, hga, hgb, gEmb]
    simp only [map_mul]
    ring

  let rep : Ideal (𝓞 (Ext F)) → 𝓞 (Ext F) := fun J =>
    if h : ∃ x, J = Ideal.span {x} then h.choose else 0
  have hrep : ∀ c, Associated (rep (Ideal.span {y c})) (y c) := by
    intro c
    have hex : ∃ x, Ideal.span {y c} = Ideal.span {x} := ⟨y c, rfl⟩
    refine Ideal.span_singleton_eq_span_singleton.1 ?_
    simp only [rep, dif_pos hex]
    exact hex.choose_spec.symm
  choose u hu using hrep
  let Q := (𝓞 (Ext F))ˣ ⧸ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range
  let φ : Quotient (latRel 𝔞 𝔟) → Ideal (𝓞 (Ext F)) × Q := fun c =>
    (Ideal.span {y c}, (QuotientGroup.mk (u c) : Q))
  have hinj : Function.Injective φ := by
    intro c c' h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨hJ, hq⟩ := h
    obtain ⟨η, hη⟩ := QuotientGroup.eq.1 hq
    have hu' : ((u c' : (𝓞 (Ext F))ˣ) : 𝓞 (Ext F)) = (u c : 𝓞 (Ext F)) * algebraMap (𝓞 F) (𝓞 (Ext F)) (η : 𝓞 F) := by
      have : u c' = u c * Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom η := by
        rw [hη]; group
      rw [this]; simp
    have key : y c' = y c * algebraMap (𝓞 F) (𝓞 (Ext F)) (η : 𝓞 F) := by
      rw [← hu c', ← hu c, ← hJ, hu']; ring
    have h3 : ((y c' : 𝓞 (Ext F)) : Ext F) = (y c : Ext F) * algebraMap F (Ext F) ((η : 𝓞 F) : F) := by
      rw [key]; rfl
    rw [hy, hy] at h3
    have h4 : gEmb F c'.out.1 = gEmb F c.out.1 * algebraMap F (Ext F) ((η : 𝓞 F) : F) :=
      mul_left_cancel₀ ((_root_.map_ne_zero _).2 hd) (by rw [h3]; ring)
    unfold gEmb at h4
    have h5 : algebraMap F (Ext F) (c'.out.1.1 - ((η : 𝓞 F) : F) * c.out.1.1) +
        algebraMap F (Ext F) (c'.out.1.2 - ((η : 𝓞 F) : F) * c.out.1.2) * ii F = 0 := by
      simp only [map_sub, map_mul]
      linear_combination h4
    obtain ⟨e1, e2⟩ := eq_zero_of_add_mul_ii h5
    exact (Quotient.out_equiv_out.1 ⟨η, by linear_combination e1, by linear_combination e2⟩)
  haveI := hQ
  have hS : Summable (fun p : Ideal (𝓞 (Ext F)) × Q => ((Ideal.absNorm p.1 : ℕ) : ℝ) ^ (-t) * (fun _ : Q => (1 : ℝ)) p.2) :=
    (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal (Ext F) ht).mul_of_nonneg (Summable.of_finite)
      (fun J => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun _ => zero_le_one)
  have hS' := hS.comp_injective hinj
  set K : ℝ := |((Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) : ℚ) : ℝ)| with hK
  have hK0 : 0 < K := by
    rw [hK]
    have h0 : algebraMap F (Ext F) ((d₁ : F) * (d₂ : F)) ≠ 0 := (_root_.map_ne_zero _).2 hd
    have h1 : Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) ≠ 0 := Algebra.norm_ne_zero_iff.2 h0
    exact abs_pos.2 (by exact_mod_cast h1)
  refine (hS'.mul_left (K ^ t)).congr fun c => ?_
  have e1 : ((Algebra.norm ℤ (y c) : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) * Algebra.norm ℚ (gEmb F c.out.1) := by
    rw [Algebra.coe_norm_int, hy, map_mul]
  have e2 : ((Algebra.norm ℤ (y c) : ℤ) : ℝ) =
      ((Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) : ℚ) : ℝ) * ((Algebra.norm ℚ (gEmb F c.out.1) : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  have hN : ((Ideal.absNorm (Ideal.span ({y c} : Set (𝓞 (Ext F)))) : ℕ) : ℝ) =
      K * |((Algebra.norm ℚ (gEmb F c.out.1) : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, e2, abs_mul]
  simp only [Function.comp_apply, φ, mul_one]
  rw [hN, Real.mul_rpow hK0.le (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hK0, add_neg_cancel,
    Real.rpow_zero, one_mul]

end GlobalTheory.GaussSum

/- English proof (translation)
Introduce `F _ _ _ 𝔞 𝔟 t ht hQ`. Conclude with `GlobalTheory.GaussSum.summable_norm_rpow 𝔞 𝔟 ht hQ`.
-/
theorem GlobalTheory.GaussSum.summable_gauss_norm : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (t : ℝ), 1 < t → Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸ (Units.map (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => |((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F c.out.1) : ℚ) : ℝ)| ^ (-t)) := by
  intro F _ _ _ 𝔞 𝔟 t ht hQ
  exact GlobalTheory.GaussSum.summable_norm_rpow 𝔞 𝔟 ht hQ
