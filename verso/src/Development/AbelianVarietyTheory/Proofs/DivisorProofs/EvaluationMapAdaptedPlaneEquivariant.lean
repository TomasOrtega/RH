import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMixedEmbeddingNatMulLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalMapExistsScalarFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalMapExistsScalarFactorAltBis

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ExpandSumm

open scoped Classical

/- English proof (translation)
Use `haveI := GlobalTheory.WeilM.discreteTopology_denomLattice E (Fin n) one_pos`. Use `set L := GlobalTheory.WeilM.denomLattice E (Fin n) 1 with hLdef`. Use `set r := Module.finrank ℤ L + 1 with hr`. Establish `hL` using `GlobalTheory.SchwartzMajorant.summable_one_add_norm_pow_inv L`. Use `⟨r, fun M h hM hsupp B hdec => ?_⟩` and prove the remaining obligations.

Establish `hB : 0 ≤ B` using `le_trans (by positivity) (hdec 0)`. Set `S : Set (Fin n → E)` to `{ξ | ∀ i, ∃ o : 𝓞 E, (M : E) * ξ i = o}`. Set `v : (Fin n → E) → (Fin n → mixedEmbedding.mixedSpace E)` to `fun ξ i => mixedEmbedding E ((M : E) * ξ i)`. Establish `hmem : ∀ ξ ∈ S, v ξ ∈ L`. Introduce `ξ hξ i`.

Take `⟨o, ho⟩` from `hξ i`. Rewrite using `[Nat.cast_one, one_smul]`. Use `show mixedEmbedding E ((M : E) * ξ i) ∈ mixedEmbedding.integerLattice E`. Rewrite using `[ho]`. Conclude with `⟨o, rfl⟩`.

Set `j : S → L` to `fun ξ => ⟨v ξ.1, hmem ξ.1 ξ.2⟩`. Establish `hMF : (M : E) ≠ 0` using `by exact_mod_cast (show M ≠ 0 by omega)`. Establish `hj : Function.Injective j` using `fun a b hab => Subtype.ext (funext fun i => mul_left_cancel₀ hMF (mixedEmbedding_injective E (congrFun (congrArg Subtype.val hab) i)))`. Set `G : (Fin n → E) → ℝ` to `S.indicator fun ξ => B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹`. Establish `hGs : Summable G`.

Rewrite using `[← summable_subtype_iff_indicator]`. Conclude with `(hL.comp_injective hj).mul_left _`. Establish `hbound : ∀ ξ : Fin n → E, ‖h ξ‖ ≤ G ξ`. Introduce `ξ`. Distinguish the cases in `h0 : h ξ = 0`.

Rewrite using `[h0, norm_zero]`. Conclude with `Set.indicator_nonneg (fun ξ _ => by positivity) ξ`. Establish `hξ : ξ ∈ S` using `hsupp ξ h0`. Rewrite using `[show G ξ = B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹ from Set.indicator_of_mem hξ _]`. Use `set s := ∑ i, ∑ w : InfinitePlace E, w (ξ i) with hs`.

Establish `hs0 : 0 ≤ s` using `Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _`. Establish `hv` using `GlobalTheory.RatPointSum.norm_mixedEmbedding_nat_mul_le M ξ`. Establish `hM1 : (1 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `h1 : 1 + ‖v ξ‖ ≤ (M : ℝ) * (1 + s)` using `by show 1 + ‖(fun i => mixedEmbedding E ((M : E) * ξ i))‖ ≤ _`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hpos : 0 < (1 + s) ^ r` using `by positivity`. Establish `hvpos : 0 < (1 + ‖v ξ‖) ^ r` using `by positivity`. Establish `h2 : ‖h ξ‖ ≤ B / (1 + s) ^ r`. Rewrite using `[le_div_iff₀ hpos]`. Conclude with `hdec ξ`.

Use `h2.trans ?_` and prove the remaining obligations. Rewrite using `[div_eq_mul_inv, mul_assoc]`. Use `mul_le_mul_of_nonneg_left ?_ hB` and prove the remaining obligations. Rewrite using `[← div_eq_mul_inv, le_div_iff₀ hvpos, inv_mul_eq_div, div_le_iff₀ hpos]`. Rewrite using `[← mul_pow]`.

Conclude with `pow_le_pow_left₀ (by positivity) h1 r`. Conclude with `Summable.of_norm_bounded hGs hbound`.
-/
theorem summable_of_denom_decay (E : Type) [Field E] [NumberField E] (n : ℕ) :
    ∃ K : ℕ, ∀ (N : ℕ) (h : (Fin n → E) → ℂ), 1 ≤ N → (∀ ξ, h ξ ≠ 0 → ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o) →
      ∀ C : ℝ, (∀ ξ, ‖h ξ‖ * (1 + ∑ i, ∑ w : InfinitePlace E, w (ξ i)) ^ K ≤ C) → Summable h := by
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice E (Fin n) one_pos
  set L := GlobalTheory.WeilM.denomLattice E (Fin n) 1 with hLdef
  set r := Module.finrank ℤ L + 1 with hr
  have hL := GlobalTheory.SchwartzMajorant.summable_one_add_norm_pow_inv L
  refine ⟨r, fun M h hM hsupp B hdec => ?_⟩
  have hB : 0 ≤ B := le_trans (by positivity) (hdec 0)
  let S : Set (Fin n → E) := {ξ | ∀ i, ∃ o : 𝓞 E, (M : E) * ξ i = o}
  let v : (Fin n → E) → (Fin n → mixedEmbedding.mixedSpace E) := fun ξ i => mixedEmbedding E ((M : E) * ξ i)
  have hmem : ∀ ξ ∈ S, v ξ ∈ L := by
    intro ξ hξ i
    obtain ⟨o, ho⟩ := hξ i
    rw [Nat.cast_one, one_smul]
    show mixedEmbedding E ((M : E) * ξ i) ∈ mixedEmbedding.integerLattice E
    rw [ho]
    exact ⟨o, rfl⟩
  let j : S → L := fun ξ => ⟨v ξ.1, hmem ξ.1 ξ.2⟩
  have hMF : (M : E) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hj : Function.Injective j := fun a b hab => Subtype.ext (funext fun i =>
    mul_left_cancel₀ hMF (mixedEmbedding_injective E (congrFun (congrArg Subtype.val hab) i)))
  let G : (Fin n → E) → ℝ := S.indicator fun ξ => B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹
  have hGs : Summable G := by
    rw [← summable_subtype_iff_indicator]
    exact (hL.comp_injective hj).mul_left _
  have hbound : ∀ ξ : Fin n → E, ‖h ξ‖ ≤ G ξ := by
    intro ξ
    by_cases h0 : h ξ = 0
    · rw [h0, norm_zero]
      exact Set.indicator_nonneg (fun ξ _ => by positivity) ξ
    have hξ : ξ ∈ S := hsupp ξ h0
    rw [show G ξ = B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹ from Set.indicator_of_mem hξ _]
    set s := ∑ i, ∑ w : InfinitePlace E, w (ξ i) with hs
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
    have hv := GlobalTheory.RatPointSum.norm_mixedEmbedding_nat_mul_le M ξ
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have h1 : 1 + ‖v ξ‖ ≤ (M : ℝ) * (1 + s) := by
      show 1 + ‖(fun i => mixedEmbedding E ((M : E) * ξ i))‖ ≤ _
      nlinarith
    have hpos : 0 < (1 + s) ^ r := by positivity
    have hvpos : 0 < (1 + ‖v ξ‖) ^ r := by positivity
    have h2 : ‖h ξ‖ ≤ B / (1 + s) ^ r := by
      rw [le_div_iff₀ hpos]; exact hdec ξ
    refine h2.trans ?_
    rw [div_eq_mul_inv, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hB
    rw [← div_eq_mul_inv, le_div_iff₀ hvpos, inv_mul_eq_div, div_le_iff₀ hpos]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 r
  exact Summable.of_norm_bounded hGs hbound

end GlobalTheory.ExpandSumm

namespace GlobalTheory.ExpandSumm

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he hB hM hXW Ψ hΨ`. Take `⟨N, hN, hsupp⟩` from `GlobalTheory.T.eval_map_exists_scalar_factor hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he hB hM hXW Ψ hΨ`. Take `⟨K, hA⟩` from `summable_of_denom_decay E n`. Take `⟨C, hC⟩` from `GlobalTheory.T.norm_thetaSum_rho_vecMulVec_mul_pow_bounded hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he hB hM hXW Ψ hΨ N K hN`. Establish `hz : ∀ ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ)) ≠ 0 → ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o`.

Introduce `ξ h0`. Use `hsupp ξ fun h1 => h0 ?_` and prove the remaining obligations. Rewrite using `[h1]`. Simplify using `[thetaSum]`. Use `hA N _ hN hz (max C 0) fun ξ => ?_` and prove the remaining obligations.

Distinguish the cases in `hξ : ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o`. Conclude with `(hC ξ hξ).trans (le_max_left _ _)`. Establish `h0 : thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ)) = 0`. Assume the negation of the conclusion as `h`. Conclude with `hξ (hz ξ h)`.

Rewrite using `[h0, norm_zero, zero_mul]`. Conclude with `le_max_right _ _`.
-/
theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∀ Ψ ∈ schA F (Fin n × Fin d), Summable (fun ξ : Fin n → E => thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ))) := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he hB hM hXW Ψ hΨ
  obtain ⟨N, hN, hsupp⟩ := GlobalTheory.T.eval_map_exists_scalar_factor hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he hB hM hXW Ψ hΨ
  obtain ⟨K, hA⟩ := summable_of_denom_decay E n
  obtain ⟨C, hC⟩ := GlobalTheory.T.norm_thetaSum_rho_vecMulVec_mul_pow_bounded hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he hB hM hXW Ψ hΨ N K hN
  have hz : ∀ ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ)) ≠ 0 →
      ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o := by
    intro ξ h0
    refine hsupp ξ fun h1 => h0 ?_
    rw [h1]
    simp [thetaSum]
  refine hA N _ hN hz (max C 0) fun ξ => ?_
  by_cases hξ : ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o
  · exact (hC ξ hξ).trans (le_max_left _ _)
  · have h0 : thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ)) = 0 := by
      by_contra h
      exact hξ (hz ξ h)
    rw [h0, norm_zero, zero_mul]
    exact le_max_right _ _

end GlobalTheory.ExpandSumm
