import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section
namespace GlobalTheory.ThetaDiagUnfold

/- English proof (translation)
Simplify using `[dotProduct, Fintype.sum_sum_type]`.
-/
theorem dot_sumElim {R : Type} [CommSemiring R] {κ : Type} [Fintype κ] (a b c d : κ → R) :
    Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _`. Introduce `μ hμ 𝓕₁ hF hfin Φ hΦ x`. Use `letI : MeasurableSpace (κ → AF F) := borel _`. Use `haveI : BorelSpace (κ → AF F) := ⟨rfl⟩`. Use `haveI : Countable F := GlobalTheory.ThetaParsevalInner.countable_numberField F`.

Use `haveI : IsFiniteMeasure (μ.restrict 𝓕₁) := isFiniteMeasure_restrict.mpr hfin`. Use `haveI := hμ`. Take `⟨hcont, hnorm, htriv, s0, hs0⟩` from `hψ`. Take `⟨emb, hemb⟩ : ∃ emb : (κ → F) → (κ → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i)` from `⟨_, rfl⟩`. Take `⟨e, he⟩ : ∃ e : (κ → F) → (κ → AF F) → ℂ, e = fun ξ y => ψ (emb ξ ⬝ᵥ y)` from `⟨_, rfl⟩`.

Take `⟨a, ha⟩ : ∃ a : (κ ⊕ κ → F) → ℂ, a = fun ξ => Φ ((fun i => algebraMap F (AF F) (ξ i)) + Sum.elim x x)` from `⟨_, rfl⟩`. Take `⟨d, hd⟩ : ∃ d : (κ ⊕ κ → F) → (κ → F), d = fun ξ => ξ ∘ Sum.inl - ξ ∘ Sum.inr` from `⟨_, rfl⟩`. Establish `hsum : Summable fun ξ => ‖a ξ‖`. Establish `h0` using `GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F (Sum.elim x x) hΦ)`. Substitute `ha` using the available equality.

Conclude with `h0`. Establish `he_norm : ∀ ξ y, ‖e ξ y‖ = 1` using `fun ξ y => by rw [he]; exact hnorm _`. Establish `he_cont : ∀ ξ, Continuous (e ξ)` using `fun ξ => by`. Rewrite using `[he]`. Conclude with `hcont.comp (continuous_const.dotProduct continuous_id)`.

Establish `hpt : ∀ y, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = ∑' ξ, a ξ * e (d ξ) y`. Introduce `y`. Unfold `GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Establish `hsplit : (fun i => algebraMap F (AF F) (ξ i)) = Sum.elim (emb (ξ ∘ Sum.inl)) (emb (ξ ∘ Sum.inr))`.

Apply the tactic sequence `funext s; cases s <;> simp [hemb]`. Establish `hx0 : Sum.elim x x ⬝ᵥ Sum.elim y (-y) = 0`. Rewrite using `[dot_sumElim, dotProduct_neg, add_neg_cancel]`. Establish `hdot : (fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ Sum.elim y (-y) = emb (d ξ) ⬝ᵥ y`. Rewrite using `[hsplit, dot_sumElim, dotProduct_neg, hd]`.

Establish `: emb (ξ ∘ Sum.inl - ξ ∘ Sum.inr) = emb (ξ ∘ Sum.inl) - emb (ξ ∘ Sum.inr)`. Rewrite using `[hemb]`. Use function extensionality and compare the values at `i`. Simplify using `[map_sub]`. Rewrite using `[this, sub_dotProduct, sub_eq_add_neg]`.

Simplify using `only`. Rewrite using `[hx0, mul_zero, add_zero, hdot, ha, he]`. Expand and normalize the polynomial expressions, which then agree. Establish `hFint : ∀ ξ : κ ⊕ κ → F, Integrable (fun y => a ξ * e (d ξ) y) (μ.restrict 𝓕₁)` using `fun ξ => (Integrable.of_bound (he_cont _).aestronglyMeasurable 1 (ae_of_all _ fun y => (he_norm _ _).le)).const_mul _`. Establish `hnormint : ∀ ξ : κ ⊕ κ → F, ∫ y in 𝓕₁, ‖a ξ * e (d ξ) y‖ ∂μ = ‖a ξ‖ * μ.real 𝓕₁`.

Introduce `ξ`. Simplify using `only [norm_mul, he_norm, mul_one]`. Rewrite using `[setIntegral_const, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsumint : Summable fun ξ : κ ⊕ κ → F => ∫ y in 𝓕₁, ‖a ξ * e (d ξ) y‖ ∂μ`.

Repeatedly rewrite using `[hnormint]`. Conclude with `hsum.mul_right _`. Establish `horth : ∀ ζ : κ → F, ∫ y in 𝓕₁, e ζ y ∂μ = if ζ = 0 then (μ.real 𝓕₁ : ℂ) else 0`. Introduce `ζ`. Use `split_ifs with hζ`.

Substitute `hζ` using the available equality. Establish `: ∀ y, e 0 y = 1` using `fun y => by simp [he, hemb]`. Repeatedly rewrite using `[this]`. Rewrite using `[setIntegral_const]`. Simplify using the standard rewrite rules.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hζ (funext h)`. Use `haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := by`.

Use `Function.Surjective.countable (f := fun ρ : κ → F => (⟨emb ρ, ?_⟩ : GlobalTheory.ThetaParseval.ratVec F κ)) ?_` and prove the remaining obligations. Conclude with `(GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ρ, by rw [hemb]⟩`. Introduce and unpack `⟨r, hr⟩`. Take `⟨ρ, rfl⟩` from `(GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr`. Conclude with `⟨ρ, by subst hemb; rfl⟩`.

Use `GlobalTheory.ThetaParsevalInner.setIntegral_eq_zero_of_twist μ (GlobalTheory.ThetaParseval.ratVec F κ) hF (h := e ζ) ?_ (c := Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0)) (a := ψ s0) ?_ hs0` and prove the remaining obligations. Introduce `r hr y`. Take `⟨ρ, rfl⟩` from `(GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr`. Simplify using `only [he, dotProduct_add, AddChar.map_add_eq_mul]`. Rewrite using `[show emb ζ ⬝ᵥ (fun i => algebraMap F (AF F) (ρ i)) = algebraMap F (AF F) (ζ ⬝ᵥ ρ) by`.

Substitute `hemb` using the available equality. Simplify using `[dotProduct, map_sum, map_mul], htriv, one_mul]`. Introduce `y`. Simplify using `only [he, dotProduct_add, AddChar.map_add_eq_mul]`. Use `congr 2`.

Rewrite using `[dotProduct_single, hemb]`. Simplify using `only`. Rewrite using `[← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]`. Establish `hFval : ∀ ξ : κ ⊕ κ → F, ∫ y in 𝓕₁, a ξ * e (d ξ) y ∂μ = if d ξ = 0 then (μ.real 𝓕₁ : ℂ) * a ξ else 0`. Introduce `ξ`.

Rewrite using `[integral_const_mul, horth]`. Apply the tactic sequence `split_ifs <;> ring`. Repeatedly rewrite using `[hpt]`. Rewrite using `[← integral_tsum_of_summable_integral_norm hFint hsumint]`. Repeatedly rewrite using `[hFval]`.

Establish `hinj : Function.Injective (fun η : κ → F => (Sum.elim η η : κ ⊕ κ → F))` using `fun η η' h => by`. Use function extensionality and compare the values at `i`. Conclude with `congrFun h (Sum.inl i)`. Rewrite using `[← hinj.tsum_eq, ← tsum_mul_left]`. Use `tsum_congr fun η => ?_` and prove the remaining obligations.

Establish `hd0 : d (Sum.elim η η) = 0` using `by rw [hd]; funext i; simp`. Rewrite using `[if_pos hd0, ha]`. Simplify using `only`. Use `congr 2`. Apply the tactic sequence `funext s; cases s <;> simp`.

Introduce `ξ hξ`. Establish `h0 : d ξ = 0`. Assume the negation of the conclusion as `h`. Conclude with `hξ (if_neg h)`. Use `⟨ξ ∘ Sum.inl, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `s`. Consider the cases of `s with`. Consider the case `inl i => rfl`. Consider the case `inr i`. Use `congrFun h0 i` as an intermediate fact.

Rewrite `this` using `[hd]`. Simplify using `only [Pi.sub_apply, Function.comp_apply, Pi.zero_apply, sub_eq_zero] at this`. Simplify using `using this`.
-/
theorem integral_thetaSum_schr_diag : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (κ ⊕ κ), ∀ x : κ → AF F,
      ∫ y in 𝓕₁, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) ∂μ =
        (μ.real 𝓕₁ : ℂ) * ∑' η : κ → F, Φ (Sum.elim ((fun i => algebraMap F (AF F) (η i)) + x)
          ((fun i => algebraMap F (AF F) (η i)) + x)) := by
  intro F _ _ ψ hψ κ _
  intro μ hμ 𝓕₁ hF hfin Φ hΦ x
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : Countable F := GlobalTheory.ThetaParsevalInner.countable_numberField F
  haveI : IsFiniteMeasure (μ.restrict 𝓕₁) := isFiniteMeasure_restrict.mpr hfin
  haveI := hμ
  obtain ⟨hcont, hnorm, htriv, s0, hs0⟩ := hψ
  obtain ⟨emb, hemb⟩ : ∃ emb : (κ → F) → (κ → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (κ → F) → (κ → AF F) → ℂ, e = fun ξ y => ψ (emb ξ ⬝ᵥ y) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (κ ⊕ κ → F) → ℂ, a = fun ξ => Φ ((fun i => algebraMap F (AF F) (ξ i)) + Sum.elim x x) :=
    ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : (κ ⊕ κ → F) → (κ → F), d = fun ξ => ξ ∘ Sum.inl - ξ ∘ Sum.inr := ⟨_, rfl⟩
  have hsum : Summable fun ξ => ‖a ξ‖ := by
    have h0 := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F (Sum.elim x x) hΦ)
    subst ha
    exact h0
  have he_norm : ∀ ξ y, ‖e ξ y‖ = 1 := fun ξ y => by rw [he]; exact hnorm _
  have he_cont : ∀ ξ, Continuous (e ξ) := fun ξ => by
    rw [he]; exact hcont.comp (continuous_const.dotProduct continuous_id)
  have hpt : ∀ y, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) =
      ∑' ξ, a ξ * e (d ξ) y := by
    intro y
    unfold GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
    refine tsum_congr fun ξ => ?_
    have hsplit : (fun i => algebraMap F (AF F) (ξ i)) =
        Sum.elim (emb (ξ ∘ Sum.inl)) (emb (ξ ∘ Sum.inr)) := by
      funext s; cases s <;> simp [hemb]
    have hx0 : Sum.elim x x ⬝ᵥ Sum.elim y (-y) = 0 := by
      rw [dot_sumElim, dotProduct_neg, add_neg_cancel]
    have hdot : (fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ Sum.elim y (-y) = emb (d ξ) ⬝ᵥ y := by
      rw [hsplit, dot_sumElim, dotProduct_neg, hd]
      have : emb (ξ ∘ Sum.inl - ξ ∘ Sum.inr) = emb (ξ ∘ Sum.inl) - emb (ξ ∘ Sum.inr) := by
        rw [hemb]; funext i; simp [map_sub]
      rw [this, sub_dotProduct, sub_eq_add_neg]
    simp only
    rw [hx0, mul_zero, add_zero, hdot, ha, he]
    ring
  have hFint : ∀ ξ : κ ⊕ κ → F, Integrable (fun y => a ξ * e (d ξ) y) (μ.restrict 𝓕₁) := fun ξ =>
    (Integrable.of_bound (he_cont _).aestronglyMeasurable 1 (ae_of_all _ fun y => (he_norm _ _).le)).const_mul _
  have hnormint : ∀ ξ : κ ⊕ κ → F, ∫ y in 𝓕₁, ‖a ξ * e (d ξ) y‖ ∂μ = ‖a ξ‖ * μ.real 𝓕₁ := by
    intro ξ
    simp only [norm_mul, he_norm, mul_one]
    rw [setIntegral_const, smul_eq_mul]; ring
  have hsumint : Summable fun ξ : κ ⊕ κ → F => ∫ y in 𝓕₁, ‖a ξ * e (d ξ) y‖ ∂μ := by
    simp_rw [hnormint]
    exact hsum.mul_right _
  have horth : ∀ ζ : κ → F, ∫ y in 𝓕₁, e ζ y ∂μ = if ζ = 0 then (μ.real 𝓕₁ : ℂ) else 0 := by
    intro ζ
    split_ifs with hζ
    · subst hζ
      have : ∀ y, e 0 y = 1 := fun y => by simp [he, hemb]
      simp_rw [this]; rw [setIntegral_const]; simp
    · obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
        by_contra h; push_neg at h; exact hζ (funext h)
      haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := by
        refine Function.Surjective.countable (f := fun ρ : κ → F => (⟨emb ρ, ?_⟩ : GlobalTheory.ThetaParseval.ratVec F κ)) ?_
        · exact (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ρ, by rw [hemb]⟩
        · rintro ⟨r, hr⟩
          obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
          exact ⟨ρ, by subst hemb; rfl⟩
      refine GlobalTheory.ThetaParsevalInner.setIntegral_eq_zero_of_twist μ (GlobalTheory.ThetaParseval.ratVec F κ) hF (h := e ζ) ?_
        (c := Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0)) (a := ψ s0) ?_ hs0
      · intro r hr y
        obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        rw [show emb ζ ⬝ᵥ (fun i => algebraMap F (AF F) (ρ i)) = algebraMap F (AF F) (ζ ⬝ᵥ ρ) by
          subst hemb; simp [dotProduct, map_sum, map_mul], htriv, one_mul]
      · intro y
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        congr 2
        rw [dotProduct_single, hemb]
        simp only
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  have hFval : ∀ ξ : κ ⊕ κ → F, ∫ y in 𝓕₁, a ξ * e (d ξ) y ∂μ =
      if d ξ = 0 then (μ.real 𝓕₁ : ℂ) * a ξ else 0 := by
    intro ξ
    rw [integral_const_mul, horth]
    split_ifs <;> ring
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hFint hsumint]
  simp_rw [hFval]
  have hinj : Function.Injective (fun η : κ → F => (Sum.elim η η : κ ⊕ κ → F)) := fun η η' h => by
    funext i; exact congrFun h (Sum.inl i)
  rw [← hinj.tsum_eq, ← tsum_mul_left]
  · refine tsum_congr fun η => ?_
    have hd0 : d (Sum.elim η η) = 0 := by rw [hd]; funext i; simp
    rw [if_pos hd0, ha]
    dsimp only
    congr 2
    funext s; cases s <;> simp
  · intro ξ hξ
    have h0 : d ξ = 0 := by
      by_contra h; exact hξ (if_neg h)
    refine ⟨ξ ∘ Sum.inl, ?_⟩
    funext s
    cases s with
    | inl i => rfl
    | inr i =>
      have := congrFun h0 i
      rw [hd] at this
      simp only [Pi.sub_apply, Function.comp_apply, Pi.zero_apply, sub_eq_zero] at this
      simpa using this

end GlobalTheory.ThetaDiagUnfold
