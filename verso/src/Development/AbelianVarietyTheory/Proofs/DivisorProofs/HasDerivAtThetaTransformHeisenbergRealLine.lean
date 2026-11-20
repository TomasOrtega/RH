import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSummableMajorantRationalVectorsLocallyUnif

noncomputable section

namespace GlobalTheory.ThetaLineDeriv

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (realAd)
open scoped Matrix Classical

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, g, hg, rfl⟩` from `h`. Set `A : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)` to `(LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) σ).toContinuousLinearEquiv`. Set `B : (κ' → Af F) ≃ₜ (κ → Af F)` to `(Homeomorph.piCongrLeft (Y := fun _ => Af F) σ).symm`.

Use `Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f, g ∘ B, ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2`. Consider the case `smul c Φ _ h => exact Submodule.smul_mem _ c h`.
-/
theorem comp_mem_schA {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : κ ≃ κ')
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : (fun x : κ' → AF F => Φ (x ∘ σ)) ∈ schA F κ' := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let A : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
      (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) σ).toContinuousLinearEquiv
    let B : (κ' → Af F) ≃ₜ (κ → Af F) := (Homeomorph.piCongrLeft (Y := fun _ => Af F) σ).symm
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f, g ∘ B,
      ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩, ?_⟩
    rfl
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c Φ _ h => exact Submodule.smul_mem _ c h

/- English proof (translation)
Take `⟨-, ⟨K, hK, hKz⟩, hdec⟩` from `hΦ`. Take `⟨k, hk⟩` from `GlobalTheory.SumMaj.summable_majorant F N hF K hK`. Take `⟨C, hC⟩` from `hdec k`. Establish `hC0 : 0 ≤ C` using `le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k)) (hC 0)`. Take `⟨c, hcs, hc0, hcb⟩` from `hk ω hω`.

Use `⟨fun ξ => C * c ξ, hcs.mul_left C, fun ξ y hy => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hmem : fin (rat ξ + y) ∈ K`. Establish `h1` using `hcb ξ y hy hmem`. Establish `h2` using `hC (rat ξ + y)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hKz _ hmem, norm_zero]`. Conclude with `mul_nonneg hC0 (hc0 ξ)`.
-/
theorem decay_majorant {N : ℕ} (hF : IsTotallyReal F)
    {Φ : (Fin N → AF F) → ℂ} (hΦ : Decay Φ) (ω : Set (Fin N → AF F)) (hω : IsCompact ω) :
    ∃ c : (Fin N → F) → ℝ, Summable c ∧ ∀ ξ, ∀ y ∈ ω, ‖Φ (rat ξ + y)‖ ≤ c ξ := by
  obtain ⟨-, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨k, hk⟩ := GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k))
      (hC 0)
  obtain ⟨c, hcs, hc0, hcb⟩ := hk ω hω
  refine ⟨fun ξ => C * c ξ, hcs.mul_left C, fun ξ y hy => ?_⟩
  by_cases hmem : fin (rat ξ + y) ∈ K
  · have h1 := hcb ξ y hy hmem
    have h2 := hC (rat ξ + y)
    calc ‖Φ (rat ξ + y)‖ = ‖Φ (rat ξ + y)‖ * 1 := (mul_one _).symm
      _ ≤ ‖Φ (rat ξ + y)‖ * (c ξ * (1 + sz (rat ξ + y)) ^ k) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = c ξ * (‖Φ (rat ξ + y)‖ * (1 + sz (rat ξ + y)) ^ k) := by ring
      _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
      _ = C * c ξ := mul_comm _ _
  · rw [hKz _ hmem, norm_zero]
    exact mul_nonneg hC0 (hc0 ξ)

/- English proof (translation)
Set `σ` to `Fintype.equivFin κ`. Establish `hc : Continuous fun y : κ → AF F => y ∘ σ.symm` using `continuous_pi fun i => continuous_apply _`. Take `⟨c, hcs, hcb⟩` from `decay_majorant hF (GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (comp_mem_schA σ hΦ)) _ (hω.image hc)`. Use `⟨fun ξ => c (ξ ∘ σ.symm), (Equiv.arrowCongr σ (Equiv.refl F)).summable_iff.2 hcs, fun ξ y hy => ?_⟩` and prove the remaining obligations. Establish `h` using `hcb (ξ ∘ σ.symm) _ ⟨y, hy, rfl⟩`.

Establish `e : (rat (ξ ∘ σ.symm) + y ∘ σ.symm) ∘ σ = (fun i => algebraMap F (AF F) (ξ i)) + y`. Use function extensionality and compare the values at `i`. Simplify using `[rat]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem schA_majorant {κ : Type} [Fintype κ] (hF : IsTotallyReal F)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (ω : Set (κ → AF F)) (hω : IsCompact ω) :
    ∃ c : (κ → F) → ℝ, Summable c ∧
      ∀ ξ : κ → F, ∀ y ∈ ω, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + y)‖ ≤ c ξ := by
  let σ := Fintype.equivFin κ
  have hc : Continuous fun y : κ → AF F => y ∘ σ.symm := continuous_pi fun i => continuous_apply _
  obtain ⟨c, hcs, hcb⟩ := decay_majorant hF
    (GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (comp_mem_schA σ hΦ)) _ (hω.image hc)
  refine ⟨fun ξ => c (ξ ∘ σ.symm), (Equiv.arrowCongr σ (Equiv.refl F)).summable_iff.2 hcs, fun ξ y hy => ?_⟩
  have h := hcb (ξ ∘ σ.symm) _ ⟨y, hy, rfl⟩
  have e : (rat (ξ ∘ σ.symm) + y ∘ σ.symm) ∘ σ = (fun i => algebraMap F (AF F) (ξ i)) + y := by
    funext i
    simp [rat]
  rwa [e] at h

/- English proof (translation)
Use `continuous_pi fun v => ?_` and prove the remaining obligations. Break down `v.isReal_or_isComplex with hv | hv` into its components or cases. Rewrite using `[(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]`. Conclude with `((continuous_apply _).comp continuous_fst).congr fun y => (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm`. Rewrite using `[(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]`.

Conclude with `((continuous_apply _).comp continuous_snd).congr fun y => (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm`.
-/
theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

/- English proof (translation)
The claim follows from `Continuous.prodMk (continuous_ofMixed.comp (continuous_algebraMap ℝ _)) continuous_const`.
-/
theorem continuous_realAd : Continuous (realAd F) :=
  Continuous.prodMk (continuous_ofMixed.comp (continuous_algebraMap ℝ _)) continuous_const

/- English proof (translation)
Simplify using `only [realAd, map_add]`. Both sides reduce to the same expression.
-/
theorem realAd_add (s t : ℝ) : realAd F (s + t) = realAd F s + realAd F t := by
  simp only [realAd, map_add]
  rfl

/- English proof (translation)
Simplify using `only [realAd, map_zero]`. Both sides reduce to the same expression.
-/
theorem realAd_zero : realAd F 0 = 0 := by
  simp only [realAd, map_zero]
  rfl

/- English proof (translation)
Simplify using `only [schr, Prod.smul_fst, Prod.smul_snd, ← mul_assoc, ← AddChar.map_add_eq_mul, add_smul, add_assoc]`. Use `congr 2`. Simplify using `only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]`. Use `first`. Consider the case `linear_combination (a * b * (v.1 ⬝ᵥ v.2)) * invOf_mul_self (2 : R)`.

Consider the case `linear_combination (-(a * b * (v.1 ⬝ᵥ v.2))) * invOf_mul_self (2 : R)`.
-/
theorem schr_smul_add {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (v : (κ → R) × (κ → R)) (a b : R) (Φ : (κ → R) → ℂ) (z : κ → R) :
    schr ψ ((a + b) • v) Φ z = schr ψ (a • v) (schr ψ (b • v) Φ) z := by
  simp only [schr, Prod.smul_fst, Prod.smul_snd, ← mul_assoc, ← AddChar.map_add_eq_mul, add_smul, add_assoc]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  first
    | linear_combination (a * b * (v.1 ⬝ᵥ v.2)) * invOf_mul_self (2 : R)
    | linear_combination (-(a * b * (v.1 ⬝ᵥ v.2))) * invOf_mul_self (2 : R)

variable [Invertible (2 : AF F)] {κ : Type} [Fintype κ]

/- English proof (translation)
Establish `h1 : HasDerivAt (fun h : ℝ => schr ψ (realAd F (t + h) • v) Φ z) (schr ψ (realAd F t • v) Φ' z) (t - t)`. Establish `e : (fun h : ℝ => schr ψ (realAd F (t + h) • v) Φ z) = fun h => ψ (z ⬝ᵥ (realAd F t • v).2 + ⅟(2 : AF F) * ((realAd F t • v).1 ⬝ᵥ (realAd F t • v).2)) * schr ψ (realAd F h • v) Φ (z + (realAd F t • v).1)`. Use function extensionality and compare the values at `h`. Rewrite using `[realAd_add, schr_smul_add]`. Both sides reduce to the same expression.

Rewrite using `[e, sub_self]`. Conclude with `(hd _).const_mul _`. Establish `h2` using `h1.comp_sub_const t t`. Simplify `h2` using `only [add_sub_cancel]`.
-/
theorem hasDerivAt_schr (ψ : AddChar (AF F) ℂ) (v : (κ → AF F) × (κ → AF F))
    {Φ Φ' : (κ → AF F) → ℂ} (hd : ∀ z, HasDerivAt (fun s : ℝ => schr ψ (realAd F s • v) Φ z) (Φ' z) 0)
    (z : κ → AF F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => schr ψ (realAd F s • v) Φ z) (schr ψ (realAd F t • v) Φ' z) t := by
  have h1 : HasDerivAt (fun h : ℝ => schr ψ (realAd F (t + h) • v) Φ z) (schr ψ (realAd F t • v) Φ' z) (t - t) := by
    have e : (fun h : ℝ => schr ψ (realAd F (t + h) • v) Φ z) = fun h =>
        ψ (z ⬝ᵥ (realAd F t • v).2 + ⅟(2 : AF F) * ((realAd F t • v).1 ⬝ᵥ (realAd F t • v).2)) *
          schr ψ (realAd F h • v) Φ (z + (realAd F t • v).1) := by
      funext h
      rw [realAd_add, schr_smul_add]
      rfl
    rw [e, sub_self]
    exact (hd _).const_mul _
  have h2 := h1.comp_sub_const t t
  simpa only [add_sub_cancel] using h2

/- English proof (translation)
Establish `hnorm : ∀ x, ‖ψ x‖ = 1` using `hψ.2.1`. Establish `hM0 : realAd F 0 • v = 0` using `by rw [realAd_zero, zero_smul]`. Use `set ω : Set (κ → AF F) := (fun s : ℝ => w.1 + (realAd F s • v).1) '' Set.Icc (-1) 1 with hω`. Establish `hωc : IsCompact ω` using `isCompact_Icc.image (continuous_const.add (continuous_pi fun i => continuous_realAd.mul (continuous_const (y := v.1 i))))`. Take `⟨c, hcs, hcb⟩` from `schA_majorant hF hΦ' ω hωc`.

Take `⟨c₀, hcs₀, hcb₀⟩` from `schA_majorant hF hΦ {w.1} isCompact_singleton`. Use `set r : (κ → F) → (κ → AF F) := fun ξ i => algebraMap F (AF F) (ξ i) with hr`. Use `set ph : (κ → F) → ℂ := fun ξ => ψ (r ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph`. Establish `e : (fun t : ℝ => thetaSum F (schr ψ w (schr ψ (realAd F t • v) Φ))) = fun t => ∑' ξ : κ → F, ph ξ * schr ψ (realAd F t • v) Φ (r ξ + w.1)` using `rfl`. Establish `h0 : ∀ Ψ : (κ → AF F) → ℂ, schr ψ (realAd F 0 • v) Ψ = Ψ` using `fun Ψ => by`.

Rewrite using `[hM0]`. Use function extensionality and compare the values at `z`. Simplify using `[schr]`. Establish `hv : thetaSum F (schr ψ w Φ') = ∑' ξ : κ → F, ph ξ * schr ψ (realAd F 0 • v) Φ' (r ξ + w.1)`. Rewrite using `[h0]`.

Both sides reduce to the same expression. Rewrite using `[e, hv]`. Establish `hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1` using `⟨by norm_num, by norm_num⟩`. Use `hasDerivAt_tsum_of_isPreconnected hcs isOpen_Ioo isPreconnected_Ioo (fun ξ t _ => (hasDerivAt_schr ψ v hd (r ξ + w.1) t).const_mul (ph ξ)) (fun ξ t ht => ?_) hmem ?_ hmem` and prove the remaining obligations. Establish `hy : w.1 + (realAd F t • v).1 ∈ ω` using `⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩`.

Use `hcb ξ _ hy` as an intermediate fact. Simplify using `only [ph, schr, norm_mul, hnorm, one_mul, add_assoc]`. Conclude with `this`. Use `Summable.of_norm_bounded hcs₀ fun ξ => ?_` and prove the remaining obligations. Use `hcb₀ ξ w.1 rfl` as an intermediate fact.

Simplify using `only [h0, ph, norm_mul, hnorm, one_mul]`. Conclude with `this`.
-/
theorem hasDerivAt_thetaSum_schr (ψ : AddChar (AF F) ℂ) (hF : IsTotallyReal F) (hψ : IsCharAF F ψ)
    (v : (κ → AF F) × (κ → AF F)) {Φ Φ' : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (hΦ' : Φ' ∈ schA F κ)
    (hd : ∀ z, HasDerivAt (fun s : ℝ => schr ψ (realAd F s • v) Φ z) (Φ' z) 0) (w : (κ → AF F) × (κ → AF F)) :
    HasDerivAt (fun t : ℝ => thetaSum F (schr ψ w (schr ψ (realAd F t • v) Φ))) (thetaSum F (schr ψ w Φ')) 0 := by
  have hnorm : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hM0 : realAd F 0 • v = 0 := by rw [realAd_zero, zero_smul]
  set ω : Set (κ → AF F) := (fun s : ℝ => w.1 + (realAd F s • v).1) '' Set.Icc (-1) 1 with hω
  have hωc : IsCompact ω := isCompact_Icc.image
    (continuous_const.add (continuous_pi fun i => continuous_realAd.mul (continuous_const (y := v.1 i))))
  obtain ⟨c, hcs, hcb⟩ := schA_majorant hF hΦ' ω hωc
  obtain ⟨c₀, hcs₀, hcb₀⟩ := schA_majorant hF hΦ {w.1} isCompact_singleton
  set r : (κ → F) → (κ → AF F) := fun ξ i => algebraMap F (AF F) (ξ i) with hr
  set ph : (κ → F) → ℂ := fun ξ => ψ (r ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph
  have e : (fun t : ℝ => thetaSum F (schr ψ w (schr ψ (realAd F t • v) Φ))) =
      fun t => ∑' ξ : κ → F, ph ξ * schr ψ (realAd F t • v) Φ (r ξ + w.1) := rfl
  have h0 : ∀ Ψ : (κ → AF F) → ℂ, schr ψ (realAd F 0 • v) Ψ = Ψ := fun Ψ => by
    rw [hM0]
    funext z
    simp [schr]
  have hv : thetaSum F (schr ψ w Φ') = ∑' ξ : κ → F, ph ξ * schr ψ (realAd F 0 • v) Φ' (r ξ + w.1) := by
    rw [h0]
    rfl
  rw [e, hv]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine hasDerivAt_tsum_of_isPreconnected hcs isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (hasDerivAt_schr ψ v hd (r ξ + w.1) t).const_mul (ph ξ)) (fun ξ t ht => ?_) hmem ?_ hmem
  · have hy : w.1 + (realAd F t • v).1 ∈ ω := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have := hcb ξ _ hy
    simp only [ph, schr, norm_mul, hnorm, one_mul, add_assoc]
    exact this
  · refine Summable.of_norm_bounded hcs₀ fun ξ => ?_
    have := hcb₀ ξ w.1 rfl
    simp only [h0, ph, norm_mul, hnorm, one_mul]
    exact this

end SlopeTestRemainingChoices

end GlobalTheory.ThetaLineDeriv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

/- English proof (translation)
Introduce `F _ _ U _ _ B κ _ co ψ hF hψ u Φ hΦ Φ' hΦ' hd w`. Simplify using `only [Darboux.rho, map_smul] at hd ⊢`. Conclude with `GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_schr ψ hF hψ (co.e u) hΦ hΦ' hd (co.e w)`.
-/
theorem GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho : ∀ {F : Type} [Field F] [NumberField F] {U : Type} [AddCommGroup U] [Module (AF F) U] {B : U → U → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ (u : U), ∀ Φ ∈ schA F κ, ∀ Φ' ∈ schA F κ,
    (∀ x, HasDerivAt (fun t : ℝ => co.rho ψ (realAd F t • u) Φ x) (Φ' x) 0) →
    ∀ w : U, HasDerivAt (fun t : ℝ => thetaSum F (co.rho ψ w (co.rho ψ (realAd F t • u) Φ))) (thetaSum F (co.rho ψ w Φ')) 0 := by
  intro F _ _ U _ _ B κ _ co ψ hF hψ u Φ hΦ Φ' hΦ' hd w
  simp only [Darboux.rho, map_smul] at hd ⊢
  exact GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_schr ψ hF hψ (co.e u) hΦ hΦ' hd (co.e w)

end
