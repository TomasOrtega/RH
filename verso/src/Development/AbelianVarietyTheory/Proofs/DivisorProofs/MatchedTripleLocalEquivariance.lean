import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaExistsDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLocalGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrabilityStatement

noncomputable section

namespace GlobalTheory.ThKAdj

open scoped ComplexConjugate
open MeasureTheory

section Abstract

variable {V Y : Type*} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `h` using `hT 0 D.zero_mem 0 D.zero_mem 1`. Simplify using `using h`.
-/
theorem map_zero_of (D : Submodule ℂ V) (T : V → Y → ℂ)
    (hT : ∀ Φ ∈ D, ∀ Ψ ∈ D, ∀ c : ℂ, T (Φ + c • Ψ) = T Φ + c • T Ψ) : T 0 = 0 := by
  have h := hT 0 D.zero_mem 0 D.zero_mem 1
  simpa using h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [map_zero_of D T hT]`. Consider the case `insert a s ha ih`. Establish `hs : ∀ i ∈ s, Φ i ∈ D` using `fun i hi => hΦ i (Finset.mem_insert_of_mem hi)`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, add_comm, hT _ (D.sum_mem fun i hi => D.smul_mem (c i) (hs i hi)) _ (hΦ a (Finset.mem_insert_self a s)), ih hs, add_comm]`.
-/
theorem map_sum_of (D : Submodule ℂ V) (T : V → Y → ℂ)
    (hT : ∀ Φ ∈ D, ∀ Ψ ∈ D, ∀ c : ℂ, T (Φ + c • Ψ) = T Φ + c • T Ψ) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (Φ : ι → V) (hΦ : ∀ i ∈ s, Φ i ∈ D) : T (∑ i ∈ s, c i • Φ i) = ∑ i ∈ s, c i • T (Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [map_zero_of D T hT]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, Φ i ∈ D := fun i hi => hΦ i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm,
      hT _ (D.sum_mem fun i hi => D.smul_mem (c i) (hs i hi)) _ (hΦ a (Finset.mem_insert_self a s)), ih hs, add_comm]

/- English proof (translation)
Establish `e : (fun x => f x * conj (g x)) = fun x => ((((‖f x + (1 : ℂ) * g x‖ ^ 2 : ℝ) : ℂ) - ((‖f x + (-1 : ℂ) * g x‖ ^ 2 : ℝ) : ℂ) + Complex.I * ((‖f x + Complex.I * g x‖ ^ 2 : ℝ) : ℂ) - Complex.I * ((‖f x + (-Complex.I) * g x‖ ^ 2 : ℝ) : ℂ)) / 4)`. Use function extensionality and compare the values at `x`. Rewrite using `[one_mul]`. Conclude with `GlobalTheory.ThetaFacCompl.mul_conj_polar (f x) (g x)`. Rewrite using `[e]`.

Conclude with `(((((h 1).ofReal (𝕜 := ℂ)).sub ((h (-1)).ofReal (𝕜 := ℂ))).add (((h Complex.I).ofReal (𝕜 := ℂ)).const_mul Complex.I)).sub (((h (-Complex.I)).ofReal (𝕜 := ℂ)).const_mul Complex.I)).div_const 4`.
-/
theorem integrable_mul_conj {X : Type*} [MeasurableSpace X] {ν : Measure X} (f g : X → ℂ)
    (h : ∀ c : ℂ, Integrable (fun x => ‖f x + c * g x‖ ^ 2) ν) : Integrable (fun x => f x * conj (g x)) ν := by
  have e : (fun x => f x * conj (g x)) = fun x =>
      ((((‖f x + (1 : ℂ) * g x‖ ^ 2 : ℝ) : ℂ) - ((‖f x + (-1 : ℂ) * g x‖ ^ 2 : ℝ) : ℂ)
        + Complex.I * ((‖f x + Complex.I * g x‖ ^ 2 : ℝ) : ℂ)
        - Complex.I * ((‖f x + (-Complex.I) * g x‖ ^ 2 : ℝ) : ℂ)) / 4) := by
    funext x
    rw [one_mul]
    exact GlobalTheory.ThetaFacCompl.mul_conj_polar (f x) (g x)
  rw [e]
  exact (((((h 1).ofReal (𝕜 := ℂ)).sub ((h (-1)).ofReal (𝕜 := ℂ))).add
    (((h Complex.I).ofReal (𝕜 := ℂ)).const_mul Complex.I)).sub
    (((h (-Complex.I)).ofReal (𝕜 := ℂ)).const_mul Complex.I)).div_const 4

end Abstract

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 Ψ hΨ Ψ' hΨ' n c k hk`. Establish `hlin` using `GlobalTheory.T.matched_pair_theta_local_global hKP F E σ B a a' G X om om' R Rf hM`. Establish `hstab` using `(GlobalTheory.T.matched_pair_theta_exists_data hKP F E σ B a a' G X om om' R Rf hM).2`. Establish `hinv` using `GlobalTheory.T.matched_pair_theta_finite_places hKP F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕`. Establish `hsq` using `(GlobalTheory.T.square_integrability hKP F E σ B a a' G X om om' hM.triple μ 𝓕 hμ h𝓕).2`.

Establish `hmem : ∀ i, om' (1, k i) Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁` using `fun i => hstab _ (hk i) Ψ hΨ`. Establish `hmem' : ∀ i, om' (1, (k i)⁻¹) Ψ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁` using `fun i => hstab _ (GlobalTheory.ThetaFacCompl.inv_mem_KInf B.emb (hk i)) Ψ' hΨ'`. Establish `hint : ∀ Φ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, IntegrableOn (fun x => G.M'.I om' Φ x * conj (G.M'.I om' Φ' x)) 𝓕 μ`. Introduce `Φ hΦ Φ' hΦ'`. Apply `integrable_mul_conj` to reduce the goal to its premises.

Introduce `c'`. Establish `h` using `hsq _ (Submodule.add_mem _ hΦ (Submodule.smul_mem _ c' hΦ'))`. Rewrite `h` using `[hlin Φ hΦ Φ' hΦ' c']`. Conclude with `h`. Establish `hterm : ∀ i, ∫ x in 𝓕, G.M'.I om' (om' (1, k i) Ψ) x * conj (G.M'.I om' Ψ' x) ∂μ = ∫ x in 𝓕, G.M'.I om' Ψ x * conj (G.M'.I om' (om' (1, (k i)⁻¹) Ψ') x) ∂μ`.

Introduce `i`. Rewrite using `[← hinv Ψ hΨ _ (hmem' i) (k i)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[GlobalTheory.ThetaFacCompl.I_transl, GlobalTheory.ThetaFacCompl.I_transl, mul_assoc, mul_inv_cancel, mul_one]`.

Establish `eL : (fun x => G.M'.I om' (∑ i, c i • om' (1, k i) Ψ) x * conj (G.M'.I om' Ψ' x)) = fun x => ∑ i, c i * (G.M'.I om' (om' (1, k i) Ψ) x * conj (G.M'.I om' Ψ' x))`. Use function extensionality and compare the values at `x`. Rewrite using `[map_sum_of _ (G.M'.I om') hlin Finset.univ c (fun i => om' (1, k i) Ψ) (fun i _ => hmem i)]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]`. Establish `eR : (fun x => G.M'.I om' Ψ x * conj (G.M'.I om' (∑ i, conj (c i) • om' (1, (k i)⁻¹) Ψ') x)) = fun x => ∑ i, c i * (G.M'.I om' Ψ x * conj (G.M'.I om' (om' (1, (k i)⁻¹) Ψ') x))`.

Use function extensionality and compare the values at `x`. Rewrite using `[map_sum_of _ (G.M'.I om') hlin Finset.univ (fun i => conj (c i)) (fun i => om' (1, (k i)⁻¹) Ψ') (fun i _ => hmem' i)]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations. Rewrite using `[eL, eR, integral_finset_sum _ (fun i _ => (hint _ (hmem i) _ hΨ').const_mul (c i)), integral_finset_sum _ (fun i _ => (hint _ hΨ _ (hmem' i)).const_mul (c i))]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul, integral_const_mul, hterm i]`.
-/
theorem setIntegral_comb_transl : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (μ : MeasureTheory.Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) (𝓕 : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)), μ.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ G.W.J) 𝓕 μ → ∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ Ψ' ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ (n : ℕ) (c : Fin n → ℂ) (k : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), (∀ i, k i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb) → ∫ x in 𝓕, G.M'.I om' (∑ i, c i • om' (1, k i) Ψ) x * starRingEnd ℂ (G.M'.I om' Ψ' x) ∂μ = ∫ x in 𝓕, G.M'.I om' Ψ x * starRingEnd ℂ (G.M'.I om' (∑ i, starRingEnd ℂ (c i) • om' (1, (k i)⁻¹) Ψ') x) ∂μ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 Ψ hΨ Ψ' hΨ' n c k hk
  have hlin := GlobalTheory.T.matched_pair_theta_local_global hKP F E σ B a a' G X om om' R Rf hM
  have hstab := (GlobalTheory.T.matched_pair_theta_exists_data hKP F E σ B a a' G X om om' R Rf hM).2
  have hinv := GlobalTheory.T.matched_pair_theta_finite_places hKP F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕
  have hsq := (GlobalTheory.T.square_integrability hKP F E σ B a a' G X om om' hM.triple μ 𝓕 hμ h𝓕).2
  have hmem : ∀ i, om' (1, k i) Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ := fun i => hstab _ (hk i) Ψ hΨ
  have hmem' : ∀ i, om' (1, (k i)⁻¹) Ψ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ :=
    fun i => hstab _ (GlobalTheory.ThetaFacCompl.inv_mem_KInf B.emb (hk i)) Ψ' hΨ'
  have hint : ∀ Φ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      IntegrableOn (fun x => G.M'.I om' Φ x * conj (G.M'.I om' Φ' x)) 𝓕 μ := by
    intro Φ hΦ Φ' hΦ'
    apply integrable_mul_conj
    intro c'
    have h := hsq _ (Submodule.add_mem _ hΦ (Submodule.smul_mem _ c' hΦ'))
    rw [hlin Φ hΦ Φ' hΦ' c'] at h
    exact h
  have hterm : ∀ i, ∫ x in 𝓕, G.M'.I om' (om' (1, k i) Ψ) x * conj (G.M'.I om' Ψ' x) ∂μ =
      ∫ x in 𝓕, G.M'.I om' Ψ x * conj (G.M'.I om' (om' (1, (k i)⁻¹) Ψ') x) ∂μ := by
    intro i
    rw [← hinv Ψ hΨ _ (hmem' i) (k i)]
    congr 1
    funext x
    rw [GlobalTheory.ThetaFacCompl.I_transl, GlobalTheory.ThetaFacCompl.I_transl, mul_assoc, mul_inv_cancel, mul_one]
  have eL : (fun x => G.M'.I om' (∑ i, c i • om' (1, k i) Ψ) x * conj (G.M'.I om' Ψ' x)) =
      fun x => ∑ i, c i * (G.M'.I om' (om' (1, k i) Ψ) x * conj (G.M'.I om' Ψ' x)) := by
    funext x
    rw [map_sum_of _ (G.M'.I om') hlin Finset.univ c (fun i => om' (1, k i) Ψ) (fun i _ => hmem i)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
  have eR : (fun x => G.M'.I om' Ψ x * conj (G.M'.I om' (∑ i, conj (c i) • om' (1, (k i)⁻¹) Ψ') x)) =
      fun x => ∑ i, c i * (G.M'.I om' Ψ x * conj (G.M'.I om' (om' (1, (k i)⁻¹) Ψ') x)) := by
    funext x
    rw [map_sum_of _ (G.M'.I om') hlin Finset.univ (fun i => conj (c i)) (fun i => om' (1, (k i)⁻¹) Ψ')
      (fun i _ => hmem' i)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [eL, eR, integral_finset_sum _ (fun i _ => (hint _ (hmem i) _ hΨ').const_mul (c i)),
    integral_finset_sum _ (fun i _ => (hint _ hΨ _ (hmem' i)).const_mul (c i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_const_mul, hterm i]

end GlobalTheory.ThKAdj

end
