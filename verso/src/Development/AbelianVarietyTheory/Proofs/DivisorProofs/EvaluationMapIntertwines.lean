import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticTraceBasisExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.IsoXArchDecay

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay GlobalTheory.XTermDecay

section Scalar

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [finOp, finS, h1, h2, dotProduct, mul_zero, Finset.sum_const_zero, add_zero, AddChar.map_zero_eq_one, one_mul]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `add_zero _`.
-/
theorem finite_heisenberg_op_trivial (ψ : AddChar (AF F) ℂ) (g : (κ → Af F) → ℂ) (w : (κ → AF F) × (κ → AF F))
    (h1 : ∀ a, p2 (w.1 a) = 0) (h2 : ∀ a, p2 (w.2 a) = 0) : finOp ψ g w = g := by
  funext z
  simp only [finOp, finS, h1, h2, dotProduct, mul_zero, Finset.sum_const_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
  congr 1
  funext a
  exact add_zero _

/- English proof (translation)
Apply the tactic sequence `constructor <;> intro a <;>`. Simplify using `only [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hx, zero_mul, Finset.sum_const_zero]`.
-/
theorem finite_part_sum_smul_zero {ι : Type} [Fintype ι] (x : ι → AF F) (hx : ∀ i, p2 (x i) = 0) (S : ι → (κ → AF F) × (κ → AF F)) :
    (∀ a, p2 ((∑ i, x i • S i).1 a) = 0) ∧ ∀ a, p2 ((∑ i, x i • S i).2 a) = 0 := by
  constructor <;> intro a <;>
    simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      map_sum, map_mul, hx, zero_mul, Finset.sum_const_zero]

/- English proof (translation)
Take `⟨C₀, hC₀⟩` from `GlobalTheory.T.heisenberg_character_minus_one F ψ hψ ι`. Take `⟨L, hL⟩` from `he g hg`. Take `⟨q, hq, hdec⟩` from `(tame_archOp (F := F) (κ := κ)).decay ((normSeminorm ℂ ℂ).comp L.toLinearMap) (continuous_norm.comp L.continuous) (∑ i, ‖archW (S i)‖) (C₀ * ∑ i, ‖archW (U i)‖) N`. Use `⟨q f, fun x hx => ?_⟩` and prove the remaining obligations. Use `set s := ∑ i, x i • S i with hs`.

Use `set r := ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ with hr`. Establish `hr0 : 0 ≤ r` using `by positivity`. Take `⟨hs1, hs2⟩` from `finite_part_sum_smul_zero x hx S`. Establish `hLs : ∀ h : SInf F κ, L (archOp (archW s) h) = e (schr ψ s (pureA F h g))` using `fun h => by`. Rewrite using `[schr_pureA ψ hψ, finite_heisenberg_op_trivial ψ g s hs1 hs2, hL]`.

Rewrite using `[← hLs]`. Use `hdec (archW s) r hr0 ?_ (fun hr1 => ?_) f` and prove the remaining obligations. Rewrite using `[hs, archW_sum, Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[archW_smul, mul_comm]`.

Use `(norm_smul_le _ _).trans ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `(norm_qA_le _).trans (Finset.single_le_sum (f := fun i => ∑ v : InfinitePlace F, ‖(x i).1 v‖) (fun _ _ => by positivity) (Finset.mem_univ i))`. Take `⟨i, a, ha, ha'⟩` from `hC₀ x hr1`. Use `⟨archW (mk a 0 • U i), ?_, fun h => ?_⟩` and prove the remaining obligations.

Rewrite using `[archW_smul]`. Establish `h1 : ‖archW (U i)‖ ≤ ∑ i, ‖archW (U i)‖` using `Finset.single_le_sum (f := fun i => ‖archW (U i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)`. Combine the equalities or inequalities in the displayed calculation. Establish `hz : L (archOp (archW s) (archOp (archW (mk a 0 • U i)) h + h)) = 0`. Establish `hΦ : pureA F h g ∈ schA F κ` using `Submodule.subset_span ⟨h, g, hg, rfl⟩`.

Establish `hω : s.1 ⬝ᵥ (mk a 0 • U i).2 - (mk a 0 • U i).1 ⬝ᵥ s.2 = x i * mk a 0`. Establish `: ∀ j, (x j • S j).1 ⬝ᵥ (mk a 0 • U i).2 - (mk a 0 • U i).1 ⬝ᵥ (x j • S j).2 = if i = j then x j * mk a 0 else 0` using `fun j => by`. Simplify using `only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]`. Use `hSU i j` as an intermediate fact. Use `split_ifs at this ⊢`.

Take the linear combination `(x j * mk a 0) * this`. Take the linear combination `(x j * mk a 0) * this`. Rewrite using `[hs, Prod.fst_sum, Prod.snd_sum, sum_dotProduct, dotProduct_sum, ← Finset.sum_sub_distrib]`. Simplify using `only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Establish `h1 : pureA F (archOp (archW (mk a 0 • U i)) h + h : SInf F κ) g = schr ψ (mk a 0 • U i) (pureA F h g) + pureA F h g`.

Rewrite using `[schr_pureA ψ hψ, finOp_arch]`. Conclude with `pureA_add _ _ _`. Rewrite using `[hLs, h1]`. Express the relevant statement in the definitionally equal form `e (schrL ψ s _) = 0`. Rewrite using `[map_add, map_add]`.

Express the relevant statement in the definitionally equal form `e (schr ψ s _) + e (schr ψ s _) = 0`. Rewrite using `[schr_comm, map_smul, hinv _ _ _ (schr_mem_schA ψ hψ s _ hΦ), hω, ha, neg_one_smul, neg_add_cancel]`. Express the relevant statement in the definitionally equal form `‖L _‖ = 0`. Rewrite using `[hz, norm_zero]`.
-/
theorem scalar_decay_pure {ι : Type} [Fintype ι] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (S U : ι → (κ → AF F) × (κ → AF F)) (hSU : ∀ i j, (S j).1 ⬝ᵥ (U i).2 - (U i).1 ⬝ᵥ (S j).2 = if i = j then 1 else 0)
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (he : e ∈ (adeleClass F).adm κ)
    (hinv : ∀ i (a : AF F), ∀ Φ ∈ schA F κ, e (schr ψ (a • U i) Φ) = e Φ)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (f : SInf F κ) (N : ℕ) :
    ∃ C : ℝ, ∀ x : ι → AF F, (∀ i, p2 (x i) = 0) →
      ‖e (schr ψ (∑ i, x i • S i) (pureA F f g))‖ ≤ C * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖) ^ (-(N : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.heisenberg_character_minus_one F ψ hψ ι
  obtain ⟨L, hL⟩ := he g hg
  obtain ⟨q, hq, hdec⟩ := (tame_archOp (F := F) (κ := κ)).decay ((normSeminorm ℂ ℂ).comp L.toLinearMap)
    (continuous_norm.comp L.continuous) (∑ i, ‖archW (S i)‖) (C₀ * ∑ i, ‖archW (U i)‖) N
  refine ⟨q f, fun x hx => ?_⟩
  set s := ∑ i, x i • S i with hs
  set r := ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ with hr
  have hr0 : 0 ≤ r := by positivity
  obtain ⟨hs1, hs2⟩ := finite_part_sum_smul_zero x hx S
  have hLs : ∀ h : SInf F κ, L (archOp (archW s) h) = e (schr ψ s (pureA F h g)) := fun h => by
    rw [schr_pureA ψ hψ, finite_heisenberg_op_trivial ψ g s hs1 hs2, hL]
  rw [← hLs]
  refine hdec (archW s) r hr0 ?_ (fun hr1 => ?_) f
  · rw [hs, archW_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [archW_smul, mul_comm]
    refine (norm_smul_le _ _).trans ?_
    gcongr
    exact (norm_qA_le _).trans (Finset.single_le_sum (f := fun i => ∑ v : InfinitePlace F, ‖(x i).1 v‖)
      (fun _ _ => by positivity) (Finset.mem_univ i))
  · obtain ⟨i, a, ha, ha'⟩ := hC₀ x hr1
    refine ⟨archW (mk a 0 • U i), ?_, fun h => ?_⟩
    · rw [archW_smul]
      have h1 : ‖archW (U i)‖ ≤ ∑ i, ‖archW (U i)‖ :=
        Finset.single_le_sum (f := fun i => ‖archW (U i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      calc _ ≤ ‖qA (mk a 0)‖ * ‖archW (U i)‖ * r := by gcongr; exact norm_smul_le _ _
        _ = (‖qA (mk a 0)‖ * r) * ‖archW (U i)‖ := by ring
        _ ≤ _ := mul_le_mul ha' h1 (norm_nonneg _) (le_trans (by positivity) ha')
    · have hz : L (archOp (archW s) (archOp (archW (mk a 0 • U i)) h + h)) = 0 := by
        have hΦ : pureA F h g ∈ schA F κ := Submodule.subset_span ⟨h, g, hg, rfl⟩
        have hω : s.1 ⬝ᵥ (mk a 0 • U i).2 - (mk a 0 • U i).1 ⬝ᵥ s.2 = x i * mk a 0 := by
          have : ∀ j, (x j • S j).1 ⬝ᵥ (mk a 0 • U i).2 - (mk a 0 • U i).1 ⬝ᵥ (x j • S j).2 =
              if i = j then x j * mk a 0 else 0 := fun j => by
            simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
            have := hSU i j
            split_ifs at this ⊢
            · linear_combination (x j * mk a 0) * this
            · linear_combination (x j * mk a 0) * this
          rw [hs, Prod.fst_sum, Prod.snd_sum, sum_dotProduct, dotProduct_sum, ← Finset.sum_sub_distrib]
          simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        have h1 : pureA F (archOp (archW (mk a 0 • U i)) h + h : SInf F κ) g =
            schr ψ (mk a 0 • U i) (pureA F h g) + pureA F h g := by
          rw [schr_pureA ψ hψ, finOp_arch]
          exact pureA_add _ _ _
        rw [hLs, h1]
        change e (schrL ψ s _) = 0
        rw [map_add, map_add]
        change e (schr ψ s _) + e (schr ψ s _) = 0
        rw [schr_comm, map_smul, hinv _ _ _ (schr_mem_schA ψ hψ s _ hΦ), hω, ha, neg_one_smul, neg_add_cancel]
      change ‖L _‖ = 0
      rw [hz, norm_zero]

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, g, hg, rfl⟩` from `h`. Conclude with `scalar_decay_pure ψ hψ S U hSU e he hinv hg f N`. Consider the case `zero`.

Use `⟨0, fun x _ => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖e (schrL ψ _ 0)‖ ≤ _`. Rewrite using `[map_zero, map_zero, norm_zero, zero_mul]`. Consider the case `add Φ Φ' _ _ h1 h2`. Take `⟨C₁, h1⟩` from `h1`.

Take `⟨C₂, h2⟩` from `h2`. Use `⟨C₁ + C₂, fun x hx => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖e (schrL ψ _ (Φ + Φ'))‖ ≤ _`. Rewrite using `[map_add, map_add, add_mul]`. Conclude with `(norm_add_le _ _).trans (add_le_add (h1 x hx) (h2 x hx))`.

Consider the case `smul c Φ _ h`. Take `⟨C, h⟩` from `h`. Use `⟨‖c‖ * C, fun x hx => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖e (schrL ψ _ (c • Φ))‖ ≤ _`. Rewrite using `[map_smul, map_smul, norm_smul, mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_left (h x hx) (norm_nonneg _)`.
-/
theorem scalar_decay {ι : Type} [Fintype ι] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (S U : ι → (κ → AF F) × (κ → AF F)) (hSU : ∀ i j, (S j).1 ⬝ᵥ (U i).2 - (U i).1 ⬝ᵥ (S j).2 = if i = j then 1 else 0)
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (he : e ∈ (adeleClass F).adm κ)
    (hinv : ∀ i (a : AF F), ∀ Φ ∈ schA F κ, e (schr ψ (a • U i) Φ) = e Φ)
    (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (N : ℕ) :
    ∃ C : ℝ, ∀ x : ι → AF F, (∀ i, p2 (x i) = 0) →
      ‖e (schr ψ (∑ i, x i • S i) Φ)‖ ≤ C * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖) ^ (-(N : ℝ)) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact scalar_decay_pure ψ hψ S U hSU e he hinv hg f N
  | zero =>
    refine ⟨0, fun x _ => ?_⟩
    change ‖e (schrL ψ _ 0)‖ ≤ _
    rw [map_zero, map_zero, norm_zero, zero_mul]
  | add Φ Φ' _ _ h1 h2 =>
    obtain ⟨C₁, h1⟩ := h1
    obtain ⟨C₂, h2⟩ := h2
    refine ⟨C₁ + C₂, fun x hx => ?_⟩
    change ‖e (schrL ψ _ (Φ + Φ'))‖ ≤ _
    rw [map_add, map_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h1 x hx) (h2 x hx))
  | smul c Φ _ h =>
    obtain ⟨C, h⟩ := h
    refine ⟨‖c‖ * C, fun x hx => ?_⟩
    change ‖e (schrL ψ _ (c • Φ))‖ ≤ _
    rw [map_smul, map_smul, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h x hx) (norm_nonneg _)

end Scalar

end GlobalTheory.IsoXArchDecay

namespace GlobalTheory.IsoXArchDecay

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay GlobalTheory.XTermDecay

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hσ : ∀ z, σ (σ z) = z` using `fun z => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Conclude with `τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])`. Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [← hJ j i]; ring`.
-/
theorem form_swap_herm {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) : form σ J y x = σ (form σ J x y) := by
  have hσ : ∀ z, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [← hJ j i]; ring

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `h` using `GlobalTheory.ArchTraceNondeg.det_ne_zero_of_hasSig (hW.sig w)`. Rewrite `h` using `[Matrix.det_smul]`. Introduce `h0`. Apply `h` to reduce the goal to its premises.

Rewrite using `[show (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det from (RingHom.map_det _ _).symm, h0, map_zero, mul_zero]`.
-/
theorem det_ne_zero_of_skew {σ : E →ₐ[F] E} {B : Base F E} {d r s : ℕ} {W : Spc F E d} (hW : W.IsSkew σ B r s) :
    W.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.ArchTraceNondeg.det_ne_zero_of_hasSig (hW.sig w)
  rw [Matrix.det_smul] at h
  intro h0
  apply h
  rw [show (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det from (RingHom.map_det _ _).symm, h0, map_zero, mul_zero]

/- English proof (translation)
Establish `hbij : Function.Bijective σ` using `σ.bijective`. Set `s : E ≃ₐ[F] E` to `AlgEquiv.ofBijective σ hbij`. Use `⟨fun i c => s.symm (-(J⁻¹ *ᵥ Pi.single i 1) c), fun k i => ?_⟩` and prove the remaining obligations. Establish `hs : (fun c => σ (s.symm (-(J⁻¹ *ᵥ Pi.single i 1) c))) = -(J⁻¹ *ᵥ Pi.single i 1)`. Use function extensionality and compare the values at `fun c => s.apply_symm_apply _`.

Rewrite using `[form, hs, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv J (Ne.isUnit hJ), Matrix.one_mulVec, dotProduct_neg, single_one_dotProduct, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem exists_dual_vec (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (hJ : J.det ≠ 0) :
    ∃ x' : Fin d → Fin d → E, ∀ k i, form σ J (Pi.single k 1) (x' i) = if k = i then -1 else 0 := by
  have hbij : Function.Bijective σ := σ.bijective
  let s : E ≃ₐ[F] E := AlgEquiv.ofBijective σ hbij
  refine ⟨fun i c => s.symm (-(J⁻¹ *ᵥ Pi.single i 1) c), fun k i => ?_⟩
  have hs : (fun c => σ (s.symm (-(J⁻¹ *ᵥ Pi.single i 1) c))) = -(J⁻¹ *ᵥ Pi.single i 1) :=
    funext fun c => s.apply_symm_apply _
  rw [form, hs, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv J (Ne.isUnit hJ), Matrix.one_mulVec,
    dotProduct_neg, single_one_dotProduct, Pi.single_apply]
  split_ifs <;> simp

end Field

end GlobalTheory.IsoXArchDecay

namespace GlobalTheory.IsoXArchDecay

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay GlobalTheory.XTermDecay

section Pair

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Set `bb` to `Module.finBasis F E`. Set `b'` to `(Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) bb`. Establish `hbij : Function.Bijective σ` using `σ.bijective`. Set `s : E ≃ₐ[F] E` to `AlgEquiv.ofBijective σ hbij`.

Use `⟨fun j => s.symm (b' j), fun p q => ?_⟩` and prove the remaining obligations. Take `⟨i, j⟩` from `p`. Take `⟨k, l⟩` from `q`. Establish `hσt : σ (s.symm (b' j)) = b' j` using `s.apply_symm_apply (b' j)`. Rewrite using `[GlobalTheory.ArchDualPair.lhs_eq, GlobalTheory.ArchDualPair.rhs_eq, symp, GlobalTheory.ArchDualPair.hTens_incM, GlobalTheory.ArchDualPair.hTens_vecMulVec', GlobalTheory.ArchDualPair.form_smul, hσt, h1, h2, show (-1 : AE F E) = inclR (F := F) (AF F) (-1) by simp, ← map_mul, Globa …`.

Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality. Rewrite using `[if_pos rfl]`. Establish `ht : Algebra.trace F E (-1 * (bb l * b' j * 1 * -1)) = Algebra.traceForm F E (b' j) (bb l)`. Rewrite using `[Algebra.traceForm_apply]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ht, LinearMap.BilinForm.apply_dualBasis_left]`. Distinguish the cases in `hjl : j = l`. Substitute `hjl` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (Ne.symm hjl), if_neg (fun h => hjl (Prod.mk.inj h).2), map_zero]`. Rewrite using `[if_neg hki, if_neg (fun h => hki (Prod.mk.inj h).1.symm)]`. Simplify using the standard rewrite rules.
-/
theorem dualPair_family (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E)
    (x y : Fin n → E) (x' : Fin d → Fin d → E) (h1 : form σ J x y = 1)
    (h2 : ∀ k i, form σ J' (Pi.single k 1) (x' i) = if k = i then -1 else 0) :
    ∃ t : Fin (Module.finrank F E) → E, ∀ (p q : Fin d × Fin (Module.finrank F E)),
      symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')
        (inclR (F := F) (AF F) (Module.finBasis F E q.2) • Matrix.vecMulVec (incV F x) (incV F (Pi.single q.1 1)))
        (Matrix.vecMulVec (inclR (F := F) (AF F) (t p.2) • incV F y) (incV F (x' p.1))) = if p = q then 1 else 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let bb := Module.finBasis F E
  let b' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) bb
  have hbij : Function.Bijective σ := σ.bijective
  let s : E ≃ₐ[F] E := AlgEquiv.ofBijective σ hbij
  refine ⟨fun j => s.symm (b' j), fun p q => ?_⟩
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  have hσt : σ (s.symm (b' j)) = b' j := s.apply_symm_apply (b' j)
  rw [GlobalTheory.ArchDualPair.lhs_eq, GlobalTheory.ArchDualPair.rhs_eq, symp, GlobalTheory.ArchDualPair.hTens_incM,
    GlobalTheory.ArchDualPair.hTens_vecMulVec', GlobalTheory.ArchDualPair.form_smul, hσt, h1, h2,
    show (-1 : AE F E) = inclR (F := F) (AF F) (-1) by simp, ← map_mul, GlobalTheory.ArchDualPair.trace_inclR']
  by_cases hki : k = i
  · subst hki
    rw [if_pos rfl]
    have ht : Algebra.trace F E (-1 * (bb l * b' j * 1 * -1)) = Algebra.traceForm F E (b' j) (bb l) := by
      rw [Algebra.traceForm_apply]; congr 1; ring
    rw [ht, LinearMap.BilinForm.apply_dualBasis_left]
    by_cases hjl : j = l
    · subst hjl; simp
    · rw [if_neg (Ne.symm hjl), if_neg (fun h => hjl (Prod.mk.inj h).2), map_zero]
  · rw [if_neg hki, if_neg (fun h => hki (Prod.mk.inj h).1.symm)]
    simp

/- English proof (translation)
Establish `hw : ∀ k, inclR (F` using `F) (AF F) (w k) = ∑ j, algebraMap F (AF F) ((Module.finBasis F E).repr (w k) j) • inclR (F := F) (AF F) (Module.finBasis F E j) := fun k => by conv_lhs => rw [← (Module.finBasis F E).sum_repr (w k)]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `show (1 : AF F) ⊗ₜ[F] (_ • _) = _ • ((1 : AF F) ⊗ₜ[F] _)`. Rewrite using `[← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]`.

Use extensionality with `a k`. Simplify using `only [Matrix.smul_apply, Matrix.vecMulVec_apply, incV, Matrix.sum_apply, Fintype.sum_prod_type, Pi.single_apply, hw, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single k (fun x _ hx => by simp [Ne.symm hx]) (by simp)]`. Simplify using `only [if_true, map_one, mul_one, Finset.mul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vecMulVec_sum {n d : ℕ} (y : Fin n → E) (w : Fin d → E) :
    realAd F 1 • Matrix.vecMulVec (incV F y) (incV F w) = ∑ p : Fin d × Fin (Module.finrank F E),
      (realAd F 1 * algebraMap F (AF F) ((Module.finBasis F E).repr (w p.1) p.2)) •
        (inclR (F := F) (AF F) (Module.finBasis F E p.2) • Matrix.vecMulVec (incV F y) (incV F (Pi.single p.1 1))) := by
  have hw : ∀ k, inclR (F := F) (AF F) (w k) = ∑ j, algebraMap F (AF F) ((Module.finBasis F E).repr (w k) j) •
      inclR (F := F) (AF F) (Module.finBasis F E j) := fun k => by
    conv_lhs => rw [← (Module.finBasis F E).sum_repr (w k)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show (1 : AF F) ⊗ₜ[F] (_ • _) = _ • ((1 : AF F) ⊗ₜ[F] _)
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
  ext a k
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, incV, Matrix.sum_apply, Fintype.sum_prod_type, Pi.single_apply,
    hw, smul_eq_mul]
  rw [Finset.sum_eq_single k (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp only [if_true, map_one, mul_one, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Algebra.smul_def, map_mul]
  ring

end Pair

end GlobalTheory.IsoXArchDecay

namespace GlobalTheory.IsoXArchDecay

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Rewrite using `[map_mul]`. Establish `: GlobalTheory.HeisSchA.p2 (realAd F 1) = 0` using `rfl`. Rewrite using `[this, zero_mul]`.
-/
theorem real_adele_mul_finite_part_zero (c : AF F) : GlobalTheory.HeisSchA.p2 (realAd F 1 * c) = 0 := by
  rw [map_mul]
  have : GlobalTheory.HeisSchA.p2 (realAd F 1) = 0 := rfl
  rw [this, zero_mul]

/- English proof (translation)
Establish `h1 : (realAd F 1).1 = 1` using `by show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ 1) = 1`. Rewrite using `[map_one, map_one]`. Use `show ‖((realAd F 1).1 * (algebraMap F (AF F) c).1) v‖ = v c`. Rewrite using `[h1, one_mul]`. Use `show ‖algebraMap F (InfiniteAdeleRing F) c v‖ = v c`.

Rewrite using `[InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]`. Both sides reduce to the same expression.
-/
theorem norm_realAd_mul_algebraMap (c : F) (v : InfinitePlace F) :
    ‖(realAd F 1 * algebraMap F (AF F) c).1 v‖ = v c := by
  have h1 : (realAd F 1).1 = 1 := by
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ 1) = 1
    rw [map_one, map_one]
  show ‖((realAd F 1).1 * (algebraMap F (AF F) c).1) v‖ = v c
  rw [h1, one_mul]
  show ‖algebraMap F (InfiniteAdeleRing F) c v‖ = v c
  rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
  rfl

/- English proof (translation)
Set `b` to `Module.finBasis F E`. Set `B₀ : ℝ` to `∑ u : InfinitePlace E, ∑ j, u (b j)`. Establish `hB₀ : 0 ≤ B₀` using `by positivity`. Establish `hb : ∀ (u : InfinitePlace E) j, u (b j) ≤ B₀` using `fun u j => (Finset.single_le_sum (f := fun j => u (b j)) (fun _ _ => by positivity) (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun u : InfinitePlace E => ∑ j, u (b j)) (fun _ _ => by positivity) (Finset.mem_univ u))`. Use `⟨Fintype.card (InfinitePlace E) * B₀, by positivity, fun w => ?_⟩` and prove the remaining obligations.

Use `set c := fun i j => b.repr (w i) j with hc`. Establish `key : ∀ i (u : InfinitePlace E), u (w i) ≤ B₀ * ∑ j, ∑ v : InfinitePlace F, v (c i j)`. Introduce `i u`. Establish `h1 : u (w i) ≤ ∑ j, u (algebraMap F E (c i j) * b j)` using `by conv_lhs => rw [← b.sum_repr (w i)]`. Simplify using `only [Algebra.smul_def]`.

Conclude with `AbsoluteValue.sum_le u.1 _ _`. Use `h1.trans ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul u, mul_comm]`.

Establish `h2 : u (algebraMap F E (c i j)) ≤ ∑ v : InfinitePlace F, v (c i j)`. Rewrite using `[← InfinitePlace.comap_apply]`. Conclude with `Finset.single_le_sum (f := fun v : InfinitePlace F => v (c i j)) (fun _ _ => by positivity) (Finset.mem_univ _)`. Conclude with `mul_le_mul (hb u j) h2 (by positivity) hB₀`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.sum_prod_type, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`.
-/
theorem sum_places_le (d : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ w : Fin d → E,
    ∑ i, ∑ u : InfinitePlace E, u (w i) ≤
      A * ∑ p : Fin d × Fin (Module.finrank F E), ∑ v : InfinitePlace F, v ((Module.finBasis F E).repr (w p.1) p.2) := by
  let b := Module.finBasis F E
  let B₀ : ℝ := ∑ u : InfinitePlace E, ∑ j, u (b j)
  have hB₀ : 0 ≤ B₀ := by positivity
  have hb : ∀ (u : InfinitePlace E) j, u (b j) ≤ B₀ := fun u j =>
    (Finset.single_le_sum (f := fun j => u (b j)) (fun _ _ => by positivity) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun u : InfinitePlace E => ∑ j, u (b j)) (fun _ _ => by positivity) (Finset.mem_univ u))
  refine ⟨Fintype.card (InfinitePlace E) * B₀, by positivity, fun w => ?_⟩
  set c := fun i j => b.repr (w i) j with hc
  have key : ∀ i (u : InfinitePlace E), u (w i) ≤ B₀ * ∑ j, ∑ v : InfinitePlace F, v (c i j) := by
    intro i u
    have h1 : u (w i) ≤ ∑ j, u (algebraMap F E (c i j) * b j) := by
      conv_lhs => rw [← b.sum_repr (w i)]
      simp only [Algebra.smul_def]
      exact AbsoluteValue.sum_le u.1 _ _
    refine h1.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [map_mul u, mul_comm]
    have h2 : u (algebraMap F E (c i j)) ≤ ∑ v : InfinitePlace F, v (c i j) := by
      rw [← InfinitePlace.comap_apply]
      exact Finset.single_le_sum (f := fun v : InfinitePlace F => v (c i j)) (fun _ _ => by positivity)
        (Finset.mem_univ _)
    exact mul_le_mul (hb u j) h2 (by positivity) hB₀
  calc ∑ i, ∑ u : InfinitePlace E, u (w i) ≤ ∑ i, ∑ _u : InfinitePlace E, B₀ * ∑ j, ∑ v : InfinitePlace F, v (c i j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u _ => key i u
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => ?_
      rw [mul_assoc]

end Places

end GlobalTheory.IsoXArchDecay

namespace GlobalTheory.IsoXArchDecay

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Algebra.smul_def, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem smul_vecMulVec_move {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (a : AF F) (c : AE F E) (u : Fin n → AE F E) (v : Fin d → AE F E) :
    a • Matrix.vecMulVec (c • u) v = Matrix.vecMulVec u (a • c • v) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def, Algebra.smul_def]
  ring

end GlobalTheory.IsoXArchDecay

namespace GlobalTheory.IsoXArchDecay

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay GlobalTheory.XTermDecay

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' hev hB hsig Φ hΦ N K hN`. Take `⟨r, s, r', s', hX, hW⟩` from `hsig`. Take `⟨l, hl, hlθ⟩` from `GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n₁ × Fin d₁)`. Establish `hadm` using `GlobalTheory.EvAdm.comp_mem_adm F E σ B n d₁ n₁ d₁ X W₁ X₁ W₁ M₁ M₂ H.ι 1 _ e' hM₁ hM₂ hev l hl`. Take `⟨x', hx'⟩` from `exists_dual_vec σ W₁.J (det_ne_zero_of_skew hW)`.

Establish `hyx : form σ X.J H.y H.x = 1` using `by rw [form_swap_herm hB.cm hX.herm, hH.xy, map_one]`. Take `⟨t, ht⟩` from `dualPair_family σ X.J W₁.J H.y H.x x' hyx hx'`. Set `Sm : Fin d₁ × Fin (Module.finrank F E) → Matrix (Fin n) (Fin d₁) (AE F E)` to `fun q => inclR (F := F) (AF F) (Module.finBasis F E q.2) • Matrix.vecMulVec (incV F H.y) (incV F (Pi.single q.1 1))`. Set `Um : Fin d₁ × Fin (Module.finrank F E) → Matrix (Fin n) (Fin d₁) (AE F E)` to `fun p => Matrix.vecMulVec (inclR (F := F) (AF F) (t p.2) • incV F H.x) (incV F (x' p.1))`. Establish `hUI : ∀ p (a : AF F), a • Um p ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}` using `fun p a => ⟨a • inclR (F := F) (AF F) (t p.2) • incV F (x' p.1), smul_vecMulVec_move _ _ _ _⟩`.

Establish `hinv : ∀ p (a : AF F), ∀ Ψ ∈ schA F (Fin n × Fin d₁), (l ∘ₗ e') (schr B.ψ (a • M₁.co.e (Um p)) Ψ) = (l ∘ₗ e') Ψ` using `fun p a Ψ hΨ => by`. Rewrite using `[← map_smul, LinearMap.comp_apply, LinearMap.comp_apply]`. Conclude with `congrArg l (hev.inv _ (hUI p a) Ψ hΨ)`. Take `⟨C₁, hC₁⟩` from `scalar_decay B.ψ hB.std (fun q => M₁.co.e (Sm q)) (fun p => M₁.co.e (Um p)) (fun p q => by rw [← M₁.co.form]; convert ht p q) (l ∘ₗ e') hadm hinv Φ hΦ K`. Take `⟨A, hA, hAw⟩` from `sum_places_le (F := F) (E := E) d₁`.

Use `⟨max C₁ 0 * (1 + A) ^ K, fun w _ => ?_⟩` and prove the remaining obligations. Set `x : Fin d₁ × Fin (Module.finrank F E) → AF F` to `fun p => realAd F 1 * algebraMap F (AF F) ((Module.finBasis F E).repr (w p.1) p.2)`. Establish `hx : ∀ p, p2 (x p) = 0` using `fun p => real_adele_mul_finite_part_zero _`. Establish `hrho : M₁.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F H.y) (incV F w)) Φ = schr B.ψ (∑ p, x p • M₁.co.e (Sm p)) Φ`. Rewrite using `[Darboux.rho, vecMulVec_sum, map_sum]`.

Simplify using `only [map_smul]`. Both sides reduce to the same expression. Establish `hθ : thetaSum F (e' (M₁.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F H.y) (incV F w)) Φ)) = (l ∘ₗ e') (schr B.ψ (∑ p, x p • M₁.co.e (Sm p)) Φ)`. Rewrite using `[hrho, LinearMap.comp_apply, hlθ _ (hev.maps _ (schr_mem_schA B.ψ hB.std _ _ hΦ))]`. Establish `hb` using `hC₁ x hx`.

Establish `hr : ∑ p, ∑ v : InfinitePlace F, ‖(x p).1 v‖ = ∑ p : Fin d₁ × Fin (Module.finrank F E), ∑ v : InfinitePlace F, v ((Module.finBasis F E).repr (w p.1) p.2)`. Simplify using `only [x, norm_realAd_mul_algebraMap]`. Rewrite `hb` using `[hr]`. Use `set ρ := ∑ p : Fin d₁ × Fin (Module.finrank F E), ∑ v : InfinitePlace F, v ((Module.finBasis F E).repr (w p.1) p.2) with hρ`. Establish `hρ0 : 0 ≤ ρ` using `by positivity`.

Establish `hR` using `hAw w`. Establish `hR0 : 0 ≤ ∑ i, ∑ v : InfinitePlace E, v (w i)` using `by positivity`. Rewrite using `[hθ]`. Establish `h1 : (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K ≤ (1 + A) ^ K * (1 + ρ) ^ K`. Rewrite using `[← mul_pow]`.

Use `gcongr`. Use polynomial arithmetic with `[mul_nonneg hA hρ0]`. Establish `h2 : (1 + ρ) ^ (-(K : ℝ)) * (1 + ρ) ^ K = 1`. Rewrite using `[Real.rpow_neg (by positivity), Real.rpow_natCast, inv_mul_cancel₀ (by positivity)]`. Establish `h3 : ‖(l ∘ₗ e') (schr B.ψ (∑ p, x p • M₁.co.e (Sm p)) Φ)‖ ≤ max C₁ 0 * (1 + ρ) ^ (-(K : ℝ))` using `hb.trans (by gcongr; exact le_max_left _ _)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem thetaSum_arch_decay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁), M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ →
    ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ →
    (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') →
    ∀ Φ ∈ schA F (Fin n × Fin d₁), ∀ N K : ℕ, 1 ≤ N → ∃ C : ℝ, ∀ w : Fin d₁ → E, (∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) →
      ‖thetaSum F (e' (M₁.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F H.y) (incV F w)) Φ))‖ *
        (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K ≤ C := by
  intro _ F E _ _ _ _ _ σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' hev hB hsig Φ hΦ N K hN
  obtain ⟨r, s, r', s', hX, hW⟩ := hsig
  obtain ⟨l, hl, hlθ⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n₁ × Fin d₁)
  have hadm := GlobalTheory.EvAdm.comp_mem_adm F E σ B n d₁ n₁ d₁ X W₁ X₁ W₁ M₁ M₂ H.ι 1 _ e' hM₁ hM₂ hev l hl
  obtain ⟨x', hx'⟩ := exists_dual_vec σ W₁.J (det_ne_zero_of_skew hW)
  have hyx : form σ X.J H.y H.x = 1 := by rw [form_swap_herm hB.cm hX.herm, hH.xy, map_one]
  obtain ⟨t, ht⟩ := dualPair_family σ X.J W₁.J H.y H.x x' hyx hx'
  let Sm : Fin d₁ × Fin (Module.finrank F E) → Matrix (Fin n) (Fin d₁) (AE F E) := fun q =>
    inclR (F := F) (AF F) (Module.finBasis F E q.2) • Matrix.vecMulVec (incV F H.y) (incV F (Pi.single q.1 1))
  let Um : Fin d₁ × Fin (Module.finrank F E) → Matrix (Fin n) (Fin d₁) (AE F E) := fun p =>
    Matrix.vecMulVec (inclR (F := F) (AF F) (t p.2) • incV F H.x) (incV F (x' p.1))
  have hUI : ∀ p (a : AF F), a • Um p ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} := fun p a =>
    ⟨a • inclR (F := F) (AF F) (t p.2) • incV F (x' p.1), smul_vecMulVec_move _ _ _ _⟩
  have hinv : ∀ p (a : AF F), ∀ Ψ ∈ schA F (Fin n × Fin d₁),
      (l ∘ₗ e') (schr B.ψ (a • M₁.co.e (Um p)) Ψ) = (l ∘ₗ e') Ψ := fun p a Ψ hΨ => by
    rw [← map_smul, LinearMap.comp_apply, LinearMap.comp_apply]
    exact congrArg l (hev.inv _ (hUI p a) Ψ hΨ)
  obtain ⟨C₁, hC₁⟩ := scalar_decay B.ψ hB.std (fun q => M₁.co.e (Sm q)) (fun p => M₁.co.e (Um p))
    (fun p q => by rw [← M₁.co.form]; convert ht p q) (l ∘ₗ e') hadm
    hinv Φ hΦ K
  obtain ⟨A, hA, hAw⟩ := sum_places_le (F := F) (E := E) d₁
  refine ⟨max C₁ 0 * (1 + A) ^ K, fun w _ => ?_⟩
  let x : Fin d₁ × Fin (Module.finrank F E) → AF F := fun p =>
    realAd F 1 * algebraMap F (AF F) ((Module.finBasis F E).repr (w p.1) p.2)
  have hx : ∀ p, p2 (x p) = 0 := fun p => real_adele_mul_finite_part_zero _
  have hrho : M₁.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F H.y) (incV F w)) Φ =
      schr B.ψ (∑ p, x p • M₁.co.e (Sm p)) Φ := by
    rw [Darboux.rho, vecMulVec_sum, map_sum]
    simp only [map_smul]
    rfl
  have hθ : thetaSum F (e' (M₁.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F H.y) (incV F w)) Φ)) =
      (l ∘ₗ e') (schr B.ψ (∑ p, x p • M₁.co.e (Sm p)) Φ) := by
    rw [hrho, LinearMap.comp_apply, hlθ _ (hev.maps _ (schr_mem_schA B.ψ hB.std _ _ hΦ))]
  have hb := hC₁ x hx
  have hr : ∑ p, ∑ v : InfinitePlace F, ‖(x p).1 v‖ =
      ∑ p : Fin d₁ × Fin (Module.finrank F E), ∑ v : InfinitePlace F, v ((Module.finBasis F E).repr (w p.1) p.2) := by
    simp only [x, norm_realAd_mul_algebraMap]
  rw [hr] at hb
  set ρ := ∑ p : Fin d₁ × Fin (Module.finrank F E), ∑ v : InfinitePlace F, v ((Module.finBasis F E).repr (w p.1) p.2)
    with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hR := hAw w
  have hR0 : 0 ≤ ∑ i, ∑ v : InfinitePlace E, v (w i) := by positivity
  rw [hθ]
  have h1 : (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K ≤ (1 + A) ^ K * (1 + ρ) ^ K := by
    rw [← mul_pow]
    gcongr
    nlinarith [mul_nonneg hA hρ0]
  have h2 : (1 + ρ) ^ (-(K : ℝ)) * (1 + ρ) ^ K = 1 := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_mul_cancel₀ (by positivity)]
  have h3 : ‖(l ∘ₗ e') (schr B.ψ (∑ p, x p • M₁.co.e (Sm p)) Φ)‖ ≤ max C₁ 0 * (1 + ρ) ^ (-(K : ℝ)) :=
    hb.trans (by gcongr; exact le_max_left _ _)
  calc _ ≤ (max C₁ 0 * (1 + ρ) ^ (-(K : ℝ))) * ((1 + A) ^ K * (1 + ρ) ^ K) :=
        mul_le_mul h3 h1 (by positivity) (by positivity)
    _ = max C₁ 0 * (1 + A) ^ K * ((1 + ρ) ^ (-(K : ℝ)) * (1 + ρ) ^ K) := by ring
    _ = _ := by rw [h2, mul_one]

end GlobalTheory.IsoXArchDecay
