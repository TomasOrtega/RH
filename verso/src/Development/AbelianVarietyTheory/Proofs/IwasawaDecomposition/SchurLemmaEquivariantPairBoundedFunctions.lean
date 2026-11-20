import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosableOfSmoothing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsContinuousL2Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInnerL2Translate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsInnerProductStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurInnerEqPairClosableNormInvariantStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

/- English proof (translation)
Establish `hm : ∀ w : D, MemLp (a w) 2 ν` using `fun w => by`. Take `⟨hc, C, hC⟩` from `ha w w.2`. Conclude with `MemLp.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)`. Set `f : D →ₗ[ℂ] Lp ℂ 2 ν` to `{ toFun := fun w => (hm w).toLp (a w) map_add' := fun w w' => by`. Use `Lp.ext ?_` and prove the remaining obligations.

Use `filter_upwards [(hm (w + w')).coeFn_toLp, (hm w).coeFn_toLp, (hm w').coeFn_toLp, Lp.coeFn_add ((hm w).toLp (a w)) ((hm w').toLp (a w'))] with x h1 h2 h3 h4`. Rewrite using `[h4, Pi.add_apply, h1, h2, h3, Submodule.coe_add, map_add, Pi.add_apply]`. Use the proof step `map_smul' := fun c w => by`. Use `Lp.ext ?_` and prove the remaining obligations. Use `filter_upwards [(hm (c • w)).coeFn_toLp, (hm w).coeFn_toLp, Lp.coeFn_smul c ((hm w).toLp (a w))] with x h1 h2 h3`.

Rewrite using `[RingHom.id_apply, h3, Pi.smul_apply, h1, h2, Submodule.coe_smul, map_smul, Pi.smul_apply] }`. Take `⟨g, hg⟩` from `LinearMap.exists_extend f`. Use `⟨g, fun w hw => ?_⟩` and prove the remaining obligations. Establish `hgw : g w = f ⟨w, hw⟩` using `by rw [← hg]; rfl`. Rewrite using `[hgw]`.

Conclude with `(hm ⟨w, hw⟩).coeFn_toLp`.
-/
theorem exists_l2_lift {H : Type} [AddCommGroup H] [Module ℂ H] (D : Submodule ℂ H) {X : Type} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (a : H →ₗ[ℂ] (X → ℂ))
    (ha : ∀ w ∈ D, Continuous (a w) ∧ ∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) :
    ∃ A : H →ₗ[ℂ] Lp ℂ 2 ν, ∀ w ∈ D, (A w : X → ℂ) =ᵐ[ν] a w := by
  classical
  have hm : ∀ w : D, MemLp (a w) 2 ν := fun w => by
    obtain ⟨hc, C, hC⟩ := ha w w.2
    exact MemLp.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  let f : D →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun w => (hm w).toLp (a w)
      map_add' := fun w w' => by
        refine Lp.ext ?_
        filter_upwards [(hm (w + w')).coeFn_toLp, (hm w).coeFn_toLp, (hm w').coeFn_toLp,
          Lp.coeFn_add ((hm w).toLp (a w)) ((hm w').toLp (a w'))] with x h1 h2 h3 h4
        rw [h4, Pi.add_apply, h1, h2, h3, Submodule.coe_add, map_add, Pi.add_apply]
      map_smul' := fun c w => by
        refine Lp.ext ?_
        filter_upwards [(hm (c • w)).coeFn_toLp, (hm w).coeFn_toLp,
          Lp.coeFn_smul c ((hm w).toLp (a w))] with x h1 h2 h3
        rw [RingHom.id_apply, h3, Pi.smul_apply, h1, h2, Submodule.coe_smul, map_smul, Pi.smul_apply] }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨g, fun w hw => ?_⟩
  have hgw : g w = f ⟨w, hw⟩ := by rw [← hg]; rfl
  rw [hgw]
  exact (hm ⟨w, hw⟩).coeFn_toLp

/- English proof (translation)
Rewrite using `[MeasureTheory.L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hf, hg] with x hx hy`. Rewrite using `[hx, hy, RCLike.inner_apply, mul_comm, starRingEnd_apply]`.
-/
theorem l2_inner_of_ae {X : Type} [MeasurableSpace X] {ν : Measure X} {f g : Lp ℂ 2 ν} {u v : X → ℂ}
    (hf : (f : X → ℂ) =ᵐ[ν] u) (hg : (g : X → ℂ) =ᵐ[ν] v) : ⟪f, g⟫_ℂ = ∫ x, star (u x) * v x ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf, hg] with x hx hy
  rw [hx, hy, RCLike.inner_apply, mul_comm, starRingEnd_apply]

/- English proof (translation)
Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private lemma jm_sq_lemma {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases h : ε i <;> simp [h]`.
-/
private lemma jm_herm_lemma_2 {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : ε i <;> simp [h]

/- English proof (translation)
Establish `h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε` using `hg`. Establish `jj : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Y) = Y` using `fun Y => by`. Rewrite using `[← Matrix.mul_assoc, jm_sq_lemma, Matrix.one_mul]`. Establish `hl : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [h, jm_sq_lemma]`. Establish `hr : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1` using `mul_eq_one_comm.mp hl`. Use `⟨?_, hl, hr⟩` and prove the remaining obligations. Establish `hr' : g * (Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε)) = 1` using `by simpa only [Matrix.mul_assoc] using hr`.

Use `show (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε`. Simplify using `only [Matrix.conjTranspose_mul, jm_herm_lemma_2, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, jj]`. Rewrite using `[hr', Matrix.mul_one]`.
-/
private lemma jm_conjTranspose_jm_mem_and_inverse {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε ∈ UJset ε ∧ (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 ∧
      g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have jj : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, jm_sq_lemma, Matrix.one_mul]
  have hl : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    calc (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, jm_sq_lemma]
  have hr : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.mp hl
  refine ⟨?_, hl, hr⟩
  have hr' : g * (Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε)) = 1 := by simpa only [Matrix.mul_assoc] using hr
  show (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε
  simp only [Matrix.conjTranspose_mul, jm_herm_lemma_2, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, jj]
  rw [hr', Matrix.mul_one]

/- English proof (translation)
Introduce `n ε H _ _ _ σ P G hP hG hσ hirr X _ _ _ _ ν _ act hact a a' ha hsa ha' hsa' hI hI' hIx`. Take `⟨A, hA⟩` from `exists_l2_lift (smSub G (trRep σ P)) ν a (fun w hw => ⟨(ha w hw).1, (ha w hw).2.1⟩)`. Take `⟨A', hA'⟩` from `exists_l2_lift (smSub G (trRep σ P)) ν a' (fun w hw => ⟨(ha' w hw).1, (ha' w hw).2.1⟩)`. Establish `hmem : ∀ g ∈ UJset ε, ∀ w ∈ smSub G (trRep σ P), σ g w ∈ smSub G (trRep σ P)` using `fun g hg w hw => sigma_mem hP hG hσ hw hg`. Establish `hAinv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ⟪A (σ g u), A (σ g w)⟫_ℂ = ⟪A u, A w⟫_ℂ`.

Introduce `g hg u hu w hw`. Rewrite using `[l2_inner_of_ae (hA _ (hmem g hg u hu)) (hA _ (hmem g hg w hw)), l2_inner_of_ae (hA u hu) (hA w hw)]`. Conclude with `hI g hg u hu w hw`. Establish `hA'inv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ⟪A' (σ g u), A' (σ g w)⟫_ℂ = ⟪A' u, A' w⟫_ℂ`. Introduce `g hg u hu w hw`.

Rewrite using `[l2_inner_of_ae (hA' _ (hmem g hg u hu)) (hA' _ (hmem g hg w hw)), l2_inner_of_ae (hA' u hu) (hA' w hw)]`. Conclude with `hI' g hg u hu w hw`. Establish `hxinv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ⟪A (σ g u), A' (σ g w)⟫_ℂ = ⟪A u, A' w⟫_ℂ`. Introduce `g hg u hu w hw`. Rewrite using `[l2_inner_of_ae (hA _ (hmem g hg u hu)) (hA' _ (hmem g hg w hw)), l2_inner_of_ae (hA u hu) (hA' w hw)]`.

Conclude with `hIx g hg u hu w hw`. Establish `hcl` using `closable_of_smoothing n ε H σ P G hP hG hσ (Lp ℂ 2 ν) A hAinv (continuous_inner_l2_translate n ε H σ P G hP hG hσ X ν act hact a A ha hsa hA) (GlobalTheory.T.smooth_vectors_continuous_l2 n ε H σ P G hP hG hσ X ν act hact a A ha hsa hA) (GlobalTheory.T.smooth_vectors_inner_product …`. Establish `hcl'` using `closable_of_smoothing n ε H σ P G hP hG hσ (Lp ℂ 2 ν) A' hA'inv (continuous_inner_l2_translate n ε H σ P G hP hG hσ X ν act hact a' A' ha' hsa' hA') (GlobalTheory.T.smooth_vectors_continuous_l2 n ε H σ P G hP hG hσ X ν act hact a' A' ha' hsa' hA') (GlobalTheory.T.smooth_vectors_i …`. Establish `hnorm : ∀ B : H →ₗ[ℂ] Lp ℂ 2 ν, (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ⟪B (σ g u), B (σ g w)⟫_ℂ = ⟪B u, B w⟫_ℂ) → ∀ i : UJset ε, ∀ w ∈ smSub G (trRep σ P), ‖B (σ i.1 w)‖ = ‖B w‖`. Introduce `B hB i w hw`.

Rewrite using `[norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (B w), hB i.1 i.2 w hw w hw]`. Establish `hrep` using `hσ.1`. Take `⟨c, hc⟩` from `GlobalTheory.T.schur_inner_eq_pair_closable_normInvariant (UJset ε) H (Lp ℂ 2 ν) (fun i => σ i.1) (smSub G (trRep σ P)) (fun i v => hσ.2.1 i.1 i.2 v) (fun i => by`. Take `⟨hj, hl, hr⟩` from `jm_conjTranspose_jm_mem_and_inverse i.2`. Use `⟨⟨_, hj⟩, fun v => ?_, fun v => ?_⟩` and prove the remaining obligations.

Use `show σ _ (σ i.1 v) = v`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← hrep.2 _ hj _ i.2, hl, hrep.1, ContinuousLinearMap.one_apply]`. Use `show σ i.1 (σ _ v) = v`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← hrep.2 _ i.2 _ hj, hr, hrep.1, ContinuousLinearMap.one_apply])`. Use the proof step `(fun S hS hS' => hirr S hS (fun g hg v hv => hS' ⟨g, hg⟩ v hv))`.

Use the proof step `(fun i v hv => hmem i.1 i.2 v hv)`. Use `A A' (hnorm A hAinv) (hnorm A' hA'inv) (fun i w hw => hxinv i.1 i.2 w hw w hw) hcl hcl'`. Conclude with `⟨c, fun w hw w' hw' => by rw [← l2_inner_of_ae (hA w hw) (hA' w' hw')]; exact hc w hw w' hw'⟩`.
-/
theorem schurLemma_equivariant_pair_boundedFunctions : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a a' : H →ₗ[ℂ] (X → ℂ)), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), Continuous (a' w) ∧ (∃ C : ℝ, ∀ x, ‖a' w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a' (σ (umat g) w) x = a' w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a')) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a (σ g u) x) * a (σ g w) x ∂ν = ∫ x, star (a u x) * a w x ∂ν) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a' (σ g u) x) * a' (σ g w) x ∂ν = ∫ x, star (a' u x) * a' w x ∂ν) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a (σ g u) x) * a' (σ g w) x ∂ν = ∫ x, star (a u x) * a' w x ∂ν) → ∃ c : ℂ, ∀ w ∈ smSub G (trRep σ P), ∀ w' ∈ smSub G (trRep σ P), ∫ x, star (a w x) * a' w' x ∂ν = c * ⟪w, w'⟫_ℂ := by
  intro n ε H _ _ _ σ P G hP hG hσ hirr X _ _ _ _ ν _ act hact a a' ha hsa ha' hsa' hI hI' hIx
  obtain ⟨A, hA⟩ := exists_l2_lift (smSub G (trRep σ P)) ν a (fun w hw => ⟨(ha w hw).1, (ha w hw).2.1⟩)
  obtain ⟨A', hA'⟩ := exists_l2_lift (smSub G (trRep σ P)) ν a' (fun w hw => ⟨(ha' w hw).1, (ha' w hw).2.1⟩)
  have hmem : ∀ g ∈ UJset ε, ∀ w ∈ smSub G (trRep σ P), σ g w ∈ smSub G (trRep σ P) :=
    fun g hg w hw => sigma_mem hP hG hσ hw hg
  have hAinv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪A (σ g u), A (σ g w)⟫_ℂ = ⟪A u, A w⟫_ℂ := by
    intro g hg u hu w hw
    rw [l2_inner_of_ae (hA _ (hmem g hg u hu)) (hA _ (hmem g hg w hw)), l2_inner_of_ae (hA u hu) (hA w hw)]
    exact hI g hg u hu w hw
  have hA'inv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪A' (σ g u), A' (σ g w)⟫_ℂ = ⟪A' u, A' w⟫_ℂ := by
    intro g hg u hu w hw
    rw [l2_inner_of_ae (hA' _ (hmem g hg u hu)) (hA' _ (hmem g hg w hw)), l2_inner_of_ae (hA' u hu) (hA' w hw)]
    exact hI' g hg u hu w hw
  have hxinv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪A (σ g u), A' (σ g w)⟫_ℂ = ⟪A u, A' w⟫_ℂ := by
    intro g hg u hu w hw
    rw [l2_inner_of_ae (hA _ (hmem g hg u hu)) (hA' _ (hmem g hg w hw)), l2_inner_of_ae (hA u hu) (hA' w hw)]
    exact hIx g hg u hu w hw
  have hcl := closable_of_smoothing n ε H σ P G hP hG hσ (Lp ℂ 2 ν) A hAinv
    (continuous_inner_l2_translate n ε H σ P G hP hG hσ X ν act hact a A ha hsa hA)
    (GlobalTheory.T.smooth_vectors_continuous_l2 n ε H σ P G hP hG hσ X ν act hact a A ha hsa hA)
    (GlobalTheory.T.smooth_vectors_inner_product n ε H σ P G hP hG hσ X ν act hact a A ha hsa hA)
  have hcl' := closable_of_smoothing n ε H σ P G hP hG hσ (Lp ℂ 2 ν) A' hA'inv
    (continuous_inner_l2_translate n ε H σ P G hP hG hσ X ν act hact a' A' ha' hsa' hA')
    (GlobalTheory.T.smooth_vectors_continuous_l2 n ε H σ P G hP hG hσ X ν act hact a' A' ha' hsa' hA')
    (GlobalTheory.T.smooth_vectors_inner_product n ε H σ P G hP hG hσ X ν act hact a' A' ha' hsa' hA')
  have hnorm : ∀ B : H →ₗ[ℂ] Lp ℂ 2 ν, (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪B (σ g u), B (σ g w)⟫_ℂ = ⟪B u, B w⟫_ℂ) →
      ∀ i : UJset ε, ∀ w ∈ smSub G (trRep σ P), ‖B (σ i.1 w)‖ = ‖B w‖ := by
    intro B hB i w hw
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (B w), hB i.1 i.2 w hw w hw]
  have hrep := hσ.1
  obtain ⟨c, hc⟩ := GlobalTheory.T.schur_inner_eq_pair_closable_normInvariant (UJset ε) H (Lp ℂ 2 ν) (fun i => σ i.1) (smSub G (trRep σ P))
    (fun i v => hσ.2.1 i.1 i.2 v)
    (fun i => by
      obtain ⟨hj, hl, hr⟩ := jm_conjTranspose_jm_mem_and_inverse i.2
      refine ⟨⟨_, hj⟩, fun v => ?_, fun v => ?_⟩
      · show σ _ (σ i.1 v) = v
        rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hj _ i.2, hl, hrep.1,
          ContinuousLinearMap.one_apply]
      · show σ i.1 (σ _ v) = v
        rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ i.2 _ hj, hr, hrep.1,
          ContinuousLinearMap.one_apply])
    (fun S hS hS' => hirr S hS (fun g hg v hv => hS' ⟨g, hg⟩ v hv))
    (fun i v hv => hmem i.1 i.2 v hv)
    A A' (hnorm A hAinv) (hnorm A' hA'inv) (fun i w hw => hxinv i.1 i.2 w hw w hw) hcl hcl'
  exact ⟨c, fun w hw w' hw' => by rw [← l2_inner_of_ae (hA w hw) (hA' w' hw')]; exact hc w hw w' hw'⟩

end GlobalTheory.SmVec
