import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFrameIdem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusArchimedeanFrameActionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFrameLevelTriangularStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFrameWeightRatioBoundStatement

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h n J hJ r X Y hW Q c hQ hc s`. Take `⟨K, hK0, hK⟩` from `GlobalTheory.T.cone_frame_weight_ratio_bound r c hc`. Establish `hb : ∀ q : (Σ w : InfinitePlace F, EmbOver E w) × FrameIx r × FrameIx r × Fin n × Fin n, ∃ B : ℝ, ∀ g ∈ Q, ‖((frameIdem (σ : E →+* E) J X Y q.2.1).map q.1.2.1 * (archMat σ J q.1.2 (projArch σ J q.1.1 g) - 1) * (frameIdem (σ : E →+* E) J X Y q.2.2.1).map q.1.2.1) q.2.2.2.1 q.2.2.2 …` using `fun q => by`. Establish `hcont : Continuous fun g : GAd σ J => archMat σ J q.1.2 (projArch σ J q.1.1 g)` using `(GlobalTheory.Orb.continuous_archMat σ J q.1.2).comp (continuous_projArch σ J q.1.1)`. Use `hQ.exists_bound_of_continuousOn (Continuous.continuousOn ?_)` and prove the remaining obligations.

Conclude with `((continuous_const.matrix_mul (hcont.sub continuous_const)).matrix_mul continuous_const).matrix_elem _ _`. Use `choose B hB using hb`. Use `set Bt : ℝ := ∑ q, |B q| with hBt`. Establish `hBt0 : 0 ≤ Bt` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Use `⟨(Fintype.card (FrameIx r) : ℝ) * ((Fintype.card (FrameIx r) : ℝ) * (K * Bt)), by positivity, ?_⟩` and prove the remaining obligations.

Introduce `m hm hmU t ht a ha w τ i j`. Establish `hr : 0 < ratio t s` using `ratio_pos ht s`. Establish `hd : ∀ α, 0 < frameWt t α` using `frameWt_pos ht.1`. Use `set A := archMat σ J τ (projArch σ J w a) with hAdef`. Use `set A' := archMat σ J τ (projArch σ J w a⁻¹) with hA'def`.

Use `set M₁ := archMat σ J τ (projArch σ J w m) - 1 with hM₁`. Use `set P : FrameIx r → Matrix (Fin n) (Fin n) ℂ := fun α => (frameIdem (σ : E →+* E) J X Y α).map τ.1 with hPdef`. Establish `hAA : A' * A = 1`. Rewrite using `[hAdef, hA'def, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]`. Establish `e2 : archMat σ J τ (projArch σ J w (a⁻¹ * m * a)) - 1 = A' * M₁ * A`.

Rewrite using `[map_mul, map_mul, map_mul, map_mul, ← hAdef, ← hA'def, hM₁, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAA]`. Establish `hP : ∑ α, P α = 1`. Establish `: ∑ α, P α = (τ.1.mapMatrix) (∑ α, frameIdem (σ : E →+* E) J X Y α)`. Rewrite using `[map_sum]`. Both sides reduce to the same expression.

Rewrite using `[this, sum_frameIdem, map_one]`. Establish `hTor : ∀ β, A * P β = ((frameWt t β : ℝ) : ℂ) • P β` using `fun β => GlobalTheory.T.torus_archimedean_frame_action F E σ h n J hJ r X Y hW t a ha ht.1 w τ β`. Establish `hA : A = ∑ β, ((frameWt t β : ℝ) : ℂ) • P β`. Combine the equalities or inequalities in the displayed calculation. Establish `hTor' : ∀ α, A' * P α = ((frameWt t α : ℝ) : ℂ)⁻¹ • P α` using `fun α => by`.

Establish `hne : ((frameWt t α : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (hd α).ne'`. Rewrite using `[eq_inv_smul_iff₀ hne, ← Matrix.mul_smul, ← hTor α, ← Matrix.mul_assoc, hAA, Matrix.one_mul]`. Establish `hA' : A' = ∑ α, ((frameWt t α : ℝ) : ℂ)⁻¹ • P α`. Combine the equalities or inequalities in the displayed calculation. Establish `e3 : A' * M₁ * A = ∑ α, ∑ β, (((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)) • (P α * M₁ * P β)` using `by conv_lhs => rw [hA', hA]`.

Rewrite using `[Finset.sum_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun β _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, smul_mul_assoc, Matrix.mul_smul, smul_smul]`.

Establish `term : ∀ α β, ‖((((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)) • (P α * M₁ * P β)) i j‖ ≤ K * Bt / ratio t s` using `fun α β => by`. Distinguish the cases in `hl : frameLev s α ≤ frameLev s β`. Establish `h0 : P α * M₁ * P β = 0` using `GlobalTheory.T.unipotent_frame_level_triangular F E σ h n J hJ r X Y hW s m hmU w τ α β hl`. Rewrite using `[h0, smul_zero]`. Simplify using `using div_nonneg (mul_nonneg hK0 hBt0) hr.le`.

Establish `h1` using `hK s t ht α β (not_le.1 hl)`. Establish `h2 : ‖(P α * M₁ * P β) i j‖ ≤ Bt` using `((hB (⟨w, τ⟩, α, β, i, j) m hm).trans (le_abs_self _)).trans (Finset.single_le_sum (f := fun q => |B q|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _))`. Establish `h3 : ‖((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)‖ = frameWt t β / frameWt t α`. Rewrite using `[norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hd α).le, Real.norm_of_nonneg (hd β).le, div_eq_inv_mul]`. Rewrite using `[Matrix.smul_apply, norm_smul, h3]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e2, e3, Matrix.sum_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.sum_apply]`. Conclude with `(norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => term α β)`.

Use `_ = _ := by`. Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem torus_contracts_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Q : Set (GAd σ J)) (c : ℝ), IsCompact Q → 0 < c → ∀ s : Fin r, ∃ M : ℝ, 0 ≤ M ∧ ∀ m ∈ Q, m ∈ unipRad σ J (pre X s) → ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n), ‖(archMat σ J τ (projArch σ J w (a⁻¹ * m * a)) - 1) i j‖ ≤ M / ratio t s := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW Q c hQ hc s
  obtain ⟨K, hK0, hK⟩ := GlobalTheory.T.cone_frame_weight_ratio_bound r c hc
  have hb : ∀ q : (Σ w : InfinitePlace F, EmbOver E w) × FrameIx r × FrameIx r × Fin n × Fin n, ∃ B : ℝ, ∀ g ∈ Q,
      ‖((frameIdem (σ : E →+* E) J X Y q.2.1).map q.1.2.1 * (archMat σ J q.1.2 (projArch σ J q.1.1 g) - 1) *
        (frameIdem (σ : E →+* E) J X Y q.2.2.1).map q.1.2.1) q.2.2.2.1 q.2.2.2.2‖ ≤ B := fun q => by
    have hcont : Continuous fun g : GAd σ J => archMat σ J q.1.2 (projArch σ J q.1.1 g) :=
      (GlobalTheory.Orb.continuous_archMat σ J q.1.2).comp (continuous_projArch σ J q.1.1)
    refine hQ.exists_bound_of_continuousOn (Continuous.continuousOn ?_)
    exact ((continuous_const.matrix_mul (hcont.sub continuous_const)).matrix_mul continuous_const).matrix_elem _ _
  choose B hB using hb
  set Bt : ℝ := ∑ q, |B q| with hBt
  have hBt0 : 0 ≤ Bt := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(Fintype.card (FrameIx r) : ℝ) * ((Fintype.card (FrameIx r) : ℝ) * (K * Bt)), by positivity, ?_⟩
  intro m hm hmU t ht a ha w τ i j
  have hr : 0 < ratio t s := ratio_pos ht s
  have hd : ∀ α, 0 < frameWt t α := frameWt_pos ht.1
  set A := archMat σ J τ (projArch σ J w a) with hAdef
  set A' := archMat σ J τ (projArch σ J w a⁻¹) with hA'def
  set M₁ := archMat σ J τ (projArch σ J w m) - 1 with hM₁
  set P : FrameIx r → Matrix (Fin n) (Fin n) ℂ := fun α => (frameIdem (σ : E →+* E) J X Y α).map τ.1 with hPdef
  have hAA : A' * A = 1 := by
    rw [hAdef, hA'def, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  have e2 : archMat σ J τ (projArch σ J w (a⁻¹ * m * a)) - 1 = A' * M₁ * A := by
    rw [map_mul, map_mul, map_mul, map_mul, ← hAdef, ← hA'def, hM₁, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAA]
  have hP : ∑ α, P α = 1 := by
    have : ∑ α, P α = (τ.1.mapMatrix) (∑ α, frameIdem (σ : E →+* E) J X Y α) := by
      rw [map_sum]; rfl
    rw [this, sum_frameIdem, map_one]
  have hTor : ∀ β, A * P β = ((frameWt t β : ℝ) : ℂ) • P β := fun β =>
    GlobalTheory.T.torus_archimedean_frame_action F E σ h n J hJ r X Y hW t a ha ht.1 w τ β
  have hA : A = ∑ β, ((frameWt t β : ℝ) : ℂ) • P β := by
    calc A = A * ∑ β, P β := by rw [hP, Matrix.mul_one]
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun β _ => hTor β
  have hTor' : ∀ α, A' * P α = ((frameWt t α : ℝ) : ℂ)⁻¹ • P α := fun α => by
    have hne : ((frameWt t α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hd α).ne'
    rw [eq_inv_smul_iff₀ hne, ← Matrix.mul_smul, ← hTor α, ← Matrix.mul_assoc, hAA, Matrix.one_mul]
  have hA' : A' = ∑ α, ((frameWt t α : ℝ) : ℂ)⁻¹ • P α := by
    calc A' = A' * ∑ α, P α := by rw [hP, Matrix.mul_one]
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun α _ => hTor' α
  have e3 : A' * M₁ * A = ∑ α, ∑ β, (((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)) • (P α * M₁ * P β) := by
    conv_lhs => rw [hA', hA]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, Matrix.mul_smul, smul_smul]
  have term : ∀ α β, ‖((((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)) • (P α * M₁ * P β)) i j‖ ≤ K * Bt / ratio t s := fun α β => by
    by_cases hl : frameLev s α ≤ frameLev s β
    · have h0 : P α * M₁ * P β = 0 := GlobalTheory.T.unipotent_frame_level_triangular F E σ h n J hJ r X Y hW s m hmU w τ α β hl
      rw [h0, smul_zero]
      simpa using div_nonneg (mul_nonneg hK0 hBt0) hr.le
    · have h1 := hK s t ht α β (not_le.1 hl)
      have h2 : ‖(P α * M₁ * P β) i j‖ ≤ Bt :=
        ((hB (⟨w, τ⟩, α, β, i, j) m hm).trans (le_abs_self _)).trans
          (Finset.single_le_sum (f := fun q => |B q|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _))
      have h3 : ‖((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)‖ = frameWt t β / frameWt t α := by
        rw [norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hd α).le,
          Real.norm_of_nonneg (hd β).le, div_eq_inv_mul]
      rw [Matrix.smul_apply, norm_smul, h3]
      calc _ ≤ K / ratio t s * Bt := mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg hK0 hr.le)
        _ = _ := by ring
  rw [e2, e3, Matrix.sum_apply]
  calc _ ≤ ∑ α : FrameIx r, ‖(∑ β, (((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)) • (P α * M₁ * P β)) i j‖ := norm_sum_le _ _
    _ ≤ ∑ α : FrameIx r, ∑ β : FrameIx r, K * Bt / ratio t s := Finset.sum_le_sum fun α _ => by
        rw [Matrix.sum_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => term α β)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end GlobalTheory.CompanionTheory.RapidDecay

end
