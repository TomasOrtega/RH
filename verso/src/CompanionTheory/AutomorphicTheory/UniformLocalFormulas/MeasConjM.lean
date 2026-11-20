import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnipotentRadicalContracting
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P WlocSk.NB
open scoped ENNReal Kronecker

noncomputable section

namespace Formalism.MainStatements.RowRest

variable {k r : ℕ}

def rowM (r : ℕ) (ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Matrix (CI k r) (CI k r) ℂ :=
  Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ νᵀ) 0 0 1)

/- English proof (translation)
Unfold `rowM`. Rewrite using `[Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_kronecker]`. Simplify using the standard rewrite rules.
-/
theorem rowM_det (ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : (rowM r ν).det = ν.det ^ r := by
  unfold rowM
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_kronecker]
  simp

/- English proof (translation)
Simplify using `[rowM, Matrix.fromBlocks_mulVec]`.
-/
theorem rowM_A (ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (x : CI k r → ℂ) (p : UP r) :
    (rowM r ν *ᵥ x) (Sum.inl p) = x (Sum.inl p) := by
  simp [rowM, Matrix.fromBlocks_mulVec]

/- English proof (translation)
Simplify using `[rowM, Matrix.fromBlocks_mulVec]`.
-/
theorem rowM_K (ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (x : CI k r → ℂ) (p : UP r) :
    (rowM r ν *ᵥ x) (Sum.inr (Sum.inr p)) = x (Sum.inr (Sum.inr p)) := by
  simp [rowM, Matrix.fromBlocks_mulVec]

/- English proof (translation)
Simplify using `only [rowM, Matrix.fromBlocks_mulVec, Sum.elim_inr, Sum.elim_inl, Matrix.zero_mulVec, zero_add, add_zero]`. Simplify using `[Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, mul_comm]`.
-/
theorem rowM_B (ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (x : CI k r → ℂ) (a : Fin r) (j : Fin (k + 1)) :
    (rowM r ν *ᵥ x) (Sum.inr (Sum.inl (a, j))) = ∑ c, x (Sum.inr (Sum.inl (a, c))) * ν c j := by
  simp only [rowM, Matrix.fromBlocks_mulVec, Sum.elim_inr, Sum.elim_inl, Matrix.zero_mulVec, zero_add, add_zero]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, mul_comm]

/- English proof (translation)
Set `L : (CI k r → ℂ) →ₗ[ℝ] (CI k r → ℂ)` to `(Matrix.toLin' (rowM r ν)).restrictScalars ℝ`. Establish `hd : LinearMap.det L = 1`. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', rowM_det, Algebra.norm_complex_apply, map_pow, hν, one_pow]`. Use `⟨L.continuous_of_finiteDimensional.measurable, ?_⟩` and prove the remaining obligations. Use `Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (CI k r → ℂ)) (f := L) (by rw [hd]; exact one_ne_zero)` as an intermediate fact.

Rewrite `this` using `[hd]`. Use `show Measure.map L volume = volume`. Simplify using `using this`.
-/
theorem rowM_mp {ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hν : Complex.normSq ν.det = 1) :
    MeasurePreserving (fun x : CI k r → ℂ => rowM r ν *ᵥ x) volume volume := by
  let L : (CI k r → ℂ) →ₗ[ℝ] (CI k r → ℂ) := (Matrix.toLin' (rowM r ν)).restrictScalars ℝ
  have hd : LinearMap.det L = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', rowM_det, Algebra.norm_complex_apply, map_pow, hν, one_pow]
  refine ⟨L.continuous_of_finiteDimensional.measurable, ?_⟩
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (CI k r → ℂ)) (f := L) (by rw [hd]; exact one_ne_zero)
  rw [hd] at this
  show Measure.map L volume = volume
  simpa using this

/- English proof (translation)
Establish `: Continuous (conjM (k` using `k) (r := r) a) := by show Continuous fun x : Mt k r => (a * (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * a⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)`. Conclude with `(continuous_const.matrix_mul (continuous_id : Continuous fun x : Mt k r => x)).matrix_mul continuous_const`. Conclude with `this.measurable`.
-/
theorem meas_conjM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Measurable (conjM (k := k) (r := r) a) := by
  have : Continuous (conjM (k := k) (r := r) a) := by
    show Continuous fun x : Mt k r => (a * (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * a⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    exact (continuous_const.matrix_mul (continuous_id : Continuous fun x : Mt k r => x)).matrix_mul continuous_const
  exact this.measurable

/- English proof (translation)
Establish `hρ0 : ρ ∈ UWset k r 0` using `⟨hρ.1, hρ.2, by simp⟩`. Take `⟨μ, hμ, rfl⟩` from `(TwoByOneBlock.UWb_iff ρ).1 hρ`. Establish `hνU : (μ⁻¹)ᴴ * Hb k * μ⁻¹ = Hb k` using `(TwoByOneBlock.UHb_inv hμ).2`. Establish `hν : Complex.normSq (μ⁻¹).det = 1`. Establish `h` using `congrArg Matrix.det hνU`.

Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`. Establish `h0 : (Hb k).det ≠ 0` using `TwoByOneBlock.Hb_unit.ne_zero`. Establish `h2 : ((Complex.normSq (μ⁻¹).det : ℝ) : ℂ) = 1`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Use `mul_right_cancel₀ h0 ?_` and prove the remaining obligations.

Rewrite `h` using `[RCLike.star_def]`. Take the linear combination `h`. Conclude with `h2` after adjusting the coercions. Set `Φ : (CI k r → ℂ) × (Fin r → ℝ) → Mt k r` to `fun t => phi0 t.1 t.2`. Establish `hΦc : Continuous Φ` using `continuous_nilpotent_chart`.

Establish `hΦ : Measurable Φ` using `hΦc.measurable`. Establish `hmp` using `(rowM_mp (r := r) hν).prod (MeasurePreserving.id (volume : Measure (Fin r → ℝ)))`. Establish `key : conjM (B2.embWb k r μ) ∘ Φ = Φ ∘ Prod.map (fun x : CI k r → ℂ => rowM r μ⁻¹ *ᵥ x) id`. Use function extensionality and compare the values at `t`. Use `set g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := phi0 t.1 t.2 with hg`.

Establish `hN : B2.embWb k r μ * g * (B2.embWb k r μ)⁻¹ ∈ Nset k r` using `PI.QuotSetU.UnitaryGroupMassFormula.SW.uw_conj_N hρ0 (test_vector_mem_schwartz_bruhat t.1 t.2)`. Use `show B2.embWb k r μ * g * (B2.embWb k r μ)⁻¹ = phi0 (rowM r μ⁻¹ *ᵥ t.1) t.2`. Rewrite using `[← nilpotent_chart_left_inverse hN, TwoByOneBlock.emb_inv hμ]`. Use `set g' := B2.embWb k r μ * g * B2.embWb k r μ⁻¹ with hg'`. Establish `ho : ∀ i j, ¬ TwoByOneBlock.mid k r i → ¬ TwoByOneBlock.mid k r j → g' i j = g i j` using `fun i j hi hj => by`.

Rewrite using `[hg', TwoByOneBlock.mul_emb_out _ _ _ _ hj, TwoByOneBlock.emb_mul_out _ _ _ _ hi]`. Establish `hm : mof g' = mof g`. Establish `e1 : bF g' = bF g` using `by ext a b; exact ho _ _ (TwoByOneBlock.esI_out a) (TwoByOneBlock.esI_out b)`. Establish `e2 : bC g' = bC g` using `by ext a b; exact ho _ _ (TwoByOneBlock.eI_out a) (TwoByOneBlock.esI_out b)`. Unfold `mof`.

Rewrite using `[e1, e2]`. Take `⟨p1, p2⟩` from `nilpotent_chart_right_inverse t.1 t.2`. Rewrite `p1`, `p2` using `[← hg]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Break down `i with p | ⟨a, j⟩ | p` into its components or cases. Rewrite using `[rowM_A, ← p1]`. Conclude with `ho _ _ (TwoByOneBlock.eI_out _) (TwoByOneBlock.eI_out _)`. Rewrite using `[rowM_B, ← p1] show g' (eI k r a) (wI k r j) = _`. Rewrite using `[hg', TwoByOneBlock.mul_emb_mid]`.

Conclude with `Finset.sum_congr rfl fun c _ => by rw [TwoByOneBlock.emb_mul_out _ _ _ _ (TwoByOneBlock.eI_out a)]; rfl`. Rewrite using `[rowM_K, ← p1] show kof g' _ _ = kof g _ _`. Unfold `kof`. Rewrite using `[hm]`. Rewrite using `[← p2]`.

Unfold `psiR`. Rewrite using `[hm]`. Establish `hH : haarLie (Nset k r) 1 = ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) • (volume : Measure ((CI k r → ℂ) × (Fin r → ℝ))).map Φ` using `Formalism.L2.SG.Pf.NcReal.JX.exponential_chart_haar k r`. Rewrite using `[hH, Measure.map_smul, Measure.map_map (meas_conjM _) hΦ, key, ← Measure.map_map hΦ hmp.measurable]`. Conclude with `congrArg (fun m => ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) • Measure.map Φ m) hmp.map_eq`.
-/
theorem conj_uwb {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hρ : ρ ∈ B2.UWb k r) :
    (haarLie (Nset k r) 1).map (conjM ρ) = haarLie (Nset k r) 1 := by
  have hρ0 : ρ ∈ UWset k r 0 := ⟨hρ.1, hρ.2, by simp⟩
  obtain ⟨μ, hμ, rfl⟩ := (TwoByOneBlock.UWb_iff ρ).1 hρ
  have hνU : (μ⁻¹)ᴴ * Hb k * μ⁻¹ = Hb k := (TwoByOneBlock.UHb_inv hμ).2
  have hν : Complex.normSq (μ⁻¹).det = 1 := by
    have h := congrArg Matrix.det hνU
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
    have h0 : (Hb k).det ≠ 0 := TwoByOneBlock.Hb_unit.ne_zero
    have h2 : ((Complex.normSq (μ⁻¹).det : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      refine mul_right_cancel₀ h0 ?_
      rw [RCLike.star_def] at h
      linear_combination h
    exact_mod_cast h2
  let Φ : (CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => phi0 t.1 t.2
  have hΦc : Continuous Φ := continuous_nilpotent_chart
  have hΦ : Measurable Φ := hΦc.measurable
  have hmp := (rowM_mp (r := r) hν).prod (MeasurePreserving.id (volume : Measure (Fin r → ℝ)))
  have key : conjM (B2.embWb k r μ) ∘ Φ = Φ ∘ Prod.map (fun x : CI k r → ℂ => rowM r μ⁻¹ *ᵥ x) id := by
    funext t
    set g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := phi0 t.1 t.2 with hg
    have hN : B2.embWb k r μ * g * (B2.embWb k r μ)⁻¹ ∈ Nset k r :=
      PI.QuotSetU.UnitaryGroupMassFormula.SW.uw_conj_N hρ0 (test_vector_mem_schwartz_bruhat t.1 t.2)
    show B2.embWb k r μ * g * (B2.embWb k r μ)⁻¹ = phi0 (rowM r μ⁻¹ *ᵥ t.1) t.2
    rw [← nilpotent_chart_left_inverse hN, TwoByOneBlock.emb_inv hμ]
    set g' := B2.embWb k r μ * g * B2.embWb k r μ⁻¹ with hg'
    have ho : ∀ i j, ¬ TwoByOneBlock.mid k r i → ¬ TwoByOneBlock.mid k r j → g' i j = g i j := fun i j hi hj => by
      rw [hg', TwoByOneBlock.mul_emb_out _ _ _ _ hj, TwoByOneBlock.emb_mul_out _ _ _ _ hi]
    have hm : mof g' = mof g := by
      have e1 : bF g' = bF g := by ext a b; exact ho _ _ (TwoByOneBlock.esI_out a) (TwoByOneBlock.esI_out b)
      have e2 : bC g' = bC g := by ext a b; exact ho _ _ (TwoByOneBlock.eI_out a) (TwoByOneBlock.esI_out b)
      unfold mof; rw [e1, e2]
    obtain ⟨p1, p2⟩ := nilpotent_chart_right_inverse t.1 t.2
    rw [← hg] at p1 p2
    congr 1
    · funext i
      rcases i with p | ⟨a, j⟩ | p
      · rw [rowM_A, ← p1]; exact ho _ _ (TwoByOneBlock.eI_out _) (TwoByOneBlock.eI_out _)
      · rw [rowM_B, ← p1]
        show g' (eI k r a) (wI k r j) = _
        rw [hg', TwoByOneBlock.mul_emb_mid]
        exact Finset.sum_congr rfl fun c _ => by rw [TwoByOneBlock.emb_mul_out _ _ _ _ (TwoByOneBlock.eI_out a)]; rfl
      · rw [rowM_K, ← p1]
        show kof g' _ _ = kof g _ _
        unfold kof; rw [hm]
    · rw [← p2]; unfold psiR; rw [hm]
  have hH : haarLie (Nset k r) 1 = ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) •
      (volume : Measure ((CI k r → ℂ) × (Fin r → ℝ))).map Φ := Formalism.L2.SG.Pf.NcReal.JX.exponential_chart_haar k r
  rw [hH, Measure.map_smul, Measure.map_map (meas_conjM _) hΦ, key, ← Measure.map_map hΦ hmp.measurable]
  exact congrArg (fun m => ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) • Measure.map Φ m) hmp.map_eq

/- English proof (translation)
Unfold `B.aDil bvec`. Rewrite using `[Matrix.diagonal_mulVec_single, ← Pi.single_smul']`. Establish `: (eI k r a).val < r` using `a.isLt`. Rewrite using `[if_pos this]`. Simplify using `[eI]`.
-/
theorem aDil_e (t : ℝ) (a : Fin r) :
    B.aDil k r t *ᵥ bvec (eI k r a) = ((t : ℂ) ^ (r - a.val)) • bvec (eI k r a) := by
  unfold B.aDil bvec
  rw [Matrix.diagonal_mulVec_single, ← Pi.single_smul']
  have : (eI k r a).val < r := a.isLt
  rw [if_pos this]
  simp [eI]

/- English proof (translation)
Unfold `B.aDil bvec`. Rewrite using `[Matrix.diagonal_mulVec_single, ← Pi.single_smul']`. Use `a.isLt` as an intermediate fact. Establish `h1 : ¬ (esI k r a).val < r` using `by simp only [esI]; omega`. Establish `h2 : ¬ (esI k r a).val ≤ r + k` using `by simp only [esI]; omega`.

Establish `h3 : (esI k r a).val - (r + k) = r - a.val` using `by simp only [esI]; omega`. Rewrite using `[if_neg h1, if_neg h2, h3]`. Simplify using the standard rewrite rules.
-/
theorem aDil_f (t : ℝ) (a : Fin r) :
    B.aDil k r t *ᵥ bvec (esI k r a) = ((t : ℂ) ^ (r - a.val))⁻¹ • bvec (esI k r a) := by
  unfold B.aDil bvec
  rw [Matrix.diagonal_mulVec_single, ← Pi.single_smul']
  have := a.isLt
  have h1 : ¬ (esI k r a).val < r := by simp only [esI]; omega
  have h2 : ¬ (esI k r a).val ≤ r + k := by simp only [esI]; omega
  have h3 : (esI k r a).val - (r + k) = r - a.val := by simp only [esI]; omega
  rw [if_neg h1, if_neg h2, h3]
  simp

/- English proof (translation)
Establish `hG` using `unitary_group_closed k r`. Establish `ha : B.aDil k r t ∈ B.GV k r` using `B4.aDil_mem k r t ht.ne'`. Establish `htc : ∀ a : Fin r, ((t : ℂ) ^ (r - a.val)) ≠ 0` using `fun a => pow_ne_zero _ (by exact_mod_cast ht.ne')`. Establish `hi` using `B2x7.aDil_inv_mul k r t ht.ne'`. Establish `hρ : (B.aDil k r t)⁻¹ * d ∈ B2.UWb k r`.

Use `⟨hG.mul_mem _ (hG.inv_mem _ ha) _ hd, fun a => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, he, ← aDil_e, Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]`. Rewrite using `[← Matrix.mulVec_mulVec, hf, ← aDil_f, Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]`. Establish `e : conjM (k` using `k) (r := r) d = conjM (B.aDil k r t) ∘ conjM ((B.aDil k r t)⁻¹ * d) := by`. Use function extensionality and compare the values at `x`.

Use `show d * Matrix.of x * d⁻¹ = B.aDil k r t * ((B.aDil k r t)⁻¹ * d * Matrix.of x * ((B.aDil k r t)⁻¹ * d)⁻¹) * (B.aDil k r t)⁻¹`. Rewrite using `[Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hG.unit _ ha)]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[B2x7.aDil_mul_inv k r t ht.ne', Matrix.mul_one, ← Matrix.mul_assoc (B.aDil k r t), B2x7.aDil_mul_inv k r t ht.ne', Matrix.one_mul]`. Rewrite using `[e, ← Measure.map_map (meas_conjM _) (meas_conjM _), conj_uwb hρ]`.

Conclude with `dilation_jacobian_unipotent k r _ (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ (Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top)) t ht`.
-/
theorem conj_levi {d : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hd : d ∈ UH (Hpk k r)) {t : ℝ} (ht : 0 < t)
    (he : ∀ a : Fin r, d *ᵥ bvec (eI k r a) = ((t : ℂ) ^ (r - a.val)) • bvec (eI k r a))
    (hf : ∀ a : Fin r, d *ᵥ bvec (esI k r a) = ((t : ℂ) ^ (r - a.val))⁻¹ • bvec (esI k r a)) :
    (haarLie (Nset k r) 1).map (conjM d) = ENNReal.ofReal ((t ^ B.kap k r)⁻¹) • haarLie (Nset k r) 1 := by
  have hG := unitary_group_closed k r
  have ha : B.aDil k r t ∈ B.GV k r := B4.aDil_mem k r t ht.ne'
  have htc : ∀ a : Fin r, ((t : ℂ) ^ (r - a.val)) ≠ 0 := fun a => pow_ne_zero _ (by exact_mod_cast ht.ne')
  have hi := B2x7.aDil_inv_mul k r t ht.ne'
  have hρ : (B.aDil k r t)⁻¹ * d ∈ B2.UWb k r := by
    refine ⟨hG.mul_mem _ (hG.inv_mem _ ha) _ hd, fun a => ⟨?_, ?_⟩⟩
    · rw [← Matrix.mulVec_mulVec, he, ← aDil_e, Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
    · rw [← Matrix.mulVec_mulVec, hf, ← aDil_f, Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  have e : conjM (k := k) (r := r) d = conjM (B.aDil k r t) ∘ conjM ((B.aDil k r t)⁻¹ * d) := by
    funext x
    show d * Matrix.of x * d⁻¹ =
      B.aDil k r t * ((B.aDil k r t)⁻¹ * d * Matrix.of x * ((B.aDil k r t)⁻¹ * d)⁻¹) * (B.aDil k r t)⁻¹
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hG.unit _ ha)]
    simp only [Matrix.mul_assoc]
    rw [B2x7.aDil_mul_inv k r t ht.ne', Matrix.mul_one, ← Matrix.mul_assoc (B.aDil k r t), B2x7.aDil_mul_inv k r t ht.ne',
      Matrix.one_mul]
  rw [e, ← Measure.map_map (meas_conjM _) (meas_conjM _), conj_uwb hρ]
  exact dilation_jacobian_unipotent k r _ (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _
    (Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top)) t ht

end Formalism.MainStatements.RowRest
