import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemThInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMemLiftSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModerateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThetaFree

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ`. Establish `hsp` using `hP.2.isUSplitting`. Establish `hstd : IsStd B.ψ` using `hP.1`. Take `⟨m₀, hm₀, hinv⟩` from `GlobalTheory.ThetaLevel.heis_fix B.ψ hstd.1 Φ hΦ`. Take `⟨C, hC⟩` from `GlobalTheory.ThetaLevel.transport_denom (M.co.e.trans (LinearEquiv.prodComm (AF F) _ _))`.

Use `⟨m₀ * C, fun g h => ?_⟩` and prove the remaining obligations. Take `⟨N, hN, hNle, hT⟩` from `hC ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹) ((h : GL (Fin d) (AF F ⊗[F] E))⁻¹)`. Rewrite `hNle` using `[heightGL_inv, heightGL_inv]`. Use `⟨m₀ * N, Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one]`.

Establish `: ((m₀ * N : ℕ) : ℝ) = m₀ * N` using `by push_cast; ring`. Rewrite using `[this, mul_assoc (m₀ : ℝ) C]`. Conclude with `mul_le_mul_of_nonneg_left hNle (by positivity)`. Establish `hfix : ∀ y : Fin n × Fin d → AF F, IsMulInt F (m₀ * N) y → schr B.ψ (y, 0) (om (g, h) Φ) = om (g, h) Φ` using `by clear hNle hC`. Introduce `y hy`.

Use `set w' := M.co.e.symm (y, 0) with hw'`. Use `set w := ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * w' * (((h : GL (Fin d) (AF F ⊗[F] E))⁻¹ : GL (Fin d) (AF F ⊗[F] E)).1)ᵀ with hw`. Take `⟨h1, h2⟩` from `hT m₀ y hy`. Establish `hΦw : M.co.rho B.ψ w Φ = Φ` using `hinv _ _ h2 h1`. Establish `hact : actAB (cA σ) (g, h) w = w'`.

Simplify using `only [actAB, hw]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one, Matrix.mul_one]`. Establish `himpl` using `hsp.impl (g, h) w Φ hΦ`. Rewrite `himpl` using `[hΦw, hact]`. Rewrite `himpl` using `[Darboux.rho, hw', LinearEquiv.apply_symm_apply]`.

Conclude with `himpl.symm`. Introduce `x a ha`. Establish `hy : IsMulInt F (m₀ * N) (((m₀ * N : ℕ) : AF F) • a)`. Use `⟨fun i => ?_, fun v i => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `fstA F (((m₀ * N : ℕ) : AF F) * a i) = 0`.

Rewrite using `[map_mul]`. Establish `h0 : fstA F (a i) = 0`. Conclude with `(InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 (ha i).1`. Rewrite using `[h0, mul_zero]`. Express the relevant statement in the definitionally equal form `‖evFin F v (((m₀ * N : ℕ) : AF F) * a i)‖ ≤ _`.

Rewrite using `[map_mul, map_natCast, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (Valued.toNormedField.norm_le_one_iff.2 ((ha i).2 v))`. Use `congrFun (hfix _ hy) x` as an intermediate fact. Simplify `this` using `[schr]`.
-/
private theorem periodic_level_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ C : ℝ, ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ 1 ∧ ∀ x a : Fin n × Fin d → AF F, (∀ i, evI F (a i) = 0 ∧ ∀ v, evFin F v (a i) ∈ v.adicCompletionIntegers F) → om (g, h) Φ (x + (m : AF F) • a) = om (g, h) Φ x := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ
  have hsp := hP.2.isUSplitting
  have hstd : IsStd B.ψ := hP.1
  obtain ⟨m₀, hm₀, hinv⟩ := GlobalTheory.ThetaLevel.heis_fix B.ψ hstd.1 Φ hΦ
  obtain ⟨C, hC⟩ := GlobalTheory.ThetaLevel.transport_denom (M.co.e.trans (LinearEquiv.prodComm (AF F) _ _))
  refine ⟨m₀ * C, fun g h => ?_⟩
  obtain ⟨N, hN, hNle, hT⟩ := hC ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹) ((h : GL (Fin d) (AF F ⊗[F] E))⁻¹)
  rw [heightGL_inv, heightGL_inv] at hNle
  refine ⟨m₀ * N, Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩
  · rw [pow_one]
    have : ((m₀ * N : ℕ) : ℝ) = m₀ * N := by push_cast; ring
    rw [this, mul_assoc (m₀ : ℝ) C]
    exact mul_le_mul_of_nonneg_left hNle (by positivity)
  have hfix : ∀ y : Fin n × Fin d → AF F, IsMulInt F (m₀ * N) y → schr B.ψ (y, 0) (om (g, h) Φ) = om (g, h) Φ := by
    clear hNle hC
    intro y hy
    set w' := M.co.e.symm (y, 0) with hw'
    set w := ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * w' *
      (((h : GL (Fin d) (AF F ⊗[F] E))⁻¹ : GL (Fin d) (AF F ⊗[F] E)).1)ᵀ with hw
    obtain ⟨h1, h2⟩ := hT m₀ y hy
    have hΦw : M.co.rho B.ψ w Φ = Φ := hinv _ _ h2 h1
    have hact : actAB (cA σ) (g, h) w = w' := by
      simp only [actAB, hw]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
        Matrix.mul_one]
    have himpl := hsp.impl (g, h) w Φ hΦ
    rw [hΦw, hact] at himpl
    rw [Darboux.rho, hw', LinearEquiv.apply_symm_apply] at himpl
    exact himpl.symm
  intro x a ha
  have hy : IsMulInt F (m₀ * N) (((m₀ * N : ℕ) : AF F) • a) := by
    refine ⟨fun i => ?_, fun v i => ?_⟩
    · change fstA F (((m₀ * N : ℕ) : AF F) * a i) = 0
      rw [map_mul]
      have h0 : fstA F (a i) = 0 := by
        exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 (ha i).1
      rw [h0, mul_zero]
    · change ‖evFin F v (((m₀ * N : ℕ) : AF F) * a i)‖ ≤ _
      rw [map_mul, map_natCast, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (Valued.toNormedField.norm_le_one_iff.2 ((ha i).2 v))
  have := congrFun (hfix _ hy) x
  simpa [schr] using this

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ`. Establish `hsp` using `hP.2.isUSplitting`. Establish `hstd : IsStd B.ψ` using `hP.1`. Take `⟨m₀, hm₀, hinv⟩` from `GlobalTheory.ThetaLevel.heis_fix B.ψ hstd.1 Φ hΦ`. Take `⟨D, hD, hcond⟩` from `std_char_denom B.ψ hstd`.

Take `⟨C, hC⟩` from `GlobalTheory.ThetaLevel.transport_denom M.co.e`. Use `⟨D * m₀ * C, fun g h => ?_⟩` and prove the remaining obligations. Take `⟨N, hN, hNle, hT⟩` from `hC ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹) ((h : GL (Fin d) (AF F ⊗[F] E))⁻¹)`. Rewrite `hNle` using `[heightGL_inv, heightGL_inv]`. Use `⟨D * m₀ * N, Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_one]`. Establish `: ((D * m₀ * N : ℕ) : ℝ) = D * m₀ * N` using `by push_cast; ring`. Rewrite using `[this, mul_assoc (D * m₀ : ℝ) C]`. Conclude with `mul_le_mul_of_nonneg_left hNle (by positivity)`. Introduce `ξ hξ i`.

Establish `hfix : ∀ y : Fin n × Fin d → AF F, IsMulInt F (m₀ * N) y → schr B.ψ (0, y) (om (g, h) Φ) = om (g, h) Φ` using `by clear hξ hcond hNle hC`. Introduce `y hy`. Use `set w' := M.co.e.symm (0, y) with hw'`. Use `set w := ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * w' * (((h : GL (Fin d) (AF F ⊗[F] E))⁻¹ : GL (Fin d) (AF F ⊗[F] E)).1)ᵀ with hw`. Take `⟨h1, h2⟩` from `hT m₀ y hy`.

Establish `hΦw : M.co.rho B.ψ w Φ = Φ` using `hinv _ _ h1 h2`. Establish `hact : actAB (cA σ) (g, h) w = w'`. Simplify using `only [actAB, hw]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one, Matrix.mul_one]`. Establish `himpl` using `hsp.impl (g, h) w Φ hΦ`.

Rewrite `himpl` using `[hΦw, hact]`. Rewrite `himpl` using `[Darboux.rho, hw', LinearEquiv.apply_symm_apply]`. Conclude with `himpl.symm`. Take `⟨o, ho⟩` from `hcond _ (fin_step B.ψ (m₀ * N) _ hfix ξ hξ i)`. Conclude with `⟨o, by rw [← ho]; push_cast; ring⟩`.
-/
private theorem support_denom_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ C : ℝ, ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ 1 ∧ ∀ ξ : Fin n × Fin d → F, om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, ∃ o : 𝓞 F, (m : F) * ξ i = o := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ
  have hsp := hP.2.isUSplitting
  have hstd : IsStd B.ψ := hP.1
  obtain ⟨m₀, hm₀, hinv⟩ := GlobalTheory.ThetaLevel.heis_fix B.ψ hstd.1 Φ hΦ
  obtain ⟨D, hD, hcond⟩ := std_char_denom B.ψ hstd
  obtain ⟨C, hC⟩ := GlobalTheory.ThetaLevel.transport_denom M.co.e
  refine ⟨D * m₀ * C, fun g h => ?_⟩
  obtain ⟨N, hN, hNle, hT⟩ := hC ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹) ((h : GL (Fin d) (AF F ⊗[F] E))⁻¹)
  rw [heightGL_inv, heightGL_inv] at hNle
  refine ⟨D * m₀ * N, Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩
  · rw [pow_one]
    have : ((D * m₀ * N : ℕ) : ℝ) = D * m₀ * N := by push_cast; ring
    rw [this, mul_assoc (D * m₀ : ℝ) C]
    exact mul_le_mul_of_nonneg_left hNle (by positivity)
  intro ξ hξ i
  have hfix : ∀ y : Fin n × Fin d → AF F, IsMulInt F (m₀ * N) y → schr B.ψ (0, y) (om (g, h) Φ) = om (g, h) Φ := by
    clear hξ hcond hNle hC
    intro y hy
    set w' := M.co.e.symm (0, y) with hw'
    set w := ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * w' *
      (((h : GL (Fin d) (AF F ⊗[F] E))⁻¹ : GL (Fin d) (AF F ⊗[F] E)).1)ᵀ with hw
    obtain ⟨h1, h2⟩ := hT m₀ y hy
    have hΦw : M.co.rho B.ψ w Φ = Φ := hinv _ _ h1 h2
    have hact : actAB (cA σ) (g, h) w = w' := by
      simp only [actAB, hw]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
        Matrix.mul_one]
    have himpl := hsp.impl (g, h) w Φ hΦ
    rw [hΦw, hact] at himpl
    rw [Darboux.rho, hw', LinearEquiv.apply_symm_apply] at himpl
    exact himpl.symm
  obtain ⟨o, ho⟩ := hcond _ (fin_step B.ψ (m₀ * N) _ hfix ξ hξ i)
  exact ⟨o, by rw [← ho]; push_cast; ring⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om hP N`. Establish `hstd : IsStd B.ψ` using `hP.1`. Establish `hU` using `hP.2.isUSplitting`. Take `⟨μ, hμ, ℓ, a, C₃, h3⟩` from `GlobalTheory.T.sobolev_uniform_bound_periodic F (Fin n × Fin d) N B.ψ hstd`. Use `⟨1 * a + 2 * ℓ, fun Φ hΦ => ?_⟩` and prove the remaining obligations.

Take `⟨B₀, hB₀⟩` from `GlobalTheory.ThetaSobolevBase.exists_l2_bound_heisenberg_word F (Fin n × Fin d) B.ψ hstd μ hμ Φ hΦ ℓ`. Take `⟨C₂, h2⟩` from `archUnit_act_bound F E σ B n d X W M χX χW om hP`. Take `⟨C₄, h4⟩` from `periodic_level_one F E σ B n d X W M χX χW om hP Φ hΦ`. Take `⟨c₅, h5⟩` from `sum_places_le (F := F)`. Establish `hC₂ : ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArchUnit (M.co.e u) → ∃ c : ℝ, 0 ≤ c ∧ c ≤ max C₂ 1 * ((ht p.1 : ℝ) * ht p.2) ∧ ∃ w, IsArchUnit w ∧ M.co.e (actAB (cA σ) p u) = realAd F c • w` using `fun p u hu => by`.

Take `⟨c, h0, hle, w, hw, he⟩` from `h2 p u hu`. Conclude with `⟨c, h0, hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))), w, hw, he⟩`. Use `⟨max c₅ 1 ^ N * (max C₃ 0 * (max C₄ 1 ^ a * (1 + max C₂ 1 ^ (2 * ℓ) * max B₀ 0))), fun g h ξ => ?_⟩` and prove the remaining obligations. Establish `hH : (1 : ℝ) ≤ (ht g : ℝ) * ht h` using `one_le_mul_of_one_le_of_one_le (by exact_mod_cast one_le_heightGL F g.1) (by exact_mod_cast one_le_heightGL F h.1)`. Establish `hCH : (1 : ℝ) ≤ max C₂ 1 * ((ht g : ℝ) * ht h)` using `one_le_mul_of_one_le_of_one_le (le_max_right _ _) hH`.

Establish `hΨ : om (g, h) Φ ∈ schA F (Fin n × Fin d)` using `hU.pres (g, h) Φ hΦ`. Take `⟨m, hm1, hmle, hper⟩` from `h4 g h`. Establish `hwords : ∀ l : List ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)), l.length ≤ ℓ → (∀ w ∈ l, IsArchUnit w) → ∫⁻ x, ‖wordH B.ψ l (om (g, h) Φ) x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ((max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * ℓ) * max B₀ 0)`. Introduce `l hl hu`. Take `⟨c, l', hc0, hcle, hl', hlen, he⟩` from `word_transport hP hΦ hC₂ (g, h) l hu`.

Establish `hF : wordH B.ψ l' Φ ∈ schA F (Fin n × Fin d)` using `wordH_mem B.ψ hstd l' (fun v hv => (hl' v hv).1) Φ hΦ`. Establish `hun` using `hU.unit μ hμ (g, h) _ hF`. Establish `hc2 : c ^ 2 ≤ (max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * ℓ)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `lintegral_sq_norm_le_of_smul μ _ _ c hc0 he B₀ _ (hun.trans_le (hB₀ l' (by omega) hl')) hc2`.

Establish `key` using `h3 (om (g, h) Φ) hΨ m hm1 hper _ (mul_nonneg (pow_nonneg (by linarith) _) (le_max_right _ _)) hwords (fun i => algebraMap F (AF F) (ξ i))`. Establish `hS0 : 0 ≤ ∑ i, ‖evI F (algebraMap F (AF F) (ξ i))‖` using `Finset.sum_nonneg fun _ _ => norm_nonneg _`. Establish `hA0 : 0 ≤ 1 + ∑ i, ∑ w : InfinitePlace F, w (ξ i)` using `add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun w _ => apply_nonneg w _)`. Establish `hA : 1 + ∑ i, ∑ w : InfinitePlace F, w (ξ i) ≤ max c₅ 1 * (1 + ∑ i, ‖evI F (algebraMap F (AF F) (ξ i))‖)`. Establish `: ∑ i, ∑ w : InfinitePlace F, w (ξ i) ≤ max c₅ 1 * ∑ i, ‖evI F (algebraMap F (AF F) (ξ i))‖`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun i _ => (h5 (ξ i)).trans ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)`. Establish `h1 : (1 : ℝ) ≤ max c₅ 1` using `le_max_right _ _`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `final_arith _ _ _ _ _ _ _ _ _ _ N a 1 ℓ (norm_nonneg _) hA0 hA (Nat.cast_nonneg m) hmle hH key`.
-/
private theorem decay_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∀ N : ℕ, ∃ k : ℕ, ∀ Φ ∈ schA F (Fin n × Fin d), ∃ C : ℝ, ∀ g h (ξ : Fin n × Fin d → F), ‖om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ∑ i, ∑ w : InfinitePlace F, w (ξ i)) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP N
  classical
  have hstd : IsStd B.ψ := hP.1
  have hU := hP.2.isUSplitting
  obtain ⟨μ, hμ, ℓ, a, C₃, h3⟩ := GlobalTheory.T.sobolev_uniform_bound_periodic F (Fin n × Fin d) N B.ψ hstd
  refine ⟨1 * a + 2 * ℓ, fun Φ hΦ => ?_⟩
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.ThetaSobolevBase.exists_l2_bound_heisenberg_word F (Fin n × Fin d) B.ψ hstd μ hμ Φ hΦ ℓ
  obtain ⟨C₂, h2⟩ := archUnit_act_bound F E σ B n d X W M χX χW om hP
  obtain ⟨C₄, h4⟩ := periodic_level_one F E σ B n d X W M χX χW om hP Φ hΦ
  obtain ⟨c₅, h5⟩ := sum_places_le (F := F)
  have hC₂ : ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArchUnit (M.co.e u) →
      ∃ c : ℝ, 0 ≤ c ∧ c ≤ max C₂ 1 * ((ht p.1 : ℝ) * ht p.2) ∧ ∃ w, IsArchUnit w ∧
        M.co.e (actAB (cA σ) p u) = realAd F c • w := fun p u hu => by
    obtain ⟨c, h0, hle, w, hw, he⟩ := h2 p u hu
    exact ⟨c, h0, hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))), w, hw, he⟩
  refine ⟨max c₅ 1 ^ N * (max C₃ 0 * (max C₄ 1 ^ a * (1 + max C₂ 1 ^ (2 * ℓ) * max B₀ 0))),
    fun g h ξ => ?_⟩
  have hH : (1 : ℝ) ≤ (ht g : ℝ) * ht h :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast one_le_heightGL F g.1) (by exact_mod_cast one_le_heightGL F h.1)
  have hCH : (1 : ℝ) ≤ max C₂ 1 * ((ht g : ℝ) * ht h) := one_le_mul_of_one_le_of_one_le (le_max_right _ _) hH
  have hΨ : om (g, h) Φ ∈ schA F (Fin n × Fin d) := hU.pres (g, h) Φ hΦ
  obtain ⟨m, hm1, hmle, hper⟩ := h4 g h
  have hwords : ∀ l : List ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)), l.length ≤ ℓ →
      (∀ w ∈ l, IsArchUnit w) → ∫⁻ x, ‖wordH B.ψ l (om (g, h) Φ) x‖ₑ ^ 2 ∂μ ≤
        ENNReal.ofReal ((max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * ℓ) * max B₀ 0) := by
    intro l hl hu
    obtain ⟨c, l', hc0, hcle, hl', hlen, he⟩ := word_transport hP hΦ hC₂ (g, h) l hu
    have hF : wordH B.ψ l' Φ ∈ schA F (Fin n × Fin d) := wordH_mem B.ψ hstd l' (fun v hv => (hl' v hv).1) Φ hΦ
    have hun := hU.unit μ hμ (g, h) _ hF
    have hc2 : c ^ 2 ≤ (max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * ℓ) := by
      calc c ^ 2 ≤ ((max C₂ 1 * ((ht g : ℝ) * ht h)) ^ l.length) ^ 2 := pow_le_pow_left₀ hc0 hcle 2
        _ = (max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * l.length) := by rw [← pow_mul, Nat.mul_comm]
        _ ≤ (max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * ℓ) := pow_le_pow_right₀ hCH (by omega)
    exact lintegral_sq_norm_le_of_smul μ _ _ c hc0 he B₀ _ (hun.trans_le (hB₀ l' (by omega) hl')) hc2
  have key := h3 (om (g, h) Φ) hΨ m hm1 hper _ (mul_nonneg (pow_nonneg (by linarith) _) (le_max_right _ _)) hwords
    (fun i => algebraMap F (AF F) (ξ i))
  have hS0 : 0 ≤ ∑ i, ‖evI F (algebraMap F (AF F) (ξ i))‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hA0 : 0 ≤ 1 + ∑ i, ∑ w : InfinitePlace F, w (ξ i) :=
    add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun w _ => apply_nonneg w _)
  have hA : 1 + ∑ i, ∑ w : InfinitePlace F, w (ξ i) ≤ max c₅ 1 * (1 + ∑ i, ‖evI F (algebraMap F (AF F) (ξ i))‖) := by
    have : ∑ i, ∑ w : InfinitePlace F, w (ξ i) ≤ max c₅ 1 * ∑ i, ‖evI F (algebraMap F (AF F) (ξ i))‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => (h5 (ξ i)).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    have h1 : (1 : ℝ) ≤ max c₅ 1 := le_max_right _ _
    nlinarith
  exact final_arith _ _ _ _ _ _ _ _ _ _ N a 1 ℓ (norm_nonneg _) hA0 hA (Nat.cast_nonneg m) hmle hH key

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om hP`. Take `⟨N, C₀, hC₀, hcount⟩` from `GlobalTheory.RatPointSum.norm_thetaSum_le F (Fin n × Fin d)`. Take `⟨k₃, hk₃⟩` from `decay_unif F E σ B n d X W M χX χW om hP N`. Use `⟨k₃ + 1 * N, fun Φ hΦ => ?_⟩` and prove the remaining obligations. Take `⟨C₂, hsupp⟩` from `support_denom_one F E σ B n d X W M χX χW om hP Φ hΦ`.

Take `⟨C₃, hdec⟩` from `hk₃ Φ hΦ`. Use `⟨C₀ * C₃ * C₂ ^ N, fun g h => ?_⟩` and prove the remaining obligations. Take `⟨m, hm1, hmle, hm⟩` from `hsupp g h`. Use `set x : ℝ := (ht g : ℝ) * ht h`. Establish `hB : 0 ≤ C₃ * x ^ k₃` using `le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun w _ => w.1.nonneg _)) _)) (hdec g h 0)`.

Establish `key` using `hcount m (C₃ * x ^ k₃) (om (g, h) Φ) hm1 (hm) (hdec g h)`. Establish `hm0 : (0 : ℝ) ≤ m` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem theta_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∃ k : ℕ, ∀ Φ ∈ schA F (Fin n × Fin d), ∃ C : ℝ, ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP
  obtain ⟨N, C₀, hC₀, hcount⟩ := GlobalTheory.RatPointSum.norm_thetaSum_le F (Fin n × Fin d)
  obtain ⟨k₃, hk₃⟩ := decay_unif F E σ B n d X W M χX χW om hP N
  refine ⟨k₃ + 1 * N, fun Φ hΦ => ?_⟩
  obtain ⟨C₂, hsupp⟩ := support_denom_one F E σ B n d X W M χX χW om hP Φ hΦ
  obtain ⟨C₃, hdec⟩ := hk₃ Φ hΦ
  refine ⟨C₀ * C₃ * C₂ ^ N, fun g h => ?_⟩
  obtain ⟨m, hm1, hmle, hm⟩ := hsupp g h
  set x : ℝ := (ht g : ℝ) * ht h
  have hB : 0 ≤ C₃ * x ^ k₃ := le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun w _ => w.1.nonneg _)) _)) (hdec g h 0)
  have key := hcount m (C₃ * x ^ k₃) (om (g, h) Φ) hm1 (hm) (hdec g h)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  calc ‖theta om Φ g h‖ = ‖GlobalTheory.WeilM.thetaSum F (om (g, h) Φ)‖ := rfl
    _ ≤ C₀ * (C₃ * x ^ k₃) * (m : ℝ) ^ N := key
    _ ≤ C₀ * (C₃ * x ^ k₃) * (C₂ * x ^ 1) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 hmle N) (mul_nonneg hC₀ hB)
    _ = C₀ * C₃ * C₂ ^ N * x ^ (k₃ + 1 * N) := by rw [mul_pow, pow_add, pow_mul]; ring

end GlobalTheory.ThetaFree

end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar GlobalTheory.ThK.TowerInt
open GlobalTheory.ThK.LiftConst GlobalTheory.ThK.SplitInv GlobalTheory.ThKLiftCusp GlobalTheory.ThK.SquareIntegrability

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP`. Take `⟨k, hk⟩` from `GlobalTheory.ThetaFree.theta_unif F E σ B n d X W M χX χW om ⟨hP.base.std, hP.weil⟩`. Use `⟨k, fun Φ hΦ => ?_⟩` and prove the remaining obligations. Take `⟨C, hCk⟩` from `hk Φ hΦ`. Establish `hinv` using `((GlobalTheory.T.theta_basic_properties hK.base F E σ B n d X W M χX χW om r s r' s' hP).1 Φ hΦ).2.1`.

Use `⟨|C|, k, fun g h => ?_⟩` and prove the remaining obligations. Establish `hb : ∀ h, ‖theta om Φ g h‖ ≤ (|C| * (ht g : ℝ) ^ k) * (ht h : ℝ) ^ k` using `fun h => by`. Use `(hCk g h).trans ?_` and prove the remaining obligations. Rewrite using `[mul_pow, ← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) (by positivity)`.

Establish `hi : ∀ γ ∈ ratU σ W.J, ∀ x, theta om Φ g (γ * x) = theta om Φ g x` using `fun γ hγ x => by`. Simplify using `using hinv 1 (one_mem _) γ hγ g x`. Use `GlobalTheory.ThKOrthVInt.norm_le_qht_of_le_ht (g := fun h => theta om Φ g h) hi hb h` as an intermediate fact. Rewrite `this` using `[max_eq_left (by positivity)]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.theta_function_polynomial_growth_bound :
    GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
                 (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
                 ∃ N : ℕ, ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * (ht g : ℝ) ^ N * (qht h : ℝ) ^ k := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨k, hk⟩ := GlobalTheory.ThetaFree.theta_unif F E σ B n d X W M χX χW om ⟨hP.base.std, hP.weil⟩
  refine ⟨k, fun Φ hΦ => ?_⟩
  obtain ⟨C, hCk⟩ := hk Φ hΦ
  have hinv := ((GlobalTheory.T.theta_basic_properties hK.base F E σ B n d X W M χX χW om r s r' s' hP).1 Φ hΦ).2.1
  refine ⟨|C|, k, fun g h => ?_⟩
  have hb : ∀ h, ‖theta om Φ g h‖ ≤ (|C| * (ht g : ℝ) ^ k) * (ht h : ℝ) ^ k := fun h => by
    refine (hCk g h).trans ?_
    rw [mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) (by positivity)
  have hi : ∀ γ ∈ ratU σ W.J, ∀ x, theta om Φ g (γ * x) = theta om Φ g x := fun γ hγ x => by
    simpa using hinv 1 (one_mem _) γ hγ g x
  have := GlobalTheory.ThKOrthVInt.norm_le_qht_of_le_ht (g := fun h => theta om Φ g h) hi hb h
  rwa [max_eq_left (by positivity)] at this
