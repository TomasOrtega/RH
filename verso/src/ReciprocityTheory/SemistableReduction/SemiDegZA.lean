import ReciprocityTheory.SemistableReduction.SemiDegZ
import Lemmata.GeneralBFactSecondAlt.Imports

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem det_map_hom {K L : Type} [Field K] [Field L] {r : ℕ} (f : K →+* L)
    (A : Matrix (Fin r) (Fin r) K) : (A.map f).det = f A.det := (RingHom.map_det f A).symm

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Clear the denominators using the available nonvanishing facts. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Use the polynomial consequences of the given equalities and inequalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem gram_det_majorant {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (M : Majorant S) (hG : S.G.det ≠ 0) (σ : K →+* ℂ) (b : Fin r → Fin r → K) :
    (gramC (M.H σ) σ b).det.re = ‖σ (hGram S b).det‖ := by
  have hσG : (S.G.map σ).det ≠ 0 := by
    rw [det_map_hom]
    exact fun h => hG (σ.injective (by rw [h, map_zero]))
  have hdet2 : (M.H σ).det * (M.H σ).det = (S.G.map σ).det * (S.G.map σ).det := by
    have h1 := congr_arg Matrix.det (M.major σ)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h1
    field_simp at h1
    linear_combination h1
  have hpos := (M.posDef σ).det_pos
  rw [Complex.lt_def] at hpos
  set x : ℝ := (M.H σ).det.re with hx
  have hxH : (M.H σ).det = (x : ℂ) := by
    apply Complex.ext
    · simp [hx]
    · simp [← hpos.2]
  have hx0 : 0 < x := by simpa using hpos.1
  have hxn : x = ‖(S.G.map σ).det‖ := by
    have h1 := congr_arg (‖·‖) hdet2
    simp only [norm_mul, hxH, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at h1
    nlinarith [norm_nonneg (S.G.map σ).det]
  rw [gramC_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hxH, hGram_eq,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hE : embMat σ b = (colMat b).map σ := rfl
  rw [det_map_hom, hE, det_map_hom, map_mul, map_mul, S.c_emb]
  rw [det_map_hom] at hxn
  set z := σ (colMat b).det
  rw [Complex.star_def, norm_mul, norm_mul, Complex.norm_conj]
  rw [show (starRingEnd ℂ) z * (x : ℂ) * z = (x : ℂ) * ((starRingEnd ℂ) z * z) by ring,
    Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hxn]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem latDeg_L_nonneg (hS : SelfDualIndexStatement) {K : Type} [Field K] [NumberField K]
    {r : ℕ} (S : HermForm K r) (M : Majorant S) (L : Submodule (𝓞 K) (Fin r → K))
    (hL : IsLattice L) (hSD : IsSelfDual S L) (hG : S.G.det ≠ 0) (b : Fin r → Fin r → K)
    (hb : IsKBasisIn L b) : 0 ≤ latDeg M.H L b := by
  unfold latDeg
  rw [Finset.sum_congr rfl fun σ _ => by rw [gram_det_majorant S M hG σ b], sum_log_norm_emb]
  have h1 := hS K r S L b hL hSD hb
  have hone : 1 ≤ (spanIdx L b : ℝ) :=
    Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 (spanIdx_ne_zero L b hL.1 hb))
  have hlog1 := Real.log_nonneg hone
  by_cases hN0 : |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)| = 0
  · rw [hN0, Real.log_zero]
    unfold spanIdx at hlog1
    linarith
  · have h2 := Real.log_le_log (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hN0)) h1
    rw [Real.log_pow] at h2
    unfold spanIdx at h2
    push_cast at h2
    linarith

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem clear_denom {K : Type} [Field K] [NumberField K] {r : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (v : Fin r → K)
    (hv : v ∈ Submodule.span K (L : Set (Fin r → K))) : ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ L := by
  first | exact Bl.general_b_fact_second_alt.goal1 .. | (apply Bl.general_b_fact_second_alt.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_alt.goal1 <;> assumption)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem kBasis_card {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : IsLattice L) (b : Fin k → Fin r → K)
    (hb : IsKBasisIn L b) : k = r := by
  have hspan : Submodule.span K (Set.range b) = ⊤ := by
    rw [eq_top_iff, ← hL.2, Submodule.span_le]
    intro x hx
    exact hb.2.2 x hx
  have h := finrank_span_eq_card hb.2.1
  rw [hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h
  exact h.symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem g_ne_zero {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K)
    (haniso : ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
      ∑ i, S.c (t i) * g i * t i = 0 → t = 0) :
    ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0 := by
  classical
  intro i h1 h2 hg
  have ht := haniso (Pi.single i 1) (fun j hj => by
    have : j ≠ i := fun e => by rw [e] at hj; omega
    simp [this]) (by
    rw [Finset.sum_eq_single i]
    · simp [hg]
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ _) h)
  have := congr_fun ht i
  simp at this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem semiPoint_of (hW : WittBasisStatement) (hB : LatDegBasisStatement)
    (hN : IntegralIndexStatement) (hS : SelfDualIndexStatement) (hE : GradedExtStatement)
    (hA : AbsDetStatement) : SemiPointStatement := by
  intro K _ _ r S L hL hSD
  have hG := detG_ne_zero S L hL hSD
  obtain ⟨P, m, g, hP, h2m, hJ, haniso⟩ := hW K r S hG
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  set Q := P⁻¹ with hQdef
  have hQ : Q.det ≠ 0 := by
    rw [hQdef, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hP
  set Lp := L.map (matLin Q) with hLpdef
  have hLp : Lp.FG := hL.1.map _
  have hfix := g_fix S P m g hJ
  have hg0 := g_ne_zero S m g haniso
  have hsp : ∀ v : Fin r → K, ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Lp := by
    intro v
    obtain ⟨a, ha, hav⟩ := clear_denom L (P *ᵥ v) (by rw [hL.2]; exact Submodule.mem_top)
    refine ⟨a, ha, ⟨a • (P *ᵥ v), hav, ?_⟩⟩
    rw [map_smul, matLin_apply, Matrix.mulVec_mulVec, hQdef, Matrix.nonsing_inv_mul P hPu,
      Matrix.one_mulVec]
  have hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← hJ, formM_change, matLin_apply, matLin_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hQdef, Matrix.mul_nonsing_inv P hPu, Matrix.one_mulVec,
      Matrix.one_mulVec]
    exact hSD.1 x hx y hy
  obtain ⟨dd, hdd, hsemi⟩ :=
    adapted_semistable hB hN hA hE S m g h2m hfix hg0 haniso Lp hLp hsp hint
  obtain ⟨M, hM⟩ := exists_adapted_majorant S P m g dd hP h2m hJ hdd hg0
  have hHeq : M.H = fun σ : K →+* ℂ => (Q.map σ)ᴴ * diagMet (adMet r m g dd) σ * Q.map σ :=
    funext hM
  have hsemiL : ∀ B : Submodule (𝓞 K) (Fin r → K), B ≤ L → ∀ (k : ℕ)
      (b : Fin k → Fin r → K), IsKBasisIn B b → latDeg M.H B b ≤ 0 := by
    intro B hB k b hb
    rw [hHeq, latDeg_transport _ Q hQ B b]
    exact hsemi _ (Submodule.map_mono hB) k _ (kBasisIn_map Q hQ B b hb)
  refine ⟨M, ?_, hsemiL⟩
  intro k b hb
  obtain rfl : k = r := kBasis_card L hL b hb
  exact le_antisymm (hsemiL L le_rfl k b hb) (latDeg_L_nonneg hS S M L hL hSD hG b hb)

end ReciprocityTheory.MultiplicativeHeights.SemiPt
