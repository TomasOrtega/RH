import ReciprocityTheory.SemistableReduction.SemiDegZ
import Lemmata.GeneralBFactSecondAlt.Imports

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

/- English proof (translation)
The claim follows from `(RingHom.map_det f A).symm`.
-/
theorem det_map_hom {K L : Type} [Field K] [Field L] {r : ℕ} (f : K →+* L)
    (A : Matrix (Fin r) (Fin r) K) : (A.map f).det = f A.det := (RingHom.map_det f A).symm

/- English proof (translation)
Establish `hσG : (S.G.map σ).det ≠ 0`. Rewrite using `[det_map_hom]`. Conclude with `fun h => hG (σ.injective (by rw [h, map_zero]))`. Establish `hdet2 : (M.H σ).det * (M.H σ).det = (S.G.map σ).det * (S.G.map σ).det`. Establish `h1` using `congr_arg Matrix.det (M.major σ)`.

Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Clear denominators, using `at h1` for the nonvanishing conditions. Take the linear combination `h1`. Establish `hpos` using `(M.posDef σ).det_pos`. Rewrite `hpos` using `[Complex.lt_def]`.

Use `set x : ℝ := (M.H σ).det.re with hx`. Establish `hxH : (M.H σ).det = (x : ℂ)`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[hx]`. Simplify using `[← hpos.2]`.

Establish `hx0 : 0 < x` using `by simpa using hpos.1`. Establish `hxn : x = ‖(S.G.map σ).det‖`. Establish `h1` using `congr_arg (‖·‖) hdet2`. Simplify using `only [norm_mul, hxH, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at h1`. Use polynomial arithmetic with `[norm_nonneg (S.G.map σ).det]`.

Rewrite using `[gramC_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hxH, hGram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`. Establish `hE : embMat σ b = (colMat b).map σ` using `rfl`. Rewrite using `[det_map_hom, hE, det_map_hom, map_mul, map_mul, S.c_emb]`. Rewrite `hxn` using `[det_map_hom]`. Use `set z := σ (colMat b).det`.

Rewrite using `[Complex.star_def, norm_mul, norm_mul, Complex.norm_conj]`. Rewrite using `[show (starRingEnd ℂ) z * (x : ℂ) * z = (x : ℂ) * ((starRingEnd ℂ) z * z) by ring, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]`. Rewrite using `[hxn]`. Expand and normalize the polynomial expressions, which then agree.
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
Unfold `latDeg`. Rewrite using `[Finset.sum_congr rfl fun σ _ => by rw [gram_det_majorant S M hG σ b], sum_log_norm_emb]`. Establish `h1` using `hS K r S L b hL hSD hb`. Establish `hone : 1 ≤ (spanIdx L b : ℝ)` using `Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 (spanIdx_ne_zero L b hL.1 hb))`. Establish `hlog1` using `Real.log_nonneg hone`.

Distinguish the cases in `hN0 : |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)| = 0`. Rewrite using `[hN0, Real.log_zero]`. Unfold `spanIdx at hlog1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `Real.log_le_log (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hN0)) h1`.

Rewrite `h2` using `[Real.log_pow]`. Unfold `spanIdx at h2`. Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion.
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
Apply the tactic sequence `first | exact Bl.general_b_fact_second_alt.goal1 .. | (apply Bl.general_b_fact_second_alt.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_alt.goal1 <;> assumption)`.
-/
theorem clear_denom {K : Type} [Field K] [NumberField K] {r : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (v : Fin r → K)
    (hv : v ∈ Submodule.span K (L : Set (Fin r → K))) : ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ L := by
  first | exact Bl.general_b_fact_second_alt.goal1 .. | (apply Bl.general_b_fact_second_alt.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_alt.goal1 <;> assumption)

/- English proof (translation)
Establish `hspan : Submodule.span K (Set.range b) = ⊤`. Rewrite using `[eq_top_iff, ← hL.2, Submodule.span_le]`. Introduce `x hx`. Conclude with `hb.2.2 x hx`. Establish `h` using `finrank_span_eq_card hb.2.1`.

Rewrite `h` using `[hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_fin]`. Conclude with `h.symm`.
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
Introduce `i h1 h2 hg`. Establish `ht` using `haniso (Pi.single i 1) (fun j hj => by`. Establish `: j ≠ i` using `fun e => by rw [e] at hj; omega`. Simplify using `[this]) (by`. Rewrite using `[Finset.sum_eq_single i]`.

Simplify using `[hg]`. Introduce `j _ hj`. Simplify using `[hj]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h)`.

Use `congr_fun ht i` as an intermediate fact. Simplify using `at this`.
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
Introduce `K _ _ r S L hL hSD`. Establish `hG` using `detG_ne_zero S L hL hSD`. Take `⟨P, m, g, hP, h2m, hJ, haniso⟩` from `hW K r S hG`. Establish `hPu : IsUnit P.det` using `isUnit_iff_ne_zero.2 hP`. Use `set Q := P⁻¹ with hQdef`.

Establish `hQ : Q.det ≠ 0`. Rewrite using `[hQdef, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Conclude with `inv_ne_zero hP`. Use `set Lp := L.map (matLin Q) with hLpdef`. Establish `hLp : Lp.FG` using `hL.1.map _`.

Establish `hfix` using `g_fix S P m g hJ`. Establish `hg0` using `g_ne_zero S m g haniso`. Establish `hsp : ∀ v : Fin r → K, ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Lp`. Introduce `v`. Take `⟨a, ha, hav⟩` from `clear_denom L (P *ᵥ v) (by rw [hL.2]; exact Submodule.mem_top)`.

Use `⟨a, ha, ⟨a • (P *ᵥ v), hav, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_smul, matLin_apply, Matrix.mulVec_mulVec, hQdef, Matrix.nonsing_inv_mul P hPu, Matrix.one_mulVec]`. Establish `hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y)`. Introduce and unpack `_ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩`. Rewrite using `[← hJ, formM_change, matLin_apply, matLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQdef, Matrix.mul_nonsing_inv P hPu, Matrix.one_mulVec, Matrix.one_mulVec]`.

Conclude with `hSD.1 x hx y hy`. Take `⟨dd, hdd, hsemi⟩` from `adapted_semistable hB hN hA hE S m g h2m hfix hg0 haniso Lp hLp hsp hint`. Take `⟨M, hM⟩` from `exists_adapted_majorant S P m g dd hP h2m hJ hdd hg0`. Establish `hHeq : M.H = fun σ : K →+* ℂ => (Q.map σ)ᴴ * diagMet (adMet r m g dd) σ * Q.map σ`. Use function extensionality and compare the values at `hM`.

Establish `hsemiL : ∀ B : Submodule (𝓞 K) (Fin r → K), B ≤ L → ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b → latDeg M.H B b ≤ 0`. Introduce `B hB k b hb`. Rewrite using `[hHeq, latDeg_transport _ Q hQ B b]`. Conclude with `hsemi _ (Submodule.map_mono hB) k _ (kBasisIn_map Q hQ B b hb)`. Use `⟨M, ?_, hsemiL⟩` and prove the remaining obligations.

Introduce `k b hb`. Take `rfl : k = r` from `kBasis_card L hL b hb`. Conclude with `le_antisymm (hsemiL L le_rfl k b hb) (latDeg_L_nonneg hS S M L hL hSD hG b hb)`.
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
