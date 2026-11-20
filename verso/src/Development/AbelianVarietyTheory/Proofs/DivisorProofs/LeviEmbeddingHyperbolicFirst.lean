import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.FrameInv

open Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, form, dotProduct, mulVec, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem gram_entry (σ : E →ₐ[F] E) {N : ℕ} {ι₁ ι₂ : Type*} (J : Matrix (Fin N) (Fin N) E) (A : Matrix (Fin N) ι₁ E)
    (B : Matrix (Fin N) ι₂ E) (i : ι₁) (j : ι₂) :
    (Aᵀ * J * B.map σ) i j = form σ J (fun r => A r i) (fun r => B r j) := by
  simp only [Matrix.mul_apply, form, dotProduct, mulVec, transpose_apply, map_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Simplify using `only [form, dotProduct, mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hsk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {N : ℕ} {J : Matrix (Fin N) (Fin N) E}
    (hsk : ∀ i j, σ (J j i) = -J i j) (a b : Fin N → E) :
    form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsk]; ring

def idx (n₁ : ℕ) : Fin (1 + n₁ + 1) → Fin n₁ ⊕ Fin 2 :=
  Fin.addCases (Fin.addCases (fun _ => Sum.inr 0) fun k => Sum.inl k) fun _ => Sum.inr 1

/- English proof (translation)
Proceed by induction on `i using Fin.addCases with`. Consider the case `left i`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left a`. Proceed by induction on `j using Fin.addCases with`.

Consider the case `left j`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left b => simp [idx, one_apply, Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]`. Consider the case `right k => simp [idx, one_apply, Fin.ext_iff] <;> omega`. Consider the case `right b => simp [idx, one_apply, Fin.ext_iff] <;> omega`.

Consider the case `right k`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left j`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left b => simp [idx, one_apply, Fin.ext_iff] <;> omega`.

Consider the case `right l => simp [idx, one_apply, Fin.ext_iff]`. Consider the case `right b => simp [idx, one_apply, Fin.ext_iff] <;> omega`. Consider the case `right a`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left j`.

Proceed by induction on `j using Fin.addCases with`. Consider the case `left b => simp [idx, one_apply, Fin.ext_iff] <;> omega`. Consider the case `right l => simp [idx, one_apply, Fin.ext_iff] <;> omega`. Consider the case `right b => simp [idx, one_apply, Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]`.
-/
theorem one_idx {n₁ : ℕ} (i j : Fin (1 + n₁ + 1)) :
    (1 : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E) (idx n₁ i) (idx n₁ j) = (1 : Matrix _ _ E) i j := by
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left j =>
        induction j using Fin.addCases with
        | left b => simp [idx, one_apply, Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
        | right k => simp [idx, one_apply, Fin.ext_iff] <;> omega
      | right b => simp [idx, one_apply, Fin.ext_iff] <;> omega
    | right k =>
      induction j using Fin.addCases with
      | left j =>
        induction j using Fin.addCases with
        | left b => simp [idx, one_apply, Fin.ext_iff] <;> omega
        | right l => simp [idx, one_apply, Fin.ext_iff]
      | right b => simp [idx, one_apply, Fin.ext_iff] <;> omega
  | right a =>
    induction j using Fin.addCases with
    | left j =>
      induction j using Fin.addCases with
      | left b => simp [idx, one_apply, Fin.ext_iff] <;> omega
      | right l => simp [idx, one_apply, Fin.ext_iff] <;> omega
    | right b => simp [idx, one_apply, Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]

variable [NumberField F] [NumberField E]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm n n₁ Y Y₁ H hsk hn hxx hyy hxy horth hgram hdet`. Establish `hσ : ∀ e, σ (σ e) = e` using `GlobalTheory.SiegelSet.sigma_sigma hcm`. Substitute `hn` using the available equality. Use `set XY : Matrix (Fin (n₁ + 2)) (Fin 2) E := Matrix.of fun r t => ![H.x, H.y] t r with hXY`. Use `set Q : Matrix (Fin (n₁ + 2)) (Fin n₁ ⊕ Fin 2) E := fromCols H.ι XY with hQ`.

Use `set S₂ : Matrix (Fin 2) (Fin 2) E := !![0, 1; -1, 0] with hS₂`. Establish `hyx : form σ Y.J H.y H.x = -1` using `by rw [form_swap hσ hsk, hxy, map_one]`. Establish `horth' : ∀ i, form σ Y.J (fun r => H.ι r i) H.x = 0 ∧ form σ Y.J (fun r => H.ι r i) H.y = 0`. Introduce `i`. Establish `e : (fun r => H.ι r i) = H.ι *ᵥ Pi.single i 1`.

Use function extensionality and compare the values at `r`. Simplify using `[mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[e]`. Conclude with `horth _`. Establish `hK : Qᵀ * Y.J * Q.map σ = fromBlocks Y₁.J 0 0 S₂`.

Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`. Rewrite using `[fromBlocks_apply₁₁, ← hgram, gram_entry, gram_entry]`. Both sides reduce to the same expression. Rewrite using `[fromBlocks_apply₁₂, gram_entry] fin_cases j`.

Simplify `(horth' i).1` using `[Q, XY]`. Simplify `(horth' i).2` using `[Q, XY]`. Rewrite using `[fromBlocks_apply₂₁, gram_entry, form_swap hσ hsk] fin_cases i`. Simplify using `[Q, XY, (horth' j).1]`. Simplify using `[Q, XY, (horth' j).2]`.

Apply the tactic sequence `rw [fromBlocks_apply₂₂, gram_entry] fin_cases i <;> fin_cases j <;> simp [Q, XY, S₂, hxx, hyy, hxy, hyx]`. Establish `hdetK : (fromBlocks Y₁.J 0 0 S₂).det ≠ 0`. Rewrite using `[det_fromBlocks_zero₂₁]`. Simplify using `[S₂, Matrix.det_fin_two_of, hdet]`. Establish `hKu : IsUnit (fromBlocks Y₁.J 0 0 S₂).det` using `isUnit_iff_ne_zero.2 hdetK`.

Use `set R' : Matrix (Fin n₁ ⊕ Fin 2) (Fin (n₁ + 2)) E := ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J).map σ with hR'`. Establish `h0 : (fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ = 1`. Establish `: (fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ = (fromBlocks Y₁.J 0 0 S₂)⁻¹ * (Qᵀ * Y.J * Q.map σ)`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[this, hK, nonsing_inv_mul _ hKu]`.

Establish `hQQ : (Q.map σ).map (σ : E →+* E) = Q` using `by ext i j; simp [hσ]`. Establish `hRQ : R' * Q = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hQQ]`. Both sides reduce to the same expression.

Use `_ = ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ).map (σ : E →+* E) := Matrix.map_mul.symm`. Use `_ = 1 := by rw [h0]; exact Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hfr : ∀ r c, frame H r c = Q r (idx n₁ c)`. Introduce `r c`. Proceed by induction on `c using Fin.addCases with`.

Consider the case `left c`. Proceed by induction on `c using Fin.addCases with`. Consider the case `left a => simp [frame, idx, Q, XY]`. Consider the case `right k => simp [frame, idx, Q, XY]`. Consider the case `right a => simp [frame, idx, Q, XY]`.

Use `⟨Matrix.of fun i r => R' (idx n₁ i) r, ?_, ?_⟩` and prove the remaining obligations. Use `(mul_eq_one_comm_of_card_eq (Fin (n₁ + 2)) (Fin (1 + n₁ + 1)) E (by simp; omega)).2 ?_` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [mul_apply, of_apply, hfr]`. Rewrite using `[← one_idx (E := E) i j, ← hRQ, mul_apply]`.

Use extensionality with `i j`. Simplify using `only [mul_apply, of_apply, hfr]`. Rewrite using `[← one_idx (E := E) i j, ← hRQ, mul_apply]`.
-/
theorem frame_invertible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y₁.J.det ≠ 0 →
    ∃ R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E, frame H * R = 1 ∧ R * frame H = 1 := by
  intro F E _ _ _ _ _ σ hcm n n₁ Y Y₁ H hsk hn hxx hyy hxy horth hgram hdet
  have hσ : ∀ e, σ (σ e) = e := GlobalTheory.SiegelSet.sigma_sigma hcm
  subst hn
  set XY : Matrix (Fin (n₁ + 2)) (Fin 2) E := Matrix.of fun r t => ![H.x, H.y] t r with hXY
  set Q : Matrix (Fin (n₁ + 2)) (Fin n₁ ⊕ Fin 2) E := fromCols H.ι XY with hQ
  set S₂ : Matrix (Fin 2) (Fin 2) E := !![0, 1; -1, 0] with hS₂
  have hyx : form σ Y.J H.y H.x = -1 := by rw [form_swap hσ hsk, hxy, map_one]
  have horth' : ∀ i, form σ Y.J (fun r => H.ι r i) H.x = 0 ∧ form σ Y.J (fun r => H.ι r i) H.y = 0 := by
    intro i
    have e : (fun r => H.ι r i) = H.ι *ᵥ Pi.single i 1 := by
      funext r; simp [mulVec, dotProduct, Pi.single_apply]
    rw [e]; exact horth _
  have hK : Qᵀ * Y.J * Q.map σ = fromBlocks Y₁.J 0 0 S₂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [fromBlocks_apply₁₁, ← hgram, gram_entry, gram_entry]; rfl
    · rw [fromBlocks_apply₁₂, gram_entry]
      fin_cases j
      · simpa [Q, XY] using (horth' i).1
      · simpa [Q, XY] using (horth' i).2
    · rw [fromBlocks_apply₂₁, gram_entry, form_swap hσ hsk]
      fin_cases i
      · simp [Q, XY, (horth' j).1]
      · simp [Q, XY, (horth' j).2]
    · rw [fromBlocks_apply₂₂, gram_entry]
      fin_cases i <;> fin_cases j <;> simp [Q, XY, S₂, hxx, hyy, hxy, hyx]
  have hdetK : (fromBlocks Y₁.J 0 0 S₂).det ≠ 0 := by
    rw [det_fromBlocks_zero₂₁]; simp [S₂, Matrix.det_fin_two_of, hdet]
  have hKu : IsUnit (fromBlocks Y₁.J 0 0 S₂).det := isUnit_iff_ne_zero.2 hdetK
  set R' : Matrix (Fin n₁ ⊕ Fin 2) (Fin (n₁ + 2)) E := ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J).map σ with hR'
  have h0 : (fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ = 1 := by
    have : (fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ = (fromBlocks Y₁.J 0 0 S₂)⁻¹ * (Qᵀ * Y.J * Q.map σ) := by
      simp only [Matrix.mul_assoc]
    rw [this, hK, nonsing_inv_mul _ hKu]
  have hQQ : (Q.map σ).map (σ : E →+* E) = Q := by ext i j; simp [hσ]
  have hRQ : R' * Q = 1 := by
    calc R' * Q = ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J).map (σ : E →+* E) * (Q.map σ).map (σ : E →+* E) := by
          rw [hQQ]; rfl
      _ = ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ).map (σ : E →+* E) := Matrix.map_mul.symm
      _ = 1 := by rw [h0]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hfr : ∀ r c, frame H r c = Q r (idx n₁ c) := by
    intro r c
    induction c using Fin.addCases with
    | left c =>
      induction c using Fin.addCases with
      | left a => simp [frame, idx, Q, XY]
      | right k => simp [frame, idx, Q, XY]
    | right a => simp [frame, idx, Q, XY]
  refine ⟨Matrix.of fun i r => R' (idx n₁ i) r, ?_, ?_⟩
  · refine (mul_eq_one_comm_of_card_eq (Fin (n₁ + 2)) (Fin (1 + n₁ + 1)) E (by simp; omega)).2 ?_
    ext i j
    simp only [mul_apply, of_apply, hfr]
    rw [← one_idx (E := E) i j, ← hRQ, mul_apply]
  · ext i j
    simp only [mul_apply, of_apply, hfr]
    rw [← one_idx (E := E) i j, ← hRQ, mul_apply]

end GlobalTheory.LeviHC.FrameInv

end
