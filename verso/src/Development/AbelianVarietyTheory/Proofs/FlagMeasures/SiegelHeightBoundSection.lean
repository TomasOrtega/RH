import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedDualVectorPairingBoundedMajorantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.SecBound

variable {k r : ℕ}

def midVec (k r : ℕ) (w : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if h : r ≤ i.val ∧ i.val ≤ r + k then w ⟨i.val - r, by omega⟩ else 0

/- English proof (translation)
Introduce `a b h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [wI] at this`. Conclude with `Fin.ext (by omega)`.
-/
theorem wI_inj : Function.Injective (wI k r) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [wI] at this
  exact Fin.ext (by omega)

/- English proof (translation)
Establish `hj` using `j.isLt`. Unfold `midVec`. Rewrite using `[dif_pos (by simp only [wI]; omega)]`. Use `congr 1`. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `[wI]`.
-/
theorem midVec_wI (w : Fin (k + 1) → ℂ) (j : Fin (k + 1)) : midVec k r w (wI k r j) = w j := by
  have hj := j.isLt
  unfold midVec
  rw [dif_pos (by simp only [wI]; omega)]
  congr 1
  apply Fin.ext; simp [wI]

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨i.val - r, by omega⟩, Fin.ext (by simp only [wI]; omega)⟩`.
-/
theorem mem_range_wI {i : Fin (2 * r + k + 1)} (h : r ≤ i.val ∧ i.val ≤ r + k) : i ∈ Set.range (wI k r) :=
  ⟨⟨i.val - r, by omega⟩, Fin.ext (by simp only [wI]; omega)⟩

/- English proof (translation)
Unfold `midVec`. Rewrite using `[dif_neg fun h' => h (mem_range_wI h')]`.
-/
theorem midVec_out (w : Fin (k + 1) → ℂ) {i : Fin (2 * r + k + 1)} (h : i ∉ Set.range (wI k r)) :
    midVec k r w i = 0 := by
  unfold midVec
  rw [dif_neg fun h' => h (mem_range_wI h')]

/- English proof (translation)
Introduce `i hi`. Unfold `midVec`. Rewrite using `[dif_neg (by omega)]`.
-/
theorem midVec_inWb (w : Fin (k + 1) → ℂ) : inWb k r (midVec k r w) := by
  intro i hi
  unfold midVec
  rw [dif_neg (by omega)]

/- English proof (translation)
Use extensionality with `i`. Distinguish the cases in `h : i ∈ Set.range (wI k r)`. Take `⟨j, rfl⟩` from `h`. Rewrite using `[midVec_wI]`. Simplify using `[bvec, Pi.single_apply, wI_inj.eq_iff]`.

Rewrite using `[midVec_out w h]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, bvec]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.single_eq_of_ne (fun e => h ⟨j, e.symm⟩), smul_zero]`.
-/
theorem sum_wI (w : Fin (k + 1) → ℂ) : ∑ j, w j • bvec (wI k r j) = midVec k r w := by
  ext i
  by_cases h : i ∈ Set.range (wI k r)
  · obtain ⟨j, rfl⟩ := h
    rw [midVec_wI]
    simp [bvec, Pi.single_apply, wI_inj.eq_iff]
  · rw [midVec_out w h]
    simp only [Finset.sum_apply, Pi.smul_apply, bvec]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Pi.single_eq_of_ne (fun e => h ⟨j, e.symm⟩), smul_zero]

/- English proof (translation)
Unfold `eucl`. Use `congr 1`. Use `symm`. Use `Fintype.sum_of_injective (wI k r) wI_inj _ _ (fun i hi => ?_) (fun j => ?_)` and prove the remaining obligations. Simplify using `[midVec_out w hi]`.

Rewrite using `[midVec_wI]`.
-/
theorem eucl_midVec (w : Fin (k + 1) → ℂ) : eucl (midVec k r w) = eucl w := by
  unfold eucl
  congr 1
  symm
  refine Fintype.sum_of_injective (wI k r) wI_inj _ _ (fun i hi => ?_) (fun j => ?_)
  · simp [midVec_out w hi]
  · rw [midVec_wI]

/- English proof (translation)
Use extensionality with `i`. Establish `h1 : (mEmb k r m *ᵥ midVec k r w) i = ∑ j, mEmb k r m i (wI k r j) * w j`. Use `symm`. Use `Fintype.sum_of_injective (wI k r) wI_inj _ _ (fun i hi => ?_) (fun j => ?_)` and prove the remaining obligations. Simplify using `[midVec_out w hi]`.

Simplify using `only [midVec_wI]`. Rewrite using `[h1]`. Distinguish the cases in `h : i ∈ Set.range (wI k r)`. Take `⟨l, rfl⟩` from `h`. Rewrite using `[midVec_wI]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hj` using `j.isLt`. Establish `hl` using `l.isLt`. Unfold `mEmb`. Rewrite using `[dif_pos (by simp only [wI]; omega)]`.

Apply the tactic sequence `congr 2 <;> (apply Fin.ext; simp [wI])`. Rewrite using `[midVec_out _ h]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Unfold `mEmb`. Rewrite using `[dif_neg (fun h' => h (mem_range_wI h'.1)), if_neg (fun e => h ⟨j, e.symm⟩), zero_mul]`.
-/
theorem mEmb_midVec (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (w : Fin (k + 1) → ℂ) :
    mEmb k r m *ᵥ midVec k r w = midVec k r (m *ᵥ w) := by
  ext i
  have h1 : (mEmb k r m *ᵥ midVec k r w) i = ∑ j, mEmb k r m i (wI k r j) * w j := by
    symm
    refine Fintype.sum_of_injective (wI k r) wI_inj _ _ (fun i hi => ?_) (fun j => ?_)
    · simp [midVec_out w hi]
    · simp only [midVec_wI]
  rw [h1]
  by_cases h : i ∈ Set.range (wI k r)
  · obtain ⟨l, rfl⟩ := h
    rw [midVec_wI]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj := j.isLt
    have hl := l.isLt
    unfold mEmb
    rw [dif_pos (by simp only [wI]; omega)]
    congr 2 <;> (apply Fin.ext; simp [wI])
  · rw [midVec_out _ h]
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold mEmb
    rw [dif_neg (fun h' => h (mem_range_wI h'.1)), if_neg (fun e => h ⟨j, e.symm⟩), zero_mul]

/- English proof (translation)
Use extensionality with `l`. Simplify using `only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]`. Unfold `mEmb`. Rewrite using `[dif_neg (by omega)]`.
-/
theorem mEmb_bvec (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i : Fin (2 * r + k + 1)}
    (hi : i.val < r ∨ r + k < i.val) : mEmb k r m *ᵥ bvec i = bvec i := by
  ext l
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]
  unfold mEmb
  rw [dif_neg (by omega)]

/- English proof (translation)
Unfold `eucl`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[bvec, Complex.normSq_eq_norm_sq]`. Introduce `b _ hb`. Simplify using `[bvec, Pi.single_eq_of_ne hb]`.

Simplify using the standard rewrite rules.
-/
theorem eucl_smul_bvec {n : ℕ} (c : ℂ) (i : Fin n) : eucl (c • bvec i) = ‖c‖ := by
  unfold eucl
  rw [Finset.sum_eq_single i]
  · simp [bvec, Complex.normSq_eq_norm_sq]
  · intro b _ hb; simp [bvec, Pi.single_eq_of_ne hb]
  · simp

/- English proof (translation)
Establish `: star (bvec i) = Pi.single i (1 : ℂ)`. Use extensionality with `l`. Simplify using `[bvec, Pi.single_apply]`. Unfold `herm`. Rewrite using `[this, single_one_dotProduct]`.

Both sides reduce to the same expression.
-/
theorem herm_bvec {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (i : Fin n) :
    herm G v (bvec i) = ∑ l, G i l * v l := by
  have : star (bvec i) = Pi.single i (1 : ℂ) := by
    ext l; simp [bvec, Pi.single_apply]
  unfold herm
  rw [this, single_one_dotProduct]; rfl

/- English proof (translation)
Establish `ha` using `a.isLt`. Rewrite using `[herm_bvec, Finset.sum_eq_single (esI k r a)]`. Unfold `Hpk`. Rewrite using `[if_pos (by simp only [eI, esI]; omega), one_mul]`. Introduce `b _ hb`.

Establish `hb' : b.val ≠ 2 * r + k - a.val` using `fun e => hb (Fin.ext e)`. Unfold `Hpk`. Rewrite using `[if_neg (by simp only [eI]; omega), if_neg (by simp only [eI]; omega), if_neg (by simp only [eI]; omega), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem herm_eI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  have ha := a.isLt
  rw [herm_bvec, Finset.sum_eq_single (esI k r a)]
  · unfold Hpk
    rw [if_pos (by simp only [eI, esI]; omega), one_mul]
  · intro b _ hb
    have hb' : b.val ≠ 2 * r + k - a.val := fun e => hb (Fin.ext e)
    unfold Hpk
    rw [if_neg (by simp only [eI]; omega), if_neg (by simp only [eI]; omega),
      if_neg (by simp only [eI]; omega), zero_mul]
  · simp

/- English proof (translation)
Establish `ha` using `a.isLt`. Rewrite using `[herm_bvec, Finset.sum_eq_single (eI k r a)]`. Unfold `Hpk`. Rewrite using `[if_neg (by simp only [eI, esI]; omega), if_pos (by simp only [eI, esI]; omega), one_mul]`. Introduce `b _ hb`.

Establish `hb' : b.val ≠ a.val` using `fun e => hb (Fin.ext e)`. Unfold `Hpk`. Rewrite using `[if_neg (by simp only [esI]; omega), if_neg (by simp only [esI]; omega), if_neg (by simp only [esI]; omega), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem herm_esI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (esI k r a)) = v (eI k r a) := by
  have ha := a.isLt
  rw [herm_bvec, Finset.sum_eq_single (eI k r a)]
  · unfold Hpk
    rw [if_neg (by simp only [eI, esI]; omega), if_pos (by simp only [eI, esI]; omega), one_mul]
  · intro b _ hb
    have hb' : b.val ≠ a.val := fun e => hb (Fin.ext e)
    unfold Hpk
    rw [if_neg (by simp only [esI]; omega), if_neg (by simp only [esI]; omega),
      if_neg (by simp only [esI]; omega), zero_mul]
  · simp

/- English proof (translation)
Establish `hj` using `j.isLt`. Unfold `Hb`. Rewrite using `[Matrix.mulVec_diagonal]`. Use `show ∑ l, Hpk k r (wI k r j) l * v l = _`. Rewrite using `[Finset.sum_eq_single (wI k r j)]`.

Unfold `Hpk`. Rewrite using `[if_neg (by simp only [wI]; omega), if_neg (by simp only [wI]; omega), if_pos ⟨by simp only [wI]; omega, by simp only [wI]; omega, rfl⟩]`. Use `congr 1`. Simplify using `[wI, Fin.ext_iff]`. Introduce `b _ hb`.

Unfold `Hpk`. Rewrite using `[if_neg (by simp only [wI]; omega), if_neg (by simp only [wI]; omega), if_neg (fun h => hb h.2.2.symm), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem Hpk_mulVec_wI (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (k + 1)) :
    (Hpk k r *ᵥ v) (wI k r j) = (Hb k *ᵥ fun l => v (wI k r l)) j := by
  have hj := j.isLt
  unfold Hb
  rw [Matrix.mulVec_diagonal]
  show ∑ l, Hpk k r (wI k r j) l * v l = _
  rw [Finset.sum_eq_single (wI k r j)]
  · unfold Hpk
    rw [if_neg (by simp only [wI]; omega), if_neg (by simp only [wI]; omega),
      if_pos ⟨by simp only [wI]; omega, by simp only [wI]; omega, rfl⟩]
    congr 1
    simp [wI, Fin.ext_iff]
  · intro b _ hb
    unfold Hpk
    rw [if_neg (by simp only [wI]; omega), if_neg (by simp only [wI]; omega),
      if_neg (fun h => hb h.2.2.symm), zero_mul]
  · simp

/- English proof (translation)
Unfold `herm dotProduct`. Use `symm`. Use `Fintype.sum_of_injective (wI k r) wI_inj _ _ (fun i hi => ?_) (fun j => ?_)` and prove the remaining obligations. Simplify using `[midVec_out w hi]`. Simplify using `only [Pi.star_apply, midVec_wI, Hpk_mulVec_wI]`.
-/
theorem herm_midVec (v : Fin (2 * r + k + 1) → ℂ) (w : Fin (k + 1) → ℂ) :
    herm (Hpk k r) v (midVec k r w) = herm (Hb k) (fun l => v (wI k r l)) w := by
  unfold herm dotProduct
  symm
  refine Fintype.sum_of_injective (wI k r) wI_inj _ _ (fun i hi => ?_) (fun j => ?_)
  · simp [midVec_out w hi]
  · simp only [Pi.star_apply, midVec_wI, Hpk_mulVec_wI]

/- English proof (translation)
Establish `h : mᴴ * G * m = G` using `hm`. Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]`.
-/
theorem herm_UH {n : ℕ} {G m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ UH G) (v w : Fin n → ℂ) :
    herm G (m *ᵥ v) (m *ᵥ w) = herm G v w := by
  have h : mᴴ * G * m = G := hm
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

/- English proof (translation)
Establish `h1 : gᴴ * G * g = G` using `hg`. Establish `h2 : hᴴ * G * h = G` using `hh`. Use `show (g * h)ᴴ * G * (g * h) = G`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UH_mul {n : ℕ} {G g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH G) (hh : h ∈ UH G) : g * h ∈ UH G := by
  have h1 : gᴴ * G * g = G := hg
  have h2 : hᴴ * G * h = G := hh
  show (g * h)ᴴ * G * (g * h) = G
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * G * (g * h) = hᴴ * (gᴴ * G * g) * h := by simp only [Matrix.mul_assoc]
    _ = G := by rw [h1, h2]

/- English proof (translation)
Establish `h : mᴴ * Hb k * m = Hb k` using `hm`. Establish `h2` using `congrArg Matrix.det h`. Rewrite `h2` using `[Matrix.det_mul]`. Establish `h3 : (Hb k).det ≠ 0`. Unfold `Hb`.

Rewrite using `[Matrix.det_diagonal]`. Use `Finset.prod_ne_zero_iff.2 fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Use `isUnit_iff_ne_zero.2 fun e => h3 ?_` and prove the remaining obligations. Rewrite using `[← h2, e, mul_zero]`.
-/
theorem isUnit_det_of_UH {m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hm : m ∈ UH (Hb k)) : IsUnit m.det := by
  have h : mᴴ * Hb k * m = Hb k := hm
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul] at h2
  have h3 : (Hb k).det ≠ 0 := by
    unfold Hb
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    split_ifs <;> simp
  refine isUnit_iff_ne_zero.2 fun e => h3 ?_
  rw [← h2, e, mul_zero]

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq]`. Simplify using `[eucl, Complex.normSq_eq_norm_sq]`.
-/
theorem eucl_eq_norm {n : ℕ} (v : Fin n → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [eucl, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Unfold `eucl Hb`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_diagonal]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem eucl_Hb (v : Fin (k + 1) → ℂ) : eucl (Hb k *ᵥ v) = eucl v := by
  unfold eucl Hb
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_diagonal]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← eucl_Hb v, eucl_eq_norm, eucl_eq_norm, mul_comm]`. Use `le_trans (le_of_eq ?_) (norm_inner_le_norm (𝕜 := ℂ) _ _)` and prove the remaining obligations. Rewrite using `[EuclideanSpace.inner_toLp_toLp, dotProduct_comm]`. Both sides reduce to the same expression.
-/
theorem norm_herm_Hb_le (v w : Fin (k + 1) → ℂ) : ‖herm (Hb k) v w‖ ≤ eucl v * eucl w := by
  rw [← eucl_Hb v, eucl_eq_norm, eucl_eq_norm, mul_comm]
  refine le_trans (le_of_eq ?_) (norm_inner_le_norm (𝕜 := ℂ) _ _)
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]; rfl

/- English proof (translation)
Rewrite using `[← eucl_Hb v, eucl, Real.sq_sqrt (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)]`. Unfold `herm dotProduct`. Use `push_cast`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_eq_conj_mul_self]`.

Both sides reduce to the same expression.
-/
theorem herm_Hb_self (v : Fin (k + 1) → ℂ) : herm (Hb k) v (Hb k *ᵥ v) = ((eucl v ^ 2 : ℝ) : ℂ) := by
  rw [← eucl_Hb v, eucl, Real.sq_sqrt (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)]
  unfold herm dotProduct
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]; rfl

/- English proof (translation)
Establish `h0 : 0 ≤ eucl v` using `Real.sqrt_nonneg _`. Break down `h0.eq_or_lt with e | hpos` into its components or cases. Rewrite using `[← e]`. Conclude with `hM`. Establish `h1` using `h ((((eucl v)⁻¹ : ℝ) : ℂ) • (Hb k *ᵥ v)) (by`.

Rewrite using `[eucl_eq_norm, WithLp.toLp_smul, norm_smul, ← eucl_eq_norm, eucl_Hb, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 h0), inv_mul_cancel₀ hpos.ne'])`. Establish `h2 : herm (Hb k) v ((((eucl v)⁻¹ : ℝ) : ℂ) • (Hb k *ᵥ v)) = ((eucl v : ℝ) : ℂ)`. Use `herm_Hb_self v` as an intermediate fact. Unfold `herm at this ⊢`. Rewrite using `[star_smul, smul_dotProduct, this, Complex.star_def, Complex.conj_ofReal, smul_eq_mul, ← Complex.ofReal_mul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite `h1` using `[h2, Complex.norm_real, Real.norm_of_nonneg h0]`. Then use the resulting hypothesis.
-/
theorem eucl_le_of_herm (v : Fin (k + 1) → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ w, eucl w ≤ 1 → ‖herm (Hb k) v w‖ ≤ M) : eucl v ≤ M := by
  have h0 : 0 ≤ eucl v := Real.sqrt_nonneg _
  rcases h0.eq_or_lt with e | hpos
  · rw [← e]; exact hM
  have h1 := h ((((eucl v)⁻¹ : ℝ) : ℂ) • (Hb k *ᵥ v)) (by
    rw [eucl_eq_norm, WithLp.toLp_smul, norm_smul, ← eucl_eq_norm, eucl_Hb, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.2 h0), inv_mul_cancel₀ hpos.ne'])
  have h2 : herm (Hb k) v ((((eucl v)⁻¹ : ℝ) : ℂ) • (Hb k *ᵥ v)) = ((eucl v : ℝ) : ℂ) := by
    have := herm_Hb_self v
    unfold herm at this ⊢
    rw [star_smul, smul_dotProduct, this, Complex.star_def, Complex.conj_ofReal, smul_eq_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
  rwa [h2, Complex.norm_real, Real.norm_of_nonneg h0] at h1

/- English proof (translation)
Introduce `_ _ h` and use `Fin.ext (by simpa [eI] using congrArg Fin.val h)`.
-/
theorem eI_inj : Function.Injective (eI k r) := fun _ _ h => Fin.ext (by simpa [eI] using congrArg Fin.val h)

/- English proof (translation)
Introduce `a b h`. Use `congrArg Fin.val h` as an intermediate fact. Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Simplify using `only [esI] at this`.

Conclude with `Fin.ext (by omega)`.
-/
theorem esI_inj : Function.Injective (esI k r) := by
  intro a b h
  have := congrArg Fin.val h
  have ha := a.isLt
  have hb := b.isLt
  simp only [esI] at this
  exact Fin.ext (by omega)

def xVec (k r : ℕ) (x : Fin r → ℂ) : Fin (2 * r + k + 1) → ℂ := ∑ a, x a • bvec (eI k r a)

def yVec (k r : ℕ) (x : Fin r → ℂ) : Fin (2 * r + k + 1) → ℂ := ∑ a, x a • bvec (esI k r a)

/- English proof (translation)
Simplify using `[xVec, bvec, Pi.single_apply, eI_inj.eq_iff]`.
-/
theorem xVec_eI (x : Fin r → ℂ) (a : Fin r) : xVec k r x (eI k r a) = x a := by
  simp [xVec, bvec, Pi.single_apply, eI_inj.eq_iff]

/- English proof (translation)
Simplify using `[yVec, bvec, Pi.single_apply, esI_inj.eq_iff]`.
-/
theorem yVec_esI (x : Fin r → ℂ) (a : Fin r) : yVec k r x (esI k r a) = x a := by
  simp [yVec, bvec, Pi.single_apply, esI_inj.eq_iff]

/- English proof (translation)
Simplify using `only [xVec, Finset.sum_apply, Pi.smul_apply, bvec]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Establish `ha` using `a.isLt`. Rewrite using `[Pi.single_eq_of_ne (fun e => by have := congrArg Fin.val e; simp only [eI] at this; omega), smul_zero]`.
-/
theorem xVec_out (x : Fin r → ℂ) {i : Fin (2 * r + k + 1)} (hi : r ≤ i.val) : xVec k r x i = 0 := by
  simp only [xVec, Finset.sum_apply, Pi.smul_apply, bvec]
  refine Finset.sum_eq_zero fun a _ => ?_
  have ha := a.isLt
  rw [Pi.single_eq_of_ne (fun e => by have := congrArg Fin.val e; simp only [eI] at this; omega), smul_zero]

/- English proof (translation)
Simplify using `only [yVec, Finset.sum_apply, Pi.smul_apply, bvec]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Establish `ha` using `a.isLt`. Rewrite using `[Pi.single_eq_of_ne (fun e => by have := congrArg Fin.val e; simp only [esI] at this; omega), smul_zero]`.
-/
theorem yVec_out (x : Fin r → ℂ) {i : Fin (2 * r + k + 1)} (hi : i.val ≤ r + k) : yVec k r x i = 0 := by
  simp only [yVec, Finset.sum_apply, Pi.smul_apply, bvec]
  refine Finset.sum_eq_zero fun a _ => ?_
  have ha := a.isLt
  rw [Pi.single_eq_of_ne (fun e => by have := congrArg Fin.val e; simp only [esI] at this; omega), smul_zero]

/- English proof (translation)
Establish `h` using `((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 u hu).2.2.1`. Unfold `xVec`. Rewrite using `[Matrix.mulVec_sum]`. Simplify using `only [Matrix.mulVec_smul, h, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun b _ => mul_comm _ _`.
-/
theorem uEmb_xVec {u : Matrix (Fin r) (Fin r) ℂ} (hu : IsUnit u.det) (x : Fin r → ℂ) :
    uEmb k r u *ᵥ xVec k r x = xVec k r (u *ᵥ x) := by
  have h := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 u hu).2.2.1
  unfold xVec
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/- English proof (translation)
Establish `hu' : IsUnit u⁻¹.det` using `Matrix.isUnit_nonsing_inv_det u hu`. Establish `h1` using `(GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1`. Establish `h2` using `(GlobalTheory.Amp.Rad.radical k r).1`. Rewrite using `[Matrix.mul_inv_rev, (h1 u hu).2.1, ((h2 B S).2.2.2 hS).2, ← Matrix.mulVec_mulVec, (h2 (-B) (-S)).2.2.1, Matrix.mulVec_add, Matrix.mulVec_add, (h1 _ hu').2.2.2.1, sum_wI, (h1 _ hu').2.2.2.2 _ (midVec_inWb _), Matrix.nonsing_inv_nonsing_inv u hu, ← uEmb_xVec hu']`. Use `congr 2`.

Unfold `xVec`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 2`. Simplify using `[herm, Matrix.mulVec_neg]`.
-/
theorem inv_mulVec_esI (B : Fin r → Fin (k + 1) → ℂ) {S u : Matrix (Fin r) (Fin r) ℂ} (hS : Sᴴ = -S)
    (hu : IsUnit u.det) (b : Fin r) :
    (pEl k r B S * uEmb k r u)⁻¹ *ᵥ bvec (esI k r b) =
      yVec k r (fun a => star (u b a)) + midVec k r (-B b) +
        xVec k r (u⁻¹ *ᵥ fun a => -S a b - herm (Hb k) (B b) (B a) / 2) := by
  have hu' : IsUnit u⁻¹.det := Matrix.isUnit_nonsing_inv_det u hu
  have h1 := (GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1
  have h2 := (GlobalTheory.Amp.Rad.radical k r).1
  rw [Matrix.mul_inv_rev, (h1 u hu).2.1, ((h2 B S).2.2.2 hS).2, ← Matrix.mulVec_mulVec, (h2 (-B) (-S)).2.2.1,
    Matrix.mulVec_add, Matrix.mulVec_add, (h1 _ hu').2.2.2.1, sum_wI, (h1 _ hu').2.2.2.2 _ (midVec_inWb _),
    Matrix.nonsing_inv_nonsing_inv u hu, ← uEmb_xVec hu']
  congr 2
  unfold xVec
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  simp [herm, Matrix.mulVec_neg]

/- English proof (translation)
Rewrite using `[Matrix.det_diagonal, isUnit_iff_ne_zero]`. Conclude with `Finset.prod_ne_zero_iff.2 fun b _ => Complex.ofReal_ne_zero.2 (ha b).ne'`.
-/
theorem isUnit_det_diag {a : Fin r → ℝ} (ha : ∀ b, 0 < a b) :
    IsUnit (Matrix.diagonal fun b => (a b : ℂ)).det := by
  rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.2 fun b _ => Complex.ofReal_ne_zero.2 (ha b).ne'

/- English proof (translation)
Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Conclude with `mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (ha b).ne')`.
-/
theorem inv_diag {a : Fin r → ℝ} (ha : ∀ b, 0 < a b) :
    (Matrix.diagonal fun b => (a b : ℂ))⁻¹ = Matrix.diagonal fun b => (a b : ℂ)⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (ha b).ne')

/- English proof (translation)
Establish `hu` using `isUnit_det_diag ha`. Establish `hu'` using `Matrix.isUnit_nonsing_inv_det _ hu`. Establish `h1` using `(GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1`. Establish `h2` using `((GlobalTheory.Amp.Rad.radical k r).2.2.2.2 m hm).2`. Rewrite using `[Matrix.mul_inv_rev, (h1 _ hu).2.1, h2]`.

Use `⟨fun b => ?_, fun b => ?_, fun w => ?_⟩` and prove the remaining obligations. Establish `hb` using `b.isLt`. Rewrite using `[← Matrix.mulVec_mulVec, (h1 _ hu').2.2.1, inv_diag ha, Finset.sum_eq_single b, Matrix.mulVec_smul, mEmb_bvec _ (Or.inl (by simp only [eI]; omega)), eucl_smul_bvec]`. Simplify using `[abs_of_pos (ha b)]`. Introduce `c _ hc`.

Simplify using `[Matrix.diagonal_apply_ne _ hc]`. Simplify using the standard rewrite rules. Establish `hb` using `b.isLt`. Rewrite using `[← Matrix.mulVec_mulVec, (h1 _ hu').2.2.2.1, Matrix.nonsing_inv_nonsing_inv _ hu, Finset.sum_eq_single b, Matrix.mulVec_smul, mEmb_bvec _ (Or.inr (by simp only [esI]; omega)), eucl_smul_bvec]`. Simplify using `[abs_of_pos (ha b)]`.

Introduce `c _ hc`. Simplify using `[Matrix.diagonal_apply_ne _ hc.symm]`. Simplify using the standard rewrite rules. Rewrite using `[← Matrix.mulVec_mulVec, (h1 _ hu').2.2.2.2 _ (midVec_inWb _), mEmb_midVec, eucl_midVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_of_UH hm), Matrix.one_mulVec]`.
-/
theorem eucl_levi {a : Fin r → ℝ} (ha : ∀ b, 0 < a b) {m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hm : m ∈ UH (Hb k)) :
    (∀ b, eucl ((uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ bvec (eI k r b)) = (a b)⁻¹) ∧
    (∀ b, eucl ((uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ bvec (esI k r b)) = a b) ∧
    ∀ w, eucl ((uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ midVec k r (m *ᵥ w)) = eucl w := by
  have hu := isUnit_det_diag ha
  have hu' := Matrix.isUnit_nonsing_inv_det _ hu
  have h1 := (GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1
  have h2 := ((GlobalTheory.Amp.Rad.radical k r).2.2.2.2 m hm).2
  rw [Matrix.mul_inv_rev, (h1 _ hu).2.1, h2]
  refine ⟨fun b => ?_, fun b => ?_, fun w => ?_⟩
  · have hb := b.isLt
    rw [← Matrix.mulVec_mulVec, (h1 _ hu').2.2.1, inv_diag ha, Finset.sum_eq_single b, Matrix.mulVec_smul,
      mEmb_bvec _ (Or.inl (by simp only [eI]; omega)), eucl_smul_bvec]
    · simp [abs_of_pos (ha b)]
    · intro c _ hc; simp [Matrix.diagonal_apply_ne _ hc]
    · simp
  · have hb := b.isLt
    rw [← Matrix.mulVec_mulVec, (h1 _ hu').2.2.2.1, Matrix.nonsing_inv_nonsing_inv _ hu, Finset.sum_eq_single b,
      Matrix.mulVec_smul, mEmb_bvec _ (Or.inr (by simp only [esI]; omega)), eucl_smul_bvec]
    · simp [abs_of_pos (ha b)]
    · intro c _ hc; simp [Matrix.diagonal_apply_ne _ hc.symm]
    · simp
  · rw [← Matrix.mulVec_mulVec, (h1 _ hu').2.2.2.2 _ (midVec_inWb _), mEmb_midVec, eucl_midVec,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_of_UH hm), Matrix.one_mulVec]

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, ⟨by show (1 : Mat k r)ᴴ * _ * 1 = _; simp, fun a => by simp, by simp⟩, n, hn, by simp⟩`.
-/
theorem mem_Sset_of_Nset (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨by show (1 : Mat k r)ᴴ * _ * 1 = _; simp, fun a => by simp, by simp⟩, n, hn, by simp⟩

/- English proof (translation)
Establish `hl` using `GlobalTheory.Amp.LInv.lengths_basic k r z hz`. Establish `hx : uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m ∈ GG k r` using `UH_mul ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 _ (isUnit_det_diag ha)).1 ((GlobalTheory.Amp.Rad.radical k r).2.2.2.2 m hm).1`. Establish `h1 : (1 : Mat k r) ∈ GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))` using `⟨by show (1 : Mat k r)ᴴ * _ * 1 = _; simp, one_mem _⟩`. Establish `e1` using `(hl.1 _ hx n' (mem_Sset_of_Nset z hn') 1 h1).1 b.castSucc`. Establish `e2` using `(hl.1 _ (UH_mul hn'.1 hx) n (mem_Sset_of_Nset z hn) 1 h1).1 b.castSucc`.

Rewrite `e1`, `e2` using `[Matrix.mul_one]`. Establish `e3` using `hl.2.1 a ha m hm b`. Establish `h2` using `((Finset.fold_max_le _).1 h).2 b.castSucc (Finset.mem_univ _)`. Rewrite `h2` using `[Matrix.mul_assoc, e2, e1, e3, inv_inv, max_le_iff]`. Conclude with `h2`.
-/
theorem torus_le {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n n' : Mat k r} (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r)
    {a : Fin r → ℝ} (ha : ∀ b, 0 < a b) {m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hm : m ∈ UH (Hb k)) {R : ℝ}
    (h : Sg2 k r z (n * n' * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R) (b : Fin r) :
    (a b)⁻¹ ≤ R ∧ a b ≤ R := by
  have hl := GlobalTheory.Amp.LInv.lengths_basic k r z hz
  have hx : uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m ∈ GG k r :=
    UH_mul ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 _ (isUnit_det_diag ha)).1 ((GlobalTheory.Amp.Rad.radical k r).2.2.2.2 m hm).1
  have h1 : (1 : Mat k r) ∈ GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r)) :=
    ⟨by show (1 : Mat k r)ᴴ * _ * 1 = _; simp, one_mem _⟩
  have e1 := (hl.1 _ hx n' (mem_Sset_of_Nset z hn') 1 h1).1 b.castSucc
  have e2 := (hl.1 _ (UH_mul hn'.1 hx) n (mem_Sset_of_Nset z hn) 1 h1).1 b.castSucc
  rw [Matrix.mul_one] at e1 e2
  have e3 := hl.2.1 a ha m hm b
  have h2 := ((Finset.fold_max_le _).1 h).2 b.castSucc (Finset.mem_univ _)
  rw [Matrix.mul_assoc, e2, e1, e3, inv_inv, max_le_iff] at h2
  exact h2

/- English proof (translation)
Establish `key` using `GlobalTheory.T.moved_dual_vector_pairing_bounded_majorant k r j hj z z' g₀ β c hz hz' hT hN De R₀ hD hR m hm q a ha h1 h2`. Establish `hM : 1 ≤ R₀ ^ (2 * r) * De` using `one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) hD.1`. Generalize the expression as in `R₀ ^ (2 * r) * De = M at key hM ⊢`. Take `⟨B, hB⟩ : ∃ B : Fin r → Fin (k + 1) → ℂ, B = fun a => if h : a.val < j then q.1.1 ⟨a, h⟩ else 0` from `⟨_, rfl⟩`. Take `⟨S, hSdef⟩ : ∃ S : Matrix (Fin r) (Fin r) ℂ, S = skewM (fun p => if h : p.1.1.val < j then q.1.2.1 ⟨p, h⟩ else 0) (fun a => if h : a.val < j then q.1.2.2 ⟨a, h⟩ else 0)` from `⟨_, rfl⟩`.

Take `⟨u, hudef⟩ : ∃ u : Matrix (Fin r) (Fin r) ℂ, u = upperOff β q.2` from `⟨_, rfl⟩`. Establish `hs : sEl k r j β q = pEl k r B S * uEmb k r u` using `by rw [hB, hSdef, hudef]; rfl`. Establish `hS : Sᴴ = -S` using `hSdef ▸ (GlobalTheory.Amp.Rad.radical k r).2.1 _ _`. Establish `hu1` using `(GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 (fun p => if h : β p.1.1 ≠ β p.1.2 then q.2 ⟨p, h⟩ else 0)`. Establish `hu : IsUnit u.det`.

Rewrite using `[hudef, upperOff, hu1.1]`. Conclude with `isUnit_one`. Establish `huN : uEmb k r u ∈ Nset k r` using `hudef ▸ hu1.2`. Rewrite `key`, `h1` using `[hs]`. Establish `hpN` using `(((GlobalTheory.Amp.Rad.radical k r).1 B S).2.2.2 hS).1`.

Establish `ht` using `torus_le hz' hpN huN ha hm h1`. Establish `hl` using `eucl_levi (k := k) ha hm`. Simplify using `only [inv_mulVec_esI B hS hu] at key`. Establish `hmm : m * m⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (isUnit_det_of_UH hm)`. Establish `k1 : ∀ b : Fin r, b.val < j → ∀ d, ‖u b d‖ ≤ M`.

Introduce `b hb d`. Establish `hd` using `d.isLt`. Use `key b hb _ ((hl.1 d).le.trans (ht d).1)` as an intermediate fact. Rewrite `this` using `[herm_eI, Pi.add_apply, Pi.add_apply, yVec_esI, midVec_inWb _ _ (Or.inr (by simp only [esI]; omega)), xVec_out _ (by simp only [esI]; omega), add_zero, add_zero, norm_star]`. Then use the resulting hypothesis. Establish `c1 : ∀ p, ‖q.2 p‖ ≤ M`.

Introduce `p`. Establish `hlt : p.1.1.1 < p.1.1.2` using `p.1.2`. Establish `hb : p.1.1.1.val < j`. Assume the negation of the conclusion as `hc`. Establish `hlt' : p.1.1.1.val < p.1.1.2.val` using `hlt`.

Conclude with `p.2 ((hN.2.2.2.2.1 _ _ (by omega)).2 (by omega))`. Use `k1 _ hb p.1.1.2` as an intermediate fact. Rewrite `this` using `[hudef, upperOff, upper, dif_pos hlt, dif_pos p.2]`. Conclude with `this`. Establish `k1' : ∀ b d, ‖u b d‖ ≤ M`.

Introduce `b d`. Rewrite using `[hudef, upperOff, upper]`. Use `split_ifs`. Conclude with `c1 _`. Simplify using `using le_trans zero_le_one hM`.

Simplify using `using hM`. Simplify using `using le_trans zero_le_one hM`. Establish `k2 : ∀ b : Fin r, eucl (m⁻¹ *ᵥ B b) ≤ M`. Introduce `b`. Distinguish the cases in `hb : b.val < j`.

Use `eucl_le_of_herm _ (le_trans zero_le_one hM) fun w hw => ?_` and prove the remaining obligations. Use `key b hb _ (((hl.2.2 w).le.trans hw).trans hR)` as an intermediate fact. Rewrite `this` using `[herm_midVec]`. Establish `e : (fun l => (yVec k r (fun a => star (u b a)) + midVec k r (-B b) + xVec k r (u⁻¹ *ᵥ fun a => -S a b - herm (Hb k) (B b) (B a) / 2)) (wI k r l)) = -B b`. Use function extensionality and compare the values at `l`.

Establish `hl'` using `l.isLt`. Rewrite using `[Pi.add_apply, Pi.add_apply, midVec_wI, yVec_out _ (by simp only [wI]; omega), xVec_out _ (by simp only [wI]; omega), zero_add, add_zero]`. Rewrite `this` using `[e]`. Rewrite using `[← herm_UH hm, Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec]`. Simplify `this` using `[herm, Matrix.mulVec_neg]`.

Establish `: B b = 0` using `by rw [hB]; exact dif_neg hb`. Rewrite using `[this]`. Simplify `le_trans zero_le_one hM` using `[eucl]`. Establish `k2' : ∀ b d, ‖herm (Hb k) (B b) (B d)‖ ≤ M ^ 2`. Introduce `b d`.

Establish `e : herm (Hb k) (B b) (B d) = herm (Hb k) (m⁻¹ *ᵥ B b) (m⁻¹ *ᵥ B d)`. Rewrite using `[← herm_UH hm (m⁻¹ *ᵥ B b), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec, Matrix.one_mulVec]`. Rewrite using `[e, sq]`. Conclude with `(norm_herm_Hb_le _ _).trans (mul_le_mul (k2 b) (k2 d) (Real.sqrt_nonneg _) (le_trans zero_le_one hM))`. Establish `k3 : ∀ b : Fin r, b.val < j → ∀ d, ‖S d b‖ ≤ 2 * r * M ^ 2`.

Introduce `b hb d`. Take `⟨x, hx⟩ : ∃ x : Fin r → ℂ, x = fun a => -S a b - herm (Hb k) (B b) (B a) / 2` from `⟨_, rfl⟩`. Establish `hy : ∀ e, ‖(u⁻¹ *ᵥ x) e‖ ≤ M`. Introduce `e`. Establish `he` using `e.isLt`.

Use `key b hb _ ((hl.2.1 e).le.trans (ht e).2)` as an intermediate fact. Rewrite `this` using `[herm_esI, Pi.add_apply, Pi.add_apply, xVec_eI, midVec_inWb _ _ (Or.inl (by simp only [eI]; omega)), yVec_out _ (by simp only [eI]; omega), zero_add, zero_add, ← hx]`. Then use the resulting hypothesis. Establish `hxd : ‖x d‖ ≤ r * M ^ 2`. Establish `e : x d = ∑ e, u d e * (u⁻¹ *ᵥ x) e` using `by conv_lhs => rw [← Matrix.one_mulVec x, ← Matrix.mul_nonsing_inv u hu, ← Matrix.mulVec_mulVec]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, sq]`. Conclude with `mul_le_mul (k1' d e) (hy e) (norm_nonneg _) (le_trans zero_le_one hM)`.

Use `_ = r * M ^ 2 := by simp`. Establish `e : S d b = -(x d + herm (Hb k) (B b) (B d) / 2)` using `by rw [hx]; ring`. Establish `hr : (1 : ℝ) ≤ r` using `by exact_mod_cast (show 1 ≤ r by omega)`. Establish `h3` using `k2' b d`. Establish `h4 : 0 ≤ M ^ 2` using `sq_nonneg _`.

Rewrite using `[e, norm_neg]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_div, Complex.norm_two]`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨c1, fun b => ?_, fun p => ?_, fun b => ?_⟩` and prove the remaining obligations.

Use `k2 b.1` as an intermediate fact. Establish `e : B b.1 = q.1.1 b` using `by rw [hB]; exact dif_pos b.2`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hlt : p.1.1.1 < p.1.1.2` using `p.1.2`. Use `k3 _ p.2 p.1.1.2` as an intermediate fact.

Rewrite `this` using `[hSdef, skewM, dif_neg (not_lt.2 hlt.le), dif_pos hlt, dif_pos p.2, norm_neg, norm_star]`. Conclude with `this`. Use `k3 _ b.2 b.1` as an intermediate fact. Rewrite `this` using `[hSdef, skewM, dif_neg (lt_irrefl _), dif_neg (lt_irrefl _), dif_pos b.2]`. Simplify using `using this`.
-/
theorem section_coord_le (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ)
    (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hN : IsNormal0 k r hj β c z z' g₀) (De R₀ : ℝ)
    (hD : DeOK k r z z' g₀ De) (hR : 1 ≤ R₀) (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hm : m ∈ UH (Hb k))
    (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ) (ha : ∀ b, 0 < a b)
    (h1 : Sg2 k r z' (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀)
    (h2 : Sg k r z (g₀ * (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m))) ≤ R₀) :
    (∀ p, ‖q.2 p‖ ≤ R₀ ^ (2 * r) * De) ∧ (∀ b, eucl (m⁻¹ *ᵥ q.1.1 b) ≤ R₀ ^ (2 * r) * De) ∧
      (∀ p, ‖q.1.2.1 p‖ ≤ 2 * r * (R₀ ^ (2 * r) * De) ^ 2) ∧ ∀ b, |q.1.2.2 b| ≤ 2 * r * (R₀ ^ (2 * r) * De) ^ 2 := by
  have key := GlobalTheory.T.moved_dual_vector_pairing_bounded_majorant k r j hj z z' g₀ β c hz hz' hT hN De R₀ hD hR m hm q a ha h1 h2
  have hM : 1 ≤ R₀ ^ (2 * r) * De := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) hD.1
  generalize R₀ ^ (2 * r) * De = M at key hM ⊢
  obtain ⟨B, hB⟩ : ∃ B : Fin r → Fin (k + 1) → ℂ, B = fun a => if h : a.val < j then q.1.1 ⟨a, h⟩ else 0 := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : Matrix (Fin r) (Fin r) ℂ, S = skewM
    (fun p => if h : p.1.1.val < j then q.1.2.1 ⟨p, h⟩ else 0) (fun a => if h : a.val < j then q.1.2.2 ⟨a, h⟩ else 0) :=
    ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : Matrix (Fin r) (Fin r) ℂ, u = upperOff β q.2 := ⟨_, rfl⟩
  have hs : sEl k r j β q = pEl k r B S * uEmb k r u := by rw [hB, hSdef, hudef]; rfl
  have hS : Sᴴ = -S := hSdef ▸ (GlobalTheory.Amp.Rad.radical k r).2.1 _ _
  have hu1 := (GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 (fun p => if h : β p.1.1 ≠ β p.1.2 then q.2 ⟨p, h⟩ else 0)
  have hu : IsUnit u.det := by
    rw [hudef, upperOff, hu1.1]; exact isUnit_one
  have huN : uEmb k r u ∈ Nset k r := hudef ▸ hu1.2
  rw [hs] at key h1
  have hpN := (((GlobalTheory.Amp.Rad.radical k r).1 B S).2.2.2 hS).1
  have ht := torus_le hz' hpN huN ha hm h1
  have hl := eucl_levi (k := k) ha hm
  simp only [inv_mulVec_esI B hS hu] at key
  have hmm : m * m⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_of_UH hm)

  have k1 : ∀ b : Fin r, b.val < j → ∀ d, ‖u b d‖ ≤ M := by
    intro b hb d
    have hd := d.isLt
    have := key b hb _ ((hl.1 d).le.trans (ht d).1)
    rwa [herm_eI, Pi.add_apply, Pi.add_apply, yVec_esI, midVec_inWb _ _ (Or.inr (by simp only [esI]; omega)),
      xVec_out _ (by simp only [esI]; omega), add_zero, add_zero, norm_star] at this
  have c1 : ∀ p, ‖q.2 p‖ ≤ M := by
    intro p
    have hlt : p.1.1.1 < p.1.1.2 := p.1.2
    have hb : p.1.1.1.val < j := by
      by_contra hc
      have hlt' : p.1.1.1.val < p.1.1.2.val := hlt
      exact p.2 ((hN.2.2.2.2.1 _ _ (by omega)).2 (by omega))
    have := k1 _ hb p.1.1.2
    rw [hudef, upperOff, upper, dif_pos hlt, dif_pos p.2] at this
    exact this
  have k1' : ∀ b d, ‖u b d‖ ≤ M := by
    intro b d
    rw [hudef, upperOff, upper]
    split_ifs
    · exact c1 _
    · simpa using le_trans zero_le_one hM
    · simpa using hM
    · simpa using le_trans zero_le_one hM

  have k2 : ∀ b : Fin r, eucl (m⁻¹ *ᵥ B b) ≤ M := by
    intro b
    by_cases hb : b.val < j
    · refine eucl_le_of_herm _ (le_trans zero_le_one hM) fun w hw => ?_
      have := key b hb _ (((hl.2.2 w).le.trans hw).trans hR)
      rw [herm_midVec] at this
      have e : (fun l => (yVec k r (fun a => star (u b a)) + midVec k r (-B b) +
          xVec k r (u⁻¹ *ᵥ fun a => -S a b - herm (Hb k) (B b) (B a) / 2)) (wI k r l)) = -B b := by
        funext l
        have hl' := l.isLt
        rw [Pi.add_apply, Pi.add_apply, midVec_wI, yVec_out _ (by simp only [wI]; omega),
          xVec_out _ (by simp only [wI]; omega), zero_add, add_zero]
      rw [e] at this
      rw [← herm_UH hm, Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec]
      simpa [herm, Matrix.mulVec_neg] using this
    · have : B b = 0 := by rw [hB]; exact dif_neg hb
      rw [this]
      simpa [eucl] using le_trans zero_le_one hM
  have k2' : ∀ b d, ‖herm (Hb k) (B b) (B d)‖ ≤ M ^ 2 := by
    intro b d
    have e : herm (Hb k) (B b) (B d) = herm (Hb k) (m⁻¹ *ᵥ B b) (m⁻¹ *ᵥ B d) := by
      rw [← herm_UH hm (m⁻¹ *ᵥ B b), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec, Matrix.one_mulVec]
    rw [e, sq]
    exact (norm_herm_Hb_le _ _).trans (mul_le_mul (k2 b) (k2 d) (Real.sqrt_nonneg _) (le_trans zero_le_one hM))

  have k3 : ∀ b : Fin r, b.val < j → ∀ d, ‖S d b‖ ≤ 2 * r * M ^ 2 := by
    intro b hb d
    obtain ⟨x, hx⟩ : ∃ x : Fin r → ℂ, x = fun a => -S a b - herm (Hb k) (B b) (B a) / 2 := ⟨_, rfl⟩
    have hy : ∀ e, ‖(u⁻¹ *ᵥ x) e‖ ≤ M := by
      intro e
      have he := e.isLt
      have := key b hb _ ((hl.2.1 e).le.trans (ht e).2)
      rwa [herm_esI, Pi.add_apply, Pi.add_apply, xVec_eI, midVec_inWb _ _ (Or.inl (by simp only [eI]; omega)),
        yVec_out _ (by simp only [eI]; omega), zero_add, zero_add, ← hx] at this
    have hxd : ‖x d‖ ≤ r * M ^ 2 := by
      have e : x d = ∑ e, u d e * (u⁻¹ *ᵥ x) e := by
        conv_lhs => rw [← Matrix.one_mulVec x, ← Matrix.mul_nonsing_inv u hu, ← Matrix.mulVec_mulVec]
        rfl
      rw [e]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ e, ‖u d e * (u⁻¹ *ᵥ x) e‖ ≤ ∑ _e : Fin r, M ^ 2 := Finset.sum_le_sum fun e _ => by
            rw [norm_mul, sq]
            exact mul_le_mul (k1' d e) (hy e) (norm_nonneg _) (le_trans zero_le_one hM)
        _ = r * M ^ 2 := by simp
    have e : S d b = -(x d + herm (Hb k) (B b) (B d) / 2) := by rw [hx]; ring
    have hr : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have h3 := k2' b d
    have h4 : 0 ≤ M ^ 2 := sq_nonneg _
    rw [e, norm_neg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, Complex.norm_two]
    nlinarith
  refine ⟨c1, fun b => ?_, fun p => ?_, fun b => ?_⟩
  · have := k2 b.1
    have e : B b.1 = q.1.1 b := by rw [hB]; exact dif_pos b.2
    rwa [e] at this
  · have hlt : p.1.1.1 < p.1.1.2 := p.1.2
    have := k3 _ p.2 p.1.1.2
    rw [hSdef, skewM, dif_neg (not_lt.2 hlt.le), dif_pos hlt, dif_pos p.2, norm_neg, norm_star] at this
    exact this
  · have := k3 _ b.2 b.1
    rw [hSdef, skewM, dif_neg (lt_irrefl _), dif_neg (lt_irrefl _), dif_pos b.2] at this
    simpa using this

end GlobalTheory.Amp.SecBound
