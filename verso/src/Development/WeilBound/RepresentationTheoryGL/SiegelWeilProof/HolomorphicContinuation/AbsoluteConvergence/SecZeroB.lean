import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecZeroA

noncomputable section

open Matrix Filter Topology Set Polynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

def lowM (n : ℕ) (s : ℝ) : M2 n := fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1

/- English proof (translation)
Simplify using `only [lowM, fromBlocks_multiply]`. Simplify using `[add_smul]`.
-/
lemma lowM_mul (s s' : ℝ) : lowM n s * lowM n s' = lowM n (s + s') := by
  simp only [lowM, fromBlocks_multiply]
  simp [add_smul]

/- English proof (translation)
Unfold `lowM`. Simplify using `[fromBlocks_one]`.
-/
lemma lowM_zero : lowM n 0 = 1 := by
  unfold lowM; simp [fromBlocks_one]

def lowU (n : ℕ) (s : ℝ) : GL (Fin n ⊕ Fin n) ℂ :=
  ⟨lowM n s, lowM n (-s), by rw [lowM_mul, add_neg_cancel, lowM_zero], by rw [lowM_mul, neg_add_cancel, lowM_zero]⟩

def lowG (n : ℕ) (s : ℝ) : GR n := ⟨lowU n s, InG_lower s⟩

/- English proof (translation)
Unfold `lowG`. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Rewrite using `[Units.continuous_iff]`. Establish `hc : Continuous (fun s : ℝ => lowM n s)`. Unfold `lowM`.

Conclude with `Continuous.matrix_fromBlocks continuous_const continuous_const (Complex.continuous_ofReal.smul continuous_const) continuous_const`. Conclude with `⟨hc, hc.comp continuous_neg⟩`.
-/
lemma lowG_cont : Continuous (lowG n) := by
  unfold lowG
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  have hc : Continuous (fun s : ℝ => lowM n s) := by
    unfold lowM
    exact Continuous.matrix_fromBlocks continuous_const continuous_const
      (Complex.continuous_ofReal.smul continuous_const) continuous_const
  exact ⟨hc, hc.comp continuous_neg⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `lowM_zero`.
-/
lemma lowG_zero : lowG n 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact lowM_zero

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma mR_mul (a b : GR n) : mR (a * b) = mR a * mR b := rfl

/- English proof (translation)
Rewrite using `[mR_mul]`. Use `show (mR y * lowM n s).toBlocks₂₁ = _`. Use `conv_lhs => rw [← fromBlocks_toBlocks (mR y)]`. Unfold `lowM`. Rewrite using `[fromBlocks_multiply]`.

Simplify using the standard rewrite rules.
-/
lemma lower_left_block_lowering_mul (y : GR n) (s : ℝ) :
    (mR (y * lowG n s)).toBlocks₂₁ = (mR y).toBlocks₂₁ + (s : ℂ) • (mR y).toBlocks₂₂ := by
  rw [mR_mul]
  show (mR y * lowM n s).toBlocks₂₁ = _
  conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
  unfold lowM
  rw [fromBlocks_multiply]
  simp

/- English proof (translation)
Take `⟨C, hC⟩ : ∃ C, C = (mR y).toBlocks₂₁` from `⟨_, rfl⟩`. Take `⟨D, hD⟩ : ∃ D, D = (mR y).toBlocks₂₂` from `⟨_, rfl⟩`. Establish `hG : (mR y)ᴴ * JJ n * mR y = JJ n` using `y.2`. Establish `hgg : mR y * mR y⁻¹ = 1`. Rewrite using `[← mR_mul, mul_inv_cancel]`.

Both sides reduce to the same expression. Establish `hJJ : JJ n * JJ n = -1`. Rewrite using `[JJ, fromBlocks_multiply]`. Simplify using `[← fromBlocks_one, fromBlocks_neg]`. Establish `key : mR y * JJ n * (mR y)ᴴ = JJ n`.

Establish `h1 : (mR y)ᴴ * JJ n = JJ n * mR y⁻¹`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hJJ]`. Simplify using the standard rewrite rules.

Use `_ = mR y * JJ n * ((mR y)ᴴ * JJ n) * JJ n * (-1) := by simp only [Matrix.mul_assoc]`. Use `_ = mR y * (JJ n * JJ n) * mR y⁻¹ * JJ n * (-1) := by rw [h1]; simp only [Matrix.mul_assoc]`. Use `_ = JJ n := by`. Rewrite using `[hJJ]`. Simplify using `[hgg]`.

Establish `hherm : C * Dᴴ = D * Cᴴ`. Establish `hb` using `congrArg Matrix.toBlocks₂₂ key`. Rewrite `hb` using `[← fromBlocks_toBlocks (mR y), JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `at hb`. Rewrite `hb` using `[← hC, ← hD]`.

Conclude with `(neg_add_eq_zero.mp hb).symm`. Establish `hpos : ((C * Cᴴ + D * Dᴴ).det) ≠ 0`. Establish `hu : IsUnit (mR y)` using `⟨(y : GL (Fin n ⊕ Fin n) ℂ), rfl⟩`. Use `open ComplexOrder in`. Establish `hpd : ((mR y * (mR y)ᴴ).submatrix Sum.inr Sum.inr).PosDef` using `(Matrix.PosDef.mul_conjTranspose_self _ (Matrix.vecMul_injective_iff_isUnit.mpr hu)).submatrix Sum.inr_injective`.

Establish `he : (mR y * (mR y)ᴴ).submatrix Sum.inr Sum.inr = C * Cᴴ + D * Dᴴ`. Express the relevant statement in the definitionally equal form `Matrix.toBlocks₂₂ (mR y * (mR y)ᴴ) = _`. Rewrite using `[hC, hD]`. Use `conv_lhs => rw [← fromBlocks_toBlocks (mR y), fromBlocks_conjTranspose, fromBlocks_multiply]`. Simplify using the standard rewrite rules.

Rewrite using `[← he]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit |>.ne_zero`. Establish `hprod : (C + Complex.I • D) * (C + Complex.I • D)ᴴ = C * Cᴴ + D * Dᴴ`. Simplify using `only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_I]`. Rewrite using `[← hherm, smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]`.

Normalize the expressions using the abelian group laws. Establish `hI : (C + Complex.I • D).det ≠ 0`. Introduce `h`. Apply `hpos` to reduce the goal to its premises. Rewrite using `[← hprod, Matrix.det_mul, h, zero_mul]`.

Set `P : Polynomial ℂ` to `Matrix.det (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C)`. Establish `hev : ∀ r : ℂ, P.eval r = (C + r • D).det`. Introduce `r`. Use `show Polynomial.evalRingHom r (Matrix.det _) = _`. Rewrite using `[RingHom.map_det]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `hP : P ≠ 0` using `fun h => hI (by rw [← hev, h, Polynomial.eval_zero])`.

Establish `hfin : {s : ℝ | P.eval (s : ℂ) = 0}.Finite`. Apply `Set.Finite.subset ((P.roots.toFinset.finite_toSet).preimage Complex.ofReal_injective.injOn)` to reduce the goal to its premises. Introduce `s hs`. Simplify using `only [Set.mem_setOf_eq] at hs`. Simplify using `[Polynomial.mem_roots hP, hs]`.

Establish `hT : Tendsto (fun s : ℝ => y * lowG n s) (𝓝[≠] (0 : ℝ)) (𝓝 y)`. Establish `h0 : Tendsto (fun s : ℝ => y * lowG n s) (𝓝 0) (𝓝 (y * lowG n 0))` using `(continuous_const.mul lowG_cont).tendsto 0`. Rewrite `h0` using `[lowG_zero, mul_one]`. Conclude with `h0.mono_left nhdsWithin_le_nhds`. Apply `mem_closure_of_tendsto hT` to reduce the goal to its premises.

Establish `hopen : ({s : ℝ | P.eval (s : ℂ) = 0} \ {0})ᶜ ∈ 𝓝 (0 : ℝ)` using `(hfin.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)`. Use `filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with s hs hs0`. Use `show ((mR (y * lowG n s)).toBlocks₂₁).det ≠ 0`. Rewrite using `[lower_left_block_lowering_mul, ← hC, ← hD, ← hev]`. Introduce `h`.

Conclude with `hs ⟨h, hs0⟩`.
-/
lemma dense_cell (y : GR n) : y ∈ closure {z : GR n | ((mR z).toBlocks₂₁).det ≠ 0} := by
  classical
  obtain ⟨C, hC⟩ : ∃ C, C = (mR y).toBlocks₂₁ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (mR y).toBlocks₂₂ := ⟨_, rfl⟩
  have hG : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hgg : mR y * mR y⁻¹ = 1 := by
    rw [← mR_mul, mul_inv_cancel]
    rfl
  have hJJ : JJ n * JJ n = -1 := by
    rw [JJ, fromBlocks_multiply]
    simp [← fromBlocks_one, fromBlocks_neg]
  have key : mR y * JJ n * (mR y)ᴴ = JJ n := by
    have h1 : (mR y)ᴴ * JJ n = JJ n * mR y⁻¹ := by
      calc (mR y)ᴴ * JJ n = (mR y)ᴴ * JJ n * (mR y * mR y⁻¹) := by rw [hgg, Matrix.mul_one]
        _ = ((mR y)ᴴ * JJ n * mR y) * mR y⁻¹ := by simp only [Matrix.mul_assoc]
        _ = JJ n * mR y⁻¹ := by rw [hG]
    calc mR y * JJ n * (mR y)ᴴ = mR y * JJ n * (mR y)ᴴ * (JJ n * JJ n) * (-1) := by
          rw [hJJ]; simp
      _ = mR y * JJ n * ((mR y)ᴴ * JJ n) * JJ n * (-1) := by simp only [Matrix.mul_assoc]
      _ = mR y * (JJ n * JJ n) * mR y⁻¹ * JJ n * (-1) := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = JJ n := by
          rw [hJJ]
          simp [hgg]
  have hherm : C * Dᴴ = D * Cᴴ := by
    have hb := congrArg Matrix.toBlocks₂₂ key
    rw [← fromBlocks_toBlocks (mR y), JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply] at hb
    simp at hb
    rw [← hC, ← hD] at hb
    exact (neg_add_eq_zero.mp hb).symm
  have hpos : ((C * Cᴴ + D * Dᴴ).det) ≠ 0 := by
    have hu : IsUnit (mR y) := ⟨(y : GL (Fin n ⊕ Fin n) ℂ), rfl⟩
    open ComplexOrder in
    have hpd : ((mR y * (mR y)ᴴ).submatrix Sum.inr Sum.inr).PosDef :=
      (Matrix.PosDef.mul_conjTranspose_self _
        (Matrix.vecMul_injective_iff_isUnit.mpr hu)).submatrix Sum.inr_injective
    have he : (mR y * (mR y)ᴴ).submatrix Sum.inr Sum.inr = C * Cᴴ + D * Dᴴ := by
      change Matrix.toBlocks₂₂ (mR y * (mR y)ᴴ) = _
      rw [hC, hD]
      conv_lhs => rw [← fromBlocks_toBlocks (mR y), fromBlocks_conjTranspose, fromBlocks_multiply]
      simp
    rw [← he]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit |>.ne_zero
  have hprod : (C + Complex.I • D) * (C + Complex.I • D)ᴴ = C * Cᴴ + D * Dᴴ := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_I]
    rw [← hherm, smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]
    abel
  have hI : (C + Complex.I • D).det ≠ 0 := by
    intro h
    apply hpos
    rw [← hprod, Matrix.det_mul, h, zero_mul]
  let P : Polynomial ℂ :=
    Matrix.det (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C)
  have hev : ∀ r : ℂ, P.eval r = (C + r • D).det := by
    intro r
    show Polynomial.evalRingHom r (Matrix.det _) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hP : P ≠ 0 := fun h => hI (by rw [← hev, h, Polynomial.eval_zero])
  have hfin : {s : ℝ | P.eval (s : ℂ) = 0}.Finite := by
    apply Set.Finite.subset ((P.roots.toFinset.finite_toSet).preimage
      Complex.ofReal_injective.injOn)
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    simp [Polynomial.mem_roots hP, hs]
  have hT : Tendsto (fun s : ℝ => y * lowG n s) (𝓝[≠] (0 : ℝ)) (𝓝 y) := by
    have h0 : Tendsto (fun s : ℝ => y * lowG n s) (𝓝 0) (𝓝 (y * lowG n 0)) :=
      (continuous_const.mul lowG_cont).tendsto 0
    rw [lowG_zero, mul_one] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hT
  have hopen : ({s : ℝ | P.eval (s : ℂ) = 0} \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    (hfin.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with s hs hs0
  show ((mR (y * lowG n s)).toBlocks₂₁).det ≠ 0
  rw [lower_left_block_lowering_mul, ← hC, ← hD, ← hev]
  intro h
  exact hs ⟨h, hs0⟩

end PositivityTheory.Rg.Sw.AbsSt.SZ
