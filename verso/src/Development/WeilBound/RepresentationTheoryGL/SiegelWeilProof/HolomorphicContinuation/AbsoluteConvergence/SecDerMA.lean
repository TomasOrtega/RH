import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.WeightFactorDilation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

/- English proof (translation)
Simplify using `[aE, neg_smul]`.
-/
theorem aE_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H (-σ) = NormedSpace.exp (-((σ : ℂ) • H)) := by
  simp [aE, neg_smul]

/- English proof (translation)
Rewrite using `[aE_neg, aE, Matrix.exp_neg]`. Conclude with `Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))`.
-/
theorem aE_mul_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H (-σ) * aE H σ = 1 := by
  rw [aE_neg, aE, Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

/- English proof (translation)
Rewrite using `[aE_neg, aE, Matrix.exp_neg]`. Conclude with `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))`.
-/
theorem aE_mul_neg' (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H σ * aE H (-σ) = 1 := by
  rw [aE_neg, aE, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

/- English proof (translation)
Rewrite using `[aE, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem aE_herm {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : (aE H σ)ᴴ = aE H σ := by
  rw [aE, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq]
  congr 1
  simp

/- English proof (translation)
Rewrite using `[aE, GlobalTheory.SUVol.det_exp, Matrix.trace_smul, smul_eq_mul]`.
-/
theorem det_aE (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : (aE H σ).det = Complex.exp ((σ : ℂ) * H.trace) := by
  rw [aE, GlobalTheory.SUVol.det_exp, Matrix.trace_smul, smul_eq_mul]

/- English proof (translation)
Rewrite using `[JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]`. Simplify using the standard rewrite rules.
-/
private theorem JJ_mul_self_eq_neg_one (n : ℕ) : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp
/- English proof (translation)
Establish `hJ` using `JJ_mul_self_eq_neg_one n`. Establish `h1 : Gᴴ * JJ n = JJ n * Gi`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_neg, hJ, neg_neg, Matrix.mul_one]`.

Use `_ = G * (JJ n * (Gᴴ * JJ n)) * (-JJ n) := by simp only [Matrix.mul_assoc]`. Use `_ = G * ((JJ n * JJ n) * Gi) * (-JJ n) := by rw [h1]; simp only [Matrix.mul_assoc]`. Use `_ = JJ n := by`. Rewrite using `[hJ]`. Simplify using `[hGi]`.
-/
private theorem mul_JJ_mul_conjTranspose_eq_JJ_of_inG {n : ℕ} (G Gi : M2 n) (hGi : G * Gi = 1) (hG : InG G) :
    G * JJ n * Gᴴ = JJ n := by
  have hJ := JJ_mul_self_eq_neg_one n
  have h1 : Gᴴ * JJ n = JJ n * Gi := by
    calc Gᴴ * JJ n = Gᴴ * JJ n * (G * Gi) := by rw [hGi, Matrix.mul_one]
      _ = (Gᴴ * JJ n * G) * Gi := by simp only [Matrix.mul_assoc]
      _ = JJ n * Gi := by rw [hG]
  calc G * JJ n * Gᴴ = G * JJ n * Gᴴ * (JJ n * (-JJ n)) := by
        rw [Matrix.mul_neg, hJ, neg_neg, Matrix.mul_one]
    _ = G * (JJ n * (Gᴴ * JJ n)) * (-JJ n) := by simp only [Matrix.mul_assoc]
    _ = G * ((JJ n * JJ n) * Gi) * (-JJ n) := by rw [h1]; simp only [Matrix.mul_assoc]
    _ = JJ n := by
        rw [hJ]
        simp [hGi]
/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨⟨M, Mi, h1, h2⟩, hM⟩, rfl, rfl⟩`.
-/
private theorem exists_GR_mR_eq_of_inG_of_inverse {n : ℕ} (M Mi : M2 n) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hM : InG M) : ∃ x : GR n, mR x = M ∧ mR x⁻¹ = Mi :=
  ⟨⟨⟨M, Mi, h1, h2⟩, hM⟩, rfl, rfl⟩
/- English proof (translation)
Unfold `InG JJ nU`. Rewrite using `[fromBlocks_multiply, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `[hc.eq]`.
-/
private theorem inG_JJ_mul_nU_of_isHermitian {n : ℕ} (c : Matrix (Fin n) (Fin n) ℂ) (hc : c.IsHermitian) :
    InG (JJ n * nU c) := by
  unfold InG JJ nU
  rw [fromBlocks_multiply, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hc.eq]
/- English proof (translation)
Unfold `InG JJ`. Rewrite using `[fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, ha.eq, ha'.eq]`. Simplify using `[h, h']`.
-/
private theorem inG_fromBlocks_diag_of_hermitian_inverse {n : ℕ} (a a' : Matrix (Fin n) (Fin n) ℂ) (ha : a.IsHermitian)
    (ha' : a'.IsHermitian) (h : a * a' = 1) (h' : a' * a = 1) :
    InG (fromBlocks a' 0 0 a) := by
  unfold InG JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, ha.eq, ha'.eq]
  simp [h, h']

/- English proof (translation)
Introduce `n H hH f hf g hC`. Establish `hG : mR g = fromBlocks (toBlocks₁₁ (mR g)) (toBlocks₁₂ (mR g)) (toBlocks₂₁ (mR g)) (toBlocks₂₂ (mR g))` using `(fromBlocks_toBlocks _).symm`. Use `set A := toBlocks₁₁ (mR g)`. Use `set B := toBlocks₁₂ (mR g)`. Use `set C := toBlocks₂₁ (mR g)`.

Use `set D := toBlocks₂₂ (mR g)`. Establish `hCu : IsUnit C.det` using `isUnit_iff_ne_zero.mpr hC`. Establish `hgi : mR g * mR g⁻¹ = 1` using `congrArg mR (mul_inv_cancel g)`. Establish `hgJ : mR g * JJ n * (mR g)ᴴ = JJ n` using `mul_JJ_mul_conjTranspose_eq_JJ_of_inG (mR g) (mR g⁻¹) hgi g.2`. Establish `hCD : C * Dᴴ = D * Cᴴ`.

Establish `h22` using `congrArg toBlocks₂₂ hgJ`. Rewrite `h22` using `[hG, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `at h22`. Conclude with `((neg_add_eq_zero).mp h22).symm`. Establish `hCHu : IsUnit Cᴴ.det`.

Rewrite using `[det_conjTranspose]`. Conclude with `hCu.star`. Establish `hbH : (C⁻¹ * D).IsHermitian`. Unfold `IsHermitian`. Rewrite using `[conjTranspose_mul, conjTranspose_nonsing_inv]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, nonsing_inv_mul _ hCu, Matrix.one_mul]`. Use `_ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hCD]`. Use `_ = C⁻¹ * D := by`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCHu, Matrix.mul_one]`.

Establish `hnU : ∀ c : Matrix (Fin n) (Fin n) ℂ, nU c * nU (-c) = 1 ∧ nU (-c) * nU c = 1`. Introduce `c`. Apply the tactic sequence `constructor <;> rw [nU, nU, fromBlocks_multiply, ← fromBlocks_one] <;> simp`. Establish `hJ` using `JJ_mul_self_eq_neg_one n`. Establish `hWinv : ∀ c : Matrix (Fin n) (Fin n) ℂ, JJ n * nU c * (nU (-c) * -JJ n) = 1 ∧ nU (-c) * -JJ n * (JJ n * nU c) = 1`.

Introduce `c`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (nU c), (hnU c).1, Matrix.one_mul, Matrix.mul_neg, hJ, neg_neg]`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (-JJ n), Matrix.neg_mul, hJ, neg_neg, Matrix.one_mul, (hnU c).2]`. Take `⟨w₀, hw₀, hw₀i⟩` from `exists_GR_mR_eq_of_inG_of_inverse _ _ (hWinv (C⁻¹ * D)).1 (hWinv (C⁻¹ * D)).2 (inG_JJ_mul_nU_of_isHermitian _ hbH)`.

Use `⟨g * w₀⁻¹, C⁻¹ * D, ?_, hbH, ?_⟩` and prove the remaining obligations. Use `show toBlocks₂₁ (mR g * mR w₀⁻¹) = 0`. Rewrite using `[hw₀i, hG, nU, JJ, fromBlocks_neg, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `[← Matrix.mul_assoc, mul_nonsing_inv _ hCu]`. Introduce `p q e σ`.

Establish `h1 : aE H σ * aE H (-σ) = 1` using `aE_mul_neg' H σ`. Establish `h2 : aE H (-σ) * aE H σ = 1` using `aE_mul_neg H σ`. Establish `ha : (aE H σ).IsHermitian` using `aE_herm hH σ`. Establish `ha' : (aE H (-σ)).IsHermitian` using `aE_herm hH (-σ)`. Establish `hc : (aE H (-σ) * (C⁻¹ * D) * aE H (-σ)).IsHermitian`.

Unfold `IsHermitian`. Rewrite using `[conjTranspose_mul, conjTranspose_mul, ha'.eq, hbH.eq, ← Matrix.mul_assoc]`. Take `⟨mA, hmA, -⟩` from `exists_GR_mR_eq_of_inG_of_inverse (fromBlocks (aE H (-σ)) 0 0 (aE H σ)) (fromBlocks (aE H σ) 0 0 (aE H (-σ))) (by rw [fromBlocks_multiply, ← fromBlocks_one]; simp [h1, h2]) (by rw [fromBlocks_multiply, ← fromBlocks_one]; simp [h1, h2]) (inG_fromBlocks_diag_of_hermitian_inverse _ …`. Take `⟨w, hw, -⟩` from `exists_GR_mR_eq_of_inG_of_inverse _ _ (hWinv (aE H (-σ) * (C⁻¹ * D) * aE H (-σ))).1 (hWinv _).2 (inG_JJ_mul_nU_of_isHermitian _ hc)`. Use `⟨mA, w, ?_, ?_, hw, hc, ?_⟩` and prove the remaining obligations.

Use `show toBlocks₂₁ (mR mA) = 0`. Rewrite using `[hmA]`. Simplify using the standard rewrite rules. Unfold `F0 f0 u1 u2`. Rewrite using `[hmA]`.

Simplify using `only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_zero, zero_add, neg_zero, det_fromBlocks_zero₂₁]`. Rewrite using `[← det_mul, h2, det_one, _root_.one_zpow, one_mul, det_aE, ← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show mR g * mR (f σ) = mR g * mR w₀⁻¹ * mR mA * mR w`. Rewrite using `[hf σ, hw₀i, hmA, hw, Matrix.mul_assoc (mR g), Matrix.mul_assoc (mR g)]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `fromBlocks (aE H σ) 0 0 (NormedSpace.exp (-((σ : ℂ) • H))) = _`. Rewrite using `[← aE_neg, nU, nU, JJ, fromBlocks_neg]`. Simplify using `[fromBlocks_multiply, ← Matrix.mul_assoc, h1]`.
-/
theorem cellM : CellM := by
  intro n H hH f hf g hC
  have hG : mR g = fromBlocks (toBlocks₁₁ (mR g)) (toBlocks₁₂ (mR g)) (toBlocks₂₁ (mR g))
      (toBlocks₂₂ (mR g)) := (fromBlocks_toBlocks _).symm
  set A := toBlocks₁₁ (mR g)
  set B := toBlocks₁₂ (mR g)
  set C := toBlocks₂₁ (mR g)
  set D := toBlocks₂₂ (mR g)
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hC
  have hgi : mR g * mR g⁻¹ = 1 := congrArg mR (mul_inv_cancel g)
  have hgJ : mR g * JJ n * (mR g)ᴴ = JJ n := mul_JJ_mul_conjTranspose_eq_JJ_of_inG (mR g) (mR g⁻¹) hgi g.2
  have hCD : C * Dᴴ = D * Cᴴ := by
    have h22 := congrArg toBlocks₂₂ hgJ
    rw [hG, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h22
    simp at h22
    exact ((neg_add_eq_zero).mp h22).symm
  have hCHu : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact hCu.star
  have hbH : (C⁻¹ * D).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Dᴴ * (Cᴴ)⁻¹ = C⁻¹ * (C * Dᴴ) * (Cᴴ)⁻¹ := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hCu, Matrix.one_mul]
      _ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hCD]
      _ = C⁻¹ * D := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCHu, Matrix.mul_one]
  have hnU : ∀ c : Matrix (Fin n) (Fin n) ℂ, nU c * nU (-c) = 1 ∧ nU (-c) * nU c = 1 := by
    intro c
    constructor <;> rw [nU, nU, fromBlocks_multiply, ← fromBlocks_one] <;> simp
  have hJ := JJ_mul_self_eq_neg_one n
  have hWinv : ∀ c : Matrix (Fin n) (Fin n) ℂ,
      JJ n * nU c * (nU (-c) * -JJ n) = 1 ∧ nU (-c) * -JJ n * (JJ n * nU c) = 1 := by
    intro c
    constructor
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (nU c), (hnU c).1, Matrix.one_mul, Matrix.mul_neg, hJ,
        neg_neg]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (-JJ n), Matrix.neg_mul, hJ, neg_neg, Matrix.one_mul,
        (hnU c).2]
  obtain ⟨w₀, hw₀, hw₀i⟩ := exists_GR_mR_eq_of_inG_of_inverse _ _ (hWinv (C⁻¹ * D)).1 (hWinv (C⁻¹ * D)).2
    (inG_JJ_mul_nU_of_isHermitian _ hbH)
  refine ⟨g * w₀⁻¹, C⁻¹ * D, ?_, hbH, ?_⟩
  · show toBlocks₂₁ (mR g * mR w₀⁻¹) = 0
    rw [hw₀i, hG, nU, JJ, fromBlocks_neg, fromBlocks_multiply, fromBlocks_multiply]
    simp [← Matrix.mul_assoc, mul_nonsing_inv _ hCu]
  intro p q e σ
  have h1 : aE H σ * aE H (-σ) = 1 := aE_mul_neg' H σ
  have h2 : aE H (-σ) * aE H σ = 1 := aE_mul_neg H σ
  have ha : (aE H σ).IsHermitian := aE_herm hH σ
  have ha' : (aE H (-σ)).IsHermitian := aE_herm hH (-σ)
  have hc : (aE H (-σ) * (C⁻¹ * D) * aE H (-σ)).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, ha'.eq, hbH.eq, ← Matrix.mul_assoc]
  obtain ⟨mA, hmA, -⟩ := exists_GR_mR_eq_of_inG_of_inverse (fromBlocks (aE H (-σ)) 0 0 (aE H σ))
    (fromBlocks (aE H σ) 0 0 (aE H (-σ)))
    (by rw [fromBlocks_multiply, ← fromBlocks_one]; simp [h1, h2])
    (by rw [fromBlocks_multiply, ← fromBlocks_one]; simp [h1, h2])
    (inG_fromBlocks_diag_of_hermitian_inverse _ _ ha ha' h1 h2)
  obtain ⟨w, hw, -⟩ := exists_GR_mR_eq_of_inG_of_inverse _ _ (hWinv (aE H (-σ) * (C⁻¹ * D) * aE H (-σ))).1
    (hWinv _).2 (inG_JJ_mul_nU_of_isHermitian _ hc)
  refine ⟨mA, w, ?_, ?_, hw, hc, ?_⟩
  · show toBlocks₂₁ (mR mA) = 0
    rw [hmA]
    simp
  · unfold F0 f0 u1 u2
    rw [hmA]
    simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_zero, zero_add, neg_zero,
      det_fromBlocks_zero₂₁]
    rw [← det_mul, h2, det_one, _root_.one_zpow, one_mul, det_aE, ← Complex.exp_int_mul,
      ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · apply Subtype.ext
    apply Units.ext
    show mR g * mR (f σ) = mR g * mR w₀⁻¹ * mR mA * mR w
    rw [hf σ, hw₀i, hmA, hw, Matrix.mul_assoc (mR g), Matrix.mul_assoc (mR g)]
    congr 1
    change fromBlocks (aE H σ) 0 0 (NormedSpace.exp (-((σ : ℂ) • H))) = _
    rw [← aE_neg, nU, nU, JJ, fromBlocks_neg]
    simp [fromBlocks_multiply, ← Matrix.mul_assoc, h1]

end PositivityTheory.Rg.Sw.AbsSt.SDM
