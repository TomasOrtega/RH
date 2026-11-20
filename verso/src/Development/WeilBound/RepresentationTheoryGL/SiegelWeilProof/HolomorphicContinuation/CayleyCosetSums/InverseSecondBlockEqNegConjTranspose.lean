import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetSecondCayleyBlockNe
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CayleyInverseConjTransposeMulApply

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]`.
-/
private theorem mul_toBlocks₂₁_eq (g h : M2 n) :
    (g * h).toBlocks₂₁ = g.toBlocks₂₁ * h.toBlocks₁₁ + g.toBlocks₂₂ * h.toBlocks₂₁ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂]`.
-/
private theorem mul_toBlocks₂₂_eq (g h : M2 n) :
    (g * h).toBlocks₂₂ = g.toBlocks₂₁ * h.toBlocks₁₂ + g.toBlocks₂₂ * h.toBlocks₂₂ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]`.
-/
private theorem mul_toBlocks₁₁' (g h : M2 n) :
    (g * h).toBlocks₁₁ = g.toBlocks₁₁ * h.toBlocks₁₁ + g.toBlocks₁₂ * h.toBlocks₂₁ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₂, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]`.
-/
private theorem mul_toBlocks₁₂ (g h : M2 n) :
    (g * h).toBlocks₁₂ = g.toBlocks₁₁ * h.toBlocks₁₂ + g.toBlocks₁₂ * h.toBlocks₂₂ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₂, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>`. Simplify using `[Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.conjTranspose_apply]`.
-/
private theorem conjTranspose_toBlocks (g : M2 n) :
    (gᴴ).toBlocks₁₁ = (g.toBlocks₁₁)ᴴ ∧ (gᴴ).toBlocks₁₂ = (g.toBlocks₂₁)ᴴ ∧
      (gᴴ).toBlocks₂₁ = (g.toBlocks₁₂)ᴴ ∧ (gᴴ).toBlocks₂₂ = (g.toBlocks₂₂)ᴴ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.conjTranspose_apply]

/- English proof (translation)
Simplify using `[JJ]`.
-/
private theorem JJ_toBlocks :
    (JJ n).toBlocks₁₁ = 0 ∧ (JJ n).toBlocks₁₂ = 1 ∧ (JJ n).toBlocks₂₁ = -1 ∧ (JJ n).toBlocks₂₂ = 0 := by
  simp [JJ]

/- English proof (translation)
Establish `hG : kᴴ * JJ n * k = JJ n` using `hk.1`. Establish `h2 : k * kᴴ = 1` using `mul_eq_one_comm.mp hk.2`. Establish `h3 : JJ n * k = k * JJ n`. Combine the equalities or inequalities in the displayed calculation. Take `⟨j11, j12, j21, j22⟩` from `(JJ_toBlocks (n := n))`.

Establish `e1` using `congrArg Matrix.toBlocks₁₁ h3`. Establish `e2` using `congrArg Matrix.toBlocks₁₂ h3`. Rewrite `e1` using `[mul_toBlocks₁₁', mul_toBlocks₁₁', j11, j12, j21]`. Rewrite `e2` using `[mul_toBlocks₁₂, mul_toBlocks₁₂, j11, j12, j22]`. Simplify using `at e1 e2`.

Conclude with `⟨e1, e2⟩`.
-/
private theorem inK_toBlocks₂_eq {k : M2 n} (hk : InK k) :
    k.toBlocks₂₁ = -k.toBlocks₁₂ ∧ k.toBlocks₂₂ = k.toBlocks₁₁ := by
  have hG : kᴴ * JJ n * k = JJ n := hk.1
  have h2 : k * kᴴ = 1 := mul_eq_one_comm.mp hk.2
  have h3 : JJ n * k = k * JJ n := by
    calc JJ n * k = (k * kᴴ) * JJ n * k := by rw [h2, Matrix.one_mul]
      _ = k * (kᴴ * JJ n * k) := by simp only [Matrix.mul_assoc]
      _ = k * JJ n := by rw [hG]
  obtain ⟨j11, j12, j21, j22⟩ := (JJ_toBlocks (n := n))
  have e1 := congrArg Matrix.toBlocks₁₁ h3
  have e2 := congrArg Matrix.toBlocks₁₂ h3
  rw [mul_toBlocks₁₁', mul_toBlocks₁₁', j11, j12, j21] at e1
  rw [mul_toBlocks₁₂, mul_toBlocks₁₂, j11, j12, j22] at e2
  simp at e1 e2
  exact ⟨e1, e2⟩

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]`.
-/
private theorem neg_toBlocks₁₁_toBlocks₂₁ (g : M2 n) :
    (-g).toBlocks₁₁ = -g.toBlocks₁₁ ∧ (-g).toBlocks₂₁ = -g.toBlocks₂₁ := by
  refine ⟨?_, ?_⟩ <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.one_apply]`.
-/
private theorem one_toBlocks₁₁_toBlocks₁₂ :
    (1 : M2 n).toBlocks₁₁ = 1 ∧ (1 : M2 n).toBlocks₁₂ = 0 := by
  refine ⟨?_, ?_⟩ <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.one_apply]

/- English proof (translation)
Take `⟨hc, hd⟩` from `inK_toBlocks₂_eq hk`. Establish `hU : kᴴ * k = 1` using `hk.2`. Take `⟨c11, c12, c21, c22⟩` from `conjTranspose_toBlocks k`. Take `⟨o11, o12⟩` from `(one_toBlocks₁₁_toBlocks₁₂ (n := n))`. Establish `e1` using `congrArg Matrix.toBlocks₁₁ hU`.

Establish `e2` using `congrArg Matrix.toBlocks₁₂ hU`. Rewrite `e1` using `[mul_toBlocks₁₁', c11, c12, hc, o11]`. Rewrite `e2` using `[mul_toBlocks₁₂, c11, c12, hc, hd, o12]`. Simplify using `only [Matrix.conjTranspose_neg, neg_mul, mul_neg, neg_neg] at e1 e2`. Use `⟨e1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← sub_eq_zero]`. Simplify `e2` using `[sub_eq_add_neg]`.
-/
private theorem inK_toBlocks₁_unitary_relations {k : M2 n} (hk : InK k) :
    (k.toBlocks₁₁)ᴴ * k.toBlocks₁₁ + (k.toBlocks₁₂)ᴴ * k.toBlocks₁₂ = 1 ∧
      (k.toBlocks₁₁)ᴴ * k.toBlocks₁₂ = (k.toBlocks₁₂)ᴴ * k.toBlocks₁₁ := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  have hU : kᴴ * k = 1 := hk.2
  obtain ⟨c11, c12, c21, c22⟩ := conjTranspose_toBlocks k
  obtain ⟨o11, o12⟩ := (one_toBlocks₁₁_toBlocks₁₂ (n := n))
  have e1 := congrArg Matrix.toBlocks₁₁ hU
  have e2 := congrArg Matrix.toBlocks₁₂ hU
  rw [mul_toBlocks₁₁', c11, c12, hc, o11] at e1
  rw [mul_toBlocks₁₂, c11, c12, hc, hd, o12] at e2
  simp only [Matrix.conjTranspose_neg, neg_mul, mul_neg, neg_neg] at e1 e2
  refine ⟨e1, ?_⟩
  rw [← sub_eq_zero]
  simpa [sub_eq_add_neg] using e2

/- English proof (translation)
Take `⟨hc, hd⟩` from `inK_toBlocks₂_eq hk`. Simplify using `only [u1, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hc, hd, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, Complex.I_mul_I]`. Use `module`.
-/
theorem first_cayley_block_mul_compact (g : M2 n) {k : M2 n} (hk : InK k) : u1 (g * k) = u1 g * u1 k := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  simp only [u1, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hc, hd, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, Complex.I_mul_I]
  module

/- English proof (translation)
Take `⟨hc, hd⟩` from `inK_toBlocks₂_eq hk`. Simplify using `only [u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hc, hd, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, Complex.I_mul_I]`. Use `module`.
-/
theorem second_cayley_block_mul_compact (g : M2 n) {k : M2 n} (hk : InK k) : u2 (g * k) = u2 g * u2 k := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  simp only [u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hc, hd, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, Complex.I_mul_I]
  module

/- English proof (translation)
Take `⟨hc, hd⟩` from `inK_toBlocks₂_eq hk`. Take `⟨h1, h2⟩` from `inK_toBlocks₁_unitary_relations hk`. Establish `e : (u1 k)ᴴ * u1 k = ((k.toBlocks₁₁)ᴴ * k.toBlocks₁₁ + (k.toBlocks₁₂)ᴴ * k.toBlocks₁₂) + Complex.I • ((k.toBlocks₁₂)ᴴ * k.toBlocks₁₁ - (k.toBlocks₁₁)ᴴ * k.toBlocks₁₂)`. Simplify using `only [u1, hc, hd, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_neg, Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, neg_smul, Complex.I_ …`. Use `module`.

Rewrite using `[e, h1, h2, sub_self, smul_zero, add_zero]`.
-/
theorem first_cayley_block_compact_unitary {k : M2 n} (hk : InK k) : (u1 k)ᴴ * u1 k = 1 := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  obtain ⟨h1, h2⟩ := inK_toBlocks₁_unitary_relations hk
  have e : (u1 k)ᴴ * u1 k = ((k.toBlocks₁₁)ᴴ * k.toBlocks₁₁ + (k.toBlocks₁₂)ᴴ * k.toBlocks₁₂) +
      Complex.I • ((k.toBlocks₁₂)ᴴ * k.toBlocks₁₁ - (k.toBlocks₁₁)ᴴ * k.toBlocks₁₂) := by
    simp only [u1, hc, hd, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_neg,
      Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, neg_smul, Complex.I_mul_I, neg_mul]
    module
  rw [e, h1, h2, sub_self, smul_zero, add_zero]

def eps (n : ℕ) : M2 n := fromBlocks 1 0 0 (-1)

/- English proof (translation)
Simplify using `[eps, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]`.
-/
theorem eps_sq : eps n * eps n = 1 := by
  simp [eps, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

/- English proof (translation)
Simplify using `[eps, JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]`.
-/
theorem eps_JJ : eps n * JJ n * eps n = -JJ n := by
  simp [eps, JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]

/- English proof (translation)
Simplify using `[eps, fromBlocks_conjTranspose]`.
-/
theorem eps_conj : (eps n)ᴴ = eps n := by simp [eps, fromBlocks_conjTranspose]

/- English proof (translation)
Establish `hG : kᴴ * JJ n * k = JJ n` using `hk.1`. Establish `hU : kᴴ * k = 1` using `hk.2`. Establish `e : eps n * JJ n * eps n = -JJ n` using `eps_JJ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (eps n * k * eps n)ᴴ * JJ n * (eps n * k * eps n) = JJ n`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, eps_conj]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = -(eps n * (kᴴ * JJ n * k) * eps n) := by`. Rewrite using `[e]`.

Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`. Use `_ = JJ n := by rw [hG, e, neg_neg]`. Use `show (eps n * k * eps n)ᴴ * (eps n * k * eps n) = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, eps_conj]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [eps_sq, Matrix.mul_one, hU, Matrix.mul_one, eps_sq]`.
-/
theorem inK_eps {k : M2 n} (hk : InK k) : InK (eps n * k * eps n) := by
  have hG : kᴴ * JJ n * k = JJ n := hk.1
  have hU : kᴴ * k = 1 := hk.2
  have e : eps n * JJ n * eps n = -JJ n := eps_JJ
  refine ⟨?_, ?_⟩
  · show (eps n * k * eps n)ᴴ * JJ n * (eps n * k * eps n) = JJ n
    calc (eps n * k * eps n)ᴴ * JJ n * (eps n * k * eps n)
        = eps n * (kᴴ * (eps n * JJ n * eps n) * k) * eps n := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, eps_conj]
          simp only [Matrix.mul_assoc]
      _ = -(eps n * (kᴴ * JJ n * k) * eps n) := by
          rw [e]
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = JJ n := by rw [hG, e, neg_neg]
  · show (eps n * k * eps n)ᴴ * (eps n * k * eps n) = 1
    calc (eps n * k * eps n)ᴴ * (eps n * k * eps n)
        = eps n * (kᴴ * (eps n * eps n) * k) * eps n := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, eps_conj]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [eps_sq, Matrix.mul_one, hU, Matrix.mul_one, eps_sq]

/- English proof (translation)
Simplify using `[u1, u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, eps]`.
-/
theorem first_cayley_block_swap_conj (k : M2 n) : u1 (eps n * k * eps n) = u2 k := by
  simp [u1, u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, eps]

/- English proof (translation)
Rewrite using `[← first_cayley_block_swap_conj]`. Conclude with `first_cayley_block_compact_unitary (inK_eps hk)`.
-/
theorem second_cayley_block_compact_unitary {k : M2 n} (hk : InK k) : (u2 k)ᴴ * u2 k = 1 := by
  rw [← first_cayley_block_swap_conj]
  exact first_cayley_block_compact_unitary (inK_eps hk)

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary hk)`.
-/
theorem second_cayley_block_inv_eq_conjTranspose {k : M2 n} (hk : InK k) : (u2 k)⁻¹ = (u2 k)ᴴ := Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary hk)

/- English proof (translation)
Take `⟨c11, c12, c21, c22⟩` from `conjTranspose_toBlocks x`. Take `⟨j11, j12, j21, j22⟩` from `(JJ_toBlocks (n := n))`. Take `⟨n11, n21⟩` from `neg_toBlocks₁₁_toBlocks₂₁ (JJ n * xᴴ * JJ n)`. Simplify using `only [ub2, u2, inv_of_inG hx, n11, n21, mul_toBlocks₁₁', mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, mul_toBlocks₁₂, c11, c12, c21, c22, j11, j12, j21, j22, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.mul_one, …`. Use `module`.
-/
theorem inverse_second_block_eq_neg_conjTranspose {x : M2 n} (hx : InG x) : ub2 x = -(u2 x)ᴴ := by
  obtain ⟨c11, c12, c21, c22⟩ := conjTranspose_toBlocks x
  obtain ⟨j11, j12, j21, j22⟩ := (JJ_toBlocks (n := n))
  obtain ⟨n11, n21⟩ := neg_toBlocks₁₁_toBlocks₂₁ (JJ n * xᴴ * JJ n)
  simp only [ub2, u2, inv_of_inG hx, n11, n21, mul_toBlocks₁₁', mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, mul_toBlocks₁₂,
    c11, c12, c21, c22,
    j11, j12, j21, j22, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_I, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, neg_neg, neg_smul, smul_neg]
  module

/- English proof (translation)
Unfold `Om`. Rewrite using `[inverse_second_block_eq_neg_conjTranspose hk.1, inverse_first_block_eq_conjTranspose hk.1, Matrix.inv_eq_left_inv (mul_eq_one_comm.mp (first_cayley_block_compact_unitary hk)), ← second_cayley_block_inv_eq_conjTranspose hk, Matrix.neg_mul]`.
-/
theorem Om_K {k : M2 n} (hk : InK k) : Om k = -((u2 k)⁻¹ * u1 k) := by
  unfold Om
  rw [inverse_second_block_eq_neg_conjTranspose hk.1, inverse_first_block_eq_conjTranspose hk.1, Matrix.inv_eq_left_inv (mul_eq_one_comm.mp (first_cayley_block_compact_unitary hk)),
    ← second_cayley_block_inv_eq_conjTranspose hk, Matrix.neg_mul]

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (first_cayley_block_compact_unitary hk)`. Rewrite `h` using `[det_mul, det_conjTranspose, det_one]`. Establish `h' : (Complex.normSq (u1 k).det : ℂ) = 1` using `by rw [Complex.normSq_eq_conj_mul_self]; exact h`. Conclude with `h'` after adjusting the coercions.
-/
theorem normSq_det_u1K {k : M2 n} (hk : InK k) : Complex.normSq (u1 k).det = 1 := by
  have h := congrArg Matrix.det (first_cayley_block_compact_unitary hk)
  rw [det_mul, det_conjTranspose, det_one] at h
  have h' : (Complex.normSq (u1 k).det : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact h
  exact_mod_cast h'

/- English proof (translation)
Establish `hd : (u1 k).det * (ub1 k).det = 1`. Rewrite using `[inverse_first_block_eq_conjTranspose hk.1, Matrix.det_conjTranspose, Complex.star_def, mul_comm, ← Complex.normSq_eq_conj_mul_self, normSq_det_u1K hk, Complex.ofReal_one]`. Simplify using `only [fz, hd, Complex.one_cpow, neg_zero, Complex.cpow_zero]`.
-/
theorem fz_K (m : ℕ) (e : ℤ) (z : ℂ) {k : M2 n} (hk : InK k) : fz m e z k = fz m e 0 k := by
  have hd : (u1 k).det * (ub1 k).det = 1 := by
    rw [inverse_first_block_eq_conjTranspose hk.1, Matrix.det_conjTranspose, Complex.star_def, mul_comm,
      ← Complex.normSq_eq_conj_mul_self, normSq_det_u1K hk, Complex.ofReal_one]
  simp only [fz, hd, Complex.one_cpow, neg_zero, Complex.cpow_zero]

/- English proof (translation)
Simplify using `only [u1, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hp, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul]`.
-/
theorem first_cayley_block_upper_triangular_mul {p : M2 n} (hp : p.toBlocks₂₁ = 0) (y : M2 n) : u1 (p * y) = p.toBlocks₂₂ * u1 y := by
  simp only [u1, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hp, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul]

/- English proof (translation)
Simplify using `only [u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hp, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]`.
-/
theorem second_cayley_block_upper_triangular_mul {p : M2 n} (hp : p.toBlocks₂₁ = 0) (y : M2 n) : u2 (p * y) = p.toBlocks₂₂ * u2 y := by
  simp only [u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hp, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_neg]

/- English proof (translation)
Establish `hx' : xᴴ * JJ n * x = JJ n` using `hx`. Establish `hy' : yᴴ * JJ n * y = JJ n` using `hy`. Use `show (x * y)ᴴ * JJ n * (x * y) = JJ n`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = JJ n := by rw [hx', hy']`.
-/
theorem inG_mul {x y : M2 n} (hx : InG x) (hy : InG y) : InG (x * y) := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have hy' : yᴴ * JJ n * y = JJ n := hy
  show (x * y)ᴴ * JJ n * (x * y) = JJ n
  calc (x * y)ᴴ * JJ n * (x * y) = yᴴ * (xᴴ * JJ n * x) * y := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hx', hy']

/- English proof (translation)
Establish `hp' : pᴴ * JJ n * p = JJ n` using `hp`. Take `⟨c11, c12, c21, c22⟩` from `conjTranspose_toBlocks p`. Take `⟨j11, j12, j21, j22⟩` from `(JJ_toBlocks (n := n))`. Establish `e` using `congrArg Matrix.toBlocks₁₂ hp'`. Rewrite `e` using `[mul_toBlocks₁₂, mul_toBlocks₁₁', mul_toBlocks₁₂, c11, c12, j11, j12, j21, j22, hp21]`.

Simplify using `only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg, neg_zero] at e`. Establish `hq : (p.toBlocks₂₂)ᴴ * p.toBlocks₁₁ = 1`. Use `congrArg Matrix.conjTranspose e` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_mul]`. Unfold `Om`.

Rewrite using `[inverse_second_block_eq_neg_conjTranspose (inG_mul hp hy), inverse_first_block_eq_conjTranspose (inG_mul hp hy), inverse_second_block_eq_neg_conjTranspose hy, inverse_first_block_eq_conjTranspose hy, second_cayley_block_upper_triangular_mul hp21, first_cayley_block_upper_triangu …`.
-/
theorem Om_up {p y : M2 n} (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (hy : InG y) : Om (p * y) = Om y := by
  have hp' : pᴴ * JJ n * p = JJ n := hp
  obtain ⟨c11, c12, c21, c22⟩ := conjTranspose_toBlocks p
  obtain ⟨j11, j12, j21, j22⟩ := (JJ_toBlocks (n := n))
  have e := congrArg Matrix.toBlocks₁₂ hp'
  rw [mul_toBlocks₁₂, mul_toBlocks₁₁', mul_toBlocks₁₂, c11, c12, j11, j12, j21, j22, hp21] at e
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    zero_add, add_zero, Matrix.mul_neg, neg_zero] at e
  have hq : (p.toBlocks₂₂)ᴴ * p.toBlocks₁₁ = 1 := by
    have := congrArg Matrix.conjTranspose e
    simpa [Matrix.conjTranspose_mul] using this
  unfold Om
  rw [inverse_second_block_eq_neg_conjTranspose (inG_mul hp hy), inverse_first_block_eq_conjTranspose (inG_mul hp hy), inverse_second_block_eq_neg_conjTranspose hy, inverse_first_block_eq_conjTranspose hy, second_cayley_block_upper_triangular_mul hp21, first_cayley_block_upper_triangular_mul hp21,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv hq,
    Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (p.toBlocks₂₂)ᴴ, hq, Matrix.one_mul]

def lam (m : ℕ) (e : ℤ) (z : ℂ) (p : M2 n) : ℂ :=
  p.det ^ e * (p.toBlocks₂₂).det ^ (-(m : ℤ)) * ((Complex.normSq (p.toBlocks₂₂).det : ℝ) : ℂ) ^ (-z)

/- English proof (translation)
Establish `h1 : (u1 (p * y)).det = (p.toBlocks₂₂).det * (u1 y).det` using `by rw [first_cayley_block_upper_triangular_mul hp21, Matrix.det_mul]`. Establish `h2 : (u1 (p * y)).det * (ub1 (p * y)).det = ((Complex.normSq (p.toBlocks₂₂).det : ℝ) : ℂ) * ((Complex.normSq (u1 y).det : ℝ) : ℂ)`. Rewrite using `[inverse_first_block_eq_conjTranspose (inG_mul hp hy), Matrix.det_conjTranspose, h1, star_mul', Complex.star_def, Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : (u1 y).det * (ub1 y).det = ((Complex.normSq (u1 y).det : ℝ) : ℂ)`.

Rewrite using `[inverse_first_block_eq_conjTranspose hy, Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_eq_conj_mul_self]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [fz, lam]`. Rewrite using `[h2, h3, h1, Matrix.det_mul, mul_zpow, mul_zpow, Complex.mul_cpow_ofReal_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fz_up {p y : M2 n} (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (hy : InG y) (m : ℕ) (e : ℤ) (z : ℂ) :
    fz m e z (p * y) = lam m e z p * fz m e z y := by
  have h1 : (u1 (p * y)).det = (p.toBlocks₂₂).det * (u1 y).det := by rw [first_cayley_block_upper_triangular_mul hp21, Matrix.det_mul]
  have h2 : (u1 (p * y)).det * (ub1 (p * y)).det =
      ((Complex.normSq (p.toBlocks₂₂).det : ℝ) : ℂ) * ((Complex.normSq (u1 y).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_conjTranspose (inG_mul hp hy), Matrix.det_conjTranspose, h1, star_mul', Complex.star_def,
      Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    ring
  have h3 : (u1 y).det * (ub1 y).det = ((Complex.normSq (u1 y).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_conjTranspose hy, Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    ring
  simp only [fz, lam]
  rw [h2, h3, h1, Matrix.det_mul, mul_zpow, mul_zpow,
    Complex.mul_cpow_ofReal_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)]
  ring

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
