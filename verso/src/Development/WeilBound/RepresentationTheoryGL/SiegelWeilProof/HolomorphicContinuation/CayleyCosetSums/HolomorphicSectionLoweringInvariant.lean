import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DifferentiableAtFirstCayleyBlock

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `hl : HasDerivAt (fun τ : ℂ => x + τ • v) v 0` using `(((hasDerivAt_id' (0:ℂ)).smul_const v).const_add x).congr_deriv (one_smul ℂ v)`. Establish `h1` using `hf.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℂ) hl (by simp)`. Establish `h2 : HasDerivAt (f ∘ fun τ : ℂ => x + τ • v) 0 0`. Establish `e : (f ∘ fun τ : ℂ => x + τ • v) = fun _ => f x` using `funext fun τ => hc τ`. Rewrite using `[e]`.

Conclude with `hasDerivAt_const _ _`. Conclude with `h1.unique h2`.
-/
theorem fderiv_line_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : M2 n → E} {x : M2 n}
    (hf : DifferentiableAt ℂ f x) (v : M2 n) (hc : ∀ τ : ℂ, f (x + τ • v) = f x) : fderiv ℂ f x v = 0 := by
  have hl : HasDerivAt (fun τ : ℂ => x + τ • v) v 0 :=
    (((hasDerivAt_id' (0:ℂ)).smul_const v).const_add x).congr_deriv (one_smul ℂ v)
  have h1 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℂ) hl (by simp)
  have h2 : HasDerivAt (f ∘ fun τ : ℂ => x + τ • v) 0 0 := by
    have e : (f ∘ fun τ : ℂ => x + τ • v) = fun _ => f x := funext fun τ => hc τ
    rw [e]
    exact hasDerivAt_const _ _
  exact h1.unique h2

/- English proof (translation)
Rewrite using `[mX_low, lowQ_smul, mul_add, mul_one, Matrix.mul_smul]`.
-/
theorem line_low (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) :
    x + τ • (x * lowQ Q) = x * mX 1 (τ • Q) 0 1 := by
  rw [mX_low, lowQ_smul, mul_add, mul_one, Matrix.mul_smul]

/- English proof (translation)
Rewrite using `[zOfE_eq, zOfE_eq, first_cayley_block_mul_block, Nm_mX]`. Simplify using the standard rewrite rules.
-/
theorem zOfE_low (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) : zOfE (x * mX 1 Q 0 1) = zOfE x := by
  rw [zOfE_eq, zOfE_eq, first_cayley_block_mul_block, Nm_mX]; simp

/- English proof (translation)
Unfold `holomorphicScalarSection`. Simplify using `only [Matrix.det_mul, det_mX_low, first_cayley_block_mul_block, mul_one, mul_zero, add_zero]`.
-/
theorem holomorphic_section_lowering_invariant (m : ℕ) (e : ℤ) (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) : holomorphicScalarSection m e (x * mX 1 Q 0 1) = holomorphicScalarSection m e x := by
  unfold holomorphicScalarSection
  simp only [Matrix.det_mul, det_mX_low, first_cayley_block_mul_block, mul_one, mul_zero, add_zero]

/- English proof (translation)
The claim follows from `fderiv_line_zero (da_zOfE x h) _ fun τ => by rw [line_low, zOfE_low]`.
-/
theorem fderiv_zOfE_low (x : M2 n) (h : (u1 x).det ≠ 0) (Q : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℂ zOfE x (x * lowQ Q) = 0 :=
  fderiv_line_zero (da_zOfE x h) _ fun τ => by rw [line_low, zOfE_low]

/- English proof (translation)
The claim follows from `fderiv_line_zero (da_F0E m e x h0 h) _ fun τ => by rw [line_low, holomorphic_section_lowering_invariant]`.
-/
theorem fderiv_F0E_low (m : ℕ) (e : ℤ) (x : M2 n) (h0 : x.det ≠ 0) (h : (u1 x).det ≠ 0)
    (Q : Matrix (Fin n) (Fin n) ℂ) : fderiv ℂ (holomorphicScalarSection m e) x (x * lowQ Q) = 0 :=
  fderiv_line_zero (da_F0E m e x h0 h) _ fun τ => by rw [line_low, holomorphic_section_lowering_invariant]

/- English proof (translation)
Rewrite using `[lowQ_eq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]`. Apply the tactic sequence `congr 1 <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] <;> ring_nf <;>`. Apply the tactic sequence `simp [Complex.I_sq] <;> ring`.
-/
theorem low_blocks (R : Matrix (Fin n) (Fin n) ℂ) :
    lowQ R = fromBlocks ((-1 / 2 : ℂ) • R) ((Complex.I / 2) • R) ((Complex.I / 2) • R) ((1 / 2 : ℂ) • R) := by
  rw [lowQ_eq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

def raiseR (S : Matrix (Fin n) (Fin n) ℂ) : M2 n := mX 1 0 S 1 - 1

/- English proof (translation)
Unfold `Cm Cmi`. Rewrite using `[Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]`. Apply the tactic sequence `congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring`.
-/
private theorem Cm_mul_Cmi : Cm n * Cmi n = 1 := by
  unfold Cm Cmi
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/- English proof (translation)
Establish `hinv : (Cm n)⁻¹ = Cmi n` using `Matrix.inv_eq_right_inv Cm_mul_Cmi`. Establish `hb : (fromBlocks 1 0 S 1 : M2 n) = fromBlocks 0 0 S 0 + 1`. Rewrite using `[← Matrix.fromBlocks_one, Matrix.fromBlocks_add]`. Simplify using the standard rewrite rules. Unfold `raiseR mX`.

Rewrite using `[hinv, hb, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Cm_mul_Cmi, add_sub_cancel_right]`.
-/
theorem raise_eq (S : Matrix (Fin n) (Fin n) ℂ) : raiseR S = Cm n * fromBlocks 0 0 S 0 * Cmi n := by
  have hinv : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_right_inv Cm_mul_Cmi
  have hb : (fromBlocks 1 0 S 1 : M2 n) = fromBlocks 0 0 S 0 + 1 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
    simp
  unfold raiseR mX
  rw [hinv, hb, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Cm_mul_Cmi, add_sub_cancel_right]

/- English proof (translation)
Rewrite using `[raise_eq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]`. Apply the tactic sequence `congr 1 <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] <;> ring_nf <;>`. Apply the tactic sequence `simp [Complex.I_sq] <;> ring`.
-/
theorem raise_blocks (S : Matrix (Fin n) (Fin n) ℂ) :
    raiseR S = fromBlocks ((-1 / 2 : ℂ) • S) ((-Complex.I / 2) • S) ((-Complex.I / 2) • S) ((1 / 2 : ℂ) • S) := by
  rw [raise_eq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

/- English proof (translation)
Rewrite using `[sig_eq]`. Unfold `JJ`. Simplify using `[Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]`.
-/
theorem sig_fromBlocks (A B C D : Matrix (Fin n) (Fin n) ℂ) :
    sig (fromBlocks A B C D) = fromBlocks (-Dᴴ) Bᴴ Cᴴ (-Aᴴ) := by
  rw [sig_eq]
  unfold JJ
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

/- English proof (translation)
Rewrite using `[low_blocks, raise_blocks, sig_fromBlocks]`. Simplify using `only [Matrix.conjTranspose_smul]`. Apply the tactic sequence `congr 1 <;> ext i j <;> simp [Matrix.smul_apply] <;> ring_nf <;> simp [Complex.conj_I] <;> ring_nf`.
-/
theorem sig_low (R : Matrix (Fin n) (Fin n) ℂ) : sig (lowQ R) = raiseR Rᴴ := by
  rw [low_blocks, raise_blocks, sig_fromBlocks]
  simp only [Matrix.conjTranspose_smul]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply] <;> ring_nf <;> simp [Complex.conj_I] <;> ring_nf

/- English proof (translation)
Rewrite using `[raise_blocks, raise_blocks, Matrix.fromBlocks_smul]`. Apply the tactic sequence `congr 1 <;> exact smul_comm _ _ _`.
-/
theorem raiseR_smul (c : ℂ) (S : Matrix (Fin n) (Fin n) ℂ) : raiseR (c • S) = c • raiseR S := by
  rw [raise_blocks, raise_blocks, Matrix.fromBlocks_smul]
  congr 1 <;> exact smul_comm _ _ _

/- English proof (translation)
Establish `: mX 1 0 (τ • S) 1 = 1 + raiseR (τ • S)` using `by rw [raiseR]; abel`. Rewrite using `[this, raiseR_smul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]`.
-/
theorem line_raise (x : M2 n) (S : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) :
    x + τ • (x * raiseR S) = x * mX 1 0 (τ • S) 1 := by
  have : mX 1 0 (τ • S) 1 = 1 + raiseR (τ • S) := by rw [raiseR]; abel
  rw [this, raiseR_smul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]

end PositivityTheory.Rg.Sw.HSt.CR
