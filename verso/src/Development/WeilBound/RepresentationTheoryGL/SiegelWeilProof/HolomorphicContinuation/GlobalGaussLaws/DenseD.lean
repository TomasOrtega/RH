import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.DenseP

variable {n : ℕ}

/- English proof (translation)
Establish `hJ : JJ n * JJ n = -1`. Rewrite using `[← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]`. Simplify using `[JJ, Matrix.fromBlocks_multiply]`. Establish `h1 : (JJ n).det * (JJ n).det = (-1 : ℂ) ^ (Fintype.card (Fin n ⊕ Fin n))`. Rewrite using `[← Matrix.det_mul, hJ, Matrix.det_neg, Matrix.det_one, mul_one]`.

Establish `hJd : (JJ n).det ≠ 0`. Introduce `h0`. Rewrite `h1` using `[h0, zero_mul]`. Conclude with `(pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h1.symm`. Establish `e` using `congrArg Matrix.det hg`.

Rewrite `e` using `[Matrix.det_mul, Matrix.det_mul]`. Use `isUnit_iff_ne_zero.2 fun h0 => hJd ?_` and prove the remaining obligations. Rewrite `e` using `[h0, mul_zero]`. Conclude with `e.symm`.
-/
theorem isUnit_det_of_inG {g : M2 n} (hg : InG g) : IsUnit g.det := by
  have hJ : JJ n * JJ n = -1 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp [JJ, Matrix.fromBlocks_multiply]
  have h1 : (JJ n).det * (JJ n).det = (-1 : ℂ) ^ (Fintype.card (Fin n ⊕ Fin n)) := by
    rw [← Matrix.det_mul, hJ, Matrix.det_neg, Matrix.det_one, mul_one]
  have hJd : (JJ n).det ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h1.symm
  have e := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul] at e
  refine isUnit_iff_ne_zero.2 fun h0 => hJd ?_
  rw [h0, mul_zero] at e
  exact e.symm

def mkGR (g : M2 n) (hg : InG g) : GR n :=
  ⟨⟨g, g⁻¹, Matrix.mul_nonsing_inv g (isUnit_det_of_inG hg), Matrix.nonsing_inv_mul g (isUnit_det_of_inG hg)⟩, hg⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem mR_mkGR (g : M2 n) (hg : InG g) : mR (mkGR g hg) = g := rfl

def IsNElt (g : GR n) : Prop := ∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR g = nU b

def IsMElt (g : GR n) : Prop :=
  ∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR g = fromBlocks a 0 0 (a⁻¹)ᴴ

def IsWElt (g : GR n) : Prop := mR g = JJ n

def GenSt : Prop :=
  ∀ n : ℕ, ∀ g : GR n, g ∈ Subgroup.closure {h : GR n | IsNElt h ∨ IsMElt h ∨ IsWElt h}

end PositivityTheory.Rg.Sw.Glob.DenseP
