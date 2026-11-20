import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianSumFrames
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LeftInverseThreeBlocks
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SpanPreservation
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecomp

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm.RealDecompW

open Formalism.L2.SG.RealObj

section Ker

variable {r : ℕ}

/- English proof (translation)
Unfold `Dl`. Rewrite using `[dif_pos le_rfl]`. Simplify using the standard rewrite rules.
-/
theorem realDecompW_dl_top (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Dl Z (r + 1) = Z.det := by
  unfold Dl
  rw [dif_pos le_rfl]
  simp

/- English proof (translation)
Unfold `Dl`. Rewrite using `[dif_pos (Nat.le_succ r)]`. Both sides reduce to the same expression.
-/
theorem realDecompW_dl_r (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Dl Z r = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold Dl
  rw [dif_pos (Nat.le_succ r)]
  rfl

/- English proof (translation)
Establish `h1 : ((-1 : ℂ)) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1`. Rewrite using `[Fin.val_last]`. Conclude with `Even.neg_one_pow ⟨r, rfl⟩`. Rewrite using `[Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, realDecompW_dl_r, h1, one_mul]`.
-/
theorem realDecompW_adj_last (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    adjugate Z (Fin.last r) (Fin.last r) = Dl Z r := by
  have h1 : ((-1 : ℂ)) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1 := by
    rw [Fin.val_last]
    exact Even.neg_one_pow ⟨r, rfl⟩
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, realDecompW_dl_r, h1, one_mul]

/- English proof (translation)
Rewrite using `[← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply, realDecompW_adj_last]`.
-/
theorem realDecompW_adjH_last (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    (adjugate Zᴴ) (Fin.last r) (Fin.last r) = star (Dl Z r) := by
  rw [← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply, realDecompW_adj_last]

/- English proof (translation)
Establish `hZβ : Z *ᵥ β = fun a => if a = Fin.last r then (T : ℂ) * α (Fin.last r) else 0`. Use function extensionality and compare the values at `a`. Establish `h` using `h1 a`. Simplify using `only [Matrix.mulVec, dotProduct]`. Apply the tactic sequence `split_ifs at h ⊢ <;> linear_combination h`.

Establish `hZα : Zᴴ *ᵥ α = fun a => if a = Fin.last r then (T' : ℂ) * β (Fin.last r) else 0`. Use function extensionality and compare the values at `a`. Establish `h` using `h2 a`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]`. Apply the tactic sequence `split_ifs at h ⊢ <;> linear_combination h`.

Establish `key : ∀ (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (v : Fin (r + 1) → ℂ) (c : ℂ), A *ᵥ v = (fun a => if a = Fin.last r then c else 0) → ∀ i, A.det * v i = A.adjugate i (Fin.last r) * c`. Introduce `A v c hv i`. Establish `e : A.adjugate *ᵥ (A *ᵥ v) = A.det • v`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.adjugate_mul]`. Use extensionality with `j`.

Simplify using `[Matrix.mulVec, dotProduct, Matrix.one_apply]`. Establish `e2` using `congrFun e i`. Rewrite `e2` using `[hv]`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e2`. Conclude with `e2.symm`.

Establish `hβ` using `key Z β _ hZβ`. Establish `hα` using `key Zᴴ α _ hZα`. Establish `hβL` using `hβ (Fin.last r)`. Establish `hαL` using `hα (Fin.last r)`. Rewrite `hβL` using `[realDecompW_adj_last]`.

Rewrite `hαL` using `[realDecompW_adjH_last, Matrix.det_conjTranspose]`. Establish `e1 : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ)` using `fun z => by`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Unfold `Gv at hG`. Rewrite `hG` using `[realDecompW_dl_top]`.

Establish `hc : Z.det * star Z.det - (T : ℂ) * T' * (Dl Z r * star (Dl Z r)) ≠ 0`. Rewrite using `[e1, e1]`. Establish `e5 : ((‖Z.det‖ ^ 2 : ℝ) : ℂ) - (T : ℂ) * T' * ((‖Dl Z r‖ ^ 2 : ℝ) : ℂ) = ((‖Z.det‖ ^ 2 - T * T' * ‖Dl Z r‖ ^ 2 : ℝ) : ℂ)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e5, Ne, Complex.ofReal_eq_zero]`. Conclude with `hG`. Establish `hbL : β (Fin.last r) = 0`. Establish `h : (Z.det * star Z.det - (T : ℂ) * T' * (Dl Z r * star (Dl Z r))) * β (Fin.last r) = 0`. Take the linear combination `(star Z.det) * hβL + Dl Z r * (T : ℂ) * hαL`.

Conclude with `(mul_eq_zero.mp h).resolve_left hc`. Establish `haL : α (Fin.last r) = 0`. Establish `h : (Z.det * star Z.det - (T : ℂ) * T' * (Dl Z r * star (Dl Z r))) * α (Fin.last r) = 0`. Take the linear combination `Z.det * hαL + star (Dl Z r) * (T' : ℂ) * hβL`. Conclude with `(mul_eq_zero.mp h).resolve_left hc`.

Distinguish the cases in `hd : Z.det = 0`. Establish `hm : Dl Z r ≠ 0`. Introduce `hm`. Apply `hG` to reduce the goal to its premises. Rewrite using `[hd, hm]`.

Simplify using the standard rewrite rules. Rewrite `hm` using `[realDecompW_dl_r]`. Establish `hβ' : (Z.submatrix Fin.castSucc Fin.castSucc) *ᵥ (fun b => β (Fin.castSucc b)) = 0`. Use function extensionality and compare the values at `a`. Establish `h` using `h1 (Fin.castSucc a)`.

Rewrite `h` using `[if_neg (Fin.castSucc_lt_last a).ne, zero_add, Fin.sum_univ_castSucc, hbL, mul_zero, add_zero]`. Simplify `h` using `[Matrix.mulVec, dotProduct]`. Establish `hα' : (Z.submatrix Fin.castSucc Fin.castSucc)ᴴ *ᵥ (fun b => α (Fin.castSucc b)) = 0`. Use function extensionality and compare the values at `a`. Establish `h` using `h2 (Fin.castSucc a)`.

Rewrite `h` using `[if_neg (Fin.castSucc_lt_last a).ne, add_zero, Fin.sum_univ_castSucc, haL, mul_zero, add_zero]`. Simplify `h` using `[Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]`. Establish `e3` using `Matrix.eq_zero_of_mulVec_eq_zero hm hβ'`. Establish `e4` using `Matrix.eq_zero_of_mulVec_eq_zero (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr hm) hα'`. Prove the components needed by the constructor for the conclusion.

Use function extensionality and compare the values at `i`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => exact haL`. Consider the case `cast j => exact congrFun e4 j`. Use function extensionality and compare the values at `i`.

Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => exact hbL`. Consider the case `cast j => exact congrFun e3 j`. Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `i`.

Establish `h` using `hα i`. Rewrite `h` using `[hbL, mul_zero, mul_zero, Matrix.det_conjTranspose]`. Conclude with `(mul_eq_zero.mp h).resolve_left (star_ne_zero.mpr hd)`. Use function extensionality and compare the values at `i`. Establish `h` using `hβ i`.

Rewrite `h` using `[haL, mul_zero, mul_zero]`. Conclude with `(mul_eq_zero.mp h).resolve_left hd`.
-/
theorem ker_triv (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (T T' : ℝ) (hG : Gv T T' Z ≠ 0)
    (α β : Fin (r + 1) → ℂ)
    (h1 : ∀ a, (if a = Fin.last r then -(T : ℂ) * α (Fin.last r) else 0) + ∑ b, Z a b * β b = 0)
    (h2 : ∀ a, ∑ b, star (Z b a) * α b + (if a = Fin.last r then -(T' : ℂ) * β (Fin.last r) else 0) = 0) :
    α = 0 ∧ β = 0 := by
  have hZβ : Z *ᵥ β = fun a => if a = Fin.last r then (T : ℂ) * α (Fin.last r) else 0 := by
    funext a
    have h := h1 a
    simp only [Matrix.mulVec, dotProduct]
    split_ifs at h ⊢ <;> linear_combination h
  have hZα : Zᴴ *ᵥ α = fun a => if a = Fin.last r then (T' : ℂ) * β (Fin.last r) else 0 := by
    funext a
    have h := h2 a
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
    split_ifs at h ⊢ <;> linear_combination h
  have key : ∀ (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (v : Fin (r + 1) → ℂ) (c : ℂ),
      A *ᵥ v = (fun a => if a = Fin.last r then c else 0) →
        ∀ i, A.det * v i = A.adjugate i (Fin.last r) * c := by
    intro A v c hv i
    have e : A.adjugate *ᵥ (A *ᵥ v) = A.det • v := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
      ext j
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
    have e2 := congrFun e i
    rw [hv] at e2
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at e2
    exact e2.symm
  have hβ := key Z β _ hZβ
  have hα := key Zᴴ α _ hZα
  have hβL := hβ (Fin.last r)
  have hαL := hα (Fin.last r)
  rw [realDecompW_adj_last] at hβL
  rw [realDecompW_adjH_last, Matrix.det_conjTranspose] at hαL
  have e1 : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold Gv at hG
  rw [realDecompW_dl_top] at hG
  have hc : Z.det * star Z.det - (T : ℂ) * T' * (Dl Z r * star (Dl Z r)) ≠ 0 := by
    rw [e1, e1]
    have e5 : ((‖Z.det‖ ^ 2 : ℝ) : ℂ) - (T : ℂ) * T' * ((‖Dl Z r‖ ^ 2 : ℝ) : ℂ) =
        ((‖Z.det‖ ^ 2 - T * T' * ‖Dl Z r‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e5, Ne, Complex.ofReal_eq_zero]
    exact hG
  have hbL : β (Fin.last r) = 0 := by
    have h : (Z.det * star Z.det - (T : ℂ) * T' * (Dl Z r * star (Dl Z r))) * β (Fin.last r) = 0 := by
      linear_combination (star Z.det) * hβL + Dl Z r * (T : ℂ) * hαL
    exact (mul_eq_zero.mp h).resolve_left hc
  have haL : α (Fin.last r) = 0 := by
    have h : (Z.det * star Z.det - (T : ℂ) * T' * (Dl Z r * star (Dl Z r))) * α (Fin.last r) = 0 := by
      linear_combination Z.det * hαL + star (Dl Z r) * (T' : ℂ) * hβL
    exact (mul_eq_zero.mp h).resolve_left hc
  by_cases hd : Z.det = 0
  · have hm : Dl Z r ≠ 0 := by
      intro hm
      apply hG
      rw [hd, hm]
      simp
    rw [realDecompW_dl_r] at hm
    have hβ' : (Z.submatrix Fin.castSucc Fin.castSucc) *ᵥ (fun b => β (Fin.castSucc b)) = 0 := by
      funext a
      have h := h1 (Fin.castSucc a)
      rw [if_neg (Fin.castSucc_lt_last a).ne, zero_add, Fin.sum_univ_castSucc, hbL, mul_zero,
        add_zero] at h
      simpa [Matrix.mulVec, dotProduct] using h
    have hα' : (Z.submatrix Fin.castSucc Fin.castSucc)ᴴ *ᵥ (fun b => α (Fin.castSucc b)) = 0 := by
      funext a
      have h := h2 (Fin.castSucc a)
      rw [if_neg (Fin.castSucc_lt_last a).ne, add_zero, Fin.sum_univ_castSucc, haL, mul_zero,
        add_zero] at h
      simpa [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply] using h
    have e3 := Matrix.eq_zero_of_mulVec_eq_zero hm hβ'
    have e4 := Matrix.eq_zero_of_mulVec_eq_zero
      (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr hm) hα'
    constructor
    · funext i
      induction i using Fin.lastCases with
      | last => exact haL
      | cast j => exact congrFun e4 j
    · funext i
      induction i using Fin.lastCases with
      | last => exact hbL
      | cast j => exact congrFun e3 j
  · constructor
    · funext i
      have h := hα i
      rw [hbL, mul_zero, mul_zero, Matrix.det_conjTranspose] at h
      exact (mul_eq_zero.mp h).resolve_left (star_ne_zero.mpr hd)
    · funext i
      have h := hβ i
      rw [haL, mul_zero, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hd

end Ker

section Witt

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries

variable {n r : ℕ} (ε : Fin n → Bool)

/- English proof (translation)
Use `set f := famSc sc e z with hf`. Use `set f' := famSc sc e z' with hf'`. Use `set M := Formalism.MainNotions.S.uMat g with hM`. Use `set M' := Formalism.MainNotions.S.uMat g' with hM'`. Use `set Z := Zhat ε f f' M with hZdef`.

Establish `hz1 : ∀ a b, hJ ε (f a) (M *ᵥ f' b) = Z a b` using `fun a b => rfl`. Establish `hz2 : ∀ a b, hJ ε (f a) (M' *ᵥ f' b) = Z a b` using `fun a b => (congrFun (congrFun hZ a) b).symm`. Establish `FourierUniquenessMirabolic : ∀ a b, hJ ε (f a) (f b) = if a = Fin.last r ∧ b = Fin.last r then -(T : ℂ) else 0` using `hJ_famSc ε sc e z (T : ℂ) hee hez hzz`. Establish `G22 : ∀ a b, hJ ε (M *ᵥ f' a) (M *ᵥ f' b) = if a = Fin.last r ∧ b = Fin.last r then -(T' : ℂ) else 0` using `fun a b => by rw [isIsom_uMat ε g]; exact hJ_famSc ε sc e z' (T' : ℂ) hee hez' hzz' a b`. Establish `G21 : ∀ a b, hJ ε (M *ᵥ f' a) (f b) = star (Z b a)` using `fun a b => by`.

Rewrite using `[hJ_conj, hz1]`. Both sides reduce to the same expression. Set `x : Fin (r + 1) ⊕ Fin (r + 1) → Fin n → ℂ` to `Sum.elim f (fun b => M *ᵥ f' b)`. Set `y : Fin (r + 1) ⊕ Fin (r + 1) → Fin n → ℂ` to `Sum.elim f (fun b => M' *ᵥ f' b)`. Establish `hG' : ∀ i j, hJ ε (x i) (x j) = hJ ε (y i) (y j)`.

Introduce and unpack `(a | a) (b | b)`. Both sides reduce to the same expression. Use `show hJ ε (f a) (M *ᵥ f' b) = hJ ε (f a) (M' *ᵥ f' b)`. Rewrite using `[hz1, hz2]`. Use `show hJ ε (M *ᵥ f' a) (f b) = hJ ε (M' *ᵥ f' a) (f b)`.

Rewrite using `[hJ_conj, hz1, hJ_conj ε (M' *ᵥ f' a), hz2]`. Use `show hJ ε (M *ᵥ f' a) (M *ᵥ f' b) = hJ ε (M' *ᵥ f' a) (M' *ᵥ f' b)`. Rewrite using `[isIsom_uMat ε g, isIsom_uMat ε g']`. Establish `hnd : (Matrix.of fun i j => hJ ε (x i) (x j)).det ≠ 0`. Introduce `hdet`.

Take `⟨w, hw0, hw⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Apply `hw0` to reduce the goal to its premises. Establish `E1 : ∀ a, (if a = Fin.last r then -(T : ℂ) * w (Sum.inl (Fin.last r)) else 0) + ∑ b, Z a b * w (Sum.inr b) = 0`. Introduce `a`. Use `congrFun hw (Sum.inl a)` as an intermediate fact.

Simplify using `only [mulVec, dotProduct, Fintype.sum_sum_type, of_apply, Pi.zero_apply] at this`. Express the relevant statement in the definitionally equal form `(∑ b, hJ ε (f a) (f b) * w (Sum.inl b)) + (∑ b, hJ ε (f a) (M *ᵥ f' b) * w (Sum.inr b)) = 0 at this`. Simplify using `only [FourierUniquenessMirabolic, hz1, ite_mul, zero_mul, ite_and] at this`. Distinguish the cases in `ha : a = Fin.last r`. Substitute `ha` using the available equality.

Simplify using `using this`. Simplify `this` using `[ha]`. Establish `E2 : ∀ a, ∑ b, star (Z b a) * w (Sum.inl b) + (if a = Fin.last r then -(T' : ℂ) * w (Sum.inr (Fin.last r)) else 0) = 0`. Introduce `a`. Use `congrFun hw (Sum.inr a)` as an intermediate fact.

Simplify using `only [mulVec, dotProduct, Fintype.sum_sum_type, of_apply, Pi.zero_apply] at this`. Express the relevant statement in the definitionally equal form `(∑ b, hJ ε (M *ᵥ f' a) (f b) * w (Sum.inl b)) + (∑ b, hJ ε (M *ᵥ f' a) (M *ᵥ f' b) * w (Sum.inr b)) = 0 at this`. Simplify using `only [G21, G22, ite_mul, zero_mul, ite_and] at this`. Distinguish the cases in `ha : a = Fin.last r`. Substitute `ha` using the available equality.

Simplify using `using this`. Simplify `this` using `[ha]`. Take `⟨h0, h0'⟩` from `ker_triv Z T T' hG (fun b => w (Sum.inl b)) (fun b => w (Sum.inr b)) E1 E2`. Use function extensionality and compare the values at `i`. Break down `i with a | a` into its components or cases.

Conclude with `congrFun h0 a`. Conclude with `congrFun h0' a`. Take `⟨s, hs⟩` from `witt_of_gram' ε x y hG' hnd`. Establish `hse : ∀ a, Formalism.MainNotions.S.uMat s *ᵥ f a = f a` using `fun a => hs (Sum.inl a)`. Establish `hsg : ∀ b, Formalism.MainNotions.S.uMat s *ᵥ (M *ᵥ f' b) = M' *ᵥ f' b` using `fun b => hs (Sum.inr b)`.

Establish `hscale : ∀ a : Fin r, ((sc : ℂ) ^ (r - a.1))⁻¹ ≠ 0` using `fun a => inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hsc))`. Establish `hfix : ∀ (G : Matrix (Fin n) (Fin n) ℂ) (z0 : Fin n → ℂ), (∀ a, G *ᵥ famSc sc e z0 a = famSc sc e z0 a) → InS e z0 G`. Introduce `G z0 h`. Use `inS_of_fix (fun a => ?_) ?_` and prove the remaining obligations. Establish `h1` using `h (Fin.castSucc a)`.

Rewrite `h1` using `[famSc_castSucc, mulVec_smul]`. Conclude with `smul_right_injective _ (hscale a) h1`. Establish `h1` using `h (Fin.last r)`. Rewrite `h1` using `[famSc_last']`. Then use the resulting hypothesis. Establish `hinv : Formalism.MainNotions.S.uMat g'⁻¹ * Formalism.MainNotions.S.uMat g' = 1` using `Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' g'`.

Use `⟨s, g'⁻¹ * s * g, hfix _ z hse, hfix _ z' (fun b => ?_), by group⟩` and prove the remaining obligations. Use `show (Formalism.MainNotions.S.uMat g'⁻¹ * Formalism.MainNotions.S.uMat s * Formalism.MainNotions.S.uMat g) *ᵥ famSc sc e z' b = famSc sc e z' b`. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, ← hM, hsg, mulVec_mulVec, hinv, one_mulVec]`.
-/
theorem dc_of_zhat (sc : ℝ) (hsc : sc ≠ 0) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hez : ∀ a, hJ ε (e a) z = 0) (hez' : ∀ a, hJ ε (e a) z' = 0)
    (hzz : hJ ε z z = -(T : ℂ)) (hzz' : hJ ε z' z' = -(T' : ℂ)) (g g' : Formalism.REAL.UJ ε)
    (hZ : Zhat ε (famSc sc e z) (famSc sc e z') (Formalism.MainNotions.S.uMat g) =
      Zhat ε (famSc sc e z) (famSc sc e z') (Formalism.MainNotions.S.uMat g'))
    (hG : Gv T T' (Zhat ε (famSc sc e z) (famSc sc e z') (Formalism.MainNotions.S.uMat g)) ≠ 0) :
    ∃ s s' : Formalism.REAL.UJ ε, InS e z (Formalism.MainNotions.S.uMat s) ∧ InS e z' (Formalism.MainNotions.S.uMat s') ∧ g' = s * g * s'⁻¹ := by
  set f := famSc sc e z with hf
  set f' := famSc sc e z' with hf'
  set M := Formalism.MainNotions.S.uMat g with hM
  set M' := Formalism.MainNotions.S.uMat g' with hM'
  set Z := Zhat ε f f' M with hZdef
  have hz1 : ∀ a b, hJ ε (f a) (M *ᵥ f' b) = Z a b := fun a b => rfl
  have hz2 : ∀ a b, hJ ε (f a) (M' *ᵥ f' b) = Z a b := fun a b => (congrFun (congrFun hZ a) b).symm
  have FourierUniquenessMirabolic : ∀ a b, hJ ε (f a) (f b) = if a = Fin.last r ∧ b = Fin.last r then -(T : ℂ) else 0 :=
    hJ_famSc ε sc e z (T : ℂ) hee hez hzz
  have G22 : ∀ a b, hJ ε (M *ᵥ f' a) (M *ᵥ f' b) =
      if a = Fin.last r ∧ b = Fin.last r then -(T' : ℂ) else 0 :=
    fun a b => by rw [isIsom_uMat ε g]; exact hJ_famSc ε sc e z' (T' : ℂ) hee hez' hzz' a b
  have G21 : ∀ a b, hJ ε (M *ᵥ f' a) (f b) = star (Z b a) := fun a b => by
    rw [hJ_conj, hz1]; rfl
  let x : Fin (r + 1) ⊕ Fin (r + 1) → Fin n → ℂ := Sum.elim f (fun b => M *ᵥ f' b)
  let y : Fin (r + 1) ⊕ Fin (r + 1) → Fin n → ℂ := Sum.elim f (fun b => M' *ᵥ f' b)
  have hG' : ∀ i j, hJ ε (x i) (x j) = hJ ε (y i) (y j) := by
    rintro (a | a) (b | b)
    · rfl
    · show hJ ε (f a) (M *ᵥ f' b) = hJ ε (f a) (M' *ᵥ f' b)
      rw [hz1, hz2]
    · show hJ ε (M *ᵥ f' a) (f b) = hJ ε (M' *ᵥ f' a) (f b)
      rw [hJ_conj, hz1, hJ_conj ε (M' *ᵥ f' a), hz2]
    · show hJ ε (M *ᵥ f' a) (M *ᵥ f' b) = hJ ε (M' *ᵥ f' a) (M' *ᵥ f' b)
      rw [isIsom_uMat ε g, isIsom_uMat ε g']
  have hnd : (Matrix.of fun i j => hJ ε (x i) (x j)).det ≠ 0 := by
    intro hdet
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    apply hw0
    have E1 : ∀ a, (if a = Fin.last r then -(T : ℂ) * w (Sum.inl (Fin.last r)) else 0) +
        ∑ b, Z a b * w (Sum.inr b) = 0 := by
      intro a
      have := congrFun hw (Sum.inl a)
      simp only [mulVec, dotProduct, Fintype.sum_sum_type, of_apply, Pi.zero_apply] at this
      change (∑ b, hJ ε (f a) (f b) * w (Sum.inl b)) + (∑ b, hJ ε (f a) (M *ᵥ f' b) * w (Sum.inr b)) = 0 at this
      simp only [FourierUniquenessMirabolic, hz1, ite_mul, zero_mul, ite_and] at this
      by_cases ha : a = Fin.last r
      · subst ha; simpa using this
      · simpa [ha] using this
    have E2 : ∀ a, ∑ b, star (Z b a) * w (Sum.inl b) +
        (if a = Fin.last r then -(T' : ℂ) * w (Sum.inr (Fin.last r)) else 0) = 0 := by
      intro a
      have := congrFun hw (Sum.inr a)
      simp only [mulVec, dotProduct, Fintype.sum_sum_type, of_apply, Pi.zero_apply] at this
      change (∑ b, hJ ε (M *ᵥ f' a) (f b) * w (Sum.inl b)) +
        (∑ b, hJ ε (M *ᵥ f' a) (M *ᵥ f' b) * w (Sum.inr b)) = 0 at this
      simp only [G21, G22, ite_mul, zero_mul, ite_and] at this
      by_cases ha : a = Fin.last r
      · subst ha; simpa using this
      · simpa [ha] using this
    obtain ⟨h0, h0'⟩ := ker_triv Z T T' hG (fun b => w (Sum.inl b)) (fun b => w (Sum.inr b)) E1 E2
    funext i
    rcases i with a | a
    · exact congrFun h0 a
    · exact congrFun h0' a
  obtain ⟨s, hs⟩ := witt_of_gram' ε x y hG' hnd
  have hse : ∀ a, Formalism.MainNotions.S.uMat s *ᵥ f a = f a := fun a => hs (Sum.inl a)
  have hsg : ∀ b, Formalism.MainNotions.S.uMat s *ᵥ (M *ᵥ f' b) = M' *ᵥ f' b := fun b => hs (Sum.inr b)
  have hscale : ∀ a : Fin r, ((sc : ℂ) ^ (r - a.1))⁻¹ ≠ 0 := fun a =>
    inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hsc))
  have hfix : ∀ (G : Matrix (Fin n) (Fin n) ℂ) (z0 : Fin n → ℂ),
      (∀ a, G *ᵥ famSc sc e z0 a = famSc sc e z0 a) → InS e z0 G := by
    intro G z0 h
    refine inS_of_fix (fun a => ?_) ?_
    · have h1 := h (Fin.castSucc a)
      rw [famSc_castSucc, mulVec_smul] at h1
      exact smul_right_injective _ (hscale a) h1
    · have h1 := h (Fin.last r)
      rwa [famSc_last'] at h1
  have hinv : Formalism.MainNotions.S.uMat g'⁻¹ * Formalism.MainNotions.S.uMat g' = 1 := Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' g'
  refine ⟨s, g'⁻¹ * s * g, hfix _ z hse, hfix _ z' (fun b => ?_), by group⟩
  show (Formalism.MainNotions.S.uMat g'⁻¹ * Formalism.MainNotions.S.uMat s * Formalism.MainNotions.S.uMat g) *ᵥ famSc sc e z' b = famSc sc e z' b
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← hM, hsg, mulVec_mulVec, hinv, one_mulVec]

end Witt

section Glob

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

/- English proof (translation)
Unfold `ZhatO at h`. Use extensionality with `a b`. Establish `h2` using `congrFun (congrFun h a) b`. Conclude with `mul_right_injective₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h2`.
-/
theorem zhatO_inj {r : ℕ} {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : ZhatO Z = ZhatO Z') : Z = Z' := by
  unfold ZhatO at h
  ext a b
  have h2 := congrFun (congrFun h a) b
  exact mul_right_injective₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h2

/- English proof (translation)
Establish `key : ∀ v, ∃ s s' : Formalism.REAL.UJ (X.B.I.ε v), InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (Formalism.MainNotions.S.uMat s) ∧ InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (Formalism.MainNotions.S.uMat s') ∧ γ' v = s * γ v * s'⁻¹`. Introduce `v`. Establish `hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0` using `fun a b => by`. Rewrite using `[show X.eR a = X.crd (X.eX a) from rfl, show X.eR b = X.crd (X.eX b) from rfl, hJ_rvX, X.ee, map_zero]`. Establish `hez : ∀ (w : D.what₂.Word) a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) = 0` using `fun w a => by`.

Rewrite using `[show X.eR a = X.crd (X.eX a) from rfl, show X.zR w = X.crd (X.zu w) from rfl, hJ_rvX, (X.zu_orth w a).1, map_zero]`. Establish `hZ : ZX X u u' 1 γ v = ZX X u u' 1 γ' v` using `zhatO_inj ((h1 v).trans (h2 v).symm)`. Conclude with `dc_of_zhat (X.B.I.ε v) 1 one_ne_zero _ _ _ (Tw u) (Tw u') hee (hez u) (hez u') (hermitian_z_z_eq_neg X v u) (hermitian_z_z_eq_neg X v u') (γ v) (γ' v) hZ (hG v)`. Use `choose s s' hs hs' heq using key`. Use `⟨s, fun v => hs v, s', fun v => hs' v, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `v`. Conclude with `heq v`.
-/
theorem ptRep_dc (w : Formalism.MainNotions.S.Point D.host.E (D.R.rS + 1)) (γ γ' : X.B.I.Ginf)
    (h1 : IsPtRep X u u' w γ) (h2 : IsPtRep X u u' w γ')
    (hG : ∀ v, Gv (Tw u) (Tw u') (ZX X u u' 1 γ v) ≠ 0) :
    ∃ s ∈ X.SinfU u, ∃ s' ∈ X.SinfU u', γ' = s * γ * s'⁻¹ := by
  have key : ∀ v, ∃ s s' : Formalism.REAL.UJ (X.B.I.ε v),
      InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (Formalism.MainNotions.S.uMat s) ∧
      InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (Formalism.MainNotions.S.uMat s') ∧
      γ' v = s * γ v * s'⁻¹ := by
    intro v
    have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
      rw [show X.eR a = X.crd (X.eX a) from rfl, show X.eR b = X.crd (X.eX b) from rfl, hJ_rvX, X.ee, map_zero]
    have hez : ∀ (w : D.what₂.Word) a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) = 0 :=
      fun w a => by
        rw [show X.eR a = X.crd (X.eX a) from rfl, show X.zR w = X.crd (X.zu w) from rfl, hJ_rvX,
          (X.zu_orth w a).1, map_zero]
    have hZ : ZX X u u' 1 γ v = ZX X u u' 1 γ' v := zhatO_inj ((h1 v).trans (h2 v).symm)
    exact dc_of_zhat (X.B.I.ε v) 1 one_ne_zero _ _ _ (Tw u) (Tw u') hee (hez u) (hez u') (hermitian_z_z_eq_neg X v u)
      (hermitian_z_z_eq_neg X v u') (γ v) (γ' v) hZ (hG v)
  choose s s' hs hs' heq using key
  refine ⟨s, fun v => hs v, s', fun v => hs' v, ?_⟩
  funext v
  exact heq v

end Glob

end Formalism.L2.SG.Pf.RowForm.RealDecompW
