import Formalism.LocalToGlobal.GlobalTheory.GL4.Statement
import Formalism.LocalToGlobal.GlobalTheory.GL4.PLinks
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Interlace
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockbLemmas

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

def BranchingIntegralAt (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n) (T : ℕ) (G : GL (Fin (n + 1)) ℂ) : Prop :=
    ∃ P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ,
      (∀ f ∈ delSq ℂ (n + 1) lt, P f ∈ delSq ℂ n sg) ∧
      (∃ f ∈ delSq ℂ (n + 1) lt, P f ≠ 0) ∧
      (∀ f ∈ delSq ℤ (n + 1) lt, ∃ g ∈ delSq ℤ n sg,
        P (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g) ∧
      (∀ (g : GL (Fin n) ℂ) (H : GL (Fin (n + 1)) ℂ),
        (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = blockMat (g : Matrix (Fin n) (Fin n) ℂ) →
        ∀ f ∈ delSq ℂ (n + 1) lt, P (sqAct ℂ (n + 1) lt H f) = sqAct ℂ n sg g (P f)) ∧
      (∀ f ∈ delSq ℂ (n + 1) lt,
        (normFock sg (P f) (P f)).re ≤
          Real.exp (-(degP lt sg : ℝ) * Real.log T) *
            ((((Formalism.BranchingDeterminantCap.cCap lt.w sg.w : ℤ) : ℝ) ^ 2) * dimV lt.w) * normTil lt G f)

def BranchingIntegral : Prop :=
  ∀ (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n), Interlace lt sg →
    ∀ (T : ℕ), 0 < T →
    ∀ (G : GL (Fin (n + 1)) ℂ), (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T → BranchingIntegralAt n lt sg T G

def BranchingIntegralNormalised : Prop :=
  ∀ (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n), lt.w (Fin.last n) = 0 → Interlace lt sg →
    ∀ (T : ℕ), 0 < T →
    ∀ (G : GL (Fin (n + 1)) ℂ), (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T → BranchingIntegralAt n lt sg T G

/- English proof (translation)
Unfold `dimV`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `j hj`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hj`. Establish `h1 : lam.w j ≤ lam.w i` using `lam.anti hj.le`. Establish `h2 : (i : ℕ) < (j : ℕ)` using `hj`. Apply `div_pos` to reduce the goal to its premises. Establish `: (0 : ℤ) < lam.w i - lam.w j + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)` using `by omega`.

Conclude with `this` after adjusting the coercions. Establish `: (0 : ℤ) < ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
theorem dimV_pos {N : ℕ} (lam : DomWeight N) : 0 < dimV lam.w := by
  unfold dimV
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have h1 : lam.w j ≤ lam.w i := lam.anti hj.le
  have h2 : (i : ℕ) < (j : ℕ) := hj
  apply div_pos
  · have : (0 : ℤ) < lam.w i - lam.w j + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := by omega
    exact_mod_cast this
  · have : (0 : ℤ) < ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := by omega
    exact_mod_cast this

/- English proof (translation)
Unfold `normFock`. Rewrite using `[Formalism.GradedWeylDivisibility.LFockb_fockF_self, Formalism.GradedWeylDivisibility.LFockb_fockF_self, ← Complex.ofReal_div, Complex.ofReal_re]`. Conclude with `div_nonneg (Finset.sum_nonneg fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)) (Finset.sum_nonneg fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _))`.
-/
theorem normFock_self_re_nonneg {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    0 ≤ (normFock lam f f).re := by
  unfold normFock
  rw [Formalism.GradedWeylDivisibility.LFockb_fockF_self, Formalism.GradedWeylDivisibility.LFockb_fockF_self, ← Complex.ofReal_div, Complex.ofReal_re]
  exact div_nonneg (Finset.sum_nonneg fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _))

/- English proof (translation)
The claim follows from `normFock_self_re_nonneg lt _`.
-/
theorem normTil_nonneg {n : ℕ} (lt : DomWeight (n + 1)) (G : GL (Fin (n + 1)) ℂ)
    (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) : 0 ≤ normTil lt G f :=
  normFock_self_re_nonneg lt _

/- English proof (translation)
Unfold `DomWeight.spread`. Rewrite using `[dif_pos (Nat.succ_pos n)]`. Establish `: (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n` using `Fin.ext (by simp)`. Rewrite using `[this]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem spread_eq {n : ℕ} (lt : DomWeight (n + 1)) :
    lt.spread = lt.w 0 - lt.w (Fin.last n) + ((n : ℤ) + 1) := by
  unfold DomWeight.spread
  rw [dif_pos (Nat.succ_pos n)]
  have : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  rw [this]
  push_cast
  rfl

/- English proof (translation)
Establish `hI' : Formalism.BranchingDeterminantCap.Interlace lt.w sg.w` using `fun i => ⟨(hI i).2, (hI i).1⟩`. Take `⟨_, hc⟩` from `Formalism.BranchingDeterminantCap.capacity_constant_bound n lt.w sg.w hI'`. Establish `hd1 : 0 ≤ Formalism.BranchingDeterminantCap.d1 lt.w sg.w` using `(Formalism.BranchingDeterminantCap.interlaceIdentities n lt.w sg.w hI').2.2.2.1`. Establish `hsum : (∑ i : Fin n, (min (lenP lt i) (baseWeightDifference lt sg) : ℝ)) = ((Formalism.BranchingDeterminantCap.d1 lt.w sg.w : ℤ) : ℝ)`. Unfold `Formalism.BranchingDeterminantCap.d1 Formalism.BranchingDeterminantCap.d0 lenP baseWeightDifference`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hpos` using `dimV_pos lt`. Rewrite using `[Real.exp_add, Real.exp_log hpos]`. Apply `mul_le_mul_of_nonneg_right _ hpos.le` to reduce the goal to its premises.

Use `set c := Formalism.BranchingDeterminantCap.cCap lt.w sg.w with hcdef`. Use `set k := n * (Formalism.BranchingDeterminantCap.d1 lt.w sg.w).toNat with hk`. Use `set W : ℤ := lt.w 0 - lt.w (Fin.last n) + ((n : ℤ) + 1) with hW`. Establish `hanti : lt.w (Fin.last n) ≤ lt.w 0` using `lt.anti (Fin.zero_le _)`. Establish `hWpos : 0 < W` using `by omega`.

Establish `hBW : (lt.w 0 - lt.w (Fin.last n) + (n : ℤ) - 1) ^ k ≤ W ^ k`. Break down `Nat.eq_zero_or_pos k with h0 | h0` into its components or cases. Rewrite using `[h0, pow_zero, pow_zero]`. Establish `hn : 0 < n` using `Nat.pos_of_ne_zero (left_ne_zero_of_mul (Nat.pos_iff_ne_zero.mp h0))`. Conclude with `pow_le_pow_left₀ (by omega) (by omega) k`.

Establish `hcZ : c ^ 2 ≤ W ^ (2 * k)`. Rewrite using `[pow_mul', ← sq_abs c]`. Conclude with `pow_le_pow_left₀ (abs_nonneg c) (hc.trans hBW) 2`. Establish `hcR : ((c : ℝ)) ^ 2 ≤ (W : ℝ) ^ (2 * k)` using `by exact_mod_cast hcZ`. Use `hcR.trans (le_of_eq ?_)` and prove the remaining obligations.

Establish `hWR : (0 : ℝ) < (W : ℝ)` using `by exact_mod_cast hWpos`. Rewrite using `[← Real.rpow_natCast, Real.rpow_def_of_pos hWR, hsum, spread_eq, ← hW]`. Use `congr 1`. Establish `hkR : ((k : ℕ) : ℝ) = (n : ℝ) * ((Formalism.BranchingDeterminantCap.d1 lt.w sg.w : ℤ) : ℝ)`. Rewrite using `[hk]`.

Use `push_cast`. Use `congr 1`. Establish `h2` using `congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hd1)`. Rewrite using `[← h2, Int.cast_natCast]`. Use `push_cast`.

Rewrite using `[hkR]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem branching_constant_bound (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n) (hI : Interlace lt sg) :
    (((Formalism.BranchingDeterminantCap.cCap lt.w sg.w : ℤ) : ℝ) ^ 2) * dimV lt.w ≤
      Real.exp (2 * n * Real.log (lt.spread : ℝ) * (∑ i : Fin n, (min (lenP lt i) (baseWeightDifference lt sg) : ℝ)) +
        Real.log (dimV lt.w)) := by
  have hI' : Formalism.BranchingDeterminantCap.Interlace lt.w sg.w := fun i => ⟨(hI i).2, (hI i).1⟩
  obtain ⟨_, hc⟩ := Formalism.BranchingDeterminantCap.capacity_constant_bound n lt.w sg.w hI'
  have hd1 : 0 ≤ Formalism.BranchingDeterminantCap.d1 lt.w sg.w := (Formalism.BranchingDeterminantCap.interlaceIdentities n lt.w sg.w hI').2.2.2.1
  have hsum : (∑ i : Fin n, (min (lenP lt i) (baseWeightDifference lt sg) : ℝ)) = ((Formalism.BranchingDeterminantCap.d1 lt.w sg.w : ℤ) : ℝ) := by
    unfold Formalism.BranchingDeterminantCap.d1 Formalism.BranchingDeterminantCap.d0 lenP baseWeightDifference
    push_cast
    rfl
  have hpos := dimV_pos lt
  rw [Real.exp_add, Real.exp_log hpos]
  apply mul_le_mul_of_nonneg_right _ hpos.le

  set c := Formalism.BranchingDeterminantCap.cCap lt.w sg.w with hcdef
  set k := n * (Formalism.BranchingDeterminantCap.d1 lt.w sg.w).toNat with hk
  set W : ℤ := lt.w 0 - lt.w (Fin.last n) + ((n : ℤ) + 1) with hW
  have hanti : lt.w (Fin.last n) ≤ lt.w 0 := lt.anti (Fin.zero_le _)
  have hWpos : 0 < W := by omega
  have hBW : (lt.w 0 - lt.w (Fin.last n) + (n : ℤ) - 1) ^ k ≤ W ^ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero, pow_zero]
    · have hn : 0 < n := Nat.pos_of_ne_zero (left_ne_zero_of_mul (Nat.pos_iff_ne_zero.mp h0))
      exact pow_le_pow_left₀ (by omega) (by omega) k
  have hcZ : c ^ 2 ≤ W ^ (2 * k) := by
    rw [pow_mul', ← sq_abs c]
    exact pow_le_pow_left₀ (abs_nonneg c) (hc.trans hBW) 2
  have hcR : ((c : ℝ)) ^ 2 ≤ (W : ℝ) ^ (2 * k) := by exact_mod_cast hcZ
  refine hcR.trans (le_of_eq ?_)
  have hWR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWpos
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hWR, hsum, spread_eq, ← hW]
  congr 1
  have hkR : ((k : ℕ) : ℝ) = (n : ℝ) * ((Formalism.BranchingDeterminantCap.d1 lt.w sg.w : ℤ) : ℝ) := by
    rw [hk]
    push_cast
    congr 1
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hd1)
    rw [← h2, Int.cast_natCast]
  push_cast
  rw [hkR]
  ring

/- English proof (translation)
Introduce `D u τ n hn lt hlt sg hI G hG`. Distinguish the cases in `hT : Tu D u = 0`. It suffices to derive a contradiction. Establish `hdet : (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).det = 0`. Rewrite using `[hG, scaleMat, Matrix.det_diagonal]`.

Apply `Finset.prod_eq_zero (Finset.mem_univ (Fin.last n))` to reduce the goal to its premises. Simplify using `[hT]`. Establish `h1` using `congrArg Matrix.det (show ((G * G⁻¹ : GL (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 1 by simp)`. Rewrite `h1` using `[Units.val_mul, Matrix.det_mul, hdet, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one h1`.

Take `⟨P, h1, h2, h3, h4, h5⟩` from `h n lt sg hI (Tu D u) (Nat.pos_of_ne_zero hT) G hG`. Use `⟨P, h1, h2, h3, h4, fun f hf => (h5 f hf).trans ?_⟩` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_right _ (normTil_nonneg lt G f)` to reduce the goal to its premises. Rewrite using `[add_assoc, Real.exp_add]`. Conclude with `mul_le_mul_of_nonneg_left (branching_constant_bound n lt sg hI) (Real.exp_pos _).le`.
-/
theorem branching_link (h : BranchingIntegral) : Link3 := by
  intro D u τ n hn lt hlt sg hI G hG
  by_cases hT : Tu D u = 0
  · exfalso
    have hdet : (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).det = 0 := by
      rw [hG, scaleMat, Matrix.det_diagonal]
      apply Finset.prod_eq_zero (Finset.mem_univ (Fin.last n))
      simp [hT]
    have h1 := congrArg Matrix.det
      (show ((G * G⁻¹ : GL (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 1 by simp)
    rw [Units.val_mul, Matrix.det_mul, hdet, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := h n lt sg hI (Tu D u) (Nat.pos_of_ne_zero hT) G hG
  refine ⟨P, h1, h2, h3, h4, fun f hf => (h5 f hf).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (normTil_nonneg lt G f)
  rw [add_assoc, Real.exp_add]
  exact mul_le_mul_of_nonneg_left (branching_constant_bound n lt sg hI) (Real.exp_pos _).le

/- English proof (translation)
The claim follows from `Link3F_of_Link3 (branching_link h)`.
-/
theorem branching_link_family (h : BranchingIntegral) : Link3F := Link3F_of_Link3 (branching_link h)

def shiftW {N : ℕ} (lam : DomWeight N) (c : ℤ) : DomWeight N where
  w := fun i => lam.w i + c
  anti := fun i j h => by have := lam.anti h; simp only; omega

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shiftW_w {N : ℕ} (lam : DomWeight N) (c : ℤ) : (shiftW lam c).w = fun i => lam.w i + c := rfl

/- English proof (translation)
Consider the cases of `lam with`. Consider the case `mk w anti`. Simplify using `only [shiftW, DomWeight.mk.injEq]`. Use function extensionality and compare the values at `i`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shiftW_shiftW_neg {N : ℕ} (lam : DomWeight N) (c : ℤ) : shiftW (shiftW lam (-c)) c = lam := by
  cases lam with
  | mk w anti =>
    simp only [shiftW, DomWeight.mk.injEq]
    funext i
    ring

/- English proof (translation)
Unfold `DomWeight.detShift`. Rewrite using `[dif_pos hN, dif_pos hN]`. Both sides reduce to the same expression.
-/
theorem detShift_shiftW {N : ℕ} (lam : DomWeight N) (c : ℤ) (hN : 0 < N) :
    (shiftW lam c).detShift = lam.detShift + c := by
  unfold DomWeight.detShift
  rw [dif_pos hN, dif_pos hN]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hN : 0 < N` using `Fin.pos i`. Unfold `DomWeight.natW`. Rewrite using `[detShift_shiftW lam c hN, shiftW_w]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem natW_shiftW {N : ℕ} (lam : DomWeight N) (c : ℤ) : (shiftW lam c).natW = lam.natW := by
  funext i
  have hN : 0 < N := Fin.pos i
  unfold DomWeight.natW
  rw [detShift_shiftW lam c hN, shiftW_w]
  congr 1
  ring

/- English proof (translation)
Unfold `delSq`. Rewrite using `[natW_shiftW]`.
-/
theorem delSq_shiftW (R : Type) [CommRing R] {N : ℕ} (lam : DomWeight N) (c : ℤ) :
    delSq R N (shiftW lam c) = delSq R N lam := by
  unfold delSq
  rw [natW_shiftW]

/- English proof (translation)
Use function extensionality and compare the values at `f g`. Unfold `normFock extremal`. Rewrite using `[natW_shiftW]`.
-/
theorem normFock_shiftW {N : ℕ} (lam : DomWeight N) (c : ℤ) : normFock (shiftW lam c) = normFock lam := by
  funext f g
  unfold normFock extremal
  rw [natW_shiftW]

/- English proof (translation)
Unfold `detPow`. Rewrite using `[zpow_add, Units.val_mul]`.
-/
theorem detPow_add (R : Type) [CommRing R] {N : ℕ} (g : GL (Fin N) R) (a b : ℤ) :
    detPow R N g (a + b) = detPow R N g a * detPow R N g b := by
  unfold detPow
  rw [zpow_add, Units.val_mul]

/- English proof (translation)
Establish `h : Matrix.GeneralLinearGroup.det g = 1`. Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply]`. Simplify using the standard rewrite rules. Unfold `detPow`.

Rewrite using `[h, one_zpow, Units.val_one]`.
-/
theorem det_pow_dim_zero (R : Type) [CommRing R] (g : GL (Fin 0) R) (c : ℤ) : detPow R 0 g c = 1 := by
  have h : Matrix.GeneralLinearGroup.det g = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp
  unfold detPow
  rw [h, one_zpow, Units.val_one]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos N with hN | hN` into its components or cases. Substitute `hN` using the available equality. Establish `h1 : (shiftW lam c).detShift = lam.detShift`. Unfold `DomWeight.detShift`. Simplify using the standard rewrite rules.

Unfold `sqAct`. Rewrite using `[h1]`. Simplify using `only [det_pow_dim_zero, one_smul]`. Unfold `sqAct`. Rewrite using `[detShift_shiftW lam c hN, smul_smul, detPow_add, mul_comm]`.
-/
theorem sqAct_shiftW (R : Type) [CommRing R] {N : ℕ} (lam : DomWeight N) (c : ℤ) (g : GL (Fin N) R)
    (f : MvPolynomial (Fin N × Fin N) R) :
    sqAct R N (shiftW lam c) g f = detPow R N g c • sqAct R N lam g f := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h1 : (shiftW lam c).detShift = lam.detShift := by
      unfold DomWeight.detShift
      simp
    unfold sqAct
    rw [h1]
    simp only [det_pow_dim_zero, one_smul]
  · unfold sqAct
    rw [detShift_shiftW lam c hN, smul_smul, detPow_add, mul_comm]

/- English proof (translation)
Unfold `blockMat`. Rewrite using `[Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]`.
-/
theorem det_blockMat {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : (blockMat g).det = g.det := by
  unfold blockMat
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/- English proof (translation)
Establish `h : Matrix.GeneralLinearGroup.det H = Matrix.GeneralLinearGroup.det g`. Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hH, det_blockMat]`. Unfold `detPow`. Rewrite using `[h]`.
-/
theorem detPow_blockMat {n : ℕ} (g : GL (Fin n) ℂ) (H : GL (Fin (n + 1)) ℂ)
    (hH : (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = blockMat (g : Matrix (Fin n) (Fin n) ℂ)) (c : ℤ) :
    detPow ℂ (n + 1) H c = detPow ℂ n g c := by
  have h : Matrix.GeneralLinearGroup.det H = Matrix.GeneralLinearGroup.det g := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hH, det_blockMat]
  unfold detPow
  rw [h]

/- English proof (translation)
Establish `hd : detPow ℂ (n + 1) G c * star (detPow ℂ (n + 1) G c) = (((T : ℝ) ^ c : ℝ) : ℂ)`. Establish `hdet : ((Matrix.GeneralLinearGroup.det G : ℂˣ) : ℂ) = ((Real.sqrt T : ℝ) : ℂ)`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, hG, scaleMat, Matrix.det_diagonal]`. Simplify using the standard rewrite rules. Unfold `detPow`.

Rewrite using `[Units.val_zpow_eq_zpow_val, hdet, ← Complex.ofReal_zpow, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_zpow, Real.mul_self_sqrt (Nat.cast_nonneg T)]`. Unfold `normTil`. Rewrite using `[normFock_shiftW, sqAct_shiftW]`. Unfold `normFock`. Rewrite using `[MvPolynomial.smul_eq_C_mul, Formalism.GradedWeylDivisibility.LFocks_C_mul_left, Formalism.GradedWeylDivisibility.LFocks_C_mul_right, ← mul_assoc, mul_div_assoc, hd, Complex.re_ofReal_mul]`.
-/
theorem normTil_shiftW {n : ℕ} (lt : DomWeight (n + 1)) (c : ℤ) (T : ℕ) (G : GL (Fin (n + 1)) ℂ)
    (hG : (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T)
    (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) :
    normTil (shiftW lt c) G f = (T : ℝ) ^ c * normTil lt G f := by
  have hd : detPow ℂ (n + 1) G c * star (detPow ℂ (n + 1) G c) = (((T : ℝ) ^ c : ℝ) : ℂ) := by
    have hdet : ((Matrix.GeneralLinearGroup.det G : ℂˣ) : ℂ) = ((Real.sqrt T : ℝ) : ℂ) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hG, scaleMat, Matrix.det_diagonal]
      simp
    unfold detPow
    rw [Units.val_zpow_eq_zpow_val, hdet, ← Complex.ofReal_zpow, Complex.star_def, Complex.conj_ofReal,
      ← Complex.ofReal_mul, ← mul_zpow, Real.mul_self_sqrt (Nat.cast_nonneg T)]
  unfold normTil
  rw [normFock_shiftW, sqAct_shiftW]
  unfold normFock
  rw [MvPolynomial.smul_eq_C_mul, Formalism.GradedWeylDivisibility.LFocks_C_mul_left, Formalism.GradedWeylDivisibility.LFocks_C_mul_right, ← mul_assoc,
    mul_div_assoc, hd, Complex.re_ofReal_mul]

/- English proof (translation)
Unfold `Formalism.BranchingDeterminantCap.d0`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem interlacing_degree_shift {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) (c : ℤ) :
    Formalism.BranchingDeterminantCap.d0 (fun i => lam i + c) (fun i => sg i + c) = Formalism.BranchingDeterminantCap.d0 lam sg := by
  unfold Formalism.BranchingDeterminantCap.d0
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Unfold `Formalism.BranchingDeterminantCap.cCap Formalism.BranchingDeterminantCap.capEig`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.prod_nbij' (fun v => v - c) (fun v => v + c)` to reduce the goal to its premises. Introduce `v hv`.

Simplify using `only [Formalism.BranchingDeterminantCap.rset, interlacing_degree_shift, Finset.mem_erase, Finset.mem_Icc, le_min_iff] at hv ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `v hv`. Simplify using `only [Formalism.BranchingDeterminantCap.rset, interlacing_degree_shift, Finset.mem_erase, Finset.mem_Icc, le_min_iff] at hv ⊢`. Use linear arithmetic over natural numbers and integers.

Introduce `v _`. Expand and normalize the polynomial expressions, which then agree. Introduce `v _`. Expand and normalize the polynomial expressions, which then agree. Introduce `v _`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cCap_shift {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) (c : ℤ) :
    Formalism.BranchingDeterminantCap.cCap (fun i => lam i + c) (fun i => sg i + c) = Formalism.BranchingDeterminantCap.cCap lam sg := by
  unfold Formalism.BranchingDeterminantCap.cCap Formalism.BranchingDeterminantCap.capEig
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_nbij' (fun v => v - c) (fun v => v + c)
  · intro v hv
    simp only [Formalism.BranchingDeterminantCap.rset, interlacing_degree_shift, Finset.mem_erase, Finset.mem_Icc, le_min_iff] at hv ⊢
    omega
  · intro v hv
    simp only [Formalism.BranchingDeterminantCap.rset, interlacing_degree_shift, Finset.mem_erase, Finset.mem_Icc, le_min_iff] at hv ⊢
    omega
  · intro v _
    ring
  · intro v _
    ring
  · intro v _
    apply Finset.prod_congr rfl
    intro j _
    ring

/- English proof (translation)
Unfold `dimV`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j _`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dimV_shift {N : ℕ} (lam : Fin N → ℤ) (c : ℤ) : dimV (fun i => lam i + c) = dimV lam := by
  unfold dimV
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  congr 2
  ring

/- English proof (translation)
Unfold `degP`. Simplify using `only [shiftW_w, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem branchingDegree_shift {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (c : ℤ) :
    degP (shiftW lt c) (shiftW sg c) = degP lt sg + c := by
  unfold degP
  simp only [shiftW_w, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

/- English proof (translation)
Introduce `i`. Use `hI i` as an intermediate fact. Simplify using `only [shiftW_w]`. Apply the tactic sequence `constructor <;> omega`.
-/
theorem interlace_shift {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (c : ℤ) (hI : Interlace lt sg) :
    Interlace (shiftW lt c) (shiftW sg c) := by
  intro i
  have := hI i
  simp only [shiftW_w]
  constructor <;> omega

/- English proof (translation)
Take `⟨P, h1, h2, h3, h4, h5⟩` from `h`. Use `⟨P, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[delSq_shiftW, delSq_shiftW]`. Conclude with `h1`. Rewrite using `[delSq_shiftW]`.

Conclude with `h2`. Rewrite using `[delSq_shiftW, delSq_shiftW]`. Conclude with `h3`. Introduce `g H hH f hf`. Rewrite `hf` using `[delSq_shiftW]`.

Rewrite using `[sqAct_shiftW, sqAct_shiftW, LinearMap.map_smul, h4 g H hH f hf, detPow_blockMat g H hH]`. Introduce `f hf`. Rewrite `hf` using `[delSq_shiftW]`. Establish `hTpos : (0 : ℝ) < T` using `by exact_mod_cast hT`. Establish `hz : (T : ℝ) ^ c = Real.exp (Real.log T * c)`.

Rewrite using `[← Real.rpow_intCast, Real.rpow_def_of_pos hTpos]`. Rewrite using `[normFock_shiftW, normTil_shiftW lt c T G hG f, shiftW_w, shiftW_w, cCap_shift, dimV_shift, branchingDegree_shift, hz]`. Establish `he : Real.exp (-((degP lt sg + c : ℤ) : ℝ) * Real.log T) * Real.exp (Real.log T * c) = Real.exp (-(degP lt sg : ℝ) * Real.log T)`. Rewrite using `[← Real.exp_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.
-/
theorem branching_integral_shift {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (c : ℤ) (T : ℕ) (hT : 0 < T)
    (G : GL (Fin (n + 1)) ℂ) (hG : (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T)
    (h : BranchingIntegralAt n lt sg T G) : BranchingIntegralAt n (shiftW lt c) (shiftW sg c) T G := by
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := h
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · rw [delSq_shiftW, delSq_shiftW]
    exact h1
  · rw [delSq_shiftW]
    exact h2
  · rw [delSq_shiftW, delSq_shiftW]
    exact h3
  · intro g H hH f hf
    rw [delSq_shiftW] at hf
    rw [sqAct_shiftW, sqAct_shiftW, LinearMap.map_smul, h4 g H hH f hf, detPow_blockMat g H hH]
  · intro f hf
    rw [delSq_shiftW] at hf
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    have hz : (T : ℝ) ^ c = Real.exp (Real.log T * c) := by
      rw [← Real.rpow_intCast, Real.rpow_def_of_pos hTpos]
    rw [normFock_shiftW, normTil_shiftW lt c T G hG f, shiftW_w, shiftW_w, cCap_shift, dimV_shift,
      branchingDegree_shift, hz]
    have he : Real.exp (-((degP lt sg + c : ℤ) : ℝ) * Real.log T) * Real.exp (Real.log T * c) =
        Real.exp (-(degP lt sg : ℝ) * Real.log T) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    calc (normFock sg (P f) (P f)).re ≤ _ := h5 f hf
      _ = _ := by rw [← he]; ring

/- English proof (translation)
Introduce `n lt sg hI T hT G hG`. Establish `e1` using `shiftW_shiftW_neg lt (lt.w (Fin.last n))`. Establish `e2` using `shiftW_shiftW_neg sg (lt.w (Fin.last n))`. Establish `h0` using `h n (shiftW lt (-lt.w (Fin.last n))) (shiftW sg (-lt.w (Fin.last n))) (by simp only [shiftW_w]; ring) (interlace_shift lt sg _ hI) T hT G hG`. Establish `h1` using `branching_integral_shift _ _ (lt.w (Fin.last n)) T hT G hG h0`.

Rewrite `h1` using `[e1, e2]`. Then use the resulting hypothesis.
-/
theorem branching_integral_of_normalised (h : BranchingIntegralNormalised) : BranchingIntegral := by
  intro n lt sg hI T hT G hG
  have e1 := shiftW_shiftW_neg lt (lt.w (Fin.last n))
  have e2 := shiftW_shiftW_neg sg (lt.w (Fin.last n))
  have h0 := h n (shiftW lt (-lt.w (Fin.last n))) (shiftW sg (-lt.w (Fin.last n)))
    (by simp only [shiftW_w]; ring) (interlace_shift lt sg _ hI) T hT G hG
  have h1 := branching_integral_shift _ _ (lt.w (Fin.last n)) T hT G hG h0
  rwa [e1, e2] at h1

/- English proof (translation)
The claim follows from `branching_link (branching_integral_of_normalised h)`.
-/
theorem branching_link_of_normalised (h : BranchingIntegralNormalised) : Link3 := branching_link (branching_integral_of_normalised h)

/- English proof (translation)
The claim follows from `branching_link_family (branching_integral_of_normalised h)`.
-/
theorem branching_link_family_normalised (h : BranchingIntegralNormalised) : Link3F := branching_link_family (branching_integral_of_normalised h)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
