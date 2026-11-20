import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsHaarStabilizer
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZhatSectionExists

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.A

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Unfold `Wb`. Use `split_ifs with h`. Simplify using `only [Matrix.mulVec, dotProduct]`. Simplify using `[fun j => UnipotentSums.unipotent_apply_middle_row (k := k) vX i j h.1 h.2]`.

Both sides reduce to the same expression.
-/
theorem Wb_mX (vX : Matrix (Fin r) (Fin r) ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    Wb (C2.mX k r vX *ᵥ x) = Wb x := by
  funext i
  unfold Wb
  split_ifs with h
  · simp only [Matrix.mulVec, dotProduct]
    simp [fun j => UnipotentSums.unipotent_apply_middle_row (k := k) vX i j h.1 h.2]
  · rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Wb, Pi.zero_apply]`. Use `split_ifs with h`. Conclude with `HermitianXiVector.xiV_X ξ i h.1`. Both sides reduce to the same expression.
-/
theorem Wb_xiV (ξ : Fin r → ℂ) : Wb (C2.xiV k r ξ) = 0 := by
  funext i
  simp only [Wb, Pi.zero_apply]
  split_ifs with h
  · exact HermitianXiVector.xiV_X ξ i h.1
  · rfl

/- English proof (translation)
Rewrite using `[prW_eq, Wb_xiV]`. Simplify using `[herm]`.
-/
theorem prW_xiV (z : Fin (2 * r + k + 1) → ℂ) (ξ : Fin r → ℂ) : D.prW k r z (C2.xiV k r ξ) = 0 := by
  rw [prW_eq, Wb_xiV]
  simp [herm]

/- English proof (translation)
Establish `hW : ∀ y, D.prW k r z (C2.mX k r (v.submatrix Fin.castSucc Fin.castSucc) *ᵥ y) = D.prW k r z y`. Introduce `y`. Rewrite using `[prW_eq, prW_eq, Wb_mX]`. Unfold `C2.tauM`. Rewrite using `[← Matrix.mulVec_mulVec, HermitianXiVector.nEich_apply]`.

Simplify using `only [prW_add, prW_smul, prW_xiV, prW_self hz hzz, smul_zero, add_zero, hW]`.
-/
theorem prW_tau {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hzz : herm (Hpk k r) z z ≠ 0)
    (v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    D.prW k r z (C2.tauM k r z v *ᵥ x) = D.prW k r z x := by
  have hW : ∀ y, D.prW k r z (C2.mX k r (v.submatrix Fin.castSucc Fin.castSucc) *ᵥ y) = D.prW k r z y := by
    intro y
    rw [prW_eq, prW_eq, Wb_mX]
  unfold C2.tauM
  rw [← Matrix.mulVec_mulVec, HermitianXiVector.nEich_apply]
  simp only [prW_add, prW_smul, prW_xiV, prW_self hz hzz, smul_zero, add_zero, hW]

/- English proof (translation)
Use extensionality with `i j`. Use `congrFun (h (Pi.single j 1)) i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem mat_ext_mulVec {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℂ} (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [ee, bvec, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]`. Distinguish the cases in `h : i.val < r`. Rewrite using `[Finset.sum_eq_single ⟨i.val, h⟩]`.

Rewrite using `[if_pos (show i = eI k r ⟨i.val, h⟩ from Fin.ext rfl)]`. Simplify using `only [C2.xiV, dif_pos h]`. Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `hi`.

Conclude with `hb (Fin.ext (congrArg Fin.val hi).symm)`. Introduce `hb`. Conclude with `absurd (Finset.mem_univ _) hb`. Simplify using `only [C2.xiV, dif_neg h]`. Use `symm`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[if_neg]`. Introduce `hi`. Apply `h` to reduce the goal to its premises.

Rewrite using `[hi]`. Conclude with `a.isLt`.
-/
theorem xiV_eq_sum (ξ : Fin r → ℂ) : C2.xiV k r ξ = ∑ a : Fin r, ξ a • ee k r a := by
  funext i
  rw [Finset.sum_apply]
  simp only [ee, bvec, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
  by_cases h : i.val < r
  · rw [Finset.sum_eq_single ⟨i.val, h⟩]
    · rw [if_pos (show i = eI k r ⟨i.val, h⟩ from Fin.ext rfl)]
      simp only [C2.xiV, dif_pos h]
    · intro b _ hb
      rw [if_neg]
      intro hi
      exact hb (Fin.ext (congrArg Fin.val hi).symm)
    · intro hb
      exact absurd (Finset.mem_univ _) hb
  · simp only [C2.xiV, dif_neg h]
    symm
    apply Finset.sum_eq_zero
    intro a _
    rw [if_neg]
    intro hi
    apply h
    rw [hi]
    exact a.isLt

/- English proof (translation)
Rewrite using `[xiV_eq_sum, Matrix.mulVec_sum]`. Repeatedly rewrite using `[Matrix.mulVec_smul, hme]`.
-/
theorem fix_X {h : B.Mat k r} (hme : ∀ a : Fin r, h *ᵥ ee k r a = ee k r a) (ξ : Fin r → ℂ) :
    h *ᵥ C2.xiV k r ξ = C2.xiV k r ξ := by
  rw [xiV_eq_sum, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, hme]

/- English proof (translation)
Take `⟨hU, hfix, hZ⟩` from `hh`. Establish `hX : h *ᵥ C2.xiV k r ξ = C2.xiV k r ξ` using `fix_X (fun a => (hfix a).1) ξ`. Establish `e1 : ∀ x, herm (Hpk k r) (h *ᵥ x) z = herm (Hpk k r) x z`. Introduce `x`. Use `conv_lhs => rw [← hZ]`.

Conclude with `herm_m0_mulVec_invariant h hU x z`. Establish `e2 : ∀ x, herm (Hpk k r) (h *ᵥ x) (C2.xiV k r ξ) = herm (Hpk k r) x (C2.xiV k r ξ)`. Introduce `x`. Use `conv_lhs => rw [← hX]`. Conclude with `herm_m0_mulVec_invariant h hU x _`.

Apply `mat_ext_mulVec` to reduce the goal to its premises. Introduce `x`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, HermitianXiVector.nEich_apply, HermitianXiVector.nEich_apply, e1, e2]`. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_smul, hX, hZ]`.
-/
theorem nEich_comm {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) (ξ : Fin r → ℂ) :
    h * C2.nEich k r z ξ = C2.nEich k r z ξ * h := by
  obtain ⟨hU, hfix, hZ⟩ := hh
  have hX : h *ᵥ C2.xiV k r ξ = C2.xiV k r ξ := fix_X (fun a => (hfix a).1) ξ
  have e1 : ∀ x, herm (Hpk k r) (h *ᵥ x) z = herm (Hpk k r) x z := by
    intro x
    conv_lhs => rw [← hZ]
    exact herm_m0_mulVec_invariant h hU x z
  have e2 : ∀ x, herm (Hpk k r) (h *ᵥ x) (C2.xiV k r ξ) = herm (Hpk k r) x (C2.xiV k r ξ) := by
    intro x
    conv_lhs => rw [← hX]
    exact herm_m0_mulVec_invariant h hU x _
  apply mat_ext_mulVec
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, HermitianXiVector.nEich_apply, HermitianXiVector.nEich_apply, e1, e2]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hX, hZ]

/- English proof (translation)
Establish `hx' : x = C2.xiV k r (fun a => x (eI k r a))`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i.val < r`. Simplify using `only [C2.xiV, dif_pos hi]`. Conclude with `congrArg x (Fin.ext rfl)`.

Simplify using `only [C2.xiV, dif_neg hi]`. Conclude with `hx i (by omega)`. Rewrite using `[hx']`. Conclude with `fix_X hme _`.
-/
theorem fix_supX {h : B.Mat k r} (hme : ∀ a : Fin r, h *ᵥ ee k r a = ee k r a) {x : Fin (2 * r + k + 1) → ℂ}
    (hx : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → x i = 0) : h *ᵥ x = x := by
  have hx' : x = C2.xiV k r (fun a => x (eI k r a)) := by
    funext i
    by_cases hi : i.val < r
    · simp only [C2.xiV, dif_pos hi]
      exact congrArg x (Fin.ext rfl)
    · simp only [C2.xiV, dif_neg hi]
      exact hx i (by omega)
  rw [hx']
  exact fix_X hme _

/- English proof (translation)
Establish `h1 : ∀ a : Fin r, x (eI k r a) = 0`. Introduce `a`. Apply `hx` to reduce the goal to its premises. Establish `: (eI k r a).val = a.val` using `rfl`. Use `a.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h2 : Wb x = 0`. Use function extensionality and compare the values at `i`. Simplify using `only [Wb, Pi.zero_apply]`. Use `split_ifs with h`.

Conclude with `hx i h.2`. Both sides reduce to the same expression. Use `conv_lhs => rw [decomp x]`. Rewrite using `[h2]`. Simplify using `[h1]`.
-/
theorem sum_es (x : Fin (2 * r + k + 1) → ℂ) (hx : ∀ i : Fin (2 * r + k + 1), i.val ≤ r + k → x i = 0) :
    x = ∑ a : Fin r, x (esI k r a) • es k r a := by
  have h1 : ∀ a : Fin r, x (eI k r a) = 0 := by
    intro a
    apply hx
    have : (eI k r a).val = a.val := rfl
    have := a.isLt
    omega
  have h2 : Wb x = 0 := by
    funext i
    simp only [Wb, Pi.zero_apply]
    split_ifs with h
    · exact hx i h.2
    · rfl
  conv_lhs => rw [decomp x]
  rw [h2]
  simp [h1]

/- English proof (translation)
Rewrite using `[sum_es x hx, Matrix.mulVec_sum]`. Repeatedly rewrite using `[Matrix.mulVec_smul, hms]`.
-/
theorem fix_supXs {h : B.Mat k r} (hms : ∀ a : Fin r, h *ᵥ es k r a = es k r a) {x : Fin (2 * r + k + 1) → ℂ}
    (hx : ∀ i : Fin (2 * r + k + 1), i.val ≤ r + k → x i = 0) : h *ᵥ x = x := by
  rw [sum_es x hx, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, hms]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct]`. Establish `key : ∀ j, C2.mX k r vX i j * w j = if i = j then w j else 0`. Introduce `j`. Distinguish the cases in `hj : r ≤ j.val ∧ j.val ≤ r + k`.

Apply the tactic sequence `rw [UnipotentSums.unipotent_apply_middle_column vX i j hj.1 hj.2] split_ifs <;> simp`. Rewrite using `[hw j (by omega)]`. Simplify using the standard rewrite rules. Simplify using `only [key, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem mX_Wb (vX : Matrix (Fin r) (Fin r) ℂ) {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) :
    C2.mX k r vX *ᵥ w = w := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  have key : ∀ j, C2.mX k r vX i j * w j = if i = j then w j else 0 := by
    intro j
    by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [UnipotentSums.unipotent_apply_middle_column vX i j hj.1 hj.2]
      split_ifs <;> simp
    · rw [hw j (by omega)]
      simp
  simp only [key, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Introduce `i hi`. Establish `hc : (C2.mX k r vX *ᵥ ee k r a) i = C2.mX k r vX i (eI k r a)`. Simplify using `[ee, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[hc, UnipotentSums.mX_col_X, dif_neg (by omega)]`.
-/
theorem mX_supX (vX : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (C2.mX k r vX *ᵥ ee k r a) i = 0 := by
  intro i hi
  have hc : (C2.mX k r vX *ᵥ ee k r a) i = C2.mX k r vX i (eI k r a) := by
    simp [ee, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hc, UnipotentSums.mX_col_X, dif_neg (by omega)]

/- English proof (translation)
Introduce `i hi`. Establish `hc : (C2.mX k r vX *ᵥ es k r a) i = C2.mX k r vX i (esI k r a)`. Simplify using `[es, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[hc, UnipotentSums.mX_col_Xs, dif_neg (by omega)]`.
-/
theorem mX_supXs (vX : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    ∀ i : Fin (2 * r + k + 1), i.val ≤ r + k → (C2.mX k r vX *ᵥ es k r a) i = 0 := by
  intro i hi
  have hc : (C2.mX k r vX *ᵥ es k r a) i = C2.mX k r vX i (esI k r a) := by
    simp [es, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hc, UnipotentSums.mX_col_Xs, dif_neg (by omega)]

/- English proof (translation)
Take `⟨hU, hfix, -⟩` from `hh`. Establish `hme : ∀ a : Fin r, h *ᵥ ee k r a = ee k r a` using `fun a => (hfix a).1`. Establish `hms : ∀ a : Fin r, h *ᵥ es k r a = es k r a` using `fun a => (hfix a).2`. Establish `hWx : ∀ x, inWb k r (Wb x)`. Introduce `x i hi`.

Simplify using `only [Wb]`. Rewrite using `[if_neg (by omega)]`. Establish `hA : ∀ a, h *ᵥ (C2.mX k r vX *ᵥ ee k r a) = C2.mX k r vX *ᵥ ee k r a` using `fun a => fix_supX hme (mX_supX vX a)`. Establish `hB : ∀ a, h *ᵥ (C2.mX k r vX *ᵥ es k r a) = C2.mX k r vX *ᵥ es k r a` using `fun a => fix_supXs hms (mX_supXs vX a)`. Apply `mat_ext_mulVec` to reduce the goal to its premises.

Introduce `x`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, decomp x]`. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, hme, hms, hA, hB, mX_Wb vX (hWx x), mX_Wb vX (m0_mulVec_mem_orthogonal h hU hme hms (hWx x))]`.
-/
theorem mX_comm {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z)
    (vX : Matrix (Fin r) (Fin r) ℂ) : h * C2.mX k r vX = C2.mX k r vX * h := by
  obtain ⟨hU, hfix, -⟩ := hh
  have hme : ∀ a : Fin r, h *ᵥ ee k r a = ee k r a := fun a => (hfix a).1
  have hms : ∀ a : Fin r, h *ᵥ es k r a = es k r a := fun a => (hfix a).2
  have hWx : ∀ x, inWb k r (Wb x) := by
    intro x i hi
    simp only [Wb]
    rw [if_neg (by omega)]
  have hA : ∀ a, h *ᵥ (C2.mX k r vX *ᵥ ee k r a) = C2.mX k r vX *ᵥ ee k r a :=
    fun a => fix_supX hme (mX_supX vX a)
  have hB : ∀ a, h *ᵥ (C2.mX k r vX *ᵥ es k r a) = C2.mX k r vX *ᵥ es k r a :=
    fun a => fix_supXs hms (mX_supXs vX a)
  apply mat_ext_mulVec
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, decomp x]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, hme, hms, hA, hB,
    mX_Wb vX (hWx x), mX_Wb vX (m0_mulVec_mem_orthogonal h hU hme hms (hWx x))]

/- English proof (translation)
Unfold `C2.tauM`. Rewrite using `[← mul_assoc, nEich_comm hh _, mul_assoc, mX_comm hh _, ← mul_assoc]`.
-/
theorem tau_comm {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z)
    (v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : h * C2.tauM k r z v = C2.tauM k r z v * h := by
  unfold C2.tauM
  rw [← mul_assoc, nEich_comm hh _, mul_assoc, mX_comm hh _, ← mul_assoc]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hu`. Rewrite using `[Matrix.det_of_isUpperTriangular (fun i j hij => h1 i j hij)]`. Simplify using `[h2]`.
-/
theorem det_UT {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u.det = 1 := by
  obtain ⟨h1, h2⟩ := hu
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => h1 i j hij)]
  simp [h2]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hu`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.conjTranspose_apply, h1 j i hij]`. Simplify using `[Matrix.conjTranspose_apply, h2]`.
-/
theorem UT_star {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : uᴴ ∈ C2.LTset m := by
  obtain ⟨h1, h2⟩ := hu
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp [Matrix.conjTranspose_apply, h1 j i hij]
  · simp [Matrix.conjTranspose_apply, h2]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hl`. Rewrite using `[Matrix.det_of_isLowerTriangular l (fun i j hij => h1 i j hij)]`. Simplify using `[h2]`.
-/
theorem det_LT {m : ℕ} {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : l.det = 1 := by
  obtain ⟨h1, h2⟩ := hl
  rw [Matrix.det_of_isLowerTriangular l (fun i j hij => h1 i j hij)]
  simp [h2]

/- English proof (translation)
Rewrite using `[Matrix.inv_def, h, Ring.inverse_one, one_smul]`.
-/
theorem adj_eq_inv {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (h : A.det = 1) : A.adjugate = A⁻¹ := by
  rw [Matrix.inv_def, h, Ring.inverse_one, one_smul]

/- English proof (translation)
Rewrite using `[adj_eq_inv (det_LT hl)]`. Take `⟨h1, h2⟩` from `C2x2.lt_inv hl`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `split_ifs with hi`.

Substitute `hi` using the available equality. Conclude with `h2 _`. Conclude with `h1 i _ (lt_of_le_of_ne (Fin.le_last i) hi)`.
-/
theorem LT_col_last {l : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hl : l ∈ C2.LTset (r + 1)) :
    l.adjugate *ᵥ Pi.single (Fin.last r) 1 = Pi.single (Fin.last r) 1 := by
  rw [adj_eq_inv (det_LT hl)]
  obtain ⟨h1, h2⟩ := C2x2.lt_inv hl
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  split_ifs with hi
  · subst hi
    exact h2 _
  · exact h1 i _ (lt_of_le_of_ne (Fin.le_last i) hi)

/- English proof (translation)
Rewrite using `[adj_eq_inv (det_UT hu)]`. Take `⟨h1, h2⟩` from `C2x2.ut_inv hu`. Use function extensionality and compare the values at `j`. Simplify using `only [Matrix.vecMul, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `split_ifs with hj`.

Substitute `hj` using the available equality. Conclude with `h2 _`. Conclude with `h1 (Fin.last r) j (lt_of_le_of_ne (Fin.le_last j) hj)`.
-/
theorem UT_row_last {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ C2.UTset (r + 1)) :
    Pi.single (Fin.last r) 1 ᵥ* u.adjugate = Pi.single (Fin.last r) 1 := by
  rw [adj_eq_inv (det_UT hu)]
  obtain ⟨h1, h2⟩ := C2x2.ut_inv hu
  funext j
  simp only [Matrix.vecMul, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  split_ifs with hj
  · subst hj
    exact h2 _
  · exact h1 (Fin.last r) j (lt_of_le_of_ne (Fin.le_last j) hj)

def Fz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i a => fvec k r z a i

/- English proof (translation)
Establish `hU` using `((unipotent_map_frame k r z hz).1 s hs).1`. Use extensionality with `i b`. Use `congrFun (hU b) i` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Fz, Matrix.of_apply]`. Rewrite using `[show (∑ j, s i j * fvec k r z b j) = (s *ᵥ fvec k r z b) i from rfl, this]`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`.
-/
theorem frame_mul {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {s : B.Mat k r} (hs : s ∈ Sset k r z) :
    s * Fz k r z = Fz k r z * C2.uMap k r z s := by
  have hU := ((unipotent_map_frame k r z hz).1 s hs).1
  ext i b
  have := congrFun (hU b) i
  simp only [Matrix.mul_apply, Fz, Matrix.of_apply]
  rw [show (∑ j, s i j * fvec k r z b j) = (s *ᵥ fvec k r z b) i from rfl, this]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

/- English proof (translation)
Rewrite using `[D.cofR, ← Matrix.mulVec_mulVec]`. Establish `hw : (Zhat k r S.z S.z' γ).adjugate *ᵥ Pi.single (Fin.last r) 1 = fun b => (Zhat k r S.z S.z' γ).adjugate b (Fin.last r)`. Use function extensionality and compare the values at `b`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hF : ∀ w : Fin (r + 1) → ℂ, Fz k r S.z' *ᵥ w = ∑ b, w b • fvec k r S.z' b`.

Introduce `w`. Use function extensionality and compare the values at `i`. Simplify using `only [Fz, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun b _ => mul_comm _ _`. Rewrite using `[hw, hF, Matrix.mulVec_sum]`.

Repeatedly rewrite using `[Matrix.mulVec_smul]`.
-/
theorem cofR_eq (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) :
    D.cofR S γ = (γ * Fz k r S.z') *ᵥ ((Zhat k r S.z S.z' γ).adjugate *ᵥ Pi.single (Fin.last r) 1) := by
  rw [D.cofR, ← Matrix.mulVec_mulVec]
  have hw : (Zhat k r S.z S.z' γ).adjugate *ᵥ Pi.single (Fin.last r) 1 =
      fun b => (Zhat k r S.z S.z' γ).adjugate b (Fin.last r) := by
    funext b
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hF : ∀ w : Fin (r + 1) → ℂ, Fz k r S.z' *ᵥ w = ∑ b, w b • fvec k r S.z' b := by
    intro w
    funext i
    simp only [Fz, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [hw, hF, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul]

/- English proof (translation)
Rewrite using `[D.cofL]`. Establish `hw : star (Pi.single (Fin.last r) 1 ᵥ* (Zhat k r S.z S.z' γ).adjugate) = fun a => conj ((Zhat k r S.z S.z' γ).adjugate (Fin.last r) a)`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules. Rewrite using `[hw]`.

Use function extensionality and compare the values at `i`. Simplify using `only [Fz, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`.
-/
theorem cofL_eq (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) :
    D.cofL S γ = Fz k r S.z *ᵥ star (Pi.single (Fin.last r) 1 ᵥ* (Zhat k r S.z S.z' γ).adjugate) := by
  rw [D.cofL]
  have hw : star (Pi.single (Fin.last r) 1 ᵥ* (Zhat k r S.z S.z' γ).adjugate) =
      fun a => conj ((Zhat k r S.z S.z' γ).adjugate (Fin.last r) a) := by
    funext a
    simp
  rw [hw]
  funext i
  simp only [Fz, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/- English proof (translation)
Rewrite using `[Sset, Set.mem_ofPred_eq]`. Use `⟨1, ?_, n, hn, (one_mul n).symm⟩` and prove the remaining obligations. Simplify using `[UWset, UH]`.
-/
theorem n_in_S {z : Fin (2 * r + k + 1) → ℂ} {n : B.Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z := by
  rw [Sset, Set.mem_ofPred_eq]
  refine ⟨1, ?_, n, hn, (one_mul n).symm⟩
  simp [UWset, UH]

/- English proof (translation)
Establish `hH : Hpk k r * Hpk k r = 1` using `(majorant_estimate k r).2.1`. Establish `h1 : nᴴ * Hpk k r * n = Hpk k r` using `hn.1`. Apply `Matrix.isUnit_det_of_left_inverse (B := Hpk k r * nᴴ * Hpk k r)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isUnit_N {n : B.Mat k r} (hn : n ∈ Nset k r) : IsUnit n.det := by
  have hH : Hpk k r * Hpk k r = 1 := (majorant_estimate k r).2.1
  have h1 : nᴴ * Hpk k r * n = Hpk k r := hn.1
  apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * nᴴ * Hpk k r)
  calc Hpk k r * nᴴ * Hpk k r * n = Hpk k r * (nᴴ * Hpk k r * n) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, hH]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `congrFun (congrFun hF i) b` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Fz, Matrix.of_apply] at this`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[this]`.

Conclude with `Finset.sum_congr rfl fun c _ => mul_comm _ _`.
-/
private theorem col_lemma' {z : Fin (2 * r + k + 1) → ℂ} {M : B.Mat k r}
    {V : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hF : M * Fz k r z = Fz k r z * V) (b : Fin (r + 1)) :
    M *ᵥ fvec k r z b = ∑ c, V c b • fvec k r z c := by
  funext i
  have := congrFun (congrFun hF i) b
  simp only [Matrix.mul_apply, Fz, Matrix.of_apply] at this
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hV, Matrix.mul_one]`. Use `_ = M⁻¹ * (M * Fz k r z) * V⁻¹ := by`. Rewrite using `[hF]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Fz k r z * V⁻¹ := by`. Rewrite using `[← Matrix.mul_assoc M⁻¹, Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]`.
-/
private theorem inv_mul_fz_eq_fz_mul_inv {z : Fin (2 * r + k + 1) → ℂ} {M : B.Mat k r}
    {V : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hF : M * Fz k r z = Fz k r z * V) (hM : IsUnit M.det)
    (hV : IsUnit V.det) : M⁻¹ * Fz k r z = Fz k r z * V⁻¹ := by
  calc M⁻¹ * Fz k r z = M⁻¹ * (Fz k r z * V * V⁻¹) := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hV, Matrix.mul_one]
    _ = M⁻¹ * (M * Fz k r z) * V⁻¹ := by
        rw [hF]
        simp only [Matrix.mul_assoc]
    _ = Fz k r z * V⁻¹ := by
        rw [← Matrix.mul_assoc M⁻¹, Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]

/- English proof (translation)
Establish `hs` using `n_in_S (z := z) hn`. Establish `hU : C2.uMap k r z n ∈ C2.UTset (r + 1)` using `((unipotent_map_frame k r z hz).1 n hs).2.1`. Establish `hdet : (C2.uMap k r z n).det = 1` using `det_UT hU`. Establish `hUu : IsUnit (C2.uMap k r z n).det`. Rewrite using `[hdet]`.

Conclude with `isUnit_one`. Rewrite using `[adj_eq_inv hdet]`. Conclude with `C2x5.uMap_eq hz _ _ (col_lemma' (inv_mul_fz_eq_fz_mul_inv (frame_mul hz hs) (isUnit_N hn) hUu))`.
-/
theorem uMap_inv {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {n : B.Mat k r} (hn : n ∈ Nset k r) :
    C2.uMap k r z n⁻¹ = (C2.uMap k r z n).adjugate := by
  have hs := n_in_S (z := z) hn
  have hU : C2.uMap k r z n ∈ C2.UTset (r + 1) := ((unipotent_map_frame k r z hz).1 n hs).2.1
  have hdet : (C2.uMap k r z n).det = 1 := det_UT hU
  have hUu : IsUnit (C2.uMap k r z n).det := by
    rw [hdet]
    exact isUnit_one
  rw [adj_eq_inv hdet]
  exact C2x5.uMap_eq hz _ _ (col_lemma' (inv_mul_fz_eq_fz_mul_inv (frame_mul hz hs) (isUnit_N hn) hUu))

/- English proof (translation)
Use extensionality with `a b`. Establish `hh : ∀ y, herm (Hpk k r) (n⁻¹ *ᵥ y) (fvec k r z a) = herm (Hpk k r) y (n *ᵥ fvec k r z a)`. Introduce `y`. Rewrite using `[← herm_m0_mulVec_invariant n hnH (n⁻¹ *ᵥ y) (fvec k r z a), Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hn, Matrix.one_mulVec]`. Rewrite using `[show Zhat k r z z' (n⁻¹ * γ * n') a b = herm (Hpk k r) ((n⁻¹ * γ * n') *ᵥ fvec k r z' b) (fvec k r z a) from rfl]`.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh, col_lemma' hF, col_lemma' hF', Matrix.mulVec_sum]`. Simplify using `only [Matrix.mulVec_smul, herm_sum_right, HermitianXiVector.herm_smul_r, C2x5.herm_sum_smul]`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Simplify using `only [Zhat, starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem zhat_inv_mul_mul_eq_conjTranspose_mul_mul (z z' : Fin (2 * r + k + 1) → ℂ) {γ n n' : B.Mat k r}
    {U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hn : IsUnit n.det) (hnH : n ∈ UH (Hpk k r))
    (hF : n * Fz k r z = Fz k r z * U) (hF' : n' * Fz k r z' = Fz k r z' * U') :
    Zhat k r z z' (n⁻¹ * γ * n') = Uᴴ * Zhat k r z z' γ * U' := by
  ext a b
  have hh : ∀ y, herm (Hpk k r) (n⁻¹ *ᵥ y) (fvec k r z a) = herm (Hpk k r) y (n *ᵥ fvec k r z a) := by
    intro y
    rw [← herm_m0_mulVec_invariant n hnH (n⁻¹ *ᵥ y) (fvec k r z a), Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hn,
      Matrix.one_mulVec]
  rw [show Zhat k r z z' (n⁻¹ * γ * n') a b =
      herm (Hpk k r) ((n⁻¹ * γ * n') *ᵥ fvec k r z' b) (fvec k r z a) from rfl]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh, col_lemma' hF, col_lemma' hF', Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, herm_sum_right, HermitianXiVector.herm_smul_r, C2x5.herm_sum_smul]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [Zhat, starRingEnd_apply]
  ring

/- English proof (translation)
Establish `hdU : U.det = 1` using `det_UT hU`. Establish `hdU' : U'.det = 1` using `det_UT hU'`. Establish `hUu : IsUnit U.det`. Rewrite using `[hdU]`. Conclude with `isUnit_one`.

Establish `hU'u : IsUnit U'.det`. Rewrite using `[hdU']`. Conclude with `isUnit_one`. Establish `hZ` using `zhat_inv_mul_mul_eq_conjTranspose_mul_mul (γ := γ) S.z S.z' hn hnH hF hF'`. Establish `hdet : (Zhat k r S.z S.z' (n⁻¹ * γ * n')).det = (Zhat k r S.z S.z' γ).det`.

Rewrite using `[hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdU, hdU']`. Simplify using the standard rewrite rules. Establish `hinv : (n⁻¹ * γ * n')⁻¹ = n'⁻¹ * (γ⁻¹ * n)`. Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hn]`. Establish `hnn : ∀ x, n *ᵥ (n⁻¹ *ᵥ x) = x`.

Introduce `x`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hn, Matrix.one_mulVec]`. Establish `hnn' : ∀ x, n' *ᵥ (n'⁻¹ *ᵥ x) = x`. Introduce `x`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hn', Matrix.one_mulVec]`.

Establish `hPi : ∀ x, D.prW k r S.z (n⁻¹ *ᵥ x) = D.prW k r S.z x`. Introduce `x`. Establish `h` using `hPn (n⁻¹ *ᵥ x)`. Rewrite `h` using `[hnn]`. Conclude with `h.symm`.

Establish `hPi' : ∀ x, D.prW k r S.z' (n'⁻¹ *ᵥ x) = D.prW k r S.z' x`. Introduce `x`. Establish `h` using `hPn' (n'⁻¹ *ᵥ x)`. Rewrite `h` using `[hnn']`. Conclude with `h.symm`.

Establish `hFi : n⁻¹ * Fz k r S.z = Fz k r S.z * U⁻¹` using `inv_mul_fz_eq_fz_mul_inv hF hn hUu`. Establish `hFi' : n'⁻¹ * Fz k r S.z' = Fz k r S.z' * U'⁻¹` using `inv_mul_fz_eq_fz_mul_inv hF' hn' hU'u`. Establish `hcR : D.cofR S (n⁻¹ * γ * n') = n⁻¹ *ᵥ D.cofR S γ`. Establish `hUU : ∀ w, U' *ᵥ (U'.adjugate *ᵥ w) = w`. Introduce `w`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdU', one_smul, Matrix.one_mulVec]`. Establish `hFv : ∀ w, n' *ᵥ (Fz k r S.z' *ᵥ w) = Fz k r S.z' *ᵥ (U' *ᵥ w)`. Introduce `w`. Rewrite using `[Matrix.mulVec_mulVec, hF', ← Matrix.mulVec_mulVec]`. Rewrite using `[cofR_eq, cofR_eq, hZ, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]`.

Simplify using `only [← Matrix.mulVec_mulVec]`. Rewrite using `[LT_col_last (UT_star hU), hFv, hUU]`. Establish `hcL : D.cofL S (n⁻¹ * γ * n') = n⁻¹ *ᵥ D.cofL S γ`. Rewrite using `[cofL_eq, cofL_eq, hZ, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]`. Simplify using `only [← Matrix.vecMul_vecMul]`.

Rewrite using `[UT_row_last hU', Matrix.star_vecMul, Matrix.adjugate_conjTranspose, Matrix.conjTranspose_conjTranspose, adj_eq_inv hdU, Matrix.mulVec_mulVec, ← hFi, ← Matrix.mulVec_mulVec]`. Establish `hhn : ∀ u y, herm (Hpk k r) (n *ᵥ u) y = herm (Hpk k r) u (n⁻¹ *ᵥ y)`. Introduce `u y`. Rewrite using `[← herm_m0_mulVec_invariant n hnH u (n⁻¹ *ᵥ y), hnn]`. Unfold `D.IsDFrame at hD ⊢`.

Take `⟨h1, h2, h3⟩` from `hD`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨a, ha, h⟩` from `h1`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[hcR, hPi, hdet]`.

Conclude with `h`. Take `⟨a, ha, h⟩` from `h2`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[hcL, hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hnn, hPi', hdet]`. Conclude with `h`.

Introduce `u hu`. Establish `hcond : ∀ a, herm (Hpk k r) (n *ᵥ u) (fvec k r S.z a) = 0 ∧ herm (Hpk k r) (n *ᵥ u) (γ *ᵥ fvec k r S.z' a) = 0`. Introduce `a`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hhn, col_lemma' hFi, herm_sum_right]`.

Conclude with `Finset.sum_eq_zero fun c _ => by rw [HermitianXiVector.herm_smul_r, (hu c).1, mul_zero]`. Establish `e : n⁻¹ *ᵥ (γ *ᵥ fvec k r S.z' a) = (n⁻¹ * γ * n') *ᵥ (n'⁻¹ *ᵥ fvec k r S.z' a)`. Rewrite using `[← Matrix.mulVec_mulVec, hnn', ← Matrix.mulVec_mulVec]`. Rewrite using `[hhn, e, col_lemma' hFi', Matrix.mulVec_sum, herm_sum_right]`. Conclude with `Finset.sum_eq_zero fun c _ => by`.

Rewrite using `[Matrix.mulVec_smul, HermitianXiVector.herm_smul_r, (hu c).2, mul_zero]`. Establish `key` using `h3 (n *ᵥ u) hcond`. Rewrite using `[hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPi', ← key, hPn]`.
-/
private theorem isDFrame_inv_mul_mul_of_frame_compat (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    {γ n n' : B.Mat k r} {U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hn : IsUnit n.det) (hn' : IsUnit n'.det) (hnH : n ∈ UH (Hpk k r))
    (hU : U ∈ C2.UTset (r + 1)) (hU' : U' ∈ C2.UTset (r + 1))
    (hF : n * Fz k r S.z = Fz k r S.z * U) (hF' : n' * Fz k r S.z' = Fz k r S.z' * U')
    (hPn : ∀ x, D.prW k r S.z (n *ᵥ x) = D.prW k r S.z x)
    (hPn' : ∀ x, D.prW k r S.z' (n' *ᵥ x) = D.prW k r S.z' x)
    (hD : D.IsDFrame S ν' m₀ γ) : D.IsDFrame S ν' m₀ (n⁻¹ * γ * n') := by
  have hdU : U.det = 1 := det_UT hU
  have hdU' : U'.det = 1 := det_UT hU'
  have hUu : IsUnit U.det := by
    rw [hdU]
    exact isUnit_one
  have hU'u : IsUnit U'.det := by
    rw [hdU']
    exact isUnit_one
  have hZ := zhat_inv_mul_mul_eq_conjTranspose_mul_mul (γ := γ) S.z S.z' hn hnH hF hF'
  have hdet : (Zhat k r S.z S.z' (n⁻¹ * γ * n')).det = (Zhat k r S.z S.z' γ).det := by
    rw [hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdU, hdU']
    simp
  have hinv : (n⁻¹ * γ * n')⁻¹ = n'⁻¹ * (γ⁻¹ * n) := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hn]
  have hnn : ∀ x, n *ᵥ (n⁻¹ *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hn, Matrix.one_mulVec]
  have hnn' : ∀ x, n' *ᵥ (n'⁻¹ *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hn', Matrix.one_mulVec]
  have hPi : ∀ x, D.prW k r S.z (n⁻¹ *ᵥ x) = D.prW k r S.z x := by
    intro x
    have h := hPn (n⁻¹ *ᵥ x)
    rw [hnn] at h
    exact h.symm
  have hPi' : ∀ x, D.prW k r S.z' (n'⁻¹ *ᵥ x) = D.prW k r S.z' x := by
    intro x
    have h := hPn' (n'⁻¹ *ᵥ x)
    rw [hnn'] at h
    exact h.symm
  have hFi : n⁻¹ * Fz k r S.z = Fz k r S.z * U⁻¹ := inv_mul_fz_eq_fz_mul_inv hF hn hUu
  have hFi' : n'⁻¹ * Fz k r S.z' = Fz k r S.z' * U'⁻¹ := inv_mul_fz_eq_fz_mul_inv hF' hn' hU'u
  have hcR : D.cofR S (n⁻¹ * γ * n') = n⁻¹ *ᵥ D.cofR S γ := by
    have hUU : ∀ w, U' *ᵥ (U'.adjugate *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdU', one_smul, Matrix.one_mulVec]
    have hFv : ∀ w, n' *ᵥ (Fz k r S.z' *ᵥ w) = Fz k r S.z' *ᵥ (U' *ᵥ w) := by
      intro w
      rw [Matrix.mulVec_mulVec, hF', ← Matrix.mulVec_mulVec]
    rw [cofR_eq, cofR_eq, hZ, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
    simp only [← Matrix.mulVec_mulVec]
    rw [LT_col_last (UT_star hU), hFv, hUU]
  have hcL : D.cofL S (n⁻¹ * γ * n') = n⁻¹ *ᵥ D.cofL S γ := by
    rw [cofL_eq, cofL_eq, hZ, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
    simp only [← Matrix.vecMul_vecMul]
    rw [UT_row_last hU', Matrix.star_vecMul, Matrix.adjugate_conjTranspose, Matrix.conjTranspose_conjTranspose,
      adj_eq_inv hdU, Matrix.mulVec_mulVec, ← hFi, ← Matrix.mulVec_mulVec]
  have hhn : ∀ u y, herm (Hpk k r) (n *ᵥ u) y = herm (Hpk k r) u (n⁻¹ *ᵥ y) := by
    intro u y
    rw [← herm_m0_mulVec_invariant n hnH u (n⁻¹ *ᵥ y), hnn]
  unfold D.IsDFrame at hD ⊢
  obtain ⟨h1, h2, h3⟩ := hD
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, ha, h⟩ := h1
    refine ⟨a, ha, ?_⟩
    rw [hcR, hPi, hdet]
    exact h
  · obtain ⟨a, ha, h⟩ := h2
    refine ⟨a, ha, ?_⟩
    rw [hcL, hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hnn, hPi', hdet]
    exact h
  · intro u hu
    have hcond : ∀ a, herm (Hpk k r) (n *ᵥ u) (fvec k r S.z a) = 0 ∧
        herm (Hpk k r) (n *ᵥ u) (γ *ᵥ fvec k r S.z' a) = 0 := by
      intro a
      constructor
      · rw [hhn, col_lemma' hFi, herm_sum_right]
        exact Finset.sum_eq_zero fun c _ => by rw [HermitianXiVector.herm_smul_r, (hu c).1, mul_zero]
      · have e : n⁻¹ *ᵥ (γ *ᵥ fvec k r S.z' a) = (n⁻¹ * γ * n') *ᵥ (n'⁻¹ *ᵥ fvec k r S.z' a) := by
          rw [← Matrix.mulVec_mulVec, hnn', ← Matrix.mulVec_mulVec]
        rw [hhn, e, col_lemma' hFi', Matrix.mulVec_sum, herm_sum_right]
        exact Finset.sum_eq_zero fun c _ => by
          rw [Matrix.mulVec_smul, HermitianXiVector.herm_smul_r, (hu c).2, mul_zero]
    have key := h3 (n *ᵥ u) hcond
    rw [hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPi', ← key, hPn]

/- English proof (translation)
Conclude with `(c2_tau_mem k r z hz v hv).1`.
-/
theorem tau_N {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hv : v ∈ C2.UTset (r + 1)) : C2.tauM k r z v ∈ Nset k r := by
  exact (c2_tau_mem k r z hz v hv).1

/- English proof (translation)
Rewrite using `[herm_self_alt, neg_ne_zero, Complex.ofReal_ne_zero]`. Conclude with `hz.2.ne'`.
-/
theorem hzz_ne {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) : herm (Hpk k r) z z ≠ 0 := by
  rw [herm_self_alt, neg_ne_zero, Complex.ofReal_ne_zero]
  exact hz.2.ne'

/- English proof (translation)
Establish `hu` using `isUnit_N (tau_N hz hv)`. Establish `h` using `prW_tau hz.1 (hzz_ne hz) v ((C2.tauM k r z v)⁻¹ *ᵥ x)`. Rewrite `h` using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]`. Conclude with `h.symm`.
-/
theorem prW_tau_inv {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hv : v ∈ C2.UTset (r + 1)) (x : Fin (2 * r + k + 1) → ℂ) :
    D.prW k r z ((C2.tauM k r z v)⁻¹ *ᵥ x) = D.prW k r z x := by
  have hu := isUnit_N (tau_N hz hv)
  have h := prW_tau hz.1 (hzz_ne hz) v ((C2.tauM k r z v)⁻¹ *ᵥ x)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec] at h
  exact h.symm

/- English proof (translation)
Establish `hz : C2.StdZ k r S.z` using `⟨S.z_mem, S.T_pos⟩`. Establish `hz' : C2.StdZ k r S.z'` using `⟨S.z'_mem, S.T'_pos⟩`. Establish `hN` using `tau_N hz hv`. Establish `hN'` using `tau_N hz' hu'`. Establish `hτu` using `isUnit_N hN`.

Establish `hτu'` using `isUnit_N hN'`. Establish `hvu : IsUnit v.det`. Rewrite using `[det_UT hv]`. Conclude with `isUnit_one`. Establish `hu'u : IsUnit u'.det`.

Rewrite using `[det_UT hu']`. Conclude with `isUnit_one`. Establish `hF : C2.tauM k r S.z v * Fz k r S.z = Fz k r S.z * v`. Establish `h` using `frame_mul hz (n_in_S hN)`. Rewrite `h` using `[(c2_tau_mem k r S.z hz v hv).2.2]`. Then use the resulting hypothesis.

Establish `hF' : C2.tauM k r S.z' u' * Fz k r S.z' = Fz k r S.z' * u'`. Establish `h` using `frame_mul hz' (n_in_S hN')`. Rewrite `h` using `[(c2_tau_mem k r S.z' hz' u' hu').2.2]`. Then use the resulting hypothesis. Establish `hinvH : (C2.tauM k r S.z v)⁻¹ ∈ UH (Hpk k r)`. Establish `hg : (C2.tauM k r S.z v)ᴴ * Hpk k r * C2.tauM k r S.z v = Hpk k r` using `hN.1`.

Use `show ((C2.tauM k r S.z v)⁻¹)ᴴ * Hpk k r * (C2.tauM k r S.z v)⁻¹ = Hpk k r`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by`.

Rewrite using `[Matrix.mul_nonsing_inv _ hτu]`. Simplify using the standard rewrite rules. Establish `h` using `isDFrame_inv_mul_mul_of_frame_compat S ν' m₀ (Matrix.isUnit_nonsing_inv_det _ hτu) (Matrix.isUnit_nonsing_inv_det _ hτu') hinvH (C2x2.ut_inv hv) (C2x2.ut_inv hu') (inv_mul_fz_eq_fz_mul_inv hF hτu hvu) (inv_mul_fz_eq_fz_mul_inv hF' hτu' hu'u) (prW_tau_inv hz hv) (prW_tau_inv hz' h …`. Rewrite `h` using `[Matrix.nonsing_inv_nonsing_inv _ hτu]`. Then use the resulting hypothesis.
-/
theorem dframe_tau_inv (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) (hD : D.IsDFrame S ν' m₀ γ)
    {v u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hv : v ∈ C2.UTset (r + 1)) (hu' : u' ∈ C2.UTset (r + 1)) :
    D.IsDFrame S ν' m₀ (C2.tauM k r S.z v * γ * (C2.tauM k r S.z' u')⁻¹) := by
  have hz : C2.StdZ k r S.z := ⟨S.z_mem, S.T_pos⟩
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  have hN := tau_N hz hv
  have hN' := tau_N hz' hu'
  have hτu := isUnit_N hN
  have hτu' := isUnit_N hN'
  have hvu : IsUnit v.det := by
    rw [det_UT hv]
    exact isUnit_one
  have hu'u : IsUnit u'.det := by
    rw [det_UT hu']
    exact isUnit_one
  have hF : C2.tauM k r S.z v * Fz k r S.z = Fz k r S.z * v := by
    have h := frame_mul hz (n_in_S hN)
    rwa [(c2_tau_mem k r S.z hz v hv).2.2] at h
  have hF' : C2.tauM k r S.z' u' * Fz k r S.z' = Fz k r S.z' * u' := by
    have h := frame_mul hz' (n_in_S hN')
    rwa [(c2_tau_mem k r S.z' hz' u' hu').2.2] at h
  have hinvH : (C2.tauM k r S.z v)⁻¹ ∈ UH (Hpk k r) := by
    have hg : (C2.tauM k r S.z v)ᴴ * Hpk k r * C2.tauM k r S.z v = Hpk k r := hN.1
    show ((C2.tauM k r S.z v)⁻¹)ᴴ * Hpk k r * (C2.tauM k r S.z v)⁻¹ = Hpk k r
    calc ((C2.tauM k r S.z v)⁻¹)ᴴ * Hpk k r * (C2.tauM k r S.z v)⁻¹
        = ((C2.tauM k r S.z v)⁻¹)ᴴ * ((C2.tauM k r S.z v)ᴴ * Hpk k r * C2.tauM k r S.z v) *
            (C2.tauM k r S.z v)⁻¹ := by rw [hg]
      _ = (C2.tauM k r S.z v * (C2.tauM k r S.z v)⁻¹)ᴴ * Hpk k r *
            (C2.tauM k r S.z v * (C2.tauM k r S.z v)⁻¹) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by
          rw [Matrix.mul_nonsing_inv _ hτu]
          simp
  have h := isDFrame_inv_mul_mul_of_frame_compat S ν' m₀ (Matrix.isUnit_nonsing_inv_det _ hτu) (Matrix.isUnit_nonsing_inv_det _ hτu') hinvH
    (C2x2.ut_inv hv) (C2x2.ut_inv hu') (inv_mul_fz_eq_fz_mul_inv hF hτu hvu) (inv_mul_fz_eq_fz_mul_inv hF' hτu' hu'u)
    (prW_tau_inv hz hv) (prW_tau_inv hz' hu') hD
  rwa [Matrix.nonsing_inv_nonsing_inv _ hτu] at h

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.A
