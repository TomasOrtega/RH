import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.FormalDegreeBessel.FinalG

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x2

variable {m : ℕ}

/- English proof (translation)
Introduce `i j h` and use `hu.1 i j h`.
-/
lemma ut_bt {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u.BlockTriangular id :=
  fun i j h => hu.1 i j h

/- English proof (translation)
Introduce `i j h` and use `hl.1 i j (OrderDual.toDual_lt_toDual.mp h)`.
-/
lemma lt_bt {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : l.BlockTriangular OrderDual.toDual :=
  fun i j h => hl.1 i j (OrderDual.toDual_lt_toDual.mp h)

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne (hb.ne hk) with h | h` into its components or cases. Rewrite using `[hM h, zero_mul]`. Rewrite using `[hN h, mul_zero]`.

Simplify using the standard rewrite rules.
-/
lemma bt_mul_diag {α : Type*} [LinearOrder α] {b : Fin m → α} (hb : Function.Injective b)
    {M N : Matrix (Fin m) (Fin m) ℂ} (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) (i : Fin m) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne (hb.ne hk) with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · simp

/- English proof (translation)
Use `haveI := M.invertibleOfIsUnitDet hu`. Establish `hi` using `Matrix.blockTriangular_inv_of_blockTriangular hM`. Use `⟨hi, fun i => ?_⟩` and prove the remaining obligations. Use `congrFun (congrFun (Matrix.mul_nonsing_inv M hu) i) i` as an intermediate fact. Rewrite `this` using `[bt_mul_diag hb hM hi, hd, one_mul, Matrix.one_apply_eq]`.

Conclude with `this`.
-/
lemma bt_inv_facts {α : Type*} [LinearOrder α] {b : Fin m → α} (hb : Function.Injective b)
    {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.BlockTriangular b) (hd : ∀ i, M i i = 1) (hu : IsUnit M.det) :
    M⁻¹.BlockTriangular b ∧ ∀ i, M⁻¹ i i = 1 := by
  haveI := M.invertibleOfIsUnitDet hu
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hM
  refine ⟨hi, fun i => ?_⟩
  have := congrFun (congrFun (Matrix.mul_nonsing_inv M hu) i) i
  rw [bt_mul_diag hb hM hi, hd, one_mul, Matrix.one_apply_eq] at this
  exact this

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular (ut_bt hu)]`. Simplify using `[hu.2]`.
-/
lemma ut_det {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (ut_bt hu)]
  simp [hu.2]

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular _ (lt_bt hl)]`. Simplify using `[hl.2]`.
-/
lemma lt_det {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (lt_bt hl)]
  simp [hl.2]

/- English proof (translation)
Rewrite using `[ut_det hu]`. Conclude with `isUnit_one`.
-/
lemma ut_unit {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : IsUnit u.det := by
  rw [ut_det hu]; exact isUnit_one

/- English proof (translation)
Rewrite using `[lt_det hl]`. Conclude with `isUnit_one`.
-/
lemma lt_unit {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : IsUnit l.det := by
  rw [lt_det hl]; exact isUnit_one

/- English proof (translation)
Take `⟨h1, h2⟩` from `bt_inv_facts Function.injective_id (ut_bt hu) hu.2 (ut_unit hu)`. Conclude with `⟨fun i j h => h1 h, h2⟩`.
-/
lemma ut_inv {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u⁻¹ ∈ C2.UTset m := by
  obtain ⟨h1, h2⟩ := bt_inv_facts Function.injective_id (ut_bt hu) hu.2 (ut_unit hu)
  exact ⟨fun i j h => h1 h, h2⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `bt_inv_facts OrderDual.toDual.injective (lt_bt hl) hl.2 (lt_unit hl)`. Conclude with `⟨fun i j h => h1 (OrderDual.toDual_lt_toDual.mpr h), h2⟩`.
-/
lemma lt_inv {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : l⁻¹ ∈ C2.LTset m := by
  obtain ⟨h1, h2⟩ := bt_inv_facts OrderDual.toDual.injective (lt_bt hl) hl.2 (lt_unit hl)
  exact ⟨fun i j h => h1 (OrderDual.toDual_lt_toDual.mpr h), h2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j h => ((ut_bt hu).mul (ut_bt hv)) h, fun i => by rw [bt_mul_diag Function.injective_id (ut_bt hu) (ut_bt hv), hu.2, hv.2, one_mul]⟩`.
-/
lemma ut_mul {u v : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (hv : v ∈ C2.UTset m) :
    u * v ∈ C2.UTset m :=
  ⟨fun i j h => ((ut_bt hu).mul (ut_bt hv)) h,
   fun i => by rw [bt_mul_diag Function.injective_id (ut_bt hu) (ut_bt hv), hu.2, hv.2, one_mul]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j h => ((lt_bt hu).mul (lt_bt hv)) (OrderDual.toDual_lt_toDual.mpr h), fun i => by rw [bt_mul_diag OrderDual.toDual.injective (lt_bt hu) (lt_bt hv), hu.2, hv.2, one_mul]⟩`.
-/
lemma lt_mul {u v : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.LTset m) (hv : v ∈ C2.LTset m) :
    u * v ∈ C2.LTset m :=
  ⟨fun i j h => ((lt_bt hu).mul (lt_bt hv)) (OrderDual.toDual_lt_toDual.mpr h),
   fun i => by rw [bt_mul_diag OrderDual.toDual.injective (lt_bt hu) (lt_bt hv), hu.2, hv.2, one_mul]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j h => by rw [Matrix.conjTranspose_apply, hu.1 j i h, star_zero], fun i => by rw [Matrix.conjTranspose_apply, hu.2, star_one]⟩`.
-/
lemma ut_conjT {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : uᴴ ∈ C2.LTset m :=
  ⟨fun i j h => by rw [Matrix.conjTranspose_apply, hu.1 j i h, star_zero],
   fun i => by rw [Matrix.conjTranspose_apply, hu.2, star_one]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j h => by rw [Matrix.conjTranspose_apply, hl.1 j i h, star_zero], fun i => by rw [Matrix.conjTranspose_apply, hl.2, star_one]⟩`.
-/
lemma lt_conjT {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : lᴴ ∈ C2.UTset m :=
  ⟨fun i j h => by rw [Matrix.conjTranspose_apply, hl.1 j i h, star_zero],
   fun i => by rw [Matrix.conjTranspose_apply, hl.2, star_one]⟩

/- English proof (translation)
Establish `hi` using `ut_inv hu`. Establish `hne : a ≠ ⟨a.val + 1, h⟩` using `fun e => by have := congrArg Fin.val e; simp at this`. Establish `e` using `congrFun (congrFun (Matrix.mul_nonsing_inv u (ut_unit hu)) a) ⟨a.val + 1, h⟩`. Rewrite `e` using `[Matrix.mul_apply, Matrix.one_apply_ne hne, Fintype.sum_eq_add a ⟨a.val + 1, h⟩ hne]`. Rewrite `e` using `[hu.2, hi.2, one_mul, mul_one]`.

Take the linear combination `e`. Introduce `k ⟨hk1, hk2⟩`. Break down `lt_or_gt_of_ne hk1 with hl | hl` into its components or cases. Rewrite using `[hu.1 a k hl, zero_mul]`. Establish `: (⟨a.val + 1, h⟩ : Fin m) < k`.

Rewrite `hl`, the goal using `[Fin.lt_def]`. Establish `: k.val ≠ a.val + 1` using `fun e => hk2 (Fin.ext e)`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hi.1 k _ this, mul_zero]`.
-/
lemma ut_inv_super {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (a : Fin m) (h : a.val + 1 < m) :
    u⁻¹ a ⟨a.val + 1, h⟩ = -u a ⟨a.val + 1, h⟩ := by
  have hi := ut_inv hu
  have hne : a ≠ ⟨a.val + 1, h⟩ := fun e => by have := congrArg Fin.val e; simp at this
  have e := congrFun (congrFun (Matrix.mul_nonsing_inv u (ut_unit hu)) a) ⟨a.val + 1, h⟩
  rw [Matrix.mul_apply, Matrix.one_apply_ne hne, Fintype.sum_eq_add a ⟨a.val + 1, h⟩ hne] at e
  · rw [hu.2, hi.2, one_mul, mul_one] at e
    linear_combination e
  · intro k ⟨hk1, hk2⟩
    rcases lt_or_gt_of_ne hk1 with hl | hl
    · rw [hu.1 a k hl, zero_mul]
    · have : (⟨a.val + 1, h⟩ : Fin m) < k := by
        rw [Fin.lt_def] at hl ⊢
        have : k.val ≠ a.val + 1 := fun e => hk2 (Fin.ext e)
        simp only; omega
      rw [hi.1 k _ this, mul_zero]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [C2.monoP, Matrix.mul_apply, Matrix.of_apply]`. Rewrite using `[Finset.sum_eq_single (w j)]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `[hd i]`. Rewrite using `[if_neg (by simpa using hij), zero_mul, Matrix.one_apply_ne hij]`. Introduce `k _ hk`. Rewrite using `[if_neg hk, mul_zero]`. Simplify using the standard rewrite rules.
-/
lemma monomialMatrix_inv_left (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    C2.monoP w.symm (fun i => (d (w.symm i))⁻¹) * C2.monoP w d = 1 := by
  ext i j
  simp only [C2.monoP, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (w j)]
  · by_cases hij : i = j
    · subst hij; simp [hd i]
    · rw [if_neg (by simpa using hij), zero_mul, Matrix.one_apply_ne hij]
  · intro k _ hk; rw [if_neg hk, mul_zero]
  · simp

/- English proof (translation)
The claim follows from `Matrix.isUnit_det_of_left_inverse (monomialMatrix_inv_left w d hd)`.
-/
lemma isUnit_det_monomialMatrix (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) : IsUnit (C2.monoP w d).det :=
  Matrix.isUnit_det_of_left_inverse (monomialMatrix_inv_left w d hd)

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv (monomialMatrix_inv_left w d hd)`.
-/
lemma monomialMatrix_inv (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    (C2.monoP w d)⁻¹ = C2.monoP w.symm (fun i => (d (w.symm i))⁻¹) :=
  Matrix.inv_eq_left_inv (monomialMatrix_inv_left w d hd)

/- English proof (translation)
Rewrite using `[monomialMatrix_inv w d hd]`. Simplify using `only [Matrix.mul_apply, C2.monoP, Matrix.of_apply]`. Rewrite using `[Finset.sum_eq_single (w b)]`. Rewrite using `[if_pos rfl, Finset.sum_eq_single (w a)]`. Simplify using the standard rewrite rules.

Introduce `k _ hk`. Rewrite using `[if_neg (fun e => hk (by rw [e]; simp)), zero_mul]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Rewrite using `[if_neg hk, mul_zero]`.

Simplify using the standard rewrite rules.
-/
lemma monomialMatrix_conj_apply (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) :
    ((C2.monoP w d)⁻¹ * l * C2.monoP w d) a b = (d a)⁻¹ * l (w a) (w b) * d b := by
  rw [monomialMatrix_inv w d hd]
  simp only [Matrix.mul_apply, C2.monoP, Matrix.of_apply]
  rw [Finset.sum_eq_single (w b)]
  · rw [if_pos rfl, Finset.sum_eq_single (w a)]
    · simp
    · intro k _ hk
      rw [if_neg (fun e => hk (by rw [e]; simp)), zero_mul]
    · simp
  · intro k _ hk; rw [if_neg hk, mul_zero]
  · simp

/- English proof (translation)
Take `⟨w, d, hd, rfl⟩` from `hP`. Conclude with `isUnit_det_monomialMatrix w d hd`.
-/
lemma isMonomial_unit {P : Matrix (Fin m) (Fin m) ℂ} (hP : C2.IsMonomial P) : IsUnit P.det := by
  obtain ⟨w, d, hd, rfl⟩ := hP
  exact isUnit_det_monomialMatrix w d hd

end C2x2

open C2x2

/- English proof (translation)
Introduce `m u hu a h`. Rewrite using `[Matrix.conjTranspose_apply, ut_inv_super hu a h]`. Simplify using the standard rewrite rules.
-/
theorem inverse_star_substitution : C2.InvStarSub := by
  intro m u hu a h
  rw [Matrix.conjTranspose_apply, ut_inv_super hu a h]
  simp

/- English proof (translation)
Simplify using `only [C2.antiW, Matrix.mul_apply, Matrix.of_apply]`. Rewrite using `[Finset.sum_eq_single i.rev]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Rewrite using `[if_neg hk, zero_mul]`.

Simplify using the standard rewrite rules.
-/
lemma c2x2_antiW_mul {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ) (i j : Fin s) :
    (C2.antiW s * M) i j = M i.rev j := by
  simp only [C2.antiW, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single i.rev]
  · simp
  · intro k _ hk; rw [if_neg hk, zero_mul]
  · simp

/- English proof (translation)
Simplify using `only [C2.antiW, Matrix.mul_apply, Matrix.of_apply]`. Rewrite using `[Finset.sum_eq_single j.rev]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Rewrite using `[if_neg, mul_zero]`.

Introduce `e`. Apply `hk` to reduce the goal to its premises. Rewrite using `[e, Fin.rev_rev]`. Simplify using the standard rewrite rules.
-/
lemma c2x2_mul_antiW {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ) (i j : Fin s) :
    (M * C2.antiW s) i j = M i j.rev := by
  simp only [C2.antiW, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro k _ hk
    rw [if_neg, mul_zero]
    intro e; apply hk; rw [e, Fin.rev_rev]
  · simp

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[c2x2_antiW_mul]`. Simplify using `only [C2.antiW, Matrix.of_apply, Fin.rev_rev, Matrix.one_apply]`. Distinguish the cases in `h : i = j`. Simplify using `[h]`.

Rewrite using `[if_neg (fun e => h e.symm), if_neg h]`.
-/
lemma c2x2_antiW_sq (s : ℕ) : C2.antiW s * C2.antiW s = 1 := by
  ext i j
  rw [c2x2_antiW_mul]
  simp only [C2.antiW, Matrix.of_apply, Fin.rev_rev, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg (fun e => h e.symm), if_neg h]

/- English proof (translation)
Unfold `C2.simpleLow`. Rewrite using `[Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[dif_pos (by have := a.isLt; simp only [Fin.coe_castSucc]; omega)]`. Both sides reduce to the same expression.
-/
lemma c2x2_simpleLow_succ {n : ℕ} (l : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    C2.simpleLow l = ∑ a : Fin n, l a.succ a.castSucc := by
  unfold C2.simpleLow
  rw [Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [dif_pos (by have := a.isLt; simp only [Fin.coe_castSucc]; omega)]
  rfl

/- English proof (translation)
Unfold `C2.simpleUp`. Rewrite using `[Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[dif_pos (by have := a.isLt; simp only [Fin.coe_castSucc]; omega)]`. Both sides reduce to the same expression.
-/
lemma c2x2_simpleUp_succ {n : ℕ} (u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    C2.simpleUp u = ∑ a : Fin n, u a.castSucc a.succ := by
  unfold C2.simpleUp
  rw [Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [dif_pos (by have := a.isLt; simp only [Fin.coe_castSucc]; omega)]
  rfl

/- English proof (translation)
Introduce `s u t hu ht`. Establish `hi` using `ut_inv hu`. Use `⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[c2x2_mul_antiW, c2x2_antiW_mul]`. Conclude with `hi.1 _ _ (Fin.rev_lt_rev.mpr hij)`.

Rewrite using `[c2x2_mul_antiW, c2x2_antiW_mul]`. Conclude with `hi.2 _`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]`. Use `_ = t • C2.antiW s := by`.

Rewrite using `[c2x2_antiW_sq, Matrix.mul_one, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (ut_unit hu), Matrix.mul_one]`. Break down `s with _ | n` into its components or cases. Simplify using `[C2.simpleLow, C2.simpleUp]`. Rewrite using `[c2x2_simpleLow_succ, c2x2_simpleUp_succ]`. Establish `e1 : ∀ a : Fin n, (C2.antiW (n + 1) * u⁻¹ * C2.antiW (n + 1)) a.succ a.castSucc = -u a.rev.castSucc a.rev.succ`.

Introduce `a`. Rewrite using `[c2x2_mul_antiW, c2x2_antiW_mul, Fin.rev_succ, Fin.rev_castSucc]`. Use `ut_inv_super hu a.rev.castSucc (by simp only [Fin.coe_castSucc]; exact Nat.succ_lt_succ a.rev.isLt)` as an intermediate fact. Conclude with `this`. Simplify using `only [e1]`.

Rewrite using `[Finset.sum_neg_distrib]`. Establish `e2 : ∑ a : Fin n, u a.rev.castSucc a.rev.succ = ∑ a : Fin n, u a.castSucc a.succ` using `Equiv.sum_comp Fin.revPerm (fun a => u a.castSucc a.succ)`. Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stabilizer_antidiagonal : C2.StabAntidiag := by
  intro s u t hu ht
  have hi := ut_inv hu
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, ?_⟩
  · rw [c2x2_mul_antiW, c2x2_antiW_mul]
    exact hi.1 _ _ (Fin.rev_lt_rev.mpr hij)
  · rw [c2x2_mul_antiW, c2x2_antiW_mul]
    exact hi.2 _
  · calc C2.antiW s * u⁻¹ * C2.antiW s * (t • C2.antiW s) * u
        = t • (C2.antiW s * u⁻¹ * (C2.antiW s * C2.antiW s) * u) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = t • C2.antiW s := by
          rw [c2x2_antiW_sq, Matrix.mul_one, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (ut_unit hu),
            Matrix.mul_one]
  · rcases s with _ | n
    · simp [C2.simpleLow, C2.simpleUp]
    · rw [c2x2_simpleLow_succ, c2x2_simpleUp_succ]
      have e1 : ∀ a : Fin n, (C2.antiW (n + 1) * u⁻¹ * C2.antiW (n + 1)) a.succ a.castSucc =
          -u a.rev.castSucc a.rev.succ := by
        intro a
        rw [c2x2_mul_antiW, c2x2_antiW_mul, Fin.rev_succ, Fin.rev_castSucc]
        have := ut_inv_super hu a.rev.castSucc (by simp only [Fin.coe_castSucc]; exact Nat.succ_lt_succ a.rev.isLt)
        exact this
      simp only [e1]
      rw [Finset.sum_neg_distrib]
      have e2 : ∑ a : Fin n, u a.rev.castSucc a.rev.succ = ∑ a : Fin n, u a.castSucc a.succ :=
        Equiv.sum_comp Fin.revPerm (fun a => u a.castSucc a.succ)
      rw [e2]; ring

/- English proof (translation)
Introduce `m P hP`. Establish `hPu` using `isMonomial_unit hP`. Use extensionality with `u`. Simplify using `only [Set.mem_setOf_eq, C2.Lstg]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hu, u', hu', he⟩`. Use `⟨hu, ut_conjT hu, ?_⟩` and prove the remaining obligations. Establish `: P⁻¹ * uᴴ * P = u'⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv _ (ut_unit hu'), Matrix.mul_one]`.

Use `_ = P⁻¹ * (uᴴ * P * u') * u'⁻¹ := by simp only [Matrix.mul_assoc]`. Use `_ = u'⁻¹ := by rw [he, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul]`. Rewrite using `[this]`. Conclude with `ut_inv hu'`. Introduce and unpack `⟨hu, _, hX⟩`.

Use `⟨hu, (P⁻¹ * uᴴ * P)⁻¹, ut_inv hX, ?_⟩` and prove the remaining obligations. Establish `e : uᴴ * P = P * (P⁻¹ * uᴴ * P)`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]`. Rewrite using `[e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (ut_unit hX), Matrix.mul_one]`.
-/
theorem unipotent_radical_image : C2.URImage := by
  intro m P hP
  have hPu := isMonomial_unit hP
  ext u
  simp only [Set.mem_setOf_eq, C2.Lstg]
  constructor
  · rintro ⟨hu, u', hu', he⟩
    refine ⟨hu, ut_conjT hu, ?_⟩
    have : P⁻¹ * uᴴ * P = u'⁻¹ := by
      calc P⁻¹ * uᴴ * P = P⁻¹ * uᴴ * P * (u' * u'⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ (ut_unit hu'), Matrix.mul_one]
        _ = P⁻¹ * (uᴴ * P * u') * u'⁻¹ := by simp only [Matrix.mul_assoc]
        _ = u'⁻¹ := by rw [he, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul]
    rw [this]; exact ut_inv hu'
  · rintro ⟨hu, _, hX⟩
    refine ⟨hu, (P⁻¹ * uᴴ * P)⁻¹, ut_inv hX, ?_⟩
    have e : uᴴ * P = P * (P⁻¹ * uᴴ * P) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    rw [e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (ut_unit hX), Matrix.mul_one]

/- English proof (translation)
Introduce `hLow m P hP u hu`. Take `⟨p, ⟨hp1, hp2, hpe⟩, huniq⟩` from `hLow m P hP uᴴ (ut_conjT hu)`. Use `⟨(p.2ᴴ, p.1ᴴ), ⟨lt_conjT hp2.1, lt_conjT hp1.1, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `using hp2`. Simplify using `using hp1`.

Simplify using `only`. Rewrite using `[← Matrix.conjTranspose_mul, ← hpe, Matrix.conjTranspose_conjTranspose]`. Introduce and unpack `q ⟨_, _, hq1, hq2, hqe⟩`. Use `huniq (q.2ᴴ, q.1ᴴ) ⟨hq2, hq1, by` as an intermediate fact. Simplify using `only`.

Rewrite using `[← Matrix.conjTranspose_mul, ← hqe]⟩`. Rewrite `this` using `[Prod.ext_iff]`. Simplify using `only at this`. Take `⟨e1, e2⟩` from `this`. Apply `Prod.ext` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[← e2, Matrix.conjTranspose_conjTranspose]`. Simplify using `only`. Rewrite using `[← e1, Matrix.conjTranspose_conjTranspose]`.
-/
theorem upper_splitting_of_lower : C2.UpSplitOfLowSplit := by
  intro hLow m P hP u hu
  obtain ⟨p, ⟨hp1, hp2, hpe⟩, huniq⟩ := hLow m P hP uᴴ (ut_conjT hu)
  refine ⟨(p.2ᴴ, p.1ᴴ), ⟨lt_conjT hp2.1, lt_conjT hp1.1, ?_, ?_, ?_⟩, ?_⟩
  · simpa using hp2
  · simpa using hp1
  · simp only
    rw [← Matrix.conjTranspose_mul, ← hpe, Matrix.conjTranspose_conjTranspose]
  · rintro q ⟨_, _, hq1, hq2, hqe⟩
    have := huniq (q.2ᴴ, q.1ᴴ) ⟨hq2, hq1, by
      simp only
      rw [← Matrix.conjTranspose_mul, ← hqe]⟩
    rw [Prod.ext_iff] at this
    simp only at this
    obtain ⟨e1, e2⟩ := this
    apply Prod.ext
    · simp only; rw [← e2, Matrix.conjTranspose_conjTranspose]
    · simp only; rw [← e1, Matrix.conjTranspose_conjTranspose]

/- English proof (translation)
Simplify using `only [C2.lowOf, Matrix.add_apply, Matrix.of_apply]`. Use `congr 1`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨(i, j), h⟩]`. Simplify using the standard rewrite rules.

Introduce `q _ hq`. Rewrite using `[if_neg]`. Introduce `e`. Apply `hq` to reduce the goal to its premises. Conclude with `Subtype.ext e`.

Simplify using the standard rewrite rules. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `q _`. Rewrite using `[if_neg]`. Introduce `e`.

Apply `h` to reduce the goal to its premises. Rewrite using `[← e]`. Conclude with `q.2`.
-/
lemma c2x2_lowOf_sub {m : ℕ} (p : Fin m × Fin m → Prop) [DecidablePred p] (v : {q : Fin m × Fin m // p q} → ℂ)
    (i j : Fin m) :
    C2.lowOf (fun q : {q : Fin m × Fin m // p q} => q.1) v i j =
      (1 : Matrix (Fin m) (Fin m) ℂ) i j + if h : p (i, j) then v ⟨(i, j), h⟩ else 0 := by
  simp only [C2.lowOf, Matrix.add_apply, Matrix.of_apply]
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro q _ hq
      rw [if_neg]
      intro e; apply hq; exact Subtype.ext e
    · simp
  · apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    intro e; apply h; rw [← e]; exact q.2

/- English proof (translation)
Introduce `m w d hd`. Establish `hPu` using `isUnit_det_monomialMatrix w d hd`. Prove the components needed by the constructor for the conclusion. Use extensionality with `l`. Simplify using `only [Set.mem_range, C2.LPg, Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, rfl⟩`. Use `⟨⟨fun i j hij => ?_, fun i => ?_⟩, ⟨fun a b hab => ?_, fun a => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[c2x2_lowOf_sub, Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))), add_zero]`. Rewrite using `[c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), add_zero]`.

Rewrite using `[monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub, Matrix.one_apply_ne (fun e => (ne_of_lt hab) (w.injective e)), dif_neg]`. Simplify using the standard rewrite rules. Introduce `h`. Simplify using `at h`. Conclude with `absurd h.2 (not_lt.mpr (le_of_lt hab))`.

Rewrite using `[monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1)]`. Simplify using `[hd a]`. Introduce and unpack `⟨hl, hc⟩`. Use `⟨fun q => l q.1.1 q.1.2, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Rewrite using `[c2x2_lowOf_sub]`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases. Rewrite using `[Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))), hl.1 i j hij, add_zero]`. Rewrite using `[Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), hl.2, add_zero]`. Rewrite using `[Matrix.one_apply_ne (ne_of_gt hij), zero_add] split_ifs with h`.

Both sides reduce to the same expression. Establish `hlt : w.symm i < w.symm j`. Establish `hne : w.symm i ≠ w.symm j` using `fun e => (ne_of_gt hij) (w.symm.injective e)`. Break down `lt_or_gt_of_ne hne with h' | h'` into its components or cases. Conclude with `h'`.

Conclude with `absurd ⟨hij, h'⟩ h`. Use `hc.1 _ _ hlt` as an intermediate fact. Rewrite `this` using `[monomialMatrix_conj_apply w d hd]`. Simplify using `only [Equiv.apply_symm_apply] at this`. Establish `hdi` using `hd (w.symm i)`.

Establish `hdj` using `hd (w.symm j)`. Break down `mul_eq_zero.mp this with h1 | h1` into its components or cases. Break down `mul_eq_zero.mp h1 with h2 | h2` into its components or cases. Conclude with `absurd h2 (inv_ne_zero hdi)`. Conclude with `h2.symm`.

Conclude with `absurd h1 hdj`. Use extensionality with `l`. Simplify using `only [Set.mem_range, C2.Lstg, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, rfl⟩`.

Use `⟨⟨fun i j hij => ?_, fun i => ?_⟩, ⟨fun a b hab => ?_, fun a => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[c2x2_lowOf_sub, Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))), add_zero]`. Rewrite using `[c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), add_zero]`. Rewrite using `[monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub, Matrix.one_apply_ne (fun e => (ne_of_gt hab) (w.injective e)), dif_neg]`. Simplify using the standard rewrite rules.

Introduce `h`. Simplify using `at h`. Conclude with `absurd h.2 (not_lt.mpr (le_of_lt hab))`. Rewrite using `[monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1)]`. Simplify using `[hd a]`.

Introduce and unpack `⟨hl, hc⟩`. Use `⟨fun q => l q.1.1 q.1.2, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[c2x2_lowOf_sub]`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases.

Rewrite using `[Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))), hl.1 i j hij, add_zero]`. Rewrite using `[Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), hl.2, add_zero]`. Rewrite using `[Matrix.one_apply_ne (ne_of_gt hij), zero_add] split_ifs with h`. Both sides reduce to the same expression. Establish `hlt : w.symm j < w.symm i`.

Establish `hne : w.symm i ≠ w.symm j` using `fun e => (ne_of_gt hij) (w.symm.injective e)`. Break down `lt_or_gt_of_ne hne with h' | h'` into its components or cases. Conclude with `absurd ⟨hij, h'⟩ h`. Conclude with `h'`. Use `hc.1 _ _ hlt` as an intermediate fact.

Rewrite `this` using `[monomialMatrix_conj_apply w d hd]`. Simplify using `only [Equiv.apply_symm_apply] at this`. Establish `hdi` using `hd (w.symm i)`. Establish `hdj` using `hd (w.symm j)`. Break down `mul_eq_zero.mp this with h1 | h1` into its components or cases.

Break down `mul_eq_zero.mp h1 with h2 | h2` into its components or cases. Conclude with `absurd h2 (inv_ne_zero hdi)`. Conclude with `h2.symm`. Conclude with `absurd h1 hdj`.
-/
theorem lower_parabolic_coordinates : C2.LPCoords := by
  intro m w d hd
  have hPu := isUnit_det_monomialMatrix w d hd
  constructor
  · ext l
    simp only [Set.mem_range, C2.LPg, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ⟨fun a b hab => ?_, fun a => ?_⟩⟩
      · rw [c2x2_lowOf_sub, Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))), add_zero]
      · rw [c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), add_zero]
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub,
          Matrix.one_apply_ne (fun e => (ne_of_lt hab) (w.injective e)), dif_neg]
        · simp
        · intro h; simp at h; exact absurd h.2 (not_lt.mpr (le_of_lt hab))
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1)]
        simp [hd a]
    · rintro ⟨hl, hc⟩
      refine ⟨fun q => l q.1.1 q.1.2, ?_⟩
      ext i j
      rw [c2x2_lowOf_sub]
      rcases lt_trichotomy i j with hij | rfl | hij
      · rw [Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))),
          hl.1 i j hij, add_zero]
      · rw [Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), hl.2, add_zero]
      · rw [Matrix.one_apply_ne (ne_of_gt hij), zero_add]
        split_ifs with h
        · rfl
        · have hlt : w.symm i < w.symm j := by
            have hne : w.symm i ≠ w.symm j := fun e => (ne_of_gt hij) (w.symm.injective e)
            rcases lt_or_gt_of_ne hne with h' | h'
            · exact h'
            · exact absurd ⟨hij, h'⟩ h
          have := hc.1 _ _ hlt
          rw [monomialMatrix_conj_apply w d hd] at this
          simp only [Equiv.apply_symm_apply] at this
          have hdi := hd (w.symm i)
          have hdj := hd (w.symm j)
          rcases mul_eq_zero.mp this with h1 | h1
          · rcases mul_eq_zero.mp h1 with h2 | h2
            · exact absurd h2 (inv_ne_zero hdi)
            · exact h2.symm
          · exact absurd h1 hdj
  · ext l
    simp only [Set.mem_range, C2.Lstg, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ⟨fun a b hab => ?_, fun a => ?_⟩⟩
      · rw [c2x2_lowOf_sub, Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))), add_zero]
      · rw [c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), add_zero]
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub,
          Matrix.one_apply_ne (fun e => (ne_of_gt hab) (w.injective e)), dif_neg]
        · simp
        · intro h; simp at h; exact absurd h.2 (not_lt.mpr (le_of_lt hab))
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1)]
        simp [hd a]
    · rintro ⟨hl, hc⟩
      refine ⟨fun q => l q.1.1 q.1.2, ?_⟩
      ext i j
      rw [c2x2_lowOf_sub]
      rcases lt_trichotomy i j with hij | rfl | hij
      · rw [Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))),
          hl.1 i j hij, add_zero]
      · rw [Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), hl.2, add_zero]
      · rw [Matrix.one_apply_ne (ne_of_gt hij), zero_add]
        split_ifs with h
        · rfl
        · have hlt : w.symm j < w.symm i := by
            have hne : w.symm i ≠ w.symm j := fun e => (ne_of_gt hij) (w.symm.injective e)
            rcases lt_or_gt_of_ne hne with h' | h'
            · exact absurd ⟨hij, h'⟩ h
            · exact h'
          have := hc.1 _ _ hlt
          rw [monomialMatrix_conj_apply w d hd] at this
          simp only [Equiv.apply_symm_apply] at this
          have hdi := hd (w.symm i)
          have hdj := hd (w.symm j)
          rcases mul_eq_zero.mp this with h1 | h1
          · rcases mul_eq_zero.mp h1 with h2 | h2
            · exact absurd h2 (inv_ne_zero hdi)
            · exact h2.symm
          · exact absurd h1 hdj

end Formalism.FourierDecayAlt.P
