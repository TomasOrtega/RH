import Mathlib

namespace KStar.Tree

/- English proof (translation)
Break down `isEmpty_or_nonempty (Fin r) with hr | ⟨⟨i0⟩⟩` into its components or cases. Conclude with `⟨1, fun x => Subsingleton.elim _ _⟩`. Establish `hF : ∀ i j k l : Fin r, θ (Matrix.single i j (1 : B)) * θ (Matrix.single k l 1) = if j = k then θ (Matrix.single i l 1) else 0`. Introduce `i j k l`. Rewrite using `[← map_mul]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[Matrix.single_mul_single_same, mul_one]`. Rewrite using `[Matrix.single_mul_single_of_ne _ _ _ _ h, map_zero]`. Establish `hsum : ∑ j, θ (Matrix.single j j (1 : B)) = 1`.

Rewrite using `[← map_sum, ← map_one θ]`. Use `congr 1`. Use extensionality with `p q`. Rewrite using `[Matrix.sum_apply, Finset.sum_eq_single p]`. Simplify using `[Matrix.single_apply, Matrix.one_apply]`.

Introduce `j _ hj`. Simplify using `[Matrix.single_apply, hj]`. Simplify using the standard rewrite rules. Establish `hne : θ (Matrix.single i0 i0 (1 : B)) ≠ 0`. Introduce `h0`.

Establish `hz : ∀ j, θ (Matrix.single j j (1 : B)) = 0`. Introduce `j`. Establish `: θ (Matrix.single j j (1 : B)) = θ (Matrix.single j i0 1) * θ (Matrix.single i0 i0 1) * θ (Matrix.single i0 j 1)`. Rewrite using `[hF, if_pos rfl, hF, if_pos rfl]`. Rewrite using `[this, h0, mul_zero, zero_mul]`.

Establish `h1 : (1 : Matrix (Fin r) (Fin r) B) = 0`. Rewrite using `[← hsum]`. Conclude with `Finset.sum_eq_zero fun j _ => hz j`. Establish `h2` using `congrFun (congrFun h1 i0) i0`. Simplify using `at h2`.

Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab⟩ : ∃ a b, IsUnit (θ (Matrix.single i0 i0 (1 : B)) a b) := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hne` to reduce the goal to its premises. Establish `he : θ (Matrix.single i0 i0 (1 : B)) * θ (Matrix.single i0 i0 1) = θ (Matrix.single i0 i0 1)`.

Rewrite using `[hF, if_pos rfl]`. Establish `hres : (IsLocalRing.residue B).mapMatrix (θ (Matrix.single i0 i0 (1 : B))) = 0`. Use extensionality with `i j`. Simplify using `[IsLocalRing.residue_eq_zero_iff, hcon i j]`. Establish `hdet : IsUnit (1 - θ (Matrix.single i0 i0 (1 : B))).det`.

Assume the negation of the conclusion as `hnu`. Establish `h3 : IsLocalRing.residue B (1 - θ (Matrix.single i0 i0 (1 : B))).det = 0` using `(IsLocalRing.residue_eq_zero_iff _).mpr hnu`. Rewrite `h3` using `[RingHom.map_det, map_sub, map_one, hres, sub_zero, Matrix.det_one]`. Conclude with `one_ne_zero h3`. Establish `hu : IsUnit (1 - θ (Matrix.single i0 i0 (1 : B)))` using `(Matrix.isUnit_iff_isUnit_det _).mpr hdet`.

Establish `h4 : θ (Matrix.single i0 i0 (1 : B)) * (1 - θ (Matrix.single i0 i0 1)) = 0`. Rewrite using `[mul_sub, mul_one, he, sub_self]`. Conclude with `hu.mul_left_eq_zero.mp h4`. Establish `hKJ : (∑ j, Matrix.single j a (1 : B) * θ (Matrix.single i0 j 1)) * (∑ l, θ (Matrix.single l i0 (1 : B)) * Matrix.single b l 1) = ∑ j : Fin r, Matrix.single j j (θ (Matrix.single i0 i0 (1 : B)) a b)`. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Establish `key : ∀ l, Matrix.single j a (1 : B) * θ (Matrix.single i0 j 1) * (θ (Matrix.single l i0 (1 : B)) * Matrix.single b l 1) = if j = l then Matrix.single j j (θ (Matrix.single i0 i0 (1 : B)) a b) else 0`. Introduce `l`. Rewrite using `[← mul_assoc, mul_assoc (Matrix.single j a (1 : B)), hF]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[Matrix.single_mul_mul_single, one_mul, mul_one]`. Rewrite using `[mul_zero, zero_mul]`. Repeatedly rewrite using `[key]`.

Rewrite using `[Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]`. Establish `hdiag : ∑ j : Fin r, Matrix.single j j (θ (Matrix.single i0 i0 (1 : B)) a b) = Matrix.diagonal (fun _ : Fin r => θ (Matrix.single i0 i0 (1 : B)) a b)`. Use extensionality with `p q`. Rewrite using `[Matrix.sum_apply, Finset.sum_eq_single p]`. Simplify using `[Matrix.single_apply, Matrix.diagonal_apply]`.

Introduce `j _ hj`. Simplify using `[Matrix.single_apply, hj]`. Simplify using the standard rewrite rules. Establish `hJ : IsUnit (∑ l, θ (Matrix.single l i0 (1 : B)) * Matrix.single b l 1).det`. Establish `h5` using `congrArg Matrix.det hKJ`.

Rewrite `h5` using `[hdiag, Matrix.det_mul, Matrix.det_diagonal]`. Establish `h6 : IsUnit (∏ _i : Fin r, θ (Matrix.single i0 i0 (1 : B)) a b)`. Rewrite using `[Finset.prod_const]`. Conclude with `hab.pow _`. Rewrite `h6` using `[← h5]`.

Conclude with `isUnit_of_mul_isUnit_right h6`. Use `⟨Matrix.nonsingInvUnit _ hJ, fun x => ?_⟩` and prove the remaining obligations. Use `show θ x * (∑ l, θ (Matrix.single l i0 (1 : B)) * Matrix.single b l 1) = (∑ l, θ (Matrix.single l i0 (1 : B)) * Matrix.single b l 1) * x`. Proceed by induction on `x using Matrix.induction_on' with`. Consider the case `h_zero => simp`.

Consider the case `h_add p q hp hq => rw [map_add, add_mul, hp, hq, mul_add]`. Consider the case `h_std_basis k l c`. Establish `hs : Matrix.single k l c = c • Matrix.single k l (1 : B)`. Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[hs, map_smul, smul_mul_assoc, Matrix.mul_smul]`.

Use `congr 1`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Establish `hl : ∀ j, θ (Matrix.single k l (1 : B)) * (θ (Matrix.single j i0 1) * Matrix.single b j 1) = if l = j then θ (Matrix.single k i0 (1 : B)) * Matrix.single b l 1 else 0`. Introduce `j`. Rewrite using `[← mul_assoc, hF]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Both sides reduce to the same expression. Rewrite using `[zero_mul]`. Establish `hr : ∀ j, θ (Matrix.single j i0 (1 : B)) * Matrix.single b j 1 * Matrix.single k l 1 = if k = j then θ (Matrix.single k i0 (1 : B)) * Matrix.single b l 1 else 0`.

Introduce `j`. Rewrite using `[mul_assoc]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[Matrix.single_mul_single_same, mul_one]`.

Rewrite using `[Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h), mul_zero]`. Repeatedly rewrite using `[hl, hr]`. Rewrite using `[Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]`.
-/
theorem exists_conj_of_algHom {B : Type} [CommRing B] [IsLocalRing B] {r : ℕ}
    (θ : Matrix (Fin r) (Fin r) B →ₐ[B] Matrix (Fin r) (Fin r) B) :
    ∃ J : GL (Fin r) B, ∀ x, θ x * (J : Matrix (Fin r) (Fin r) B) = (J : Matrix (Fin r) (Fin r) B) * x := by
  classical
  rcases isEmpty_or_nonempty (Fin r) with hr | ⟨⟨i0⟩⟩
  · exact ⟨1, fun x => Subsingleton.elim _ _⟩
  have hF : ∀ i j k l : Fin r, θ (Matrix.single i j (1 : B)) * θ (Matrix.single k l 1) =
      if j = k then θ (Matrix.single i l 1) else 0 := by
    intro i j k l
    rw [← map_mul]
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, mul_one]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, map_zero]
  have hsum : ∑ j, θ (Matrix.single j j (1 : B)) = 1 := by
    rw [← map_sum, ← map_one θ]
    congr 1
    ext p q
    rw [Matrix.sum_apply, Finset.sum_eq_single p]
    · simp [Matrix.single_apply, Matrix.one_apply]
    · intro j _ hj
      simp [Matrix.single_apply, hj]
    · simp
  have hne : θ (Matrix.single i0 i0 (1 : B)) ≠ 0 := by
    intro h0
    have hz : ∀ j, θ (Matrix.single j j (1 : B)) = 0 := by
      intro j
      have : θ (Matrix.single j j (1 : B)) =
          θ (Matrix.single j i0 1) * θ (Matrix.single i0 i0 1) * θ (Matrix.single i0 j 1) := by
        rw [hF, if_pos rfl, hF, if_pos rfl]
      rw [this, h0, mul_zero, zero_mul]
    have h1 : (1 : Matrix (Fin r) (Fin r) B) = 0 := by
      rw [← hsum]
      exact Finset.sum_eq_zero fun j _ => hz j
    have h2 := congrFun (congrFun h1 i0) i0
    simp at h2
  obtain ⟨a, b, hab⟩ : ∃ a b, IsUnit (θ (Matrix.single i0 i0 (1 : B)) a b) := by
    by_contra hcon
    push_neg at hcon
    apply hne
    have he : θ (Matrix.single i0 i0 (1 : B)) * θ (Matrix.single i0 i0 1) =
        θ (Matrix.single i0 i0 1) := by
      rw [hF, if_pos rfl]
    have hres : (IsLocalRing.residue B).mapMatrix (θ (Matrix.single i0 i0 (1 : B))) = 0 := by
      ext i j
      simp [IsLocalRing.residue_eq_zero_iff, hcon i j]
    have hdet : IsUnit (1 - θ (Matrix.single i0 i0 (1 : B))).det := by
      by_contra hnu
      have h3 : IsLocalRing.residue B (1 - θ (Matrix.single i0 i0 (1 : B))).det = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr hnu
      rw [RingHom.map_det, map_sub, map_one, hres, sub_zero, Matrix.det_one] at h3
      exact one_ne_zero h3
    have hu : IsUnit (1 - θ (Matrix.single i0 i0 (1 : B))) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr hdet
    have h4 : θ (Matrix.single i0 i0 (1 : B)) * (1 - θ (Matrix.single i0 i0 1)) = 0 := by
      rw [mul_sub, mul_one, he, sub_self]
    exact hu.mul_left_eq_zero.mp h4
  have hKJ : (∑ j, Matrix.single j a (1 : B) * θ (Matrix.single i0 j 1)) *
      (∑ l, θ (Matrix.single l i0 (1 : B)) * Matrix.single b l 1) =
      ∑ j : Fin r, Matrix.single j j (θ (Matrix.single i0 i0 (1 : B)) a b) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    have key : ∀ l, Matrix.single j a (1 : B) * θ (Matrix.single i0 j 1) *
        (θ (Matrix.single l i0 (1 : B)) * Matrix.single b l 1) =
        if j = l then Matrix.single j j (θ (Matrix.single i0 i0 (1 : B)) a b) else 0 := by
      intro l
      rw [← mul_assoc, mul_assoc (Matrix.single j a (1 : B)), hF]
      split_ifs with h
      · subst h
        rw [Matrix.single_mul_mul_single, one_mul, mul_one]
      · rw [mul_zero, zero_mul]
    simp_rw [key]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  have hdiag : ∑ j : Fin r, Matrix.single j j (θ (Matrix.single i0 i0 (1 : B)) a b) =
      Matrix.diagonal (fun _ : Fin r => θ (Matrix.single i0 i0 (1 : B)) a b) := by
    ext p q
    rw [Matrix.sum_apply, Finset.sum_eq_single p]
    · simp [Matrix.single_apply, Matrix.diagonal_apply]
    · intro j _ hj
      simp [Matrix.single_apply, hj]
    · simp
  have hJ : IsUnit (∑ l, θ (Matrix.single l i0 (1 : B)) * Matrix.single b l 1).det := by
    have h5 := congrArg Matrix.det hKJ
    rw [hdiag, Matrix.det_mul, Matrix.det_diagonal] at h5
    have h6 : IsUnit (∏ _i : Fin r, θ (Matrix.single i0 i0 (1 : B)) a b) := by
      rw [Finset.prod_const]
      exact hab.pow _
    rw [← h5] at h6
    exact isUnit_of_mul_isUnit_right h6
  refine ⟨Matrix.nonsingInvUnit _ hJ, fun x => ?_⟩
  show θ x * (∑ l, θ (Matrix.single l i0 (1 : B)) * Matrix.single b l 1) =
    (∑ l, θ (Matrix.single l i0 (1 : B)) * Matrix.single b l 1) * x
  induction x using Matrix.induction_on' with
  | h_zero => simp
  | h_add p q hp hq => rw [map_add, add_mul, hp, hq, mul_add]
  | h_std_basis k l c =>
    have hs : Matrix.single k l c = c • Matrix.single k l (1 : B) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, smul_mul_assoc, Matrix.mul_smul]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    have hl : ∀ j, θ (Matrix.single k l (1 : B)) * (θ (Matrix.single j i0 1) * Matrix.single b j 1) =
        if l = j then θ (Matrix.single k i0 (1 : B)) * Matrix.single b l 1 else 0 := by
      intro j
      rw [← mul_assoc, hF]
      split_ifs with h
      · subst h
        rfl
      · rw [zero_mul]
    have hr : ∀ j, θ (Matrix.single j i0 (1 : B)) * Matrix.single b j 1 * Matrix.single k l 1 =
        if k = j then θ (Matrix.single k i0 (1 : B)) * Matrix.single b l 1 else 0 := by
      intro j
      rw [mul_assoc]
      split_ifs with h
      · subst h
        rw [Matrix.single_mul_single_same, mul_one]
      · rw [Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h), mul_zero]
    simp_rw [hl, hr]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]

/- English proof (translation)
Take `⟨J, hJ⟩` from `exists_conj_of_algHom θ`. Establish `h` using `congrArg Matrix.det (hJ x)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, mul_comm (J : Matrix (Fin r) (Fin r) B).det]`. Establish `hu : IsUnit (J : Matrix (Fin r) (Fin r) B).det` using `(Matrix.isUnit_iff_isUnit_det _).mp J.isUnit`. Conclude with `hu.mul_right_cancel h`.
-/
theorem det_algHom {B : Type} [CommRing B] [IsLocalRing B] {r : ℕ}
    (θ : Matrix (Fin r) (Fin r) B →ₐ[B] Matrix (Fin r) (Fin r) B) (x : Matrix (Fin r) (Fin r) B) : (θ x).det = x.det := by
  obtain ⟨J, hJ⟩ := exists_conj_of_algHom θ
  have h := congrArg Matrix.det (hJ x)
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (J : Matrix (Fin r) (Fin r) B).det] at h
  have hu : IsUnit (J : Matrix (Fin r) (Fin r) B).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp J.isUnit
  exact hu.mul_right_cancel h

end KStar.Tree
