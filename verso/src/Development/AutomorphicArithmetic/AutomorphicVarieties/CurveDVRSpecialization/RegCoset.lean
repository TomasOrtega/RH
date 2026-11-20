import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FullEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SepOfMinors
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExpSums
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagonalizationExistence
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StronglyIrreducible

namespace UpperTheory.V.Pr

open Matrix Polynomial

/- English proof (translation)
Distinguish the cases in `h1 : S.card ≤ 1`. Establish `hs : Subsingleton S`. Rewrite `h1` using `[Finset.card_le_one]`. Conclude with `⟨fun a b => Subtype.ext (h1 _ a.2 _ b.2)⟩`. Break down `isEmpty_or_nonempty S with h | ⟨⟨a⟩⟩` into its components or cases.

Simplify using `[Matrix.det_isEmpty]`. Rewrite using `[Matrix.det_eq_elem_of_subsingleton _ a]`. Conclude with `hM _`. Establish `h2 : Sᶜ.card ≤ 1`. Rewrite using `[Finset.card_compl, Fintype.card_fin]`.

Use linear arithmetic over natural numbers and integers. Rewrite `h2` using `[Finset.card_le_one]`. Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet`. Use `set v' : Fin n → κ := fun i => if h : i ∈ S then v ⟨i, h⟩ else 0 with hv'`.

Establish `hw1 : ∀ i ∈ S, (M *ᵥ v') i = 0`. Introduce `i hi`. Establish `h3` using `congrFun hv ⟨i, hi⟩`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply] at h3 ⊢`. Rewrite using `[← h3, ← Finset.sum_subset (Finset.subset_univ S), ← Finset.sum_coe_sort S]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[hv', j.2]`. Introduce `j _ hj`. Simplify using `[hv', hj]`. Establish `hback : N *ᵥ (M *ᵥ v') = v'`.

Rewrite using `[Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]`. Establish `hw : M *ᵥ v' = 0`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k ∈ S`. Conclude with `hw1 k hk`.

Establish `h3` using `congrFun hback k`. Establish `h4 : v' k = 0` using `by simp [hv', hk]`. Rewrite `h3` using `[h4]`. Establish `h5 : (N *ᵥ (M *ᵥ v')) k = N k k * (M *ᵥ v') k` using `by show ∑ j, N k j * (M *ᵥ v') j = _`. Use `Finset.sum_eq_single k (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ k) h)` and prove the remaining obligations.

Distinguish the cases in `hjS : j ∈ S`. Rewrite using `[hw1 j hjS, mul_zero]`. Conclude with `absurd (h2 _ (Finset.mem_compl.2 hjS) _ (Finset.mem_compl.2 hk)) hj`. Rewrite `h3` using `[h5]`. Conclude with `(mul_eq_zero.1 h3).resolve_left (hN k)`.

Rewrite `hback` using `[hw, Matrix.mulVec_zero]`. Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Use `congrFun hback j` as an intermediate fact. Simplify `this.symm` using `[hv', j.2]`.
-/
private lemma minors_ne_zero {κ : Type} [Field κ] {n : ℕ} (hn : n ≤ 3) (M N : Matrix (Fin n) (Fin n) κ)
    (hNM : N * M = 1) (hM : ∀ i, M i i ≠ 0) (hN : ∀ i, N i i ≠ 0) (S : Finset (Fin n)) :
    (M.submatrix (Subtype.val : S → Fin n) Subtype.val).det ≠ 0 := by
  classical
  by_cases h1 : S.card ≤ 1
  · have hs : Subsingleton S := by
      rw [Finset.card_le_one] at h1
      exact ⟨fun a b => Subtype.ext (h1 _ a.2 _ b.2)⟩
    rcases isEmpty_or_nonempty S with h | ⟨⟨a⟩⟩
    · simp [Matrix.det_isEmpty]
    · rw [Matrix.det_eq_elem_of_subsingleton _ a]
      exact hM _
  · have h2 : Sᶜ.card ≤ 1 := by
      rw [Finset.card_compl, Fintype.card_fin]; omega
    rw [Finset.card_le_one] at h2
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    set v' : Fin n → κ := fun i => if h : i ∈ S then v ⟨i, h⟩ else 0 with hv'
    have hw1 : ∀ i ∈ S, (M *ᵥ v') i = 0 := by
      intro i hi
      have h3 := congrFun hv ⟨i, hi⟩
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply] at h3 ⊢
      rw [← h3, ← Finset.sum_subset (Finset.subset_univ S), ← Finset.sum_coe_sort S]
      · refine Finset.sum_congr rfl fun j _ => ?_
        simp [hv', j.2]
      · intro j _ hj
        simp [hv', hj]
    have hback : N *ᵥ (M *ᵥ v') = v' := by
      rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
    have hw : M *ᵥ v' = 0 := by
      funext k
      by_cases hk : k ∈ S
      · exact hw1 k hk
      · have h3 := congrFun hback k
        have h4 : v' k = 0 := by simp [hv', hk]
        rw [h4] at h3
        have h5 : (N *ᵥ (M *ᵥ v')) k = N k k * (M *ᵥ v') k := by
          show ∑ j, N k j * (M *ᵥ v') j = _
          refine Finset.sum_eq_single k (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ k) h)
          by_cases hjS : j ∈ S
          · rw [hw1 j hjS, mul_zero]
          · exact absurd (h2 _ (Finset.mem_compl.2 hjS) _ (Finset.mem_compl.2 hk)) hj
        rw [h5] at h3
        exact (mul_eq_zero.1 h3).resolve_left (hN k)
    rw [hw, Matrix.mulVec_zero] at hback
    apply hv0
    funext j
    have := congrFun hback j
    simpa [hv', j.2] using this.symm

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.DiagonalizationExistence.exists_diag M a ha h`.
-/
private lemma exists_diag {κ : Type} [Field κ] {n : ℕ} (M : Matrix (Fin n) (Fin n) κ) (a : Fin n → κ)
    (ha : Function.Injective a) (h : M.charpoly = ∏ i, (X - C (a i))) :
    ∃ P : GL (Fin n) κ, M * (P : Matrix (Fin n) (Fin n) κ) = (P : Matrix (Fin n) (Fin n) κ) * diagonal a :=
  _root_.UpperTheory.Reformulated.B.DiagonalizationExistence.exists_diag M a ha h

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.StronglyIrreducible.strongIrr_conj r hr P`.
-/
private lemma strongIrr_conj {G κ : Type} [Group G] [Field κ] {n : ℕ} (r : G →* GL (Fin n) κ) (hr : StrongIrr r)
    (P : GL (Fin n) κ) : StrongIrr ((MulAut.conj P⁻¹).toMonoidHom.comp r) :=
  _root_.UpperTheory.Reformulated.B.StronglyIrreducible.strongIrr_conj r hr P

/- English proof (translation)
Take `⟨b, hb⟩` from `fullEx G κ n r hr u α hα hu`. Establish `hα' : FreeRatios α⁻¹`. Introduce `i j hij m hm h`. Apply `hα i j hij m hm` to reduce the goal to its premises. Simplify using `using h`.

Establish `hrow : ∀ i, ∃ j, (y : Matrix (Fin n) (Fin n) κ) i j ≠ 0`. Introduce `i`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use `congrFun (congrFun y.mul_inv i) i` as an intermediate fact.

Simplify using `only [Matrix.mul_apply, h, zero_mul, Finset.sum_const_zero, Matrix.one_apply_eq] at this`. Conclude with `zero_ne_one this`. Establish `hcol : ∀ i, ∃ j, ((y⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) j i ≠ 0`. Introduce `i`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Use `congrFun (congrFun y.mul_inv i) i` as an intermediate fact. Simplify using `only [Matrix.mul_apply, h, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at this`. Conclude with `zero_ne_one this`. Take `⟨m, hm⟩` from `expSums κ (Fin n) (Fin n ⊕ Fin n) (Sum.elim (fun _ => α) fun _ => α⁻¹) (Sum.elim (fun i j => (y : Matrix (Fin n) (Fin n) κ) i j * gm r b j i) fun i j => (((r b)⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i j * ((y⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) j i) (by rintro ( …`.

Introduce and unpack `(i | i)`. Take `⟨j, hj⟩` from `hrow i`. Conclude with `⟨j, mul_ne_zero hj (hb j i).1⟩`. Take `⟨j, hj⟩` from `hcol i`. Conclude with `⟨j, mul_ne_zero (hb i j).2 hj⟩)`.

Establish `hDD : diagonal (fun i => ((α⁻¹ i : κˣ) : κ) ^ m) * diagonal (fun i => ((α i : κˣ) : κ) ^ m) = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[← mul_pow]`.

Simplify using the standard rewrite rules. Take `⟨m', hm'⟩` from `sepOfMinors κ n hn ((y : Matrix (Fin n) (Fin n) κ) * diagonal (fun i => ((α i : κˣ) : κ) ^ m) * gm r b) α hα (minors_ne_zero hn _ ((((r b)⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) * diagonal (fun i => ((α⁻¹ i : κˣ) : κ) ^ m) * ((y⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ …`. Establish `: ∀ A B C D E F : Matrix (Fin n) (Fin n) κ, A * B * C * (D * E * F) = A * (B * (C * D) * E) * F` using `by intros; simp only [Matrix.mul_assoc]`. Rewrite using `[this, Units.inv_mul, Matrix.mul_one, hDD, Matrix.mul_one, Units.inv_mul])`. Use the proof step `(fun i => by`.

Use `hm (Sum.inl i)` as an intermediate fact. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal]`. Simplify `this)` using `only [Sum.elim_inl, mul_right_comm]`. Use the proof step `(fun i => by`.

Use `hm (Sum.inr i)` as an intermediate fact. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal]`. Simplify `this))` using `only [Sum.elim_inr, mul_right_comm]`. Use `⟨u ^ m * b * u ^ m', ?_⟩` and prove the remaining obligations.

Establish `e : ∀ k : ℕ, gm r (u ^ k) = diagonal (fun i => ((α i : κˣ) : κ)) ^ k`. Introduce `k`. Rewrite using `[← hu]`. Simplify using `[gm]`. Establish `e2 : gm r (u ^ m * b * u ^ m') = gm r (u ^ m) * gm r b * gm r (u ^ m')`.

Simplify using `[gm]`. Rewrite using `[e2, e, e, Matrix.diagonal_pow _ m, ← Matrix.mul_assoc, ← Matrix.mul_assoc]`. Conclude with `hm'`.
-/
private lemma regCoset_diag (G κ : Type) [Group G] [Field κ] (n : ℕ) (hn : n ≤ 3) (r : G →* GL (Fin n) κ)
    (hr : StrongIrr r) (u : G) (α : Fin n → κˣ) (hα : FreeRatios α)
    (hu : gm r u = diagonal (fun i => ((α i : κˣ) : κ))) (y : GL (Fin n) κ) :
    ∃ h, ((y : Matrix (Fin n) (Fin n) κ) * gm r h).charpoly.Separable := by
  classical
  obtain ⟨b, hb⟩ := fullEx G κ n r hr u α hα hu
  have hα' : FreeRatios α⁻¹ := by
    intro i j hij m hm h
    apply hα i j hij m hm
    simpa using h
  have hrow : ∀ i, ∃ j, (y : Matrix (Fin n) (Fin n) κ) i j ≠ 0 := by
    intro i
    by_contra h
    push_neg at h
    have := congrFun (congrFun y.mul_inv i) i
    simp only [Matrix.mul_apply, h, zero_mul, Finset.sum_const_zero, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  have hcol : ∀ i, ∃ j, ((y⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) j i ≠ 0 := by
    intro i
    by_contra h
    push_neg at h
    have := congrFun (congrFun y.mul_inv i) i
    simp only [Matrix.mul_apply, h, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  obtain ⟨m, hm⟩ := expSums κ (Fin n) (Fin n ⊕ Fin n) (Sum.elim (fun _ => α) fun _ => α⁻¹)
    (Sum.elim (fun i j => (y : Matrix (Fin n) (Fin n) κ) i j * gm r b j i)
      fun i j => (((r b)⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i j *
        ((y⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) j i)
    (by rintro (i | i); exacts [hα, hα'])
    (by
      rintro (i | i)
      · obtain ⟨j, hj⟩ := hrow i
        exact ⟨j, mul_ne_zero hj (hb j i).1⟩
      · obtain ⟨j, hj⟩ := hcol i
        exact ⟨j, mul_ne_zero (hb i j).2 hj⟩)
  have hDD : diagonal (fun i => ((α⁻¹ i : κˣ) : κ) ^ m) * diagonal (fun i => ((α i : κˣ) : κ) ^ m) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← mul_pow]
    simp
  obtain ⟨m', hm'⟩ := sepOfMinors κ n hn
    ((y : Matrix (Fin n) (Fin n) κ) * diagonal (fun i => ((α i : κˣ) : κ) ^ m) * gm r b) α hα
    (minors_ne_zero hn _ ((((r b)⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) *
      diagonal (fun i => ((α⁻¹ i : κˣ) : κ) ^ m) * ((y⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ))
      (by
        have : ∀ A B C D E F : Matrix (Fin n) (Fin n) κ, A * B * C * (D * E * F) = A * (B * (C * D) * E) * F := by
          intros; simp only [Matrix.mul_assoc]
        rw [this, Units.inv_mul, Matrix.mul_one, hDD, Matrix.mul_one, Units.inv_mul])
      (fun i => by
        have := hm (Sum.inl i)
        rw [Matrix.mul_apply]
        simp only [Matrix.mul_diagonal]
        simpa only [Sum.elim_inl, mul_right_comm] using this)
      (fun i => by
        have := hm (Sum.inr i)
        rw [Matrix.mul_apply]
        simp only [Matrix.mul_diagonal]
        simpa only [Sum.elim_inr, mul_right_comm] using this))
  refine ⟨u ^ m * b * u ^ m', ?_⟩
  have e : ∀ k : ℕ, gm r (u ^ k) = diagonal (fun i => ((α i : κˣ) : κ)) ^ k := by
    intro k
    rw [← hu]
    simp [gm]
  have e2 : gm r (u ^ m * b * u ^ m') = gm r (u ^ m) * gm r b * gm r (u ^ m') := by
    simp [gm]
  rw [e2, e, e, Matrix.diagonal_pow _ m, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact hm'

end UpperTheory.V.Pr

open Matrix Polynomial in
/- English proof (translation)
Introduce `G κ _ _ n hn r hr u α hα hu y`. Establish `hinj : Function.Injective fun i => ((α i : κˣ) : κ)`. Introduce `i j h`. Assume the negation of the conclusion as `hij`. Conclude with `hα i j hij 1 one_pos (by simpa using Units.ext h)`.

Take `⟨P, hP⟩` from `exists_diag (gm r u) _ hinj hu`. Establish `e : ∀ g, gm ((MulAut.conj P⁻¹).toMonoidHom.comp r) g = ((P⁻¹ * r g * P : GL (Fin n) κ) : Matrix _ _ κ)`. Introduce `g`. Simplify using `[gm]`. Take `⟨h, hh⟩` from `regCoset_diag G κ n hn _ (strongIrr_conj r hr P) u α hα (by`.

Rewrite using `[e, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hP, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul])`. Use the proof step `(P⁻¹ * y * P)`. Use `⟨h, ?_⟩` and prove the remaining obligations. Rewrite `hh` using `[e, ← Units.val_mul]`. Establish `e2 : P⁻¹ * y * P * (P⁻¹ * r h * P) = P⁻¹ * (y * r h * P)` using `by group`.

Rewrite `hh` using `[e2, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_right, Units.val_mul]`. Conclude with `hh`.
-/
theorem UpperTheory.V.Pr.regCoset :
    UpperTheory.V.Pr.RegCoset := by
  intro G κ _ _ n hn r hr u α hα hu y
  have hinj : Function.Injective fun i => ((α i : κˣ) : κ) := by
    intro i j h
    by_contra hij
    exact hα i j hij 1 one_pos (by simpa using Units.ext h)
  obtain ⟨P, hP⟩ := exists_diag (gm r u) _ hinj hu
  have e : ∀ g, gm ((MulAut.conj P⁻¹).toMonoidHom.comp r) g = ((P⁻¹ * r g * P : GL (Fin n) κ) : Matrix _ _ κ) := by
    intro g
    simp [gm]
  obtain ⟨h, hh⟩ := regCoset_diag G κ n hn _ (strongIrr_conj r hr P) u α hα (by
    rw [e, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hP, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul])
    (P⁻¹ * y * P)
  refine ⟨h, ?_⟩
  rw [e, ← Units.val_mul] at hh
  have e2 : P⁻¹ * y * P * (P⁻¹ * r h * P) = P⁻¹ * (y * r h * P) := by group
  rw [e2, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_right, Units.val_mul] at hh
  exact hh
