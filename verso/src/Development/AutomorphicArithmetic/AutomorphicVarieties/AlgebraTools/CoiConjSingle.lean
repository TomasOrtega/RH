import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hm : ∀ a b, e a b ∈ maximalIdeal R` using `fun a b => (mem_maximalIdeal _).2 (h a b)`. Establish `hmap : (1 - e).map (residue R) = 1`. Use extensionality with `a b`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[(residue_eq_zero_iff _).2 (hm a a)]`. Simplify using `[Matrix.one_apply_ne hab, (residue_eq_zero_iff _).2 (hm a b)]`. Establish `hdet : IsUnit (1 - e).det`.

Establish `h1 : residue R (1 - e).det = 1`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hmap, det_one]`. Conclude with `(isUnit_map_iff (residue R) _).1 (h1 ▸ isUnit_one)`. Establish `hu : IsUnit (1 - e)` using `(Matrix.isUnit_iff_isUnit_det _).2 hdet`. Apply `h0` to reduce the goal to its premises.

Establish `h2 : (1 - e) * e = 0` using `by rw [sub_mul, one_mul, he.eq, sub_self]`. Conclude with `hu.mul_right_eq_zero.1 h2`.
-/
private theorem UpperTheory.V.AlgebraTools.exists_unit_entry {R : Type} [CommRing R] [IsLocalRing R] {ι : Type}
    [Fintype ι] [DecidableEq ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) (h0 : e ≠ 0) :
    ∃ a b, IsUnit (e a b) := by
  classical
  by_contra h
  push_neg at h
  have hm : ∀ a b, e a b ∈ maximalIdeal R := fun a b => (mem_maximalIdeal _).2 (h a b)
  have hmap : (1 - e).map (residue R) = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [(residue_eq_zero_iff _).2 (hm a a)]
    · simp [Matrix.one_apply_ne hab, (residue_eq_zero_iff _).2 (hm a b)]
  have hdet : IsUnit (1 - e).det := by
    have h1 : residue R (1 - e).det = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, det_one]
    exact (isUnit_map_iff (residue R) _).1 (h1 ▸ isUnit_one)
  have hu : IsUnit (1 - e) := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  apply h0
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  exact hu.mul_right_eq_zero.1 h2

/- English proof (translation)
Introduce `R _ _ ι _ _ f hf h0`. Apply the tactic sequence `have hc : ∀ i, ∃ a b, IsUnit (f i a b) := fun i => UpperTheory.V.AlgebraTools.exists_unit_entry (f i) (hf.idem i) (h0 i)`. Use `choose a b hu using hc`. Use `set P : Matrix ι ι R := Matrix.of fun k j => f j k (b j) with hP`. Use `set Q : Matrix ι ι R := Matrix.of fun i k => ((hu i).unit⁻¹ : Rˣ) * f i (a i) k with hQ`.

Establish `hent : ∀ (M : Matrix ι ι R) (j k : ι), (Q * M * P) j k = ((hu j).unit⁻¹ : Rˣ) * (f j * M * f k) (a j) (b k)`. Introduce `M j k`. Simplify using `only [hP, hQ, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Establish `hidem : ∀ i, f i * f i = f i` using `fun i => (hf.idem i).eq`. Establish `hort : ∀ i j, i ≠ j → f i * f j = 0` using `fun i j hij => hf.ortho hij`.

Establish `hQP : Q * P = 1`. Use extensionality with `j k`. Establish `h1` using `hent 1 j k`. Simplify using `only [Matrix.mul_one] at h1`. Rewrite using `[h1]`.

Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality. Rewrite using `[hidem, Matrix.one_apply_eq, IsUnit.val_inv_mul]`. Rewrite using `[hort j k hjk, Matrix.one_apply_ne hjk, Matrix.zero_apply, mul_zero]`. Establish `hPQ : P * Q = 1` using `mul_eq_one_comm.1 hQP`.

Use `⟨⟨Q, P, hQP, hPQ⟩, fun i => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Q * f i * P = single i i 1`. Use extensionality with `j k`. Rewrite using `[hent, Matrix.single_apply]`. Distinguish the cases in `hji : i = j`.

Substitute `hji` using the available equality. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality. Rewrite using `[hidem, hidem, IsUnit.val_inv_mul, if_pos ⟨rfl, rfl⟩]`. Rewrite using `[hidem, hort i k hik, Matrix.zero_apply, mul_zero, if_neg (fun h => hik h.2)]`.

Rewrite using `[hort j i (Ne.symm hji), zero_mul, Matrix.zero_apply, mul_zero, if_neg (fun h => hji h.1)]`.
-/
theorem UpperTheory.V.AlgebraTools.coi_conj_single :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → Matrix ι ι R), CompleteOrthogonalIdempotents f → (∀ i, f i ≠ 0) → ∃ g : GL ι R, ∀ i, (g : Matrix ι ι R) * f i * ((g⁻¹ : GL ι R) : Matrix ι ι R) = single i i 1 := by
  intro R _ _ ι _ _ f hf h0
  classical
  have hc : ∀ i, ∃ a b, IsUnit (f i a b) := fun i =>
    UpperTheory.V.AlgebraTools.exists_unit_entry (f i) (hf.idem i) (h0 i)
  choose a b hu using hc
  set P : Matrix ι ι R := Matrix.of fun k j => f j k (b j) with hP
  set Q : Matrix ι ι R := Matrix.of fun i k => ((hu i).unit⁻¹ : Rˣ) * f i (a i) k with hQ
  have hent : ∀ (M : Matrix ι ι R) (j k : ι),
      (Q * M * P) j k = ((hu j).unit⁻¹ : Rˣ) * (f j * M * f k) (a j) (b k) := by
    intro M j k
    simp only [hP, hQ, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have hidem : ∀ i, f i * f i = f i := fun i => (hf.idem i).eq
  have hort : ∀ i j, i ≠ j → f i * f j = 0 := fun i j hij => hf.ortho hij
  have hQP : Q * P = 1 := by
    ext j k
    have h1 := hent 1 j k
    simp only [Matrix.mul_one] at h1
    rw [h1]
    by_cases hjk : j = k
    · subst hjk
      rw [hidem, Matrix.one_apply_eq, IsUnit.val_inv_mul]
    · rw [hort j k hjk, Matrix.one_apply_ne hjk, Matrix.zero_apply, mul_zero]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  refine ⟨⟨Q, P, hQP, hPQ⟩, fun i => ?_⟩
  change Q * f i * P = single i i 1
  ext j k
  rw [hent, Matrix.single_apply]
  by_cases hji : i = j
  · subst hji
    by_cases hik : i = k
    · subst hik
      rw [hidem, hidem, IsUnit.val_inv_mul, if_pos ⟨rfl, rfl⟩]
    · rw [hidem, hort i k hik, Matrix.zero_apply, mul_zero, if_neg (fun h => hik h.2)]
  · rw [hort j i (Ne.symm hji), zero_mul, Matrix.zero_apply, mul_zero, if_neg (fun h => hji h.1)]
