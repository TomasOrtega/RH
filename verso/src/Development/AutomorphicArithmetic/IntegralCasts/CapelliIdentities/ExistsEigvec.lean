import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing Polynomial

/- English proof (translation)
Establish `hd : X.map (residue R) = diagonal fun b => residue R (X b b)`. Use extensionality with `b c`. Distinguish the cases in `h : b = c`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[diagonal_apply_ne _ h, map_apply, residue_eq_zero_iff]`. Conclude with `hm b c h`. Establish `hne : ∀ b, b ≠ a → residue R (X a a) - residue R (X b b) ≠ 0` using `fun b hb => by`. Rewrite using `[← map_sub]`. Conclude with `((hu a b hb.symm).map (residue R)).ne_zero`.

Establish `hP : (∏ b ∈ Finset.univ.erase a, (residue R (X a a) - residue R (X b b))) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun b hb => hne b (Finset.ne_of_mem_erase hb)`. Establish `hc : X.charpoly.map (residue R) = (Polynomial.X - C (residue R (X a a))) * ∏ b ∈ Finset.univ.erase a, (Polynomial.X - C (residue R (X b b)))`. Rewrite using `[← Matrix.charpoly_map, hd, Matrix.charpoly_diagonal, Finset.mul_prod_erase Finset.univ (fun b => Polynomial.X - C (residue R (X b b))) (Finset.mem_univ a)]`. Take `⟨l, hl, hla⟩` from `HenselianRing.is_henselian (I := maximalIdeal R) X.charpoly X.charpoly_monic (X a a) (by`. Rewrite using `[← residue_eq_zero_iff, ← eval₂_hom, ← eval_map, hc]`.

Use the proof step `simp)`. Use the proof step `(by`. Express the relevant statement in the definitionally equal form `IsUnit (residue R _)`. Rewrite using `[← eval₂_hom, ← eval_map, ← derivative_map, hc, isUnit_iff_ne_zero]`. Simplify `hP)` using `[eval_prod]`.

Establish `hla' : residue R l = residue R (X a a)`. Rewrite using `[← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`. Conclude with `hla`. Use `set M : Matrix (Fin 3) (Fin 3) R := scalar (Fin 3) l - X with hM`. Establish `hdet : M.det = 0` using `by rw [hM, ← Matrix.eval_charpoly]; exact hl`.

Establish `hMd : M.map (residue R) = diagonal fun b => residue R (X a a) - residue R (X b b)`. Use extensionality with `b c`. Use `congrFun (congrFun hd b) c` as an intermediate fact. Distinguish the cases in `h : b = c`. Substitute `h` using the available equality.

Simplify using `[hM, hla']`. Rewrite `this`, the goal using `[diagonal_apply_ne _ h]`. Simplify `this` using `[hM, diagonal_apply_ne _ h]`. Establish `hadj : ∀ b, residue R (M.adjugate b a) = (diagonal fun i => ∏ j ∈ Finset.univ.erase i, (residue R (X a a) - residue R (X j j))) b a` using `fun b => by`. Use `(residue R).map_adjugate M` as an intermediate fact.

Rewrite `this` using `[RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hMd, adjugate_diagonal]`. Conclude with `congrFun (congrFun this b) a`. Establish `hun : IsUnit (M.adjugate a a)`. Rewrite using `[← residue_ne_zero_iff_isUnit, hadj, diagonal_apply_eq]`. Conclude with `hP`.

Take `⟨u, hu'⟩` from `hun`. Establish `hker : M *ᵥ (fun b => M.adjugate b a) = 0`. Use extensionality with `b`. Use `congrFun (congrFun (mul_adjugate M) b) a` as an intermediate fact. Rewrite `this` using `[hdet, zero_smul]`.

Conclude with `this`. Use `⟨l, (↑u⁻¹ : R) • fun b => M.adjugate b a, ?_, fun b hb => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[← hu']`. Use `Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations. Rewrite using `[← residue_eq_zero_iff, hadj, diagonal_apply_ne _ hb]`.

Rewrite `hker` using `[hM, sub_mulVec, sub_eq_zero]`. Rewrite using `[mulVec_smul, ← hker, smul_comm l]`. Use `congr 1`. Use extensionality with `b`. Simplify using `[mulVec_diagonal, hM]`.
-/
private theorem UpperTheory.Reformulated.B.Qf19.exists_eigvec {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (X : Matrix (Fin 3) (Fin 3) R)
    (hu : ∀ a b : Fin 3, a ≠ b → IsUnit (X a a - X b b))
    (hm : ∀ a b : Fin 3, a ≠ b → X a b ∈ maximalIdeal R) (a : Fin 3) :
    ∃ (l : R) (v : Fin 3 → R), v a = 1 ∧ (∀ b, b ≠ a → v b ∈ maximalIdeal R) ∧ X *ᵥ v = l • v := by
  have hd : X.map (residue R) = diagonal fun b => residue R (X b b) := by
    ext b c
    by_cases h : b = c
    · subst h; simp
    · rw [diagonal_apply_ne _ h, map_apply, residue_eq_zero_iff]; exact hm b c h
  have hne : ∀ b, b ≠ a → residue R (X a a) - residue R (X b b) ≠ 0 := fun b hb => by
    rw [← map_sub]; exact ((hu a b hb.symm).map (residue R)).ne_zero
  have hP : (∏ b ∈ Finset.univ.erase a, (residue R (X a a) - residue R (X b b))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun b hb => hne b (Finset.ne_of_mem_erase hb)
  have hc : X.charpoly.map (residue R) =
      (Polynomial.X - C (residue R (X a a))) *
        ∏ b ∈ Finset.univ.erase a, (Polynomial.X - C (residue R (X b b))) := by
    rw [← Matrix.charpoly_map, hd, Matrix.charpoly_diagonal,
      Finset.mul_prod_erase Finset.univ (fun b => Polynomial.X - C (residue R (X b b))) (Finset.mem_univ a)]
  obtain ⟨l, hl, hla⟩ := HenselianRing.is_henselian (I := maximalIdeal R) X.charpoly X.charpoly_monic (X a a)
    (by
      rw [← residue_eq_zero_iff, ← eval₂_hom, ← eval_map, hc]
      simp)
    (by
      change IsUnit (residue R _)
      rw [← eval₂_hom, ← eval_map, ← derivative_map, hc, isUnit_iff_ne_zero]
      simpa [eval_prod] using hP)
  have hla' : residue R l = residue R (X a a) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hla
  set M : Matrix (Fin 3) (Fin 3) R := scalar (Fin 3) l - X with hM
  have hdet : M.det = 0 := by rw [hM, ← Matrix.eval_charpoly]; exact hl
  have hMd : M.map (residue R) = diagonal fun b => residue R (X a a) - residue R (X b b) := by
    ext b c
    have := congrFun (congrFun hd b) c
    by_cases h : b = c
    · subst h; simp [hM, hla']
    · rw [diagonal_apply_ne _ h] at this ⊢
      simpa [hM, diagonal_apply_ne _ h] using this
  have hadj : ∀ b, residue R (M.adjugate b a) = (diagonal fun i => ∏ j ∈ Finset.univ.erase i,
      (residue R (X a a) - residue R (X j j))) b a := fun b => by
    have := (residue R).map_adjugate M
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hMd, adjugate_diagonal] at this
    exact congrFun (congrFun this b) a
  have hun : IsUnit (M.adjugate a a) := by
    rw [← residue_ne_zero_iff_isUnit, hadj, diagonal_apply_eq]; exact hP
  obtain ⟨u, hu'⟩ := hun
  have hker : M *ᵥ (fun b => M.adjugate b a) = 0 := by
    ext b
    have := congrFun (congrFun (mul_adjugate M) b) a
    rw [hdet, zero_smul] at this
    exact this
  refine ⟨l, (↑u⁻¹ : R) • fun b => M.adjugate b a, ?_, fun b hb => ?_, ?_⟩
  · simp [← hu']
  · refine Ideal.mul_mem_left _ _ ?_
    rw [← residue_eq_zero_iff, hadj, diagonal_apply_ne _ hb]
  · rw [hM, sub_mulVec, sub_eq_zero] at hker
    rw [mulVec_smul, ← hker, smul_comm l]
    congr 1
    ext b
    simp [mulVec_diagonal, hM]

/- English proof (translation)
Introduce `R _ _ _ X hu hm`. Use `choose l v h1 h2 h3 using UpperTheory.Reformulated.B.Qf19.exists_eigvec X hu hm`. Use `set H : Matrix (Fin 3) (Fin 3) R := Matrix.of fun b a => v a b with hH`. Establish `hhat : ∀ a b, (H - 1) a b ∈ maximalIdeal R` using `fun a b => by`. Distinguish the cases in `h : a = b`.

Substitute `h` using the available equality. Simplify using `[hH, h1]`. Simplify `h2 b a h` using `[hH, one_apply_ne h]`. Establish `hmap : (residue R).mapMatrix H = 1`. Use extensionality with `a b`.

Use `(residue_eq_zero_iff _).2 (hhat a b)` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Rewrite using `[RingHom.mapMatrix_apply, map_apply, this]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[one_apply_ne h]`. Establish `hdet : IsUnit H.det`. Rewrite using `[← residue_ne_zero_iff_isUnit, RingHom.map_det, hmap]`. Simplify using the standard rewrite rules.

Take `⟨h, hh⟩` from `(Matrix.isUnit_iff_isUnit_det H).2 hdet`. Establish `hXH : X * H = H * diagonal l`. Use extensionality with `b a`. Use `congrFun (h3 a) b` as an intermediate fact. Rewrite using `[mul_diagonal, mul_comm]`.

Conclude with `this`. Use `⟨h, ?_, fun a => ?_, ?_⟩` and prove the remaining obligations. Introduce `a b`. Rewrite using `[hh]`. Conclude with `hhat a b`.

Rewrite using `[hh]`. Conclude with `h1 a`. Establish `: ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h = diagonal l`. Rewrite using `[Matrix.mul_assoc, hh, hXH, ← hh, ← Matrix.mul_assoc]`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `isDiag_diagonal l`.
-/
theorem UpperTheory.Reformulated.B.Qf19.exists_canon :
    ∀ {R : Type} [inst : CommRing R] [inst_1 : IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
      (X : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R),
      (∀ (a b : Fin (3 : ℕ)), a ≠ b → IsUnit (X a a - X b b)) →
        (∀ (a b : Fin (3 : ℕ)), a ≠ b → X a b ∈ IsLocalRing.maximalIdeal R) →
          ∃ (h : GL (Fin (3 : ℕ)) R), UpperTheory.V.UnitaryThreeInertia.Canon X h := by
  intro R _ _ _ X hu hm
  choose l v h1 h2 h3 using UpperTheory.Reformulated.B.Qf19.exists_eigvec X hu hm
  set H : Matrix (Fin 3) (Fin 3) R := Matrix.of fun b a => v a b with hH
  have hhat : ∀ a b, (H - 1) a b ∈ maximalIdeal R := fun a b => by
    by_cases h : a = b
    · subst h; simp [hH, h1]
    · simpa [hH, one_apply_ne h] using h2 b a h
  have hmap : (residue R).mapMatrix H = 1 := by
    ext a b
    have := (residue_eq_zero_iff _).2 (hhat a b)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [RingHom.mapMatrix_apply, map_apply, this]
    by_cases h : a = b
    · subst h; simp
    · simp [one_apply_ne h]
  have hdet : IsUnit H.det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det, hmap]; simp
  obtain ⟨h, hh⟩ := (Matrix.isUnit_iff_isUnit_det H).2 hdet
  have hXH : X * H = H * diagonal l := by
    ext b a
    have := congrFun (h3 a) b
    rw [mul_diagonal, mul_comm]
    exact this
  refine ⟨h, ?_, fun a => ?_, ?_⟩
  · intro a b; rw [hh]; exact hhat a b
  · rw [hh]; exact h1 a
  · have : ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h = diagonal l := by
      rw [Matrix.mul_assoc, hh, hXH, ← hh, ← Matrix.mul_assoc]
      simp
    rw [this]; exact isDiag_diagonal l
