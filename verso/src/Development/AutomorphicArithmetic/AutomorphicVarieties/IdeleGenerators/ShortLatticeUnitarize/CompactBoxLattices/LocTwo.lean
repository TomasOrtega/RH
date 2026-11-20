import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

open NumberField IsDedekindDomain IsLocalRing UpperTheory.V UpperTheory.V.Sd Formalism.ConjugateSelfDual

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring`.
-/
private theorem sq_two {O : Type} [CommRing O] (M : Matrix (Fin 2) (Fin 2) O) :
    M * M = (M 0 0 + M 1 1) • M - (M 0 0 * M 1 1 - M 0 1 * M 1 0) • (1 : Matrix (Fin 2) (Fin 2) O) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, 1, by simp, by simp, by simp⟩`. Consider the case `succ n ih`. Take `⟨U, V, h, hU, hV⟩` from `ih`. Use `⟨U * (M 0 0 + M 1 1) + V, -(U * (M 0 0 * M 1 1 - M 0 1 * M 1 0)), ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ, h, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, sq_two M] module`. Rewrite using `[map_add, map_mul, ht, hU, hV]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_neg, map_mul, hd, hU]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem pow_two_dim {O k : Type} [CommRing O] [CommRing k] (r : O →+* k) (M : Matrix (Fin 2) (Fin 2) O)
    (ht : r (M 0 0 + M 1 1) = 2) (hd : r (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 1) (n : ℕ) :
    ∃ U V : O, M ^ n = U • M + V • (1 : Matrix (Fin 2) (Fin 2) O) ∧ r U = n ∧ r V = 1 - n := by
  induction n with
  | zero => exact ⟨0, 1, by simp, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨U, V, h, hU, hV⟩ := ih
    refine ⟨U * (M 0 0 + M 1 1) + V, -(U * (M 0 0 * M 1 1 - M 0 1 * M 1 0)), ?_, ?_, ?_⟩
    · rw [pow_succ, h, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, sq_two M]
      module
    · rw [map_add, map_mul, ht, hU, hV]; push_cast; ring
    · rw [map_neg, map_mul, hd, hU]; push_cast; ring

/- English proof (translation)
Establish `h1 : ∀ x : k, x ≠ 0 → x = 1`. Take `⟨y, -, hy⟩` from `(Nat.card_eq_two_iff' (0 : k)).1 hk`. Introduce `x hx`. Rewrite using `[hy x hx, hy 1 one_ne_zero]`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Use `h1 2 h` as an intermediate fact. Establish `h2 : (1 : k) = 0` using `by linear_combination this`. Conclude with `one_ne_zero h2`.
-/
private theorem field_two {k : Type} [Field k] (hk : Nat.card k = 2) :
    (∀ x : k, x ≠ 0 → x = 1) ∧ (2 : k) = 0 := by
  have h1 : ∀ x : k, x ≠ 0 → x = 1 := by
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : k)).1 hk
    intro x hx
    rw [hy x hx, hy 1 one_ne_zero]
  refine ⟨h1, ?_⟩
  by_contra h
  have := h1 2 h
  have h2 : (1 : k) = 0 := by linear_combination this
  exact one_ne_zero h2

/- English proof (translation)
Take `⟨h1, h2⟩` from `field_two hk`. Establish `hu` using `(Matrix.GeneralLinearGroup.det h).isUnit`. Rewrite `hu` using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]`. Establish `hdet : residue O (h 0 0 * h 1 1 - h 0 1 * h 1 0) = 1` using `h1 _ (hu.map (residue O)).ne_zero`. Establish `ha : residue O (h 0 0) = 1`.

Rewrite `hdet` using `[map_sub, map_mul, map_mul, hc, hd]`. Simplify using `using hdet`. Take `⟨U, V, hp, hU, -⟩` from `pow_two_dim (residue O) (h : Matrix (Fin 2) (Fin 2) O) (by rw [map_add, ha, hd]; norm_num) hdet n`. Establish `hUu : IsUnit U`. Assume the negation of the conclusion as `hU'`.

Establish `h0 : residue O U = 0` using `(residue_eq_zero_iff U).2 hU'`. Take `⟨m, rfl⟩` from `hn`. Rewrite `hU` using `[h0]`. Move the coercions through the operations in `at hU`. Rewrite `hU` using `[h2]`.

Simplify using `at hU`. Establish `hU0 : φ U ≠ 0` using `(hUu.map φ).ne_zero`. Use `set k := Matrix.GeneralLinearGroup.map φ h with hkdef`. Establish `hkp : ((k ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = φ U • (k : Matrix (Fin 2) (Fin 2) K) + φ V • (1 : Matrix (Fin 2) (Fin 2) K)`. Rewrite using `[hkdef, ← map_pow]`.

Express the relevant statement in the definitionally equal form `((h ^ n : GL (Fin 2) O) : Matrix (Fin 2) (Fin 2) O).map φ = φ U • (h : Matrix (Fin 2) (Fin 2) O).map φ + φ V • (1 : Matrix (Fin 2) (Fin 2) K)`. Rewrite using `[Units.val_pow_eq_pow_val, hp]`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply, apply_ite φ]`. Rewrite `hz`, the goal using `[Subgroup.mem_center_iff]`.

Introduce `g`. Establish `hg` using `congrArg Units.val (hz g)`. Rewrite `hg` using `[Units.val_mul, Units.val_mul, hkp, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_one, one_mul, add_left_inj]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul]`.

Conclude with `smul_right_injective _ hU0 hg`.
-/
private theorem gen {O K : Type} [CommRing O] [IsLocalRing O] [Field K] (φ : O →+* K)
    (hk : Nat.card (ResidueField O) = 2) (h : GL (Fin 2) O)
    (hc : residue O (h 1 0) = 0) (hd : residue O (h 1 1) = 1) (n : ℕ) (hn : Odd n)
    (hz : (Matrix.GeneralLinearGroup.map φ h) ^ n ∈ Subgroup.center (GL (Fin 2) K)) :
    Matrix.GeneralLinearGroup.map φ h ∈ Subgroup.center (GL (Fin 2) K) := by
  obtain ⟨h1, h2⟩ := field_two hk
  have hu := (Matrix.GeneralLinearGroup.det h).isUnit
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at hu
  have hdet : residue O (h 0 0 * h 1 1 - h 0 1 * h 1 0) = 1 := h1 _ (hu.map (residue O)).ne_zero
  have ha : residue O (h 0 0) = 1 := by
    rw [map_sub, map_mul, map_mul, hc, hd] at hdet
    simpa using hdet
  obtain ⟨U, V, hp, hU, -⟩ := pow_two_dim (residue O) (h : Matrix (Fin 2) (Fin 2) O)
    (by rw [map_add, ha, hd]; norm_num) hdet n
  have hUu : IsUnit U := by
    by_contra hU'
    have h0 : residue O U = 0 := (residue_eq_zero_iff U).2 hU'
    obtain ⟨m, rfl⟩ := hn
    rw [h0] at hU
    push_cast at hU
    rw [h2] at hU
    simp at hU
  have hU0 : φ U ≠ 0 := (hUu.map φ).ne_zero
  set k := Matrix.GeneralLinearGroup.map φ h with hkdef
  have hkp : ((k ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      φ U • (k : Matrix (Fin 2) (Fin 2) K) + φ V • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [hkdef, ← map_pow]
    change ((h ^ n : GL (Fin 2) O) : Matrix (Fin 2) (Fin 2) O).map φ =
      φ U • (h : Matrix (Fin 2) (Fin 2) O).map φ + φ V • (1 : Matrix (Fin 2) (Fin 2) K)
    rw [Units.val_pow_eq_pow_val, hp]
    ext i j
    simp [Matrix.one_apply, apply_ite φ]
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  have hg := congrArg Units.val (hz g)
  rw [Units.val_mul, Units.val_mul, hkp, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc,
    smul_mul_assoc, mul_one, one_mul, add_left_inj] at hg
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact smul_right_injective _ hU0 hg

/- English proof (translation)
Introduce `F _ _ u c hc hN k hk n hn hz`. Take `⟨h, hh, rfl⟩` from `hk`. Establish `hle : maximalIdeal (u.adicCompletionIntegers F) ^ c ≤ maximalIdeal _` using `Ideal.pow_le_self hc`. Use `gen _ ?_ h ?_ ?_ n hn hz` and prove the remaining obligations. Rewrite using `[Formalism.UG.P.tjcosets_card_residue, ← hN]`.

Simplify using `[normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `h0` using `congrFun hh 0`. Rewrite using `[residue_eq_zero_iff]`. Apply `hle` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`.

Simplify `h0` using `[Matrix.vecMul, dotProduct, Fin.sum_univ_two]`. Establish `h0` using `congrFun hh 1`. Rewrite using `[← map_one (residue (u.adicCompletionIntegers F)), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`. Apply `hle` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq, map_one]`.

Simplify `h0` using `[Matrix.vecMul, dotProduct, Fin.sum_univ_two]`.
-/
theorem UpperTheory.V.Sd.Wc.locTwo :
    UpperTheory.V.Sd.Wc.LocTwo := by
  intro F _ _ u c hc hN k hk n hn hz
  obtain ⟨h, hh, rfl⟩ := hk
  have hle : maximalIdeal (u.adicCompletionIntegers F) ^ c ≤ maximalIdeal _ := Ideal.pow_le_self hc
  refine gen _ ?_ h ?_ ?_ n hn hz
  · rw [Formalism.UG.P.tjcosets_card_residue, ← hN]
    simp [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · have h0 := congrFun hh 0
    rw [residue_eq_zero_iff]
    apply hle
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h0
  · have h0 := congrFun hh 1
    rw [← map_one (residue (u.adicCompletionIntegers F)), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    apply hle
    rw [← Ideal.Quotient.eq, map_one]
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h0
