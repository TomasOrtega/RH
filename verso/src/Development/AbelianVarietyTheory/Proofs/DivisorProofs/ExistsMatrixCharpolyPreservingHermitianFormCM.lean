import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.GlobHerm

/- English proof (translation)
Use `set V := vandermonde l with hV`. Establish `hl0 : ∀ k, l k ≠ 0` using `fun k h => by simpa [h] using h1 k`. Establish `hVd : V.det ≠ 0` using `det_vandermonde_ne_zero_iff.2 hl`. Establish `hconj : ∀ k, starRingEnd ℂ (l k) = (l k)⁻¹`. Introduce `k`.

Rewrite using `[Complex.inv_def, Complex.normSq_eq_norm_sq, h1 k]`. Simplify using the standard rewrite rules. Establish `hAd : A.det ≠ 0`. Use `congrArg Matrix.det hVA` as an intermediate fact. Rewrite `this` using `[det_mul, det_mul, det_diagonal, mul_comm]`.

Establish `h2 : A.det = ∏ k, l k` using `mul_right_cancel₀ hVd this`. Rewrite using `[h2]`. Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => hl0 k`. Use `set D' := diagonal fun k => (l k)⁻¹`. Establish `hDD : D' * diagonal l = 1`.

Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Conclude with `inv_mul_cancel₀ (hl0 k)`. Establish `hAinv : A * A⁻¹ = 1` using `mul_nonsing_inv A (isUnit_iff_ne_zero.2 hAd)`.

Establish `hVAi : V * A⁻¹ = D' * V`. Combine the equalities or inequalities in the displayed calculation. Establish `hpow : ∀ j : ℕ, V * A ^ j = diagonal l ^ j * V`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hVA, ← mul_assoc, ← pow_succ]`. Establish `hpowi : ∀ j : ℕ, V * A⁻¹ ^ j = D' ^ j * V`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hVAi, ← mul_assoc, ← pow_succ]`. Establish `hVinv : V⁻¹ * V = 1` using `nonsing_inv_mul V (isUnit_iff_ne_zero.2 hVd)`. Establish `hVinv' : V * V⁻¹ = 1` using `mul_nonsing_inv V (isUnit_iff_ne_zero.2 hVd)`. Use `⟨hAd, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Establish `hM : V * (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) * V`. Rewrite using `[← mul_assoc, hpowi, mul_assoc, hpow, ← mul_assoc]`. Establish `htr : trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = trace (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, hVinv, one_mul]`. Use `_ = trace (V⁻¹ * ((D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) * V)) := by rw [hM]`. Use `_ = trace (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) := by`. Rewrite using `[trace_mul_comm, mul_assoc, hVinv', mul_one]`. Rewrite using `[of_apply, htr, diagonal_pow, diagonal_pow, diagonal_mul_diagonal, trace_diagonal, mul_apply]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[V, D', vandermonde_apply, conjTranspose_apply, hconj, inv_pow]`. Rewrite using `[det_mul, det_conjTranspose]`. Conclude with `mul_ne_zero (by simpa using hVd) hVd`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[conjTranspose_mul]`. Simplify using `only [mul_assoc]`. Use `_ = Vᴴ * ((diagonal l)ᴴ * diagonal l) * V := by`. Rewrite using `[hVA, conjTranspose_mul]`. Simplify using `only [mul_assoc]`.

Use `_ = Vᴴ * V := by`. Rewrite using `[diagonal_conjTranspose, diagonal_mul_diagonal]`. Establish `: (diagonal fun k => star (l k) * l k) = 1`. Rewrite using `[← diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Use `show starRingEnd ℂ (l k) * l k = 1`. Rewrite using `[hconj, inv_mul_cancel₀ (hl0 k)]`. Simplify using `only [Pi.star_apply] at this ⊢`. Rewrite using `[this, mul_one]`.
-/
theorem vandermonde_diag_herm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ) (hl : Function.Injective l)
    (h1 : ∀ k, ‖l k‖ = 1) (hVA : vandermonde l * A = diagonal l * vandermonde l) :
    A.det ≠ 0 ∧ (Matrix.of fun i j : Fin n => trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ))) = (vandermonde l)ᴴ * vandermonde l ∧
      ((vandermonde l)ᴴ * vandermonde l).det ≠ 0 ∧
      Aᴴ * ((vandermonde l)ᴴ * vandermonde l) * A = (vandermonde l)ᴴ * vandermonde l := by
  set V := vandermonde l with hV
  have hl0 : ∀ k, l k ≠ 0 := fun k h => by simpa [h] using h1 k
  have hVd : V.det ≠ 0 := det_vandermonde_ne_zero_iff.2 hl
  have hconj : ∀ k, starRingEnd ℂ (l k) = (l k)⁻¹ := by
    intro k
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1 k]; simp
  have hAd : A.det ≠ 0 := by
    have := congrArg Matrix.det hVA
    rw [det_mul, det_mul, det_diagonal, mul_comm] at this
    have h2 : A.det = ∏ k, l k := mul_right_cancel₀ hVd this
    rw [h2]; exact Finset.prod_ne_zero_iff.2 fun k _ => hl0 k
  set D' := diagonal fun k => (l k)⁻¹
  have hDD : D' * diagonal l = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext k; exact inv_mul_cancel₀ (hl0 k)
  have hAinv : A * A⁻¹ = 1 := mul_nonsing_inv A (isUnit_iff_ne_zero.2 hAd)
  have hVAi : V * A⁻¹ = D' * V := by
    calc V * A⁻¹ = D' * diagonal l * V * A⁻¹ := by rw [hDD, one_mul]
      _ = D' * (V * A) * A⁻¹ := by rw [hVA, mul_assoc D']
      _ = D' * V := by rw [mul_assoc, mul_assoc, hAinv, mul_one]
  have hpow : ∀ j : ℕ, V * A ^ j = diagonal l ^ j * V := by
    intro j; induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hVA, ← mul_assoc, ← pow_succ]
  have hpowi : ∀ j : ℕ, V * A⁻¹ ^ j = D' ^ j * V := by
    intro j; induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hVAi, ← mul_assoc, ← pow_succ]
  have hVinv : V⁻¹ * V = 1 := nonsing_inv_mul V (isUnit_iff_ne_zero.2 hVd)
  have hVinv' : V * V⁻¹ = 1 := mul_nonsing_inv V (isUnit_iff_ne_zero.2 hVd)
  refine ⟨hAd, ?_, ?_, ?_⟩
  · ext i j
    have hM : V * (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) * V := by
      rw [← mul_assoc, hpowi, mul_assoc, hpow, ← mul_assoc]
    have htr : trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = trace (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) := by
      calc trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = trace (V⁻¹ * (V * (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)))) := by
            rw [← mul_assoc, hVinv, one_mul]
        _ = trace (V⁻¹ * ((D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) * V)) := by rw [hM]
        _ = trace (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) := by
            rw [trace_mul_comm, mul_assoc, hVinv', mul_one]
    rw [of_apply, htr, diagonal_pow, diagonal_pow, diagonal_mul_diagonal, trace_diagonal, mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [V, D', vandermonde_apply, conjTranspose_apply, hconj, inv_pow]
  · rw [det_mul, det_conjTranspose]
    exact mul_ne_zero (by simpa using hVd) hVd
  · calc Aᴴ * (Vᴴ * V) * A = (V * A)ᴴ * (V * A) := by
          rw [conjTranspose_mul]; simp only [mul_assoc]
      _ = Vᴴ * ((diagonal l)ᴴ * diagonal l) * V := by
          rw [hVA, conjTranspose_mul]; simp only [mul_assoc]
      _ = Vᴴ * V := by
          rw [diagonal_conjTranspose, diagonal_mul_diagonal]
          have : (diagonal fun k => star (l k) * l k) = 1 := by
            rw [← diagonal_one]; congr 1; funext k
            show starRingEnd ℂ (l k) * l k = 1
            rw [hconj, inv_mul_cancel₀ (hl0 k)]
          simp only [Pi.star_apply] at this ⊢
          rw [this, mul_one]

end GlobalTheory.GlobHerm

namespace GlobalTheory.GlobHerm

/- English proof (translation)
Introduce `E _ _ _ n P hP`. Take `⟨hmon, hdeg, hsep, hroot⟩` from `hP`. Substitute `hdeg` using the available equality. Establish `hP0 : P ≠ 0` using `hmon.ne_zero`. Set `pb` to `AdjoinRoot.powerBasis hP0`.

Set `Cm : Matrix (Fin P.natDegree) (Fin P.natDegree) E` to `Algebra.leftMulMatrix pb.basis pb.gen`. Set `H : Matrix (Fin P.natDegree) (Fin P.natDegree) E` to `Matrix.of fun i j => trace (Cm⁻¹ ^ (i : ℕ) * Cm ^ (j : ℕ))`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hτc : ∀ x, τ ((IsCMField.complexConj E).toRingEquiv.toRingHom x) = starRingEnd ℂ (τ x)` using `fun x => IsCMField.complexEmbedding_complexConj E τ x`. Establish `hQsep : (P.map τ).Separable` using `hsep.map`.

Establish `hQcard : (P.map τ).roots.card = P.natDegree`. Rewrite using `[splits_iff_card_roots.1 (IsAlgClosed.splits _), natDegree_map]`. Establish `hs : (P.map τ).roots.toFinset.card = P.natDegree`. Rewrite using `[Multiset.toFinset_card_of_nodup (nodup_roots hQsep), hQcard]`. Set `e : (P.map τ).roots.toFinset ≃ Fin P.natDegree` to `Fintype.equivFinOfCardEq (by simp [hs])`.

Set `l : Fin P.natDegree → ℂ` to `fun k => (e.symm k : ℂ)`. Establish `hl : Function.Injective l` using `Subtype.val_injective.comp e.symm.injective`. Establish `hlr : ∀ k, eval₂ τ (l k) P = 0`. Introduce `k`. Use `(e.symm k).2` as an intermediate fact.

Rewrite `this` using `[Multiset.mem_toFinset, mem_roots hQsep.ne_zero, IsRoot, eval_map]`. Conclude with `this`. Establish `h1 : ∀ k, ‖l k‖ = 1` using `fun k => hroot τ _ (Multiset.mem_toFinset.1 (e.symm k).2)`. Establish `hrep : ∀ k (x : AdjoinRoot P), ∑ i : Fin pb.dim, l k ^ (i : ℕ) * τ (pb.basis.repr x i) = AdjoinRoot.lift τ (l k) (hlr k) x`. Introduce `k x`.

Use `conv_rhs => rw [← pb.basis.sum_repr x]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, PowerBasis.coe_basis]`. Simplify using `only [pb, AdjoinRoot.powerBasis_gen, map_pow, AdjoinRoot.lift_root, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hVA : vandermonde l * Cm.map τ = diagonal l * vandermonde l`. Use extensionality with `k j`. Rewrite using `[mul_apply, diagonal_mul, vandermonde_apply]`. Use `show ∑ i : Fin pb.dim, l k ^ (i : ℕ) * τ (Algebra.leftMulMatrix pb.basis pb.gen i j) = l k * l k ^ (j : ℕ)`.

Establish `hC : ∀ i : Fin pb.dim, Algebra.leftMulMatrix pb.basis pb.gen i j = pb.basis.repr (pb.gen * pb.basis j) i` using `fun i => Algebra.leftMulMatrix_eq_repr_mul _ _ _ _`. Rewrite using `[Finset.sum_congr rfl fun i _ => by rw [hC i], hrep k]`. Simplify using `only [pb, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]`. Rewrite using `[← pow_succ', map_pow, AdjoinRoot.lift_root, pow_succ']`. Take `⟨hAd, hH, hHd, hpres⟩` from `GlobalTheory.GlobHerm.vandermonde_diag_herm (Cm.map τ) l hl h1 hVA`.

Establish `hinv : (Cm.map τ)⁻¹ = Cm⁻¹.map τ`. Apply `inv_eq_left_inv` to reduce the goal to its premises. Establish `hCd : Cm.det ≠ 0`. Introduce `h`. Apply `hAd` to reduce the goal to its premises.

Use `RingHom.map_det τ Cm` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `this.symm`. Rewrite using `[← Matrix.map_mul, nonsing_inv_mul Cm (isUnit_iff_ne_zero.2 hCd), Matrix.map_one _ (map_zero τ) (map_one τ)]`. Establish `hHm : H.map τ = (vandermonde l)ᴴ * vandermonde l`.

Rewrite using `[← hH]`. Use extensionality with `i j`. Simplify using `only [map_apply, of_apply, H]`. Rewrite using `[AddMonoidHom.map_trace τ, hinv]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `τ.mapMatrix _ = _`. Rewrite using `[map_mul, map_pow, map_pow]`. Both sides reduce to the same expression. Establish `hinj : Function.Injective (fun M : Matrix (Fin P.natDegree) (Fin P.natDegree) E => M.map τ)` using `Matrix.map_injective τ.injective`. Establish `hcT : ∀ M : Matrix (Fin P.natDegree) (Fin P.natDegree) E, (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map τ = (M.map τ)ᴴ`.

Introduce `M`. Use extensionality with `i j`. Simplify using `only [cT, map_apply, transpose_apply, conjTranspose_apply, hτc]`. Both sides reduce to the same expression. Use `⟨Cm, H, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `(charpoly_leftMulMatrix pb).trans ?_` and prove the remaining obligations. Rewrite using `[AdjoinRoot.powerBasis_gen, AdjoinRoot.minpoly_root hP0, hmon.leadingCoeff, inv_one, Polynomial.C_1, mul_one]`. Introduce `h`. Apply `hAd` to reduce the goal to its premises. Use `RingHom.map_det τ Cm` as an intermediate fact.

Rewrite `this` using `[h, map_zero]`. Conclude with `this.symm`. Introduce `h`. Apply `hHd` to reduce the goal to its premises. Use `RingHom.map_det τ H` as an intermediate fact.

Rewrite `this` using `[h, map_zero]`. Rewrite using `[← hHm]`. Conclude with `this.symm`. Apply `hinj` to reduce the goal to its premises. Simplify using `only`.

Rewrite using `[hcT, hHm, conjTranspose_mul, conjTranspose_conjTranspose]`. Apply `hinj` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hcT, hHm, hpres]`.
-/
theorem exists_mat_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ C H : Matrix (Fin n) (Fin n) E, C.charpoly = P ∧ C.det ≠ 0 ∧ H.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom C * H * C = H := by
  intro E _ _ _ n P hP
  obtain ⟨hmon, hdeg, hsep, hroot⟩ := hP
  subst hdeg
  have hP0 : P ≠ 0 := hmon.ne_zero
  let pb := AdjoinRoot.powerBasis hP0
  let Cm : Matrix (Fin P.natDegree) (Fin P.natDegree) E := Algebra.leftMulMatrix pb.basis pb.gen
  let H : Matrix (Fin P.natDegree) (Fin P.natDegree) E :=
    Matrix.of fun i j => trace (Cm⁻¹ ^ (i : ℕ) * Cm ^ (j : ℕ))
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτc : ∀ x, τ ((IsCMField.complexConj E).toRingEquiv.toRingHom x) = starRingEnd ℂ (τ x) :=
    fun x => IsCMField.complexEmbedding_complexConj E τ x
  have hQsep : (P.map τ).Separable := hsep.map
  have hQcard : (P.map τ).roots.card = P.natDegree := by
    rw [splits_iff_card_roots.1 (IsAlgClosed.splits _), natDegree_map]
  have hs : (P.map τ).roots.toFinset.card = P.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hQsep), hQcard]
  let e : (P.map τ).roots.toFinset ≃ Fin P.natDegree := Fintype.equivFinOfCardEq (by simp [hs])
  let l : Fin P.natDegree → ℂ := fun k => (e.symm k : ℂ)
  have hl : Function.Injective l := Subtype.val_injective.comp e.symm.injective
  have hlr : ∀ k, eval₂ τ (l k) P = 0 := by
    intro k
    have := (e.symm k).2
    rw [Multiset.mem_toFinset, mem_roots hQsep.ne_zero, IsRoot, eval_map] at this
    exact this
  have h1 : ∀ k, ‖l k‖ = 1 := fun k => hroot τ _ (Multiset.mem_toFinset.1 (e.symm k).2)
  have hrep : ∀ k (x : AdjoinRoot P),
      ∑ i : Fin pb.dim, l k ^ (i : ℕ) * τ (pb.basis.repr x i) = AdjoinRoot.lift τ (l k) (hlr k) x := by
    intro k x
    conv_rhs => rw [← pb.basis.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, PowerBasis.coe_basis]
    simp only [pb, AdjoinRoot.powerBasis_gen, map_pow, AdjoinRoot.lift_root, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.lift_of]
    ring
  have hVA : vandermonde l * Cm.map τ = diagonal l * vandermonde l := by
    ext k j
    rw [mul_apply, diagonal_mul, vandermonde_apply]
    show ∑ i : Fin pb.dim, l k ^ (i : ℕ) * τ (Algebra.leftMulMatrix pb.basis pb.gen i j) = l k * l k ^ (j : ℕ)
    have hC : ∀ i : Fin pb.dim, Algebra.leftMulMatrix pb.basis pb.gen i j = pb.basis.repr (pb.gen * pb.basis j) i :=
      fun i => Algebra.leftMulMatrix_eq_repr_mul _ _ _ _
    rw [Finset.sum_congr rfl fun i _ => by rw [hC i], hrep k]
    simp only [pb, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]
    rw [← pow_succ', map_pow, AdjoinRoot.lift_root, pow_succ']
  obtain ⟨hAd, hH, hHd, hpres⟩ := GlobalTheory.GlobHerm.vandermonde_diag_herm (Cm.map τ) l hl h1 hVA
  have hinv : (Cm.map τ)⁻¹ = Cm⁻¹.map τ := by
    apply inv_eq_left_inv
    have hCd : Cm.det ≠ 0 := by
      intro h; apply hAd
      have := RingHom.map_det τ Cm
      rw [h, map_zero] at this
      exact this.symm
    rw [← Matrix.map_mul, nonsing_inv_mul Cm (isUnit_iff_ne_zero.2 hCd), Matrix.map_one _ (map_zero τ) (map_one τ)]
  have hHm : H.map τ = (vandermonde l)ᴴ * vandermonde l := by
    rw [← hH]
    ext i j
    simp only [map_apply, of_apply, H]
    rw [AddMonoidHom.map_trace τ, hinv]
    congr 1
    change τ.mapMatrix _ = _
    rw [map_mul, map_pow, map_pow]
    rfl
  have hinj : Function.Injective (fun M : Matrix (Fin P.natDegree) (Fin P.natDegree) E => M.map τ) :=
    Matrix.map_injective τ.injective
  have hcT : ∀ M : Matrix (Fin P.natDegree) (Fin P.natDegree) E,
      (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map τ = (M.map τ)ᴴ := by
    intro M; ext i j
    simp only [cT, map_apply, transpose_apply, conjTranspose_apply, hτc]
    rfl
  refine ⟨Cm, H, ?_, ?_, ?_, ?_, ?_⟩
  · refine (charpoly_leftMulMatrix pb).trans ?_
    rw [AdjoinRoot.powerBasis_gen, AdjoinRoot.minpoly_root hP0, hmon.leadingCoeff, inv_one,
      Polynomial.C_1, mul_one]
  · intro h; apply hAd
    have := RingHom.map_det τ Cm
    rw [h, map_zero] at this
    exact this.symm
  · intro h; apply hHd
    have := RingHom.map_det τ H
    rw [h, map_zero] at this
    rw [← hHm]; exact this.symm
  · apply hinj
    simp only
    rw [hcT, hHm, conjTranspose_mul, conjTranspose_conjTranspose]
  · apply hinj
    simp only
    rw [Matrix.map_mul, Matrix.map_mul, hcT, hHm, hpres]
end GlobalTheory.GlobHerm
