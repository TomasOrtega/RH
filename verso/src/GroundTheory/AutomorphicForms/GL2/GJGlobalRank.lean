import Mathlib

open Matrix

namespace GroundTheory.Automorphic

namespace GJGlobal

variable {K : Type*} [Field K] {n : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]`. Establish `hs : Function.Surjective ξ.mulVecLin`. Rewrite using `[← LinearMap.range_eq_top]`.

Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[Module.finrank_fin_fun]`. Conclude with `h`. Conclude with `LinearMap.injective_iff_surjective.2 hs`. Introduce `h`.

Use `rank_of_isUnit ξ ((isUnit_iff_isUnit_det ξ).2 h)` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`. Then use the resulting hypothesis.
-/
theorem rank_eq_iff_isUnit_det (ξ : Matrix (Fin n) (Fin n) K) : ξ.rank = n ↔ IsUnit ξ.det := by
  constructor
  · intro h
    rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
    have hs : Function.Surjective ξ.mulVecLin := by
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      exact h
    exact LinearMap.injective_iff_surjective.2 hs
  · intro h
    have := rank_of_isUnit ξ ((isUnit_iff_isUnit_det ξ).2 h)
    rwa [Fintype.card_fin] at this

/- English proof (translation)
Establish `hle : ξ.rank ≤ n`. Use `rank_le_card_width ξ` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`. Then use the resulting hypothesis. Use `lt_of_le_of_ne hle fun he => ?_` and prove the remaining obligations. Use `(rank_eq_iff_isUnit_det ξ).1 he` as an intermediate fact.

Rewrite `this` using `[h]`. Conclude with `not_isUnit_zero this`.
-/
theorem rank_lt_of_det_eq_zero {ξ : Matrix (Fin n) (Fin n) K} (h : ξ.det = 0) : ξ.rank < n := by
  have hle : ξ.rank ≤ n := by
    have := rank_le_card_width ξ
    rwa [Fintype.card_fin] at this
  refine lt_of_le_of_ne hle fun he => ?_
  have := (rank_eq_iff_isUnit_det ξ).1 he
  rw [h] at this
  exact not_isUnit_zero this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hr : LinearMap.range ξ.mulVecLin = ⊥` using `Submodule.finrank_eq_zero.1 h`. Establish `hz : ξ.mulVecLin = 0` using `LinearMap.range_eq_bot.1 hr`. Use extensionality with `i j`.

Use `congrFun (congrArg DFunLike.coe hz) (Pi.single j 1)` as an intermediate fact. Simplify `congrFun this i` using `[mulVecLin_apply, mulVec_single_one]`. Introduce and unpack `rfl`. Conclude with `rank_zero`.
-/
theorem rank_eq_zero_iff {ξ : Matrix (Fin n) (Fin n) K} : ξ.rank = 0 ↔ ξ = 0 := by
  constructor
  · intro h
    have hr : LinearMap.range ξ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h
    have hz : ξ.mulVecLin = 0 := LinearMap.range_eq_bot.1 hr
    ext i j
    have := congrFun (congrArg DFunLike.coe hz) (Pi.single j 1)
    simpa [mulVecLin_apply, mulVec_single_one] using congrFun this i
  · rintro rfl
    exact rank_zero

noncomputable def unitsEquiv : GL (Fin n) K ≃ {ξ : Matrix (Fin n) (Fin n) K // IsUnit ξ.det} where
  toFun γ := ⟨γ, (isUnit_iff_isUnit_det _).1 γ.isUnit⟩
  invFun ξ := ((isUnit_iff_isUnit_det _).2 ξ.2).unit
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext rfl

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/- English proof (translation)
Rewrite using `[← hf.tsum_subtype_add_tsum_subtype_compl {ξ | IsUnit ξ.det}]`. Use `congr 1`. Conclude with `((unitsEquiv (K := K) (n := n)).tsum_eq (fun ξ => f ξ)).symm`. Establish `e : ({ξ | IsUnit ξ.det}ᶜ : Set (Matrix (Fin n) (Fin n) K)) = {ξ | ξ.det = 0}`. Use extensionality with `ξ`.

Simplify using `[isUnit_iff_ne_zero]`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem tsum_eq_tsum_GL_add {f : Matrix (Fin n) (Fin n) K → E} (hf : Summable f) :
    ∑' ξ, f ξ = ∑' γ : GL (Fin n) K, f γ + ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0}, f ξ := by
  rw [← hf.tsum_subtype_add_tsum_subtype_compl {ξ | IsUnit ξ.det}]
  congr 1
  · exact ((unitsEquiv (K := K) (n := n)).tsum_eq (fun ξ => f ξ)).symm
  · have e : ({ξ | IsUnit ξ.det}ᶜ : Set (Matrix (Fin n) (Fin n) K)) = {ξ | ξ.det = 0} := by
      ext ξ
      simp [isUnit_iff_ne_zero]
    rw [e]
    rfl

/- English proof (translation)
Establish `e : {ξ : Matrix (Fin n) (Fin n) K | ξ.det = 0} = ⋃ r ∈ (Finset.univ : Finset (Fin n)), {ξ | ξ.rank = (r : ℕ)}`. Use extensionality with `ξ`. Simplify using `only [Set.mem_ofPred_eq, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨⟨ξ.rank, rank_lt_of_det_eq_zero h⟩, rfl⟩`. Introduce and unpack `⟨r, hr⟩`. Assume the negation of the conclusion as `h`. Use `(rank_eq_iff_isUnit_det ξ).2 (isUnit_iff_ne_zero.2 h)` as an intermediate fact. Establish `hr'` using `r.2`.

Use linear arithmetic over natural numbers and integers. Establish `hd : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise (Function.onFun Disjoint fun r : Fin n => {ξ : Matrix (Fin n) (Fin n) K | ξ.rank = (r : ℕ)})`. Introduce `r _ r' _ hrr'`. Use `Set.disjoint_left.2 fun ξ h h' => hrr' (Fin.ext ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq] at h h'`.

Rewrite using `[← h, ← h']`. Establish `hsum` using `hasSum_sum_disjoint (f := f) Finset.univ hd fun r _ => (hf.subtype _).hasSum`. Use `show ∑' ξ : ({ξ | ξ.det = 0} : Set (Matrix (Fin n) (Fin n) K)), f ξ = _`. Rewrite using `[e]`. Conclude with `hsum.tsum_eq`.
-/
theorem tsum_det_eq_zero_eq_sum_rank {f : Matrix (Fin n) (Fin n) K → E} (hf : Summable f) :
    ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0}, f ξ =
      ∑ r : Fin n, ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r}, f ξ := by
  have e : {ξ : Matrix (Fin n) (Fin n) K | ξ.det = 0} =
      ⋃ r ∈ (Finset.univ : Finset (Fin n)), {ξ | ξ.rank = (r : ℕ)} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨⟨ξ.rank, rank_lt_of_det_eq_zero h⟩, rfl⟩
    · rintro ⟨r, hr⟩
      by_contra h
      have := (rank_eq_iff_isUnit_det ξ).2 (isUnit_iff_ne_zero.2 h)
      have hr' := r.2
      omega
  have hd : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      (Function.onFun Disjoint fun r : Fin n => {ξ : Matrix (Fin n) (Fin n) K | ξ.rank = (r : ℕ)}) := by
    intro r _ r' _ hrr'
    refine Set.disjoint_left.2 fun ξ h h' => hrr' (Fin.ext ?_)
    simp only [Set.mem_ofPred_eq] at h h'
    rw [← h, ← h']
  have hsum := hasSum_sum_disjoint (f := f) Finset.univ hd fun r _ => (hf.subtype _).hasSum
  show ∑' ξ : ({ξ | ξ.det = 0} : Set (Matrix (Fin n) (Fin n) K)), f ξ = _
  rw [e]
  exact hsum.tsum_eq

end GJGlobal

end GroundTheory.Automorphic
