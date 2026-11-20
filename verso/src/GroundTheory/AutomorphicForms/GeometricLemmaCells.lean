import Mathlib
import GroundTheory.AutomorphicForms.FiniteBruhat
import GroundTheory.AutomorphicForms.InductionParabolicGroups
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa Topology Set DoubleCoset

section Rank

variable {K : Type*} [Field K] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m]

/- English proof (translation)
Use `set f := A.mulVecLin with hf`. Establish `hr : Module.finrank K (LinearMap.range f) = A.rank` using `rfl`. Set `b : Module.Basis (Fin A.rank) K (LinearMap.range f)` to `Module.finBasisOfFinrankEq K _ hr`. Establish `hx : ∀ i, ∃ x, f x = (b i : m → K)` using `fun i => LinearMap.mem_range.1 (b i).2`. Use `choose x hx using hx`.

Set `R : Matrix l (Fin A.rank) K` to `Matrix.of fun j i => x i j`. Establish `hRc : ∀ c : Fin A.rank → K, R *ᵥ c = ∑ i, c i • x i`. Introduce `c`. Use extensionality with `j`. Simplify using `[R, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.

Establish `hAR : ∀ c : Fin A.rank → K, (A * R) *ᵥ c = ∑ i, c i • (b i : m → K)`. Introduce `c`. Rewrite using `[← Matrix.mulVec_mulVec, hRc]`. Establish `: A *ᵥ (∑ i, c i • x i) = f (∑ i, c i • x i)` using `rfl`. Rewrite using `[this, map_sum]`.

Simplify using `only [map_smul, hx]`. Establish `hli : LinearIndependent K (fun i => (b i : m → K))` using `b.linearIndependent.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)`. Establish `hker : LinearMap.ker (A * R).mulVecLin = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `c hc`.

Establish `h1 : ∑ i, c i • (b i : m → K) = 0`. Rewrite using `[← hAR]`. Conclude with `hc`. Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.1 hli c h1 i`.

Take `⟨h, hh⟩` from `LinearMap.exists_leftInverse_of_injective _ hker`. Use `⟨LinearMap.toMatrix' h, R, ?_⟩` and prove the remaining obligations. Establish `h2 : LinearMap.toMatrix' (h.comp (A * R).mulVecLin) = 1`. Rewrite using `[hh, LinearMap.toMatrix'_id]`. Rewrite `h2` using `[LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']`.

Rewrite using `[Matrix.mul_assoc]`. Conclude with `h2`.
-/
theorem exists_mul_mul_eq_one_of_rank (A : Matrix m l K) :
    ∃ (L : Matrix (Fin A.rank) m K) (R : Matrix l (Fin A.rank) K), L * A * R = 1 := by
  classical
  set f := A.mulVecLin with hf
  have hr : Module.finrank K (LinearMap.range f) = A.rank := rfl
  let b : Module.Basis (Fin A.rank) K (LinearMap.range f) := Module.finBasisOfFinrankEq K _ hr
  have hx : ∀ i, ∃ x, f x = (b i : m → K) := fun i => LinearMap.mem_range.1 (b i).2
  choose x hx using hx
  let R : Matrix l (Fin A.rank) K := Matrix.of fun j i => x i j
  have hRc : ∀ c : Fin A.rank → K, R *ᵥ c = ∑ i, c i • x i := by
    intro c
    ext j
    simp [R, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hAR : ∀ c : Fin A.rank → K, (A * R) *ᵥ c = ∑ i, c i • (b i : m → K) := by
    intro c
    rw [← Matrix.mulVec_mulVec, hRc]
    have : A *ᵥ (∑ i, c i • x i) = f (∑ i, c i • x i) := rfl
    rw [this, map_sum]
    simp only [map_smul, hx]
  have hli : LinearIndependent K (fun i => (b i : m → K)) :=
    b.linearIndependent.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)
  have hker : LinearMap.ker (A * R).mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have h1 : ∑ i, c i • (b i : m → K) = 0 := by
      rw [← hAR]
      exact hc
    funext i
    exact Fintype.linearIndependent_iff.1 hli c h1 i
  obtain ⟨h, hh⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' h, R, ?_⟩
  have h2 : LinearMap.toMatrix' (h.comp (A * R).mulVecLin) = 1 := by
    rw [hh, LinearMap.toMatrix'_id]
  rw [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h2
  rw [Matrix.mul_assoc]
  exact h2

variable [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]

/- English proof (translation)
Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `A₀ hA₀`. Take `⟨L, R, hLR⟩` from `exists_mul_mul_eq_one_of_rank A₀`. Use `⟨{A | (L * A * R).det ≠ 0}, fun A hA => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (L * A * R)` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hA)`.

Establish `h1 : (L * A * R).rank = A₀.rank`. Rewrite using `[Matrix.rank_of_isUnit _ hu, Fintype.card_fin]`. Establish `h2 : (L * A * R).rank ≤ A.rank` using `(Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)`. Conclude with `le_trans hA₀ (h1 ▸ h2)`. Establish `hc : Continuous fun A : Matrix m l K => (L * A * R).det` using `((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det`.

Conclude with `isOpen_compl_singleton.preimage hc`. Use `show (L * A₀ * R).det ≠ 0`. Rewrite using `[hLR, Matrix.det_one]`. Conclude with `one_ne_zero`.
-/
theorem isOpen_setOf_le_rank (k : ℕ) : IsOpen {A : Matrix m l K | k ≤ A.rank} := by
  classical
  rw [isOpen_iff_forall_mem_open]
  intro A₀ hA₀
  obtain ⟨L, R, hLR⟩ := exists_mul_mul_eq_one_of_rank A₀
  refine ⟨{A | (L * A * R).det ≠ 0}, fun A hA => ?_, ?_, ?_⟩
  · have hu : IsUnit (L * A * R) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hA)
    have h1 : (L * A * R).rank = A₀.rank := by
      rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin]
    have h2 : (L * A * R).rank ≤ A.rank :=
      (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    exact le_trans hA₀ (h1 ▸ h2)
  · have hc : Continuous fun A : Matrix m l K => (L * A * R).det :=
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det
    exact isOpen_compl_singleton.preimage hc
  · show (L * A₀ * R).det ≠ 0
    rw [hLR, Matrix.det_one]
    exact one_ne_zero

end Rank

variable {F : Type*} [Field F] {n : ℕ}

section Invariants

variable (β γ : Fin n → ℕ)

def cellRank (g : GL (Fin n) F) (a b : ℕ) : ℕ :=
  ((g : Matrix (Fin n) (Fin n) F).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n))
    (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n))).rank

variable {β γ}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [submatrix_apply, mul_apply]`. Rewrite using `[← Fintype.sum_subtype_add_sum_subtype (fun k => a ≤ β k)]`. Establish `h0 : ∑ k : {k : Fin n // ¬ a ≤ β k}, (p : Matrix (Fin n) (Fin n) F) i k * M k (c j) = 0` using `Finset.sum_eq_zero fun k _ => by`. Establish `hk : β k < β i` using `lt_of_lt_of_le (not_le.1 k.2) i.2`.

Rewrite using `[hp hk, zero_mul]`. Rewrite using `[h0, add_zero]`.
-/
theorem submatrix_mul_of_mem_blockUpper {p : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (M : Matrix (Fin n) (Fin n) F) {ι : Type*} (c : ι → Fin n) (a : ℕ) :
    ((p : Matrix (Fin n) (Fin n) F) * M).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) c =
      (p : Matrix (Fin n) (Fin n) F).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n))
          (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) *
        M.submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) c := by
  ext i j
  simp only [submatrix_apply, mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => a ≤ β k)]
  have h0 : ∑ k : {k : Fin n // ¬ a ≤ β k}, (p : Matrix (Fin n) (Fin n) F) i k * M k (c j) = 0 :=
    Finset.sum_eq_zero fun k _ => by
      have hk : β k < β i := lt_of_lt_of_le (not_le.1 k.2) i.2
      rw [hp hk, zero_mul]
  rw [h0, add_zero]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [submatrix_apply, mul_apply]`. Rewrite using `[← Fintype.sum_subtype_add_sum_subtype (fun k => γ k ≤ b)]`. Establish `h0 : ∑ k : {k : Fin n // ¬ γ k ≤ b}, M (r i) k * (q : Matrix (Fin n) (Fin n) F) k j = 0` using `Finset.sum_eq_zero fun k _ => by`. Establish `hk : γ j < γ k` using `lt_of_le_of_lt j.2 (not_le.1 k.2)`.

Rewrite using `[hq hk, mul_zero]`. Rewrite using `[h0, add_zero]`.
-/
theorem mul_submatrix_of_mem_blockUpper {q : GL (Fin n) F} (hq : q ∈ blockUpper F n γ)
    (M : Matrix (Fin n) (Fin n) F) {ι : Type*} (r : ι → Fin n) (b : ℕ) :
    (M * (q : Matrix (Fin n) (Fin n) F)).submatrix r (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)) =
      M.submatrix r (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)) *
        (q : Matrix (Fin n) (Fin n) F).submatrix (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n))
          (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)) := by
  ext i j
  simp only [submatrix_apply, mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => γ k ≤ b)]
  have h0 : ∑ k : {k : Fin n // ¬ γ k ≤ b}, M (r i) k * (q : Matrix (Fin n) (Fin n) F) k j = 0 :=
    Finset.sum_eq_zero fun k _ => by
      have hk : γ j < γ k := lt_of_le_of_lt j.2 (not_le.1 k.2)
      rw [hq hk, mul_zero]
  rw [h0, add_zero]

/- English proof (translation)
Apply `Matrix.isUnit_det_of_right_inverse (B := ((p⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)))` to reduce the goal to its premises. Rewrite using `[← submatrix_mul_of_mem_blockUpper hp, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Conclude with `Matrix.submatrix_one _ Subtype.val_injective`.
-/
theorem isUnit_det_submatrix_of_mem_blockUpper {p : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (a : ℕ) :
    IsUnit ((p : Matrix (Fin n) (Fin n) F).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n))
      (fun i : {i : Fin n // a ≤ β i} => (i : Fin n))).det := by
  classical
  apply Matrix.isUnit_det_of_right_inverse (B := ((p⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix
    (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)))
  rw [← submatrix_mul_of_mem_blockUpper hp, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Matrix.submatrix_one _ Subtype.val_injective

/- English proof (translation)
Apply `Matrix.isUnit_det_of_left_inverse (B := ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)) (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)))` to reduce the goal to its premises. Rewrite using `[← mul_submatrix_of_mem_blockUpper hq, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Conclude with `Matrix.submatrix_one _ Subtype.val_injective`.
-/
theorem isUnit_det_submatrix_of_mem_blockUpper' {q : GL (Fin n) F} (hq : q ∈ blockUpper F n γ)
    (b : ℕ) :
    IsUnit ((q : Matrix (Fin n) (Fin n) F).submatrix (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n))
      (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n))).det := by
  classical
  apply Matrix.isUnit_det_of_left_inverse (B := ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix
    (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)) (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)))
  rw [← mul_submatrix_of_mem_blockUpper hq, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact Matrix.submatrix_one _ Subtype.val_injective

/- English proof (translation)
Unfold `cellRank`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.mul_assoc, submatrix_mul_of_mem_blockUpper hp, mul_submatrix_of_mem_blockUpper hq, Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_submatrix_of_mem_blockUpper hp a), Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_submatrix_of_me …`.
-/
theorem cellRank_mul_mul {p q : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (hq : q ∈ blockUpper F n γ) (g : GL (Fin n) F) (a b : ℕ) :
    cellRank β γ (p * g * q) a b = cellRank β γ g a b := by
  classical
  unfold cellRank
  rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, submatrix_mul_of_mem_blockUpper hp,
    mul_submatrix_of_mem_blockUpper hq,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_submatrix_of_mem_blockUpper hp a),
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_submatrix_of_mem_blockUpper' hq b)]

/- English proof (translation)
Take `⟨p, hp, q, hq, rfl⟩` from `mem_doubleCoset.1 hx`. Conclude with `cellRank_mul_mul hp hq g a b`.
-/
theorem cellRank_of_mem_doubleCoset {g x : GL (Fin n) F}
    (hx : x ∈ doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) (a b : ℕ) :
    cellRank β γ x a b = cellRank β γ g a b := by
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_doubleCoset.1 hx
  exact cellRank_mul_mul hp hq g a b

end Invariants

section Permutations

variable {β γ : Fin n → ℕ}

/- English proof (translation)
Unfold `cellRank`. Use `set X := ((permGL F w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)) with hX`. Rewrite using `[Matrix.rank_eq_finrank_span_cols]`. Set `v : {j : Fin n // γ j ≤ b ∧ a ≤ β (w j)} → ({i : Fin n // a ≤ β i} → F)` to `fun t => Pi.single ⟨w t, t.2.2⟩ 1`. Establish `hv : LinearIndependent F v`.

Use `(Pi.basisFun F {i : Fin n // a ≤ β i}).linearIndependent.comp (fun t : {j : Fin n // γ j ≤ b ∧ a ≤ β (w j)} => (⟨w t, t.2.2⟩ : {i : Fin n // a ≤ β i})) (fun s t hst => Subtype.ext (w.injective (congrArg Subtype.val hst)))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`. Simplify using `[v, Pi.basisFun_apply]`. Establish `hspan : Submodule.span F (Set.range Xᵀ) = Submodule.span F (Set.range v)`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Distinguish the cases in `h : a ≤ β (w j)`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨⟨j, j.2, h⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [hX, v, transpose_apply, submatrix_apply, permGL_apply, Pi.single_apply, Subtype.ext_iff]`. Establish `h0 : Xᵀ j = 0`. Use function extensionality and compare the values at `i`.

Simplify using `only [hX, transpose_apply, submatrix_apply, permGL_apply, Pi.zero_apply]`. Rewrite using `[if_neg]`. Introduce `hi`. Conclude with `h (hi ▸ i.2)`. Rewrite using `[h0]`.

Conclude with `zero_mem _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨t, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨⟨t, t.2.1⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `only [hX, v, transpose_apply, submatrix_apply, permGL_apply, Pi.single_apply, Subtype.ext_iff]`. Rewrite using `[show Set.range X.col = Set.range Xᵀ from rfl, hspan, finrank_span_eq_card hv, Fintype.card_subtype]`.
-/
theorem cellRank_permGL (w : Equiv.Perm (Fin n)) (a b : ℕ) :
    cellRank β γ (permGL F w) a b = (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card := by
  classical
  unfold cellRank
  set X := ((permGL F w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix
    (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n))
    with hX
  rw [Matrix.rank_eq_finrank_span_cols]
  let v : {j : Fin n // γ j ≤ b ∧ a ≤ β (w j)} → ({i : Fin n // a ≤ β i} → F) :=
    fun t => Pi.single ⟨w t, t.2.2⟩ 1
  have hv : LinearIndependent F v := by
    have := (Pi.basisFun F {i : Fin n // a ≤ β i}).linearIndependent.comp
      (fun t : {j : Fin n // γ j ≤ b ∧ a ≤ β (w j)} => (⟨w t, t.2.2⟩ : {i : Fin n // a ≤ β i}))
      (fun s t hst => Subtype.ext (w.injective (congrArg Subtype.val hst)))
    convert this using 1
    funext t
    simp [v, Pi.basisFun_apply]
  have hspan : Submodule.span F (Set.range Xᵀ) = Submodule.span F (Set.range v) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      by_cases h : a ≤ β (w j)
      · apply Submodule.subset_span
        refine ⟨⟨j, j.2, h⟩, ?_⟩
        funext i
        simp only [hX, v, transpose_apply, submatrix_apply, permGL_apply, Pi.single_apply,
          Subtype.ext_iff]
      · have h0 : Xᵀ j = 0 := by
          funext i
          simp only [hX, transpose_apply, submatrix_apply, permGL_apply, Pi.zero_apply]
          rw [if_neg]
          intro hi
          exact h (hi ▸ i.2)
        rw [h0]
        exact zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      apply Submodule.subset_span
      refine ⟨⟨t, t.2.1⟩, ?_⟩
      funext i
      simp only [hX, v, transpose_apply, submatrix_apply, permGL_apply, Pi.single_apply,
        Subtype.ext_iff]
  rw [show Set.range X.col = Set.range Xᵀ from rfl, hspan, finrank_span_eq_card hv,
    Fintype.card_subtype]

/- English proof (translation)
Introduce `i j hij`. Use `show ((permGL F u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0`. Rewrite using `[permGL_apply, if_neg]`. Introduce and unpack `rfl`. Rewrite `hij` using `[hu]`.

Conclude with `lt_irrefl _ hij`.
-/
theorem permGL_mem_blockUpper {u : Equiv.Perm (Fin n)} (hu : ∀ x, β (u x) = β x) :
    permGL F u ∈ blockUpper F n β := by
  intro i j hij
  show ((permGL F u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0
  rw [permGL_apply, if_neg]
  rintro rfl
  rw [hu] at hij
  exact lt_irrefl _ hij

/- English proof (translation)
Establish `h1 : ∀ a b, (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w j)).card = (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w' j)).card`. Introduce `a b`. Consider the cases of `b with`. Consider the case `zero => simpa using h a 0`. Consider the case `succ b`.

Establish `key : ∀ u : Equiv.Perm (Fin n), (Finset.univ.filter fun j => γ j ≤ b + 1 ∧ a ≤ β (u j)).card = (Finset.univ.filter fun j => γ j = b + 1 ∧ a ≤ β (u j)).card + (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (u j)).card`. Introduce `u`. Rewrite using `[← Finset.card_union_of_disjoint]`. Use `congr 1`. Use extensionality with `j`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.disjoint_filter]`. Introduce `j _ h1 h2`. Use linear arithmetic over natural numbers and integers.

Use `h a (b + 1)` as an intermediate fact. Rewrite `this` using `[key w, key w', h a b]`. Use linear arithmetic over natural numbers and integers. Establish `h2 : ∀ a b, (Finset.univ.filter fun j => γ j = b ∧ β (w j) = a).card = (Finset.univ.filter fun j => γ j = b ∧ β (w' j) = a).card`. Introduce `a b`.

Establish `key : ∀ u : Equiv.Perm (Fin n), (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (u j)).card = (Finset.univ.filter fun j => γ j = b ∧ β (u j) = a).card + (Finset.univ.filter fun j => γ j = b ∧ a + 1 ≤ β (u j)).card`. Introduce `u`. Rewrite using `[← Finset.card_union_of_disjoint]`. Use `congr 1`. Use extensionality with `j`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.disjoint_filter]`. Introduce `j _ h1 h2`. Use linear arithmetic over natural numbers and integers.

Use `h1 a b` as an intermediate fact. Rewrite `this` using `[key w, key w', h1 (a + 1) b]`. Use linear arithmetic over natural numbers and integers. Establish `hcard : ∀ c : ℕ × ℕ, Fintype.card {j : Fin n // (β (w j), γ j) = c} = Fintype.card {j : Fin n // (β (w' j), γ j) = c}`. Introduce `c`.

Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`. Establish `e1 : (Finset.univ.filter fun j => (β (w j), γ j) = c) = Finset.univ.filter fun j => γ j = c.2 ∧ β (w j) = c.1`. Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]`. The claim follows by propositional logic.

Establish `e2 : (Finset.univ.filter fun j => (β (w' j), γ j) = c) = Finset.univ.filter fun j => γ j = c.2 ∧ β (w' j) = c.1`. Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]`. The claim follows by propositional logic. Rewrite using `[e1, e2, h2]`.

Set `v : Fin n ≃ Fin n` to `Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c)`. Establish `hv : ∀ j, (β (w' (v j)), γ (v j)) = (β (w j), γ j)` using `fun j => Equiv.ofFiberEquiv_map (fun c => Fintype.equivOfCardEq (hcard c)) j`. Establish `hvβ : ∀ j, β (w' (v j)) = β (w j)` using `fun j => (Prod.ext_iff.1 (hv j)).1`. Establish `hvγ : ∀ j, γ (v j) = γ j` using `fun j => (Prod.ext_iff.1 (hv j)).2`. Set `u : Equiv.Perm (Fin n)` to `w' * v * w⁻¹`.

Establish `hu : ∀ x, β (u x) = β x`. Introduce `x`. Simplify using `only [u, Equiv.Perm.mul_apply]`. Rewrite using `[hvβ]`. Simplify using the standard rewrite rules.

Establish `hv' : ∀ x, γ ((v⁻¹ : Equiv.Perm (Fin n)) x) = γ x`. Introduce `x`. Use `hvγ ((v⁻¹ : Equiv.Perm (Fin n)) x)` as an intermediate fact. Establish `h' : v ((v⁻¹ : Equiv.Perm (Fin n)) x) = x` using `Equiv.apply_symm_apply v x`. Rewrite `this` using `[h']`.

Conclude with `this.symm`. Use `mem_doubleCoset.2 ⟨permGL F u, permGL_mem_blockUpper hu, permGL F v⁻¹, permGL_mem_blockUpper hv', ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Simplify using `only [u]`.

Use `group`.
-/
theorem permGL_mem_doubleCoset_of_card {w w' : Equiv.Perm (Fin n)}
    (h : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card) :
    permGL F w' ∈ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ) := by
  classical
  have h1 : ∀ a b, (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w' j)).card := by
    intro a b
    cases b with
    | zero => simpa using h a 0
    | succ b =>
      have key : ∀ u : Equiv.Perm (Fin n),
          (Finset.univ.filter fun j => γ j ≤ b + 1 ∧ a ≤ β (u j)).card =
            (Finset.univ.filter fun j => γ j = b + 1 ∧ a ≤ β (u j)).card +
              (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (u j)).card := by
        intro u
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          omega
        · rw [Finset.disjoint_filter]
          intro j _ h1 h2
          omega
      have := h a (b + 1)
      rw [key w, key w', h a b] at this
      omega
  have h2 : ∀ a b, (Finset.univ.filter fun j => γ j = b ∧ β (w j) = a).card =
      (Finset.univ.filter fun j => γ j = b ∧ β (w' j) = a).card := by
    intro a b
    have key : ∀ u : Equiv.Perm (Fin n),
        (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (u j)).card =
          (Finset.univ.filter fun j => γ j = b ∧ β (u j) = a).card +
            (Finset.univ.filter fun j => γ j = b ∧ a + 1 ≤ β (u j)).card := by
      intro u
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        omega
      · rw [Finset.disjoint_filter]
        intro j _ h1 h2
        omega
    have := h1 a b
    rw [key w, key w', h1 (a + 1) b] at this
    omega

  have hcard : ∀ c : ℕ × ℕ, Fintype.card {j : Fin n // (β (w j), γ j) = c} =
      Fintype.card {j : Fin n // (β (w' j), γ j) = c} := by
    intro c
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have e1 : (Finset.univ.filter fun j => (β (w j), γ j) = c) =
        Finset.univ.filter fun j => γ j = c.2 ∧ β (w j) = c.1 := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
      tauto
    have e2 : (Finset.univ.filter fun j => (β (w' j), γ j) = c) =
        Finset.univ.filter fun j => γ j = c.2 ∧ β (w' j) = c.1 := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
      tauto
    rw [e1, e2, h2]
  let v : Fin n ≃ Fin n := Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c)
  have hv : ∀ j, (β (w' (v j)), γ (v j)) = (β (w j), γ j) := fun j =>
    Equiv.ofFiberEquiv_map (fun c => Fintype.equivOfCardEq (hcard c)) j
  have hvβ : ∀ j, β (w' (v j)) = β (w j) := fun j => (Prod.ext_iff.1 (hv j)).1
  have hvγ : ∀ j, γ (v j) = γ j := fun j => (Prod.ext_iff.1 (hv j)).2
  let u : Equiv.Perm (Fin n) := w' * v * w⁻¹
  have hu : ∀ x, β (u x) = β x := by
    intro x
    simp only [u, Equiv.Perm.mul_apply]
    rw [hvβ]
    simp
  have hv' : ∀ x, γ ((v⁻¹ : Equiv.Perm (Fin n)) x) = γ x := by
    intro x
    have := hvγ ((v⁻¹ : Equiv.Perm (Fin n)) x)
    have h' : v ((v⁻¹ : Equiv.Perm (Fin n)) x) = x := Equiv.apply_symm_apply v x
    rw [h'] at this
    exact this.symm
  refine mem_doubleCoset.2 ⟨permGL F u, permGL_mem_blockUpper hu, permGL F v⁻¹,
    permGL_mem_blockUpper hv', ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  simp only [u]
  group

/- English proof (translation)
Establish `key : ∀ r c, ((permGL F s * g * (permGL F s)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r c = (g : Matrix (Fin n) (Fin n) F) (s⁻¹ r) (s⁻¹ c)`. Introduce `r c`. Rewrite using `[← map_inv, Units.val_mul, Units.val_mul, mul_permGL_apply, permGL_mul_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j hij`.

Use `h (i := s i) (j := s j) hij` as an intermediate fact. Rewrite `this` using `[key]`. Simplify using `using this`. Introduce `h r c hrc show ((permGL F s * g * (permGL F s)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r c = 0`. Rewrite using `[key]`.

Apply `h` to reduce the goal to its premises. Simplify using `using hrc`.
-/
theorem conj_permGL_mem_blockUpper_iff {α : Type*} [LinearOrder α] {β : Fin n → α}
    (s : Equiv.Perm (Fin n)) {g : GL (Fin n) F} :
    permGL F s * g * (permGL F s)⁻¹ ∈ blockUpper F n β ↔ g ∈ blockUpper F n (β ∘ s) := by
  have key : ∀ r c, ((permGL F s * g * (permGL F s)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r c =
      (g : Matrix (Fin n) (Fin n) F) (s⁻¹ r) (s⁻¹ c) := by
    intro r c
    rw [← map_inv, Units.val_mul, Units.val_mul, mul_permGL_apply, permGL_mul_apply]
  constructor
  · intro h i j hij
    have := h (i := s i) (j := s j) hij
    rw [key] at this
    simpa using this
  · intro h r c hrc
    show ((permGL F s * g * (permGL F s)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r c = 0
    rw [key]
    apply h
    simpa using hrc

/- English proof (translation)
Use `set s := Tuple.sort β`. Use `set t := Tuple.sort γ`. Establish `hB : ∀ {δ : Fin n → ℕ} {u : Equiv.Perm (Fin n)}, Monotone (δ ∘ u) → ∀ b ∈ GroundTheory.Automorphic.borel n F, b ∈ blockUpper F n (δ ∘ u)`. Introduce `δ u hm b hb i j hij`. Apply `(mem_borel_iff b).1 hb` to reduce the goal to its premises.

Assume the negation of the conclusion as `hle`. Conclude with `absurd (hm (not_lt.1 hle)) (not_le.2 hij)`. Take `⟨w, hw⟩` from `exists_mem_doubleCoset_permGL (k := F) ((permGL F s)⁻¹ * g * permGL F t)`. Take `⟨b₁, hb₁, b₂, hb₂, heq⟩` from `mem_doubleCoset.1 hw`. Use `⟨s * w * t⁻¹, mem_doubleCoset.2 ⟨permGL F s * b₁ * (permGL F s)⁻¹, (conj_permGL_mem_blockUpper_iff s).2 (hB (Tuple.monotone_sort β) b₁ hb₁), permGL F t * b₂ * (permGL F t)⁻¹, (conj_permGL_mem_blockUpper_iff t).2 (hB (Tuple.monotone_sort γ) b₂ hb₂), ?_⟩⟩` and prove the remaining obligations.

Establish `hg : g = permGL F s * ((permGL F s)⁻¹ * g * permGL F t) * (permGL F t)⁻¹` using `by group`. Rewrite using `[hg, heq, map_mul, map_mul, map_inv]`. Use `group`.
-/
theorem exists_permGL_mem_doubleCoset (g : GL (Fin n) F) :
    ∃ w : Equiv.Perm (Fin n), g ∈ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ) := by
  set s := Tuple.sort β
  set t := Tuple.sort γ
  have hB : ∀ {δ : Fin n → ℕ} {u : Equiv.Perm (Fin n)}, Monotone (δ ∘ u) →
      ∀ b ∈ GroundTheory.Automorphic.borel n F, b ∈ blockUpper F n (δ ∘ u) := by
    intro δ u hm b hb i j hij
    apply (mem_borel_iff b).1 hb
    by_contra hle
    exact absurd (hm (not_lt.1 hle)) (not_le.2 hij)
  obtain ⟨w, hw⟩ := exists_mem_doubleCoset_permGL (k := F) ((permGL F s)⁻¹ * g * permGL F t)
  obtain ⟨b₁, hb₁, b₂, hb₂, heq⟩ := mem_doubleCoset.1 hw
  refine ⟨s * w * t⁻¹, mem_doubleCoset.2 ⟨permGL F s * b₁ * (permGL F s)⁻¹,
    (conj_permGL_mem_blockUpper_iff s).2 (hB (Tuple.monotone_sort β) b₁ hb₁),
    permGL F t * b₂ * (permGL F t)⁻¹,
    (conj_permGL_mem_blockUpper_iff t).2 (hB (Tuple.monotone_sort γ) b₂ hb₂), ?_⟩⟩
  have hg : g = permGL F s * ((permGL F s)⁻¹ * g * permGL F t) * (permGL F t)⁻¹ := by group
  rw [hg, heq, map_mul, map_mul, map_inv]
  group

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_permGL_mem_doubleCoset (β := β) (γ := γ) g`. Take `⟨w', hw'⟩` from `exists_permGL_mem_doubleCoset (β := β) (γ := γ) x`. Establish `hcnt : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card = (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card`. Introduce `a b`. Rewrite using `[← cellRank_permGL (F := F), ← cellRank_permGL (F := F), ← cellRank_of_mem_doubleCoset hw, ← cellRank_of_mem_doubleCoset hw', h]`.

Establish `hww'` using `permGL_mem_doubleCoset_of_card (F := F) hcnt`. Rewrite using `[doubleCoset_eq_of_mem hw, ← doubleCoset_eq_of_mem hww']`. Conclude with `hw'`.
-/
theorem mem_doubleCoset_of_cellRank_eq {g x : GL (Fin n) F}
    (h : ∀ a b, cellRank β γ x a b = cellRank β γ g a b) :
    x ∈ doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ) := by
  obtain ⟨w, hw⟩ := exists_permGL_mem_doubleCoset (β := β) (γ := γ) g
  obtain ⟨w', hw'⟩ := exists_permGL_mem_doubleCoset (β := β) (γ := γ) x
  have hcnt : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card := by
    intro a b
    rw [← cellRank_permGL (F := F), ← cellRank_permGL (F := F), ← cellRank_of_mem_doubleCoset hw,
      ← cellRank_of_mem_doubleCoset hw', h]
  have hww' := permGL_mem_doubleCoset_of_card (F := F) hcnt
  rw [doubleCoset_eq_of_mem hw, ← doubleCoset_eq_of_mem hww']
  exact hw'

end Permutations

section Height

variable (β γ : Fin n → ℕ)

def cellHeight (g : GL (Fin n) F) : ℕ :=
  ∑ a ∈ Finset.range (Finset.univ.sup β + 2), ∑ b ∈ Finset.range (Finset.univ.sup γ + 1),
    cellRank β γ g a b

variable {β γ}

/- English proof (translation)
Unfold `cellRank`. Establish `hcard : Fintype.card {i : Fin n // a ≤ β i} = 0`. Rewrite using `[Fintype.card_eq_zero_iff]`. Conclude with `⟨fun i => absurd (lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ i.1)) ha) (not_lt.2 i.2)⟩`. Conclude with `Nat.le_zero.1 (hcard ▸ Matrix.rank_le_card_height _)`.
-/
theorem cellRank_eq_zero_of_lt {a : ℕ} (ha : Finset.univ.sup β < a) (g : GL (Fin n) F) (b : ℕ) :
    cellRank β γ g a b = 0 := by
  unfold cellRank
  have hcard : Fintype.card {i : Fin n // a ≤ β i} = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun i => absurd (lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ i.1)) ha) (not_lt.2 i.2)⟩
  exact Nat.le_zero.1 (hcard ▸ Matrix.rank_le_card_height _)

/- English proof (translation)
Establish `key : ∀ c, Finset.univ.sup γ ≤ c → cellRank β γ g a c = ((g : Matrix (Fin n) (Fin n) F).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) id).rank`. Introduce `c hc`. Establish `hall : ∀ j, γ j ≤ c` using `fun j => (Finset.le_sup (Finset.mem_univ j)).trans hc`. Unfold `cellRank`. Rewrite using `[← Matrix.rank_submatrix _ (Equiv.refl _) (Equiv.subtypeUnivEquiv hall)]`.

Both sides reduce to the same expression. Rewrite using `[key b hb, key _ le_rfl]`.
-/
theorem cellRank_eq_of_le {b : ℕ} (hb : Finset.univ.sup γ ≤ b) (g : GL (Fin n) F) (a : ℕ) :
    cellRank β γ g a b = cellRank β γ g a (Finset.univ.sup γ) := by
  classical
  have key : ∀ c, Finset.univ.sup γ ≤ c → cellRank β γ g a c =
      ((g : Matrix (Fin n) (Fin n) F).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n))
        id).rank := by
    intro c hc
    have hall : ∀ j, γ j ≤ c := fun j => (Finset.le_sup (Finset.mem_univ j)).trans hc
    unfold cellRank
    rw [← Matrix.rank_submatrix _ (Equiv.refl _) (Equiv.subtypeUnivEquiv hall)]
    rfl
  rw [key b hb, key _ le_rfl]

/- English proof (translation)
Break down `le_or_gt a (Finset.univ.sup β + 1) with ha | ha` into its components or cases. Rewrite using `[min_eq_left ha]`. Break down `le_or_gt b (Finset.univ.sup γ) with hb | hb` into its components or cases. Rewrite using `[min_eq_left hb]`. Rewrite using `[min_eq_right hb.le, cellRank_eq_of_le hb.le]`.

Rewrite using `[min_eq_right ha.le, cellRank_eq_zero_of_lt (by omega), cellRank_eq_zero_of_lt (by omega)]`.
-/
theorem cellRank_clip (g : GL (Fin n) F) (a b : ℕ) :
    cellRank β γ g a b =
      cellRank β γ g (min a (Finset.univ.sup β + 1)) (min b (Finset.univ.sup γ)) := by
  rcases le_or_gt a (Finset.univ.sup β + 1) with ha | ha
  · rw [min_eq_left ha]
    rcases le_or_gt b (Finset.univ.sup γ) with hb | hb
    · rw [min_eq_left hb]
    · rw [min_eq_right hb.le, cellRank_eq_of_le hb.le]
  · rw [min_eq_right ha.le, cellRank_eq_zero_of_lt (by omega), cellRank_eq_zero_of_lt (by omega)]

/- English proof (translation)
Establish `hbox : ∀ a ∈ Finset.range (Finset.univ.sup β + 2), ∀ b ∈ Finset.range (Finset.univ.sup γ + 1), cellRank β γ x a b = cellRank β γ g a b`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨a, ha, b, hb, hne⟩` from `hne`. Establish `: cellHeight β γ x < cellHeight β γ g` using `Finset.sum_lt_sum (fun a _ => Finset.sum_le_sum fun b _ => h a b) ⟨a, ha, Finset.sum_lt_sum (fun b _ => h a b) ⟨b, hb, lt_of_le_of_ne (h a b) hne⟩⟩`.

Use linear arithmetic over natural numbers and integers. Introduce `a b`. Rewrite using `[cellRank_clip x, cellRank_clip g]`. Apply the tactic sequence `apply hbox <;> rw [Finset.mem_range] <;> omega`.
-/
theorem cellRank_eq_of_le_of_cellHeight_le {g x : GL (Fin n) F}
    (h : ∀ a b, cellRank β γ x a b ≤ cellRank β γ g a b)
    (hh : cellHeight β γ g ≤ cellHeight β γ x) : ∀ a b, cellRank β γ x a b = cellRank β γ g a b := by
  have hbox : ∀ a ∈ Finset.range (Finset.univ.sup β + 2),
      ∀ b ∈ Finset.range (Finset.univ.sup γ + 1), cellRank β γ x a b = cellRank β γ g a b := by
    by_contra hne
    push Not at hne
    obtain ⟨a, ha, b, hb, hne⟩ := hne
    have : cellHeight β γ x < cellHeight β γ g :=
      Finset.sum_lt_sum (fun a _ => Finset.sum_le_sum fun b _ => h a b)
        ⟨a, ha, Finset.sum_lt_sum (fun b _ => h a b) ⟨b, hb, lt_of_le_of_ne (h a b) hne⟩⟩
    omega
  intro a b
  rw [cellRank_clip x, cellRank_clip g]
  apply hbox <;> rw [Finset.mem_range] <;> omega

variable [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]

/- English proof (translation)
The claim follows from `(isOpen_setOf_le_rank k).preimage (Units.continuous_val.matrix_submatrix _ _)`.
-/
theorem isOpen_setOf_le_cellRank (a b k : ℕ) :
    IsOpen {x : GL (Fin n) F | k ≤ cellRank β γ x a b} :=
  (isOpen_setOf_le_rank k).preimage (Units.continuous_val.matrix_submatrix _ _)

/- English proof (translation)
Use `set Z := {x : GL (Fin n) F | ∀ a b, cellRank β γ x a b ≤ cellRank β γ g a b}`. Establish `hZ : IsClosed Z`. Establish `: Z = ⋂ a, ⋂ b, {x : GL (Fin n) F | cellRank β γ g a b + 1 ≤ cellRank β γ x a b}ᶜ`. Use extensionality with `x`. Simplify using `only [Z, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, not_le, Nat.lt_succ_iff]`.

Rewrite using `[this]`. Conclude with `isClosed_iInter fun a => isClosed_iInter fun b => (isOpen_setOf_le_cellRank a b _).isClosed_compl`. Establish `hsub : doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ) ⊆ Z` using `fun x hx a b => (cellRank_of_mem_doubleCoset hx a b).le`. Introduce `x hx`. Establish `hxZ : x ∈ Z` using `closure_minimal hsub hZ hx`.

Distinguish the cases in `hlt : cellHeight β γ x < cellHeight β γ g`. Conclude with `Or.inr hlt`. Conclude with `Or.inl (mem_doubleCoset_of_cellRank_eq (cellRank_eq_of_le_of_cellHeight_le hxZ (not_lt.1 hlt)))`.
-/
theorem closure_doubleCoset_subset (g : GL (Fin n) F) :
    closure (doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ⊆
      doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ) ∪
        {x | cellHeight β γ x < cellHeight β γ g} := by
  set Z := {x : GL (Fin n) F | ∀ a b, cellRank β γ x a b ≤ cellRank β γ g a b}
  have hZ : IsClosed Z := by
    have : Z = ⋂ a, ⋂ b, {x : GL (Fin n) F | cellRank β γ g a b + 1 ≤ cellRank β γ x a b}ᶜ := by
      ext x
      simp only [Z, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, not_le, Nat.lt_succ_iff]
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      (isOpen_setOf_le_cellRank a b _).isClosed_compl
  have hsub : doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ) ⊆ Z :=
    fun x hx a b => (cellRank_of_mem_doubleCoset hx a b).le
  intro x hx
  have hxZ : x ∈ Z := closure_minimal hsub hZ hx
  by_cases hlt : cellHeight β γ x < cellHeight β γ g
  · exact Or.inr hlt
  · exact Or.inl (mem_doubleCoset_of_cellRank_eq
      (cellRank_eq_of_le_of_cellHeight_le hxZ (not_lt.1 hlt)))

omit [TopologicalSpace F] [IsTopologicalRing F] [T1Space F] in

/- English proof (translation)
Unfold `cellHeight`. Simplify using `only [cellRank_of_mem_doubleCoset hx]`.
-/
theorem cellHeight_of_mem_doubleCoset {g x : GL (Fin n) F}
    (hx : x ∈ doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) :
    cellHeight β γ x = cellHeight β γ g := by
  unfold cellHeight
  simp only [cellRank_of_mem_doubleCoset hx]

end Height

end Parabolic

end GroundTheory.Automorphic
