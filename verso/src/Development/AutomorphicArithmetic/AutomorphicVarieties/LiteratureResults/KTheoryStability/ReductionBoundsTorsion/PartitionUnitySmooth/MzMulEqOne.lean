import Mathlib

open Matrix Module

noncomputable section

namespace PositivityTheory.KB.SmoothPartitionUnityBasic.TZ

abbrev cz {ι : Type*} (c : ι → ℤ) : ι → ℝ := fun i => (c i : ℝ)

abbrev mz {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℤ) : Matrix ι ι ℝ :=
  (Int.castRingHom ℝ).mapMatrix U

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mz_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℤ) (i j : ι) :
    mz U i j = (U i j : ℝ) := rfl

def Dual {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) (δ : ℝ) : Prop :=
  ∀ c : ι → ℤ, c ≠ 0 → δ ≤ cz c ⬝ᵥ (G⁻¹ *ᵥ cz c)

def Cov {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (R : ℝ) : Prop :=
  ∀ p : ι → ℝ, ∃ c : ι → ℤ, (p - cz c) ⬝ᵥ (G *ᵥ (p - cz c)) ≤ R

section Uni

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[cz, mz_apply, mulVec, dotProduct]`.
-/
theorem cz_mulVec (U : Matrix ι ι ℤ) (c : ι → ℤ) : cz (U *ᵥ c) = mz U *ᵥ cz c := by
  funext i
  simp [cz, mz_apply, mulVec, dotProduct]

/- English proof (translation)
Establish `h'` using `congrArg (Int.castRingHom ℝ).mapMatrix h`. Rewrite `h'` using `[map_mul, map_one]`. Then use the resulting hypothesis.
-/
theorem mz_mul_eq_one {U V : Matrix ι ι ℤ} (h : U * V = 1) : mz U * mz V = 1 := by
  have h' := congrArg (Int.castRingHom ℝ).mapMatrix h
  rwa [map_mul, map_one] at h'

/- English proof (translation)
Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec y (mz U)ᵀ, vecMul_transpose]`.
-/
theorem quad_mz (U : Matrix ι ι ℤ) (G : Matrix ι ι ℝ) (y : ι → ℝ) :
    (mz U *ᵥ y) ⬝ᵥ (G *ᵥ (mz U *ᵥ y)) = y ⬝ᵥ (((mz U)ᵀ * G * mz U) *ᵥ y) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec y (mz U)ᵀ, vecMul_transpose]

/- English proof (translation)
Establish `hVUr` using `mz_mul_eq_one hVU`. Establish `hinj : Function.Injective (mz U).mulVec`. Introduce `x y hxy`. Establish `h1 : mz V *ᵥ (mz U *ᵥ x) = mz V *ᵥ (mz U *ᵥ y)` using `by rw [hxy]`. Rewrite `h1` using `[mulVec_mulVec, mulVec_mulVec, hVUr, one_mulVec, one_mulVec]`. Then use the resulting hypothesis.

Use `hG.conjTranspose_mul_mul_same hinj` as an intermediate fact. Rewrite `this` using `[conjTranspose_eq_transpose_of_trivial]`. Then use the resulting hypothesis.
-/
theorem uni_pd (U V : Matrix ι ι ℤ) (hVU : V * U = 1) (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    ((mz U)ᵀ * G * mz U).PosDef := by
  have hVUr := mz_mul_eq_one hVU
  have hinj : Function.Injective (mz U).mulVec := by
    intro x y hxy
    have h1 : mz V *ᵥ (mz U *ᵥ x) = mz V *ᵥ (mz U *ᵥ y) := by rw [hxy]
    rwa [mulVec_mulVec, mulVec_mulVec, hVUr, one_mulVec, one_mulVec] at h1
  have := hG.conjTranspose_mul_mul_same hinj
  rwa [conjTranspose_eq_transpose_of_trivial] at this

/- English proof (translation)
Establish `hUVr` using `mz_mul_eq_one hUV`. Establish `hVUr` using `mz_mul_eq_one hVU`. Establish `hu : IsUnit G.det` using `isUnit_iff_ne_zero.mpr hG.det_pos.ne'`. Establish `hinv : ((mz U)ᵀ * G * mz U)⁻¹ = mz V * G⁻¹ * (mz V)ᵀ`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises.

Establish `hT : (mz V)ᵀ * (mz U)ᵀ = 1` using `by rw [← transpose_mul, hUVr, transpose_one]`. Combine the equalities or inequalities in the displayed calculation. Introduce `c hc`. Rewrite using `[hinv, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (cz c) (mz V), ← mulVec_transpose]`. Establish `e : (mz V)ᵀ *ᵥ cz c = cz (Vᵀ *ᵥ c)`.

Use function extensionality and compare the values at `i`. Simplify using `[cz, mz_apply, mulVec, dotProduct, transpose_apply]`. Rewrite using `[e]`. Apply `hD` to reduce the goal to its premises. Introduce `h0`.

Apply `hc` to reduce the goal to its premises. Establish `h1 : Uᵀ *ᵥ (Vᵀ *ᵥ c) = Uᵀ *ᵥ 0` using `by rw [h0]`. Rewrite `h1` using `[mulVec_mulVec, ← transpose_mul, hVU, transpose_one, one_mulVec, mulVec_zero]`. Then use the resulting hypothesis.
-/
theorem uni_dual (U V : Matrix ι ι ℤ) (hUV : U * V = 1) (hVU : V * U = 1) (G : Matrix ι ι ℝ)
    (hG : G.PosDef) (δ : ℝ) (hD : Dual G δ) : Dual ((mz U)ᵀ * G * mz U) δ := by
  have hUVr := mz_mul_eq_one hUV
  have hVUr := mz_mul_eq_one hVU
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG.det_pos.ne'
  have hinv : ((mz U)ᵀ * G * mz U)⁻¹ = mz V * G⁻¹ * (mz V)ᵀ := by
    apply Matrix.inv_eq_left_inv
    have hT : (mz V)ᵀ * (mz U)ᵀ = 1 := by rw [← transpose_mul, hUVr, transpose_one]
    calc mz V * G⁻¹ * (mz V)ᵀ * ((mz U)ᵀ * G * mz U)
        = mz V * (G⁻¹ * (((mz V)ᵀ * (mz U)ᵀ) * G)) * mz U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hT, Matrix.one_mul, nonsing_inv_mul G hu, Matrix.mul_one, hVUr]
  intro c hc
  rw [hinv, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (cz c) (mz V), ← mulVec_transpose]
  have e : (mz V)ᵀ *ᵥ cz c = cz (Vᵀ *ᵥ c) := by
    funext i
    simp [cz, mz_apply, mulVec, dotProduct, transpose_apply]
  rw [e]
  apply hD
  intro h0
  apply hc
  have h1 : Uᵀ *ᵥ (Vᵀ *ᵥ c) = Uᵀ *ᵥ 0 := by rw [h0]
  rwa [mulVec_mulVec, ← transpose_mul, hVU, transpose_one, one_mulVec, mulVec_zero] at h1

/- English proof (translation)
Establish `hUVr` using `mz_mul_eq_one hUV`. Introduce `p`. Take `⟨c, hc⟩` from `hC (mz V *ᵥ p)`. Use `⟨U *ᵥ c, ?_⟩` and prove the remaining obligations. Establish `e : p - cz (U *ᵥ c) = mz U *ᵥ (mz V *ᵥ p - cz c)`.

Rewrite using `[mulVec_sub, mulVec_mulVec, hUVr, one_mulVec, cz_mulVec]`. Rewrite using `[e, quad_mz]`. Conclude with `hc`.
-/
theorem uni_cov (U V : Matrix ι ι ℤ) (hUV : U * V = 1) (G : Matrix ι ι ℝ) (R : ℝ)
    (hC : Cov ((mz U)ᵀ * G * mz U) R) : Cov G R := by
  have hUVr := mz_mul_eq_one hUV
  intro p
  obtain ⟨c, hc⟩ := hC (mz V *ᵥ p)
  refine ⟨U *ᵥ c, ?_⟩
  have e : p - cz (U *ᵥ c) = mz U *ᵥ (mz V *ᵥ p - cz c) := by
    rw [mulVec_sub, mulVec_mulVec, hUVr, one_mulVec, cz_mulVec]
  rw [e, quad_mz]
  exact hc

end Uni

/- English proof (translation)
Take `⟨k, snf⟩` from `(Submodule.span ℤ {v}).smithNormalForm (Pi.basisFun ℤ (Fin n))`. Establish `hvN : v ∈ Submodule.span ℤ {v}` using `Submodule.mem_span_singleton_self v`. Establish `hk : 0 < k`. Break down `Nat.eq_zero_or_pos k with hk | hk` into its components or cases. It suffices to derive a contradiction.

Substitute `hk` using the available equality. Apply `hv` to reduce the goal to its premises. Establish `h0 : (⟨v, hvN⟩ : Submodule.span ℤ {v}) = 0` using `snf.bN.ext_elem fun i => Fin.elim0 i`. Simplify using `using congrArg Subtype.val h0`. Conclude with `hk`.

Take `⟨s, hs⟩` from `Submodule.mem_span_singleton.mp (snf.bN ⟨0, hk⟩).2`. Establish `h2 : snf.bN ⟨0, hk⟩ = s • (⟨v, hvN⟩ : Submodule.span ℤ {v})` using `Subtype.ext (by rw [Submodule.coe_smul]; exact hs.symm)`. Establish `h1 : snf.bN.repr (snf.bN ⟨0, hk⟩) ⟨0, hk⟩ = 1` using `by simp`. Rewrite `h1` using `[h2, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Establish `hsu : s * s = 1`.

Apply the tactic sequence `rcases Int.isUnit_iff.mp (isUnit_iff_exists_inv.mpr ⟨_, h1⟩) with h | h <;> simp [h]`. Establish `hv' : v = s • ((snf.bN ⟨0, hk⟩ : Submodule.span ℤ {v}) : Fin n → ℤ)`. Rewrite using `[← hs, smul_smul, hsu, one_smul]`. Set `e` to `Equiv.swap (snf.f ⟨0, hk⟩) i0`. Set `bM'` to `snf.bM.reindex e`.

Use `⟨(Pi.basisFun ℤ (Fin n)).toMatrix bM', bM'.toMatrix (Pi.basisFun ℤ (Fin n)), s * snf.a ⟨0, hk⟩, Basis.toMatrix_mul_toMatrix_flip _ _, Basis.toMatrix_mul_toMatrix_flip _ _, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hv` to reduce the goal to its premises. Rewrite using `[hv', snf.snf, smul_smul, h0, zero_smul]`. Establish `hb : (fun i => (Pi.basisFun ℤ (Fin n)).toMatrix bM' i i0) = snf.bM (snf.f ⟨0, hk⟩)`.

Use function extensionality and compare the values at `i`. Simplify using `[Basis.toMatrix_apply, bM', e]`. Rewrite using `[hb, mul_smul, ← snf.snf]`. Conclude with `hv'`.
-/
theorem complete {n : ℕ} (v : Fin n → ℤ) (hv : v ≠ 0) (i0 : Fin n) :
    ∃ (U V : Matrix (Fin n) (Fin n) ℤ) (m : ℤ), U * V = 1 ∧ V * U = 1 ∧ m ≠ 0 ∧
      v = m • fun i => U i i0 := by
  classical
  obtain ⟨k, snf⟩ := (Submodule.span ℤ {v}).smithNormalForm (Pi.basisFun ℤ (Fin n))
  have hvN : v ∈ Submodule.span ℤ {v} := Submodule.mem_span_singleton_self v
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exfalso
      subst hk
      apply hv
      have h0 : (⟨v, hvN⟩ : Submodule.span ℤ {v}) = 0 := snf.bN.ext_elem fun i => Fin.elim0 i
      simpa using congrArg Subtype.val h0
    · exact hk
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (snf.bN ⟨0, hk⟩).2
  have h2 : snf.bN ⟨0, hk⟩ = s • (⟨v, hvN⟩ : Submodule.span ℤ {v}) :=
    Subtype.ext (by rw [Submodule.coe_smul]; exact hs.symm)
  have h1 : snf.bN.repr (snf.bN ⟨0, hk⟩) ⟨0, hk⟩ = 1 := by simp
  rw [h2, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
  have hsu : s * s = 1 := by
    rcases Int.isUnit_iff.mp (isUnit_iff_exists_inv.mpr ⟨_, h1⟩) with h | h <;> simp [h]
  have hv' : v = s • ((snf.bN ⟨0, hk⟩ : Submodule.span ℤ {v}) : Fin n → ℤ) := by
    rw [← hs, smul_smul, hsu, one_smul]
  let e := Equiv.swap (snf.f ⟨0, hk⟩) i0
  let bM' := snf.bM.reindex e
  refine ⟨(Pi.basisFun ℤ (Fin n)).toMatrix bM', bM'.toMatrix (Pi.basisFun ℤ (Fin n)),
    s * snf.a ⟨0, hk⟩, Basis.toMatrix_mul_toMatrix_flip _ _, Basis.toMatrix_mul_toMatrix_flip _ _,
    ?_, ?_⟩
  · intro h0
    apply hv
    rw [hv', snf.snf, smul_smul, h0, zero_smul]
  · have hb : (fun i => (Pi.basisFun ℤ (Fin n)).toMatrix bM' i i0) = snf.bM (snf.f ⟨0, hk⟩) := by
      funext i
      simp [Basis.toMatrix_apply, bM', e]
    rw [hb, mul_smul, ← snf.snf]
    exact hv'

section Schur

variable {d : ℕ} (G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)

def sch : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0

/- English proof (translation)
Simplify using `using hs.apply i j`.
-/
theorem sym_of_herm (hs : G.IsHermitian) (i j : Fin (d + 1)) : G j i = G i j := by
  simpa using hs.apply i j

/- English proof (translation)
Establish `hL : (Fin.cons y0 y : Fin (d + 1) → ℝ) ⬝ᵥ (G *ᵥ Fin.cons y0 y) = y0 * (G 0 0 * y0) + y0 * (∑ j, G 0 j.succ * y j) + (∑ i, y i * G i.succ 0) * y0 + ∑ i, y i * ∑ j, G i.succ j.succ * y j`. Simplify using `only [dotProduct, mulVec, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : ∑ i, y i * G i.succ 0 = ∑ j, G 0 j.succ * y j` using `Finset.sum_congr rfl fun i _ => by rw [sym_of_herm G hs 0 i.succ, mul_comm]`. Establish `h3 : ∀ i : Fin d, ∑ j, (G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0) * y j = ∑ j, G i.succ j.succ * y j - G i.succ 0 / G 0 0 * ∑ j, G 0 j.succ * y j`.

Introduce `i`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Establish `e2 : y ⬝ᵥ (sch G *ᵥ y) = ∑ i, y i * ∑ j, G i.succ j.succ * y j - (∑ j, G 0 j.succ * y j) ^ 2 / G 0 0`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [dotProduct, mulVec, sch, of_apply, h3]`. Use `_ = ∑ i, y i * ∑ j, G i.succ j.succ * y j - (∑ i, y i * G i.succ 0) * ((∑ j, G 0 j.succ * y j) / G 0 0) := by`. Rewrite using `[Finset.sum_mul, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Use `_ = _ := by rw [e1]; ring`.

Rewrite using `[hL, e1, e2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sch_id (hs : G.IsHermitian) (ha : G 0 0 ≠ 0) (y0 : ℝ) (y : Fin d → ℝ) :
    (Fin.cons y0 y : Fin (d + 1) → ℝ) ⬝ᵥ (G *ᵥ Fin.cons y0 y) =
      G 0 0 * (y0 + (∑ j, G 0 j.succ * y j) / G 0 0) ^ 2 + y ⬝ᵥ (sch G *ᵥ y) := by
  have hL : (Fin.cons y0 y : Fin (d + 1) → ℝ) ⬝ᵥ (G *ᵥ Fin.cons y0 y) =
      y0 * (G 0 0 * y0) + y0 * (∑ j, G 0 j.succ * y j) + (∑ i, y i * G i.succ 0) * y0 +
        ∑ i, y i * ∑ j, G i.succ j.succ * y j := by
    simp only [dotProduct, mulVec, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_add,
      Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    ring
  have e1 : ∑ i, y i * G i.succ 0 = ∑ j, G 0 j.succ * y j :=
    Finset.sum_congr rfl fun i _ => by rw [sym_of_herm G hs 0 i.succ, mul_comm]
  have h3 : ∀ i : Fin d, ∑ j, (G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0) * y j =
      ∑ j, G i.succ j.succ * y j - G i.succ 0 / G 0 0 * ∑ j, G 0 j.succ * y j := by
    intro i
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : y ⬝ᵥ (sch G *ᵥ y) = ∑ i, y i * ∑ j, G i.succ j.succ * y j -
      (∑ j, G 0 j.succ * y j) ^ 2 / G 0 0 := by
    calc y ⬝ᵥ (sch G *ᵥ y)
        = ∑ i, y i * (∑ j, G i.succ j.succ * y j - G i.succ 0 / G 0 0 * ∑ j, G 0 j.succ * y j) := by
          simp only [dotProduct, mulVec, sch, of_apply, h3]
      _ = ∑ i, y i * ∑ j, G i.succ j.succ * y j -
            (∑ i, y i * G i.succ 0) * ((∑ j, G 0 j.succ * y j) / G 0 0) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by rw [e1]; ring
  rw [hL, e1, e2]
  field_simp
  ring

/- English proof (translation)
Introduce `h`. Apply `hy` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Simplify using `using congrFun h j.succ`.
-/
theorem fin_cons_ne {y0 : ℝ} {y : Fin d → ℝ} (hy : y ≠ 0) : (Fin.cons y0 y : Fin (d + 1) → ℝ) ≠ 0 := by
  intro h
  apply hy
  funext j
  simpa using congrFun h j.succ

/- English proof (translation)
Establish `ha : 0 < G 0 0` using `hG.diag_pos`. Establish `hs` using `hG.isHermitian`. Use `PosDef.of_dotProduct_mulVec_pos ?_ fun y hy => ?_` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [conjTranspose_apply, sch, of_apply, star_trivial]`.

Rewrite using `[sym_of_herm G hs i.succ j.succ, sym_of_herm G hs 0 j.succ, sym_of_herm G hs i.succ 0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[star_trivial]`. Establish `h` using `hG.dotProduct_mulVec_pos (fin_cons_ne (y0 := -(∑ j, G 0 j.succ * y j) / G 0 0) hy)`. Rewrite `h` using `[star_trivial, sch_id G hs ha.ne']`.

Establish `h0 : -(∑ j, G 0 j.succ * y j) / G 0 0 + (∑ j, G 0 j.succ * y j) / G 0 0 = 0` using `by ring`. Rewrite `h` using `[h0]`. Simplify using `using h`.
-/
theorem sch_pd (hG : G.PosDef) : (sch G).PosDef := by
  have ha : 0 < G 0 0 := hG.diag_pos
  have hs := hG.isHermitian
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun y hy => ?_
  · ext i j
    simp only [conjTranspose_apply, sch, of_apply, star_trivial]
    rw [sym_of_herm G hs i.succ j.succ, sym_of_herm G hs 0 j.succ, sym_of_herm G hs i.succ 0]
    ring
  · rw [star_trivial]
    have h := hG.dotProduct_mulVec_pos (fin_cons_ne (y0 := -(∑ j, G 0 j.succ * y j) / G 0 0) hy)
    rw [star_trivial, sch_id G hs ha.ne'] at h
    have h0 : -(∑ j, G 0 j.succ * y j) / G 0 0 + (∑ j, G 0 j.succ * y j) / G 0 0 = 0 := by ring
    rw [h0] at h
    simpa using h

/- English proof (translation)
Establish `ha : 0 < G 0 0` using `hG.diag_pos`. Establish `hSpd` using `sch_pd G hG`. Establish `hSu : IsUnit (sch G).det` using `isUnit_iff_ne_zero.mpr hSpd.det_pos.ne'`. Establish `hu : IsUnit G.det` using `isUnit_iff_ne_zero.mpr hG.det_pos.ne'`. Introduce `c hc`.

Take `⟨x', hx'⟩ : ∃ x', x' = (sch G)⁻¹ *ᵥ cz c` from `⟨_, rfl⟩`. Establish `hS : sch G *ᵥ x' = cz c` using `by rw [hx', mulVec_mulVec, mul_nonsing_inv _ hSu, one_mulVec]`. Establish `hGx : G *ᵥ (Fin.cons (-(∑ k, G 0 k.succ * x' k) / G 0 0) x' : Fin (d + 1) → ℝ) = Fin.cons 0 (cz c)`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations.

Simplify using `only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hSj` using `congrFun hS j`. Simplify using `only [mulVec, dotProduct, sch, of_apply, sub_mul, Finset.sum_sub_distrib] at hSj`.

Establish `e : ∑ k, G j.succ 0 * G 0 k.succ / G 0 0 * x' k = G j.succ 0 * ((∑ k, G 0 k.succ * x' k) / G 0 0)`. Rewrite using `[Finset.sum_div, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Simplify using `only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]`. Establish `e2 : G j.succ 0 * (-(∑ k, G 0 k.succ * x' k) / G 0 0) = -(G j.succ 0 * ((∑ k, G 0 k.succ * x' k) / G 0 0))` using `by ring`.

Rewrite using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hinv : G⁻¹ *ᵥ (Fin.cons 0 (cz c) : Fin (d + 1) → ℝ) = Fin.cons (-(∑ k, G 0 k.succ * x' k) / G 0 0) x'`. Rewrite using `[← hGx, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]`. Establish `hc0 : cz (Fin.cons 0 c : Fin (d + 1) → ℤ) = Fin.cons 0 (cz c)`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) i <;> simp [cz]`. Establish `hne : (Fin.cons 0 c : Fin (d + 1) → ℤ) ≠ 0`. Introduce `h`. Apply `hc` to reduce the goal to its premises.

Use function extensionality and compare the values at `j`. Simplify using `using congrFun h j.succ`. Establish `h` using `hD _ hne`. Rewrite `h` using `[hc0, hinv]`. Establish `e : (Fin.cons 0 (cz c) : Fin (d + 1) → ℝ) ⬝ᵥ (Fin.cons (-(∑ k, G 0 k.succ * x' k) / G 0 0) x' : Fin (d + 1) → ℝ) = cz c ⬝ᵥ x'`.

Simplify using `[dotProduct, Fin.sum_univ_succ]`. Rewrite `h` using `[e, hx']`. Conclude with `h`.
-/
theorem sch_dual (hG : G.PosDef) (δ : ℝ) (hD : Dual G δ) : Dual (sch G) δ := by
  have ha : 0 < G 0 0 := hG.diag_pos
  have hSpd := sch_pd G hG
  have hSu : IsUnit (sch G).det := isUnit_iff_ne_zero.mpr hSpd.det_pos.ne'
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG.det_pos.ne'
  intro c hc
  obtain ⟨x', hx'⟩ : ∃ x', x' = (sch G)⁻¹ *ᵥ cz c := ⟨_, rfl⟩
  have hS : sch G *ᵥ x' = cz c := by rw [hx', mulVec_mulVec, mul_nonsing_inv _ hSu, one_mulVec]
  have hGx : G *ᵥ (Fin.cons (-(∑ k, G 0 k.succ * x' k) / G 0 0) x' : Fin (d + 1) → ℝ) =
      Fin.cons 0 (cz c) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      field_simp
      ring
    · have hSj := congrFun hS j
      simp only [mulVec, dotProduct, sch, of_apply, sub_mul, Finset.sum_sub_distrib] at hSj
      have e : ∑ k, G j.succ 0 * G 0 k.succ / G 0 0 * x' k =
          G j.succ 0 * ((∑ k, G 0 k.succ * x' k) / G 0 0) := by
        rw [Finset.sum_div, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have e2 : G j.succ 0 * (-(∑ k, G 0 k.succ * x' k) / G 0 0) =
          -(G j.succ 0 * ((∑ k, G 0 k.succ * x' k) / G 0 0)) := by ring
      rw [e2]
      linarith
  have hinv : G⁻¹ *ᵥ (Fin.cons 0 (cz c) : Fin (d + 1) → ℝ) =
      Fin.cons (-(∑ k, G 0 k.succ * x' k) / G 0 0) x' := by
    rw [← hGx, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  have hc0 : cz (Fin.cons 0 c : Fin (d + 1) → ℤ) = Fin.cons 0 (cz c) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [cz]
  have hne : (Fin.cons 0 c : Fin (d + 1) → ℤ) ≠ 0 := by
    intro h
    apply hc
    funext j
    simpa using congrFun h j.succ
  have h := hD _ hne
  rw [hc0, hinv] at h
  have e : (Fin.cons 0 (cz c) : Fin (d + 1) → ℝ) ⬝ᵥ
      (Fin.cons (-(∑ k, G 0 k.succ * x' k) / G 0 0) x' : Fin (d + 1) → ℝ) = cz c ⬝ᵥ x' := by
    simp [dotProduct, Fin.sum_univ_succ]
  rw [e, hx'] at h
  exact h

/- English proof (translation)
Establish `ha : 0 < G 0 0` using `hG.diag_pos`. Introduce `p`. Take `⟨c', hc'⟩` from `hC (fun j => p j.succ)`. Take `⟨y, hy⟩ : ∃ y : Fin d → ℝ, y = (fun j => p j.succ) - cz c'` from `⟨_, rfl⟩`. Rewrite `hc'` using `[← hy]`.

Take `⟨t, ht⟩ : ∃ t : ℝ, t = p 0 + (∑ j, G 0 j.succ * y j) / G 0 0` from `⟨_, rfl⟩`. Use `⟨Fin.cons (round t) c', ?_⟩` and prove the remaining obligations. Establish `hp : p - cz (Fin.cons (round t) c' : Fin (d + 1) → ℤ) = Fin.cons (p 0 - ((round t : ℤ) : ℝ)) y`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations.

Simplify using `[cz]`. Simplify using `[cz, hy]`. Rewrite using `[hp, sch_id G hG.isHermitian ha.ne']`. Establish `h1 : p 0 - ((round t : ℤ) : ℝ) + (∑ j, G 0 j.succ * y j) / G 0 0 = t - round t`. Rewrite using `[ht]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Establish `h2` using `abs_sub_round t`. Establish `h3 : (t - round t) ^ 2 ≤ 1 / 4`. Establish `h4 : (t - round t) ^ 2 = |t - round t| ^ 2` using `(sq_abs _).symm`.

Rewrite using `[h4]`. Establish `h5` using `abs_nonneg (t - round t)`. Use the polynomial consequences of the given equalities and inequalities. Establish `h6 : G 0 0 * (t - round t) ^ 2 ≤ G 0 0 / 4` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sch_cov (hG : G.PosDef) (R : ℝ) (hC : Cov (sch G) R) : Cov G (G 0 0 / 4 + R) := by
  have ha : 0 < G 0 0 := hG.diag_pos
  intro p
  obtain ⟨c', hc'⟩ := hC (fun j => p j.succ)
  obtain ⟨y, hy⟩ : ∃ y : Fin d → ℝ, y = (fun j => p j.succ) - cz c' := ⟨_, rfl⟩
  rw [← hy] at hc'
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = p 0 + (∑ j, G 0 j.succ * y j) / G 0 0 := ⟨_, rfl⟩
  refine ⟨Fin.cons (round t) c', ?_⟩
  have hp : p - cz (Fin.cons (round t) c' : Fin (d + 1) → ℤ) =
      Fin.cons (p 0 - ((round t : ℤ) : ℝ)) y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [cz]
    · simp [cz, hy]
  rw [hp, sch_id G hG.isHermitian ha.ne']
  have h1 : p 0 - ((round t : ℤ) : ℝ) + (∑ j, G 0 j.succ * y j) / G 0 0 = t - round t := by
    rw [ht]; ring
  rw [h1]
  have h2 := abs_sub_round t
  have h3 : (t - round t) ^ 2 ≤ 1 / 4 := by
    have h4 : (t - round t) ^ 2 = |t - round t| ^ 2 := (sq_abs _).symm
    rw [h4]
    have h5 := abs_nonneg (t - round t)
    nlinarith
  have h6 : G 0 0 * (t - round t) ^ 2 ≤ G 0 0 / 4 := by nlinarith
  linarith

end Schur

/- English proof (translation)
Simplify using `only [dotProduct, mulVec, submatrix_apply, Function.comp_apply]`. Rewrite using `[← e.symm.sum_comp]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← e.symm.sum_comp]`. Simplify using `only [Equiv.apply_symm_apply]`.
-/
theorem quad_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (G : Matrix ι ι ℝ)
    (y : κ → ℝ) : y ⬝ᵥ (G.submatrix e.symm e.symm *ᵥ y) = (y ∘ e) ⬝ᵥ (G *ᵥ (y ∘ e)) := by
  simp only [dotProduct, mulVec, submatrix_apply, Function.comp_apply]
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply]

/- English proof (translation)
Set `e : ι ≃ Fin d` to `Fintype.equivFinOfCardEq h`. Establish `hG' : (G.submatrix e.symm e.symm).PosDef` using `hG.submatrix e.symm.injective`. Establish `hD' : Dual (G.submatrix e.symm e.symm) δ`. Introduce `c hc`. Rewrite using `[inv_submatrix_equiv, quad_reindex]`.

Establish `hne : (c ∘ e) ≠ 0`. Introduce `h0`. Apply `hc` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Simplify using `using congrFun h0 (e.symm k)`.

Conclude with `hD _ hne`. Introduce `p`. Take `⟨c, hc⟩` from `core _ hG' δ hδ hD' (p ∘ e.symm)`. Use `⟨c ∘ e, ?_⟩` and prove the remaining obligations. Establish `e1 : p - cz (c ∘ e) = (p ∘ e.symm - cz c) ∘ e`.

Use function extensionality and compare the values at `i`. Simplify using `[cz]`. Rewrite using `[e1, ← quad_reindex e G]`. Conclude with `hc`.
-/
theorem reidx {d : ℕ} {C : ℝ} (core : ∀ G : Matrix (Fin d) (Fin d) ℝ, G.PosDef → ∀ δ : ℝ, 0 < δ →
      Dual G δ → Cov G (C / δ))
    (ι : Type) [Fintype ι] [DecidableEq ι] (h : Fintype.card ι = d) (G : Matrix ι ι ℝ)
    (hG : G.PosDef) (δ : ℝ) (hδ : 0 < δ) (hD : Dual G δ) : Cov G (C / δ) := by
  let e : ι ≃ Fin d := Fintype.equivFinOfCardEq h
  have hG' : (G.submatrix e.symm e.symm).PosDef := hG.submatrix e.symm.injective
  have hD' : Dual (G.submatrix e.symm e.symm) δ := by
    intro c hc
    rw [inv_submatrix_equiv, quad_reindex]
    have hne : (c ∘ e) ≠ 0 := by
      intro h0
      apply hc
      funext k
      simpa using congrFun h0 (e.symm k)
    exact hD _ hne
  intro p
  obtain ⟨c, hc⟩ := core _ hG' δ hδ hD' (p ∘ e.symm)
  refine ⟨c ∘ e, ?_⟩
  have e1 : p - cz (c ∘ e) = (p ∘ e.symm - cz c) ∘ e := by
    funext i
    simp [cz]
  rw [e1, ← quad_reindex e G]
  exact hc

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Use `⟨1, one_pos, fun G _ δ hδ _ p => ⟨0, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [dotProduct, Finset.univ_eq_empty, Finset.sum_empty]`.

Check the signs of the components of the expression. Consider the case `succ d ih`. Take `⟨C, hC0, hC⟩` from `ih`. Establish `hTd` using `hT d`. Use `⟨C + T d / 4, by positivity, ?_⟩` and prove the remaining obligations.

Introduce `G hG δ hδ hD`. Take `⟨v, hv0, hv⟩` from `SV d G hG δ hδ hD`. Take `⟨U, V, m, hUV, hVU, hm, hvU⟩` from `complete v hv0 0`. Establish `hG'` using `uni_pd U V hVU G hG`. Establish `hD'` using `uni_dual U V hUV hVU G hG δ hD`.

Establish `hq0 : ((mz U)ᵀ * G * mz U) 0 0 = cz (fun i => U i 0) ⬝ᵥ (G *ᵥ cz (fun i => U i 0))`. Simplify using `only [Matrix.mul_apply, transpose_apply, mz_apply, dotProduct, mulVec, cz, Finset.sum_mul, Finset.mul_sum]`. Use `conv_lhs => rw [Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Establish `hcv : cz v = (m : ℝ) • cz (fun i => U i 0)`.

Substitute `hvU` using the available equality. Use function extensionality and compare the values at `i`. Simplify using `[cz]`. Establish `hQ : cz v ⬝ᵥ (G *ᵥ cz v) = (m : ℝ) ^ 2 * (cz (fun i => U i 0) ⬝ᵥ (G *ᵥ cz (fun i => U i 0)))`. Rewrite using `[hcv, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hm1 : (1 : ℝ) ≤ (m : ℝ) ^ 2`. Establish `h1 : (1 : ℤ) ≤ m ^ 2`. Establish `ha` using `Int.one_le_abs hm`. Rewrite using `[← sq_abs]`.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `h1` after adjusting the coercions. Establish `hQ0 : 0 ≤ cz (fun i => U i 0) ⬝ᵥ (G *ᵥ cz (fun i => U i 0))`. Simplify using `using hG.posSemidef.dotProduct_mulVec_nonneg (cz (fun i => U i 0))`. Establish `h00 : ((mz U)ᵀ * G * mz U) 0 0 ≤ T d / δ`.

Rewrite using `[hq0]`. Combine the equalities or inequalities in the displayed calculation. Establish `hcov` using `sch_cov _ hG' _ (hC _ (sch_pd _ hG') δ hδ (sch_dual _ hG' δ hD'))`. Apply `uni_cov U V hUV G` to reduce the goal to its premises. Introduce `p`.

Take `⟨c, hc⟩` from `hcov p`. Use `⟨c, hc.trans ?_⟩` and prove the remaining obligations. Establish `e : (C + T d / 4) / δ = C / δ + T d / δ / 4` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem core (T : ℕ → ℝ) (hT : ∀ n, 0 ≤ T n)
    (SV : ∀ (n : ℕ) (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ), G.PosDef → ∀ δ : ℝ, 0 < δ →
      Dual G δ → ∃ v : Fin (n + 1) → ℤ, v ≠ 0 ∧ cz v ⬝ᵥ (G *ᵥ cz v) ≤ T n / δ) :
    ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ G : Matrix (Fin d) (Fin d) ℝ, G.PosDef → ∀ δ : ℝ, 0 < δ →
      Dual G δ → Cov G (C / δ) := by
  intro d
  induction d with
  | zero =>
    refine ⟨1, one_pos, fun G _ δ hδ _ p => ⟨0, ?_⟩⟩
    simp only [dotProduct, Finset.univ_eq_empty, Finset.sum_empty]
    positivity
  | succ d ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    have hTd := hT d
    refine ⟨C + T d / 4, by positivity, ?_⟩
    intro G hG δ hδ hD
    obtain ⟨v, hv0, hv⟩ := SV d G hG δ hδ hD
    obtain ⟨U, V, m, hUV, hVU, hm, hvU⟩ := complete v hv0 0
    have hG' := uni_pd U V hVU G hG
    have hD' := uni_dual U V hUV hVU G hG δ hD
    have hq0 : ((mz U)ᵀ * G * mz U) 0 0 =
        cz (fun i => U i 0) ⬝ᵥ (G *ᵥ cz (fun i => U i 0)) := by
      simp only [Matrix.mul_apply, transpose_apply, mz_apply, dotProduct, mulVec, cz,
        Finset.sum_mul, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hcv : cz v = (m : ℝ) • cz (fun i => U i 0) := by
      subst hvU
      funext i
      simp [cz]
    have hQ : cz v ⬝ᵥ (G *ᵥ cz v) =
        (m : ℝ) ^ 2 * (cz (fun i => U i 0) ⬝ᵥ (G *ᵥ cz (fun i => U i 0))) := by
      rw [hcv, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
      have h1 : (1 : ℤ) ≤ m ^ 2 := by
        have ha := Int.one_le_abs hm
        rw [← sq_abs]
        nlinarith
      exact_mod_cast h1
    have hQ0 : 0 ≤ cz (fun i => U i 0) ⬝ᵥ (G *ᵥ cz (fun i => U i 0)) := by
      simpa using hG.posSemidef.dotProduct_mulVec_nonneg (cz (fun i => U i 0))
    have h00 : ((mz U)ᵀ * G * mz U) 0 0 ≤ T d / δ := by
      rw [hq0]
      calc _ ≤ (m : ℝ) ^ 2 * (cz (fun i => U i 0) ⬝ᵥ (G *ᵥ cz (fun i => U i 0))) :=
            le_mul_of_one_le_left hQ0 hm1
        _ = _ := hQ.symm
        _ ≤ T d / δ := hv
    have hcov := sch_cov _ hG' _ (hC _ (sch_pd _ hG') δ hδ (sch_dual _ hG' δ hD'))
    apply uni_cov U V hUV G
    intro p
    obtain ⟨c, hc⟩ := hcov p
    refine ⟨c, hc.trans ?_⟩
    have e : (C + T d / 4) / δ = C / δ + T d / δ / 4 := by ring
    rw [e]
    linarith

end PositivityTheory.KB.SmoothPartitionUnityBasic.TZ

end
