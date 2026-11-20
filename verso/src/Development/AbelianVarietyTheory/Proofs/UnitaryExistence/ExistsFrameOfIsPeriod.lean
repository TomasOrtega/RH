import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemRange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqIffConjNe

open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.PeriodOnto

def sgnMat (r q : ℕ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a => ((FD.sgn q a : ℝ) : ℂ)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h a b hab`. Use `congrFun (congrFun h a) b` as an intermediate fact. Simplify using `only [sgnMat, diagonal_mul, mul_diagonal, FD.sgn] at this`. Apply the tactic sequence `by_cases ha : (a : ℕ) < q <;> by_cases hb : (b : ℕ) < q <;> simp [ha, hb] at hab this`.

Take the linear combination `(1 / 2 : ℂ) * this`. Take the linear combination `(-1 / 2 : ℂ) * this`. Introduce `h`. Use extensionality with `a b`. Simplify using `only [sgnMat, diagonal_mul, mul_diagonal, FD.sgn]`.

Apply the tactic sequence `by_cases ha : (a : ℕ) < q <;> by_cases hb : (b : ℕ) < q`. Simplify using `[ha, hb]`. Simplify using `[h a b (by simp [ha, hb])]`. Simplify using `[h a b (by simp [ha, hb])]`. Simplify using `[ha, hb]`.
-/
theorem comm_sgnMat_iff {r q : ℕ} (X : Matrix (Fin r) (Fin r) ℂ) :
    sgnMat r q * X = X * sgnMat r q ↔
      ∀ a b : Fin r, ¬ (((a : ℕ) < q) ↔ ((b : ℕ) < q)) → X a b = 0 := by
  constructor
  · intro h a b hab
    have := congrFun (congrFun h a) b
    simp only [sgnMat, diagonal_mul, mul_diagonal, FD.sgn] at this
    by_cases ha : (a : ℕ) < q <;> by_cases hb : (b : ℕ) < q <;> simp [ha, hb] at hab this
    · linear_combination (1 / 2 : ℂ) * this
    · linear_combination (-1 / 2 : ℂ) * this
  · intro h
    ext a b
    simp only [sgnMat, diagonal_mul, mul_diagonal, FD.sgn]
    by_cases ha : (a : ℕ) < q <;> by_cases hb : (b : ℕ) < q
    · simp [ha, hb]
    · simp [h a b (by simp [ha, hb])]
    · simp [h a b (by simp [ha, hb])]
    · simp [ha, hb]

/- English proof (translation)
Establish `h1` using `(h.submatrix (Fin.castLE_injective (Nat.le_of_lt_succ i.isLt))).det_pos`. Establish `h2 : (sgnMat r q * X).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = (Matrix.diagonal fun a : Fin i => ((FD.sgn q a : ℝ) : ℂ)) * X.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.isLt))`. Use extensionality with `a b`. Simplify using `[sgnMat, diagonal_mul]`. Rewrite `h1` using `[h2, det_mul, det_diagonal]`.

Establish `h3 : (∏ a : Fin i, ((FD.sgn q a : ℝ) : ℂ)) = ((FD.psgn q i : ℝ) : ℂ)`. Rewrite using `[FD.psgn, ← Fin.prod_univ_eq_prod_range, Complex.ofReal_prod]`. Rewrite `h1` using `[h3]`. Use `(Complex.pos_iff.mp h1).1` as an intermediate fact. Simplify `this` using `[FD.lminor]`.
-/
theorem lminor_sign {r q : ℕ} (X : Matrix (Fin r) (Fin r) ℂ) (h : (sgnMat r q * X).PosDef)
    (i : Fin (r + 1)) : 0 < FD.psgn q i * (FD.lminor X i).re := by
  have h1 := (h.submatrix (Fin.castLE_injective (Nat.le_of_lt_succ i.isLt))).det_pos
  have h2 : (sgnMat r q * X).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) =
      (Matrix.diagonal fun a : Fin i => ((FD.sgn q a : ℝ) : ℂ)) *
        X.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
          (Fin.castLE (Nat.le_of_lt_succ i.isLt)) := by
    ext a b
    simp [sgnMat, diagonal_mul]
  rw [h2, det_mul, det_diagonal] at h1
  have h3 : (∏ a : Fin i, ((FD.sgn q a : ℝ) : ℂ)) = ((FD.psgn q i : ℝ) : ℂ) := by
    rw [FD.psgn, ← Fin.prod_univ_eq_prod_range, Complex.ofReal_prod]
  rw [h3] at h1
  have := (Complex.pos_iff.mp h1).1
  simpa [FD.lminor] using this

/- English proof (translation)
Use `set A := Miᵀ * G * Mi.map conj with hA`. Establish `hM' : Mi * M = 1` using `mul_eq_one_comm.mp hM`. Establish `hoff` using `(comm_sgnMat_iff A).mp hc`. Set `N : Matrix (Fin r) (Fin r) ℂ` to `Matrix.of fun a b => if (a : ℕ) < q then A a b else (1 : Matrix (Fin r) (Fin r) ℂ) a b`. Establish `hNc : sgnMat r q * N = N * sgnMat r q`.

Rewrite using `[comm_sgnMat_iff]`. Introduce `a b hab`. Distinguish the cases in `ha : (a : ℕ) < q`. Simplify using `[N, ha, hoff a b hab]`. Establish `: a ≠ b` using `by rintro rfl; simp at hab`.

Simplify using `[N, ha, this]`. Establish `hNu : IsUnit N`. Rewrite using `[← mulVec_injective_iff_isUnit]`. Establish `: ∀ u, N *ᵥ u = 0 → u = 0`. Introduce `u hu`.

Assume the negation of the conclusion as `hne`. Establish `h1` using `hp.dotProduct_mulVec_pos hne`. Establish `h2 : star u ⬝ᵥ ((sgnMat r q * A) *ᵥ u) = 0`. Rewrite using `[← mulVec_mulVec]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations.

Establish `ha` using `congrFun hu a`. Distinguish the cases in `hq : (a : ℕ) < q`. Establish `: (A *ᵥ u) a = 0` using `by simpa [N, mulVec, dotProduct, hq] using ha`. Simplify using `[sgnMat, mulVec_diagonal, this]`. Establish `: u a = 0` using `by simpa [N, mulVec, dotProduct, hq, one_apply] using ha`.

Simplify using `[this]`. Conclude with `h1.ne' h2`. Introduce `u u' huu`. Use `this (u - u') (by rw [mulVec_sub, huu, sub_self])` as an intermediate fact. Conclude with `sub_eq_zero.mp this`.

Take `⟨Y, hNY⟩` from `hNu.exists_right_inv`. Establish `hYN : Y * N = 1` using `mul_eq_one_comm.mp hNY`. Establish `hYc : sgnMat r q * Y = Y * sgnMat r q`. Combine the equalities or inequalities in the displayed calculation. Establish `hcc : ∀ Z : Matrix (Fin r) (Fin r) ℂ, (Z.map conj).map conj = Z`.

Introduce `Z`. Use extensionality with `a b`. Simplify using the standard rewrite rules. Establish `hinv : (N.map conj * M) * (Mi * Y.map conj) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc M, hM, Matrix.one_mul, ← Matrix.map_mul, hNY]`.

Simplify using the standard rewrite rules. Establish `hYT : (Y.map conj)ᵀ = Yᴴ` using `by ext a b; simp [conjTranspose_apply]`. Establish `hYHc : sgnMat r q * Yᴴ = Yᴴ * sgnMat r q`. Rewrite using `[comm_sgnMat_iff]`. Introduce `a b hab`.

Use `(comm_sgnMat_iff Y).mp hYc b a (fun h => hab h.symm)` as an intermediate fact. Simplify using `[conjTranspose_apply, this]`. Use `⟨Mi * Y.map conj, ?_, ?_, fun v a => ⟨fun ha => ?_, fun ha => ?_⟩⟩` and prove the remaining obligations. Introduce `h0`. Use `congrArg Matrix.det hinv` as an intermediate fact.

Rewrite `this` using `[det_mul (N.map conj * M), h0]`. Simplify using `at this`. Establish `: sgnMat r q * ((Mi * Y.map conj)ᵀ * G * (Mi * Y.map conj).map conj) = Yᴴ * (sgnMat r q * A) * Y`. Rewrite using `[transpose_mul, Matrix.map_mul, hcc, hYT, ← Matrix.mul_assoc Yᴴ, ← hYHc, hA]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[this]`. Use `hp.conjTranspose_mul_mul_same ?_` and prove the remaining obligations. Rewrite using `[mulVec_injective_iff_isUnit]`. Conclude with `IsUnit.of_mul_eq_one N hYN`. Establish `h1 : G * (Mi * Y.map conj).map conj = Mᵀ * (A * Y)`.

Rewrite using `[Matrix.map_mul, hcc, hA]`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[← transpose_mul, hM', transpose_one, Matrix.one_mul]`. Establish `hAY : sgnMat r q * (A * Y) = (A * Y) * sgnMat r q`. Rewrite using `[← Matrix.mul_assoc, hc, Matrix.mul_assoc A, hYc, Matrix.mul_assoc A]`.

Establish `h2 : ∀ c, (A * Y) c a = (1 : Matrix (Fin r) (Fin r) ℂ) c a`. Introduce `c`. Distinguish the cases in `hcq : (c : ℕ) < q`. Rewrite using `[← hNY]`. Simplify using `[Matrix.mul_apply, N, hcq]`.

Establish `: c ≠ a` using `by rintro rfl; exact hcq ha`. Rewrite using `[(comm_sgnMat_iff _).mp hAY c a (by simp [hcq, ha])]`. Simplify using `[this]`. Rewrite using `[h1, ← vecMul_vecMul, vecMul_transpose]`. Simplify using `[vecMul, dotProduct, h2, one_apply]`.

Rewrite using `[inv_eq_left_inv hinv, ← mulVec_mulVec]`. Establish `h3 : ∀ c, (N.map conj) a c = if a = c then 1 else 0`. Introduce `c`. Distinguish the cases in `h : a = c`. Substitute `h` using the available equality.

Simplify using `[N, ha]`. Simplify using `[N, ha, h]`. Generalize the expression as in `M *ᵥ v = w`. Simplify using `only [mulVec, dotProduct, h3]`. Simplify using the standard rewrite rules.
-/
theorem exists_frame {r q : ℕ} (G M Mi : Matrix (Fin r) (Fin r) ℂ) (hM : M * Mi = 1)
    (hc : sgnMat r q * (Miᵀ * G * Mi.map conj) = (Miᵀ * G * Mi.map conj) * sgnMat r q)
    (hp : (sgnMat r q * (Miᵀ * G * Mi.map conj)).PosDef) :
    ∃ x : Matrix (Fin r) (Fin r) ℂ, x.det ≠ 0 ∧ (sgnMat r q * (xᵀ * G * x.map conj)).PosDef ∧
      ∀ (v : Fin r → ℂ) (a : Fin r),
        ((a : ℕ) < q → (v ᵥ* (G * x.map conj)) a = (M *ᵥ v) a) ∧
        (¬ (a : ℕ) < q → (x⁻¹ *ᵥ v) a = (M *ᵥ v) a) := by
  set A := Miᵀ * G * Mi.map conj with hA
  have hM' : Mi * M = 1 := mul_eq_one_comm.mp hM
  have hoff := (comm_sgnMat_iff A).mp hc
  let N : Matrix (Fin r) (Fin r) ℂ :=
    Matrix.of fun a b => if (a : ℕ) < q then A a b else (1 : Matrix (Fin r) (Fin r) ℂ) a b
  have hNc : sgnMat r q * N = N * sgnMat r q := by
    rw [comm_sgnMat_iff]
    intro a b hab
    by_cases ha : (a : ℕ) < q
    · simp [N, ha, hoff a b hab]
    · have : a ≠ b := by rintro rfl; simp at hab
      simp [N, ha, this]
  have hNu : IsUnit N := by
    rw [← mulVec_injective_iff_isUnit]
    have : ∀ u, N *ᵥ u = 0 → u = 0 := by
      intro u hu
      by_contra hne
      have h1 := hp.dotProduct_mulVec_pos hne
      have h2 : star u ⬝ᵥ ((sgnMat r q * A) *ᵥ u) = 0 := by
        rw [← mulVec_mulVec]
        refine Finset.sum_eq_zero fun a _ => ?_
        have ha := congrFun hu a
        by_cases hq : (a : ℕ) < q
        · have : (A *ᵥ u) a = 0 := by simpa [N, mulVec, dotProduct, hq] using ha
          simp [sgnMat, mulVec_diagonal, this]
        · have : u a = 0 := by simpa [N, mulVec, dotProduct, hq, one_apply] using ha
          simp [this]
      exact h1.ne' h2
    intro u u' huu
    have := this (u - u') (by rw [mulVec_sub, huu, sub_self])
    exact sub_eq_zero.mp this
  obtain ⟨Y, hNY⟩ := hNu.exists_right_inv
  have hYN : Y * N = 1 := mul_eq_one_comm.mp hNY
  have hYc : sgnMat r q * Y = Y * sgnMat r q := by
    calc sgnMat r q * Y = Y * (N * sgnMat r q) * Y := by rw [← Matrix.mul_assoc Y, hYN, Matrix.one_mul]
      _ = Y * sgnMat r q := by rw [← hNc, Matrix.mul_assoc, Matrix.mul_assoc, hNY, Matrix.mul_one]
  have hcc : ∀ Z : Matrix (Fin r) (Fin r) ℂ, (Z.map conj).map conj = Z := by
    intro Z; ext a b; simp
  have hinv : (N.map conj * M) * (Mi * Y.map conj) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M, hM, Matrix.one_mul, ← Matrix.map_mul, hNY]
    simp
  have hYT : (Y.map conj)ᵀ = Yᴴ := by ext a b; simp [conjTranspose_apply]
  have hYHc : sgnMat r q * Yᴴ = Yᴴ * sgnMat r q := by
    rw [comm_sgnMat_iff]
    intro a b hab
    have := (comm_sgnMat_iff Y).mp hYc b a (fun h => hab h.symm)
    simp [conjTranspose_apply, this]
  refine ⟨Mi * Y.map conj, ?_, ?_, fun v a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · intro h0
    have := congrArg Matrix.det hinv
    rw [det_mul (N.map conj * M), h0] at this
    simp at this
  · have : sgnMat r q * ((Mi * Y.map conj)ᵀ * G * (Mi * Y.map conj).map conj) =
        Yᴴ * (sgnMat r q * A) * Y := by
      rw [transpose_mul, Matrix.map_mul, hcc, hYT, ← Matrix.mul_assoc Yᴴ, ← hYHc, hA]
      simp only [Matrix.mul_assoc]
    rw [this]
    refine hp.conjTranspose_mul_mul_same ?_
    rw [mulVec_injective_iff_isUnit]
    exact IsUnit.of_mul_eq_one N hYN
  · have h1 : G * (Mi * Y.map conj).map conj = Mᵀ * (A * Y) := by
      rw [Matrix.map_mul, hcc, hA]
      simp only [← Matrix.mul_assoc]
      rw [← transpose_mul, hM', transpose_one, Matrix.one_mul]
    have hAY : sgnMat r q * (A * Y) = (A * Y) * sgnMat r q := by
      rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc A, hYc, Matrix.mul_assoc A]
    have h2 : ∀ c, (A * Y) c a = (1 : Matrix (Fin r) (Fin r) ℂ) c a := by
      intro c
      by_cases hcq : (c : ℕ) < q
      · rw [← hNY]; simp [Matrix.mul_apply, N, hcq]
      · have : c ≠ a := by rintro rfl; exact hcq ha
        rw [(comm_sgnMat_iff _).mp hAY c a (by simp [hcq, ha])]
        simp [this]
    rw [h1, ← vecMul_vecMul, vecMul_transpose]
    simp [vecMul, dotProduct, h2, one_apply]
  · rw [inv_eq_left_inv hinv, ← mulVec_mulVec]
    have h3 : ∀ c, (N.map conj) a c = if a = c then 1 else 0 := by
      intro c
      by_cases h : a = c
      · subst h; simp [N, ha]
      · simp [N, ha, h]
    generalize M *ᵥ v = w
    simp only [mulVec, dotProduct, h3]
    simp

def kap (q a : ℕ) : ℂ →ₗ[ℝ] ℂ := if a < q then Complex.conjAe.toLinearMap else LinearMap.id

/- English proof (translation)
Apply the tactic sequence `unfold kap; split_ifs <;> simp`.
-/
theorem kap_apply (q a : ℕ) (c : ℂ) : kap q a c = if a < q then conj c else c := by
  unfold kap; split_ifs <;> simp

/- English proof (translation)
Apply the tactic sequence `simp only [kap_apply]; split_ifs <;> simp`.
-/
theorem kap_kap (q a : ℕ) (c : ℂ) : kap q a (kap q a c) = c := by
  simp only [kap_apply]; split_ifs <;> simp

section Block

variable {ι : Type} [Fintype ι] {g r : ℕ} (idx : Fin g ≃ ι × Fin r) (q : ℕ)

def blockOf (t : ι) : (Fin g → ℂ) →ₗ[ℝ] (Fin r → ℂ) :=
  LinearMap.pi fun a => (kap q a).comp (LinearMap.proj (idx.symm (t, a)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blockOf_apply (t : ι) (z : Fin g → ℂ) (a : Fin r) :
    blockOf idx q t z a = kap q a (z (idx.symm (t, a))) := rfl

open Classical in

def ofBlock (t : ι) (w : Fin r → ℂ) : Fin g → ℂ :=
  fun k => if (idx k).1 = t then kap q (idx k).2 (w (idx k).2) else 0

open Classical in
/- English proof (translation)
Use extensionality with `a`. Apply the tactic sequence `by_cases h : t' = t <;> simp [blockOf_apply, ofBlock, h, kap_kap]`.
-/
theorem blockOf_ofBlock (t t' : ι) (w : Fin r → ℂ) :
    blockOf idx q t' (ofBlock idx q t w) = if t' = t then w else 0 := by
  ext a
  by_cases h : t' = t <;> simp [blockOf_apply, ofBlock, h, kap_kap]

/- English proof (translation)
Use extensionality with `k`. Simplify using `only [ofBlock, Pi.smul_apply, sgnMat, mulVec_diagonal, kap_apply, FD.sgn]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem I_smul_ofBlock (t : ι) (w : Fin r → ℂ) :
    Complex.I • ofBlock idx q t w = ofBlock idx q t ((-Complex.I) • (sgnMat r q *ᵥ w)) := by
  ext k
  simp only [ofBlock, Pi.smul_apply, sgnMat, mulVec_diagonal, kap_apply, FD.sgn]
  split_ifs <;> simp

variable {Λ : Type} (P : Λ → Fin g → ℂ) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
  (e : ι → Λ → Fin r → ℂ) (M : ι → Matrix (Fin r) (Fin r) ℂ)
  (hM : ∀ v t, blockOf idx q t (P v) = M t *ᵥ e t v)

include hspan hM in
/- English proof (translation)
Rewrite using `[← vecMul_injective_iff_isUnit]`. Establish `: ∀ w, w ᵥ* M t = 0 → w = 0`. Introduce `w hw`. Establish `h1 : ∀ z ∈ Submodule.span ℝ (Set.range P), w ⬝ᵥ blockOf idx q t z = 0`. Introduce `z hz`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨v, rfl⟩` from `hz`. Rewrite using `[hM, dotProduct_mulVec, hw, zero_dotProduct]`. Consider the case `zero => simp`.

Consider the case `add _ _ _ _ h1 h2 => simp [h1, h2]`. Consider the case `smul c _ _ h1 => simp [h1]`. Use extensionality with `a`. Use `h1 (ofBlock idx q t (Pi.single a 1)) (by rw [hspan]; trivial)` as an intermediate fact. Simplify `this` using `[blockOf_ofBlock]`.

Introduce `u u' huu`. Use `this (u - u') (by rw [sub_vecMul]; exact sub_eq_zero.mpr huu)` as an intermediate fact. Conclude with `sub_eq_zero.mp this`.
-/
theorem isUnit_block (t : ι) : IsUnit (M t) := by
  classical
  rw [← vecMul_injective_iff_isUnit]
  have : ∀ w, w ᵥ* M t = 0 → w = 0 := by
    intro w hw
    have h1 : ∀ z ∈ Submodule.span ℝ (Set.range P), w ⬝ᵥ blockOf idx q t z = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨v, rfl⟩ := hz
        rw [hM, dotProduct_mulVec, hw, zero_dotProduct]
      | zero => simp
      | add _ _ _ _ h1 h2 => simp [h1, h2]
      | smul c _ _ h1 => simp [h1]
    ext a
    have := h1 (ofBlock idx q t (Pi.single a 1)) (by rw [hspan]; trivial)
    simpa [blockOf_ofBlock] using this
  intro u u' huu
  have := this (u - u') (by rw [sub_vecMul]; exact sub_eq_zero.mpr huu)
  exact sub_eq_zero.mp this

include hspan in
/- English proof (translation)
Establish `hz : z ∈ Submodule.span ℝ (Set.range P)` using `by rw [hspan]; trivial`. Establish `hz' : z' ∈ Submodule.span ℝ (Set.range P)` using `by rw [hspan]; trivial`. Unfold `hermForm at *`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨x, rfl⟩` from `hz`. Proceed by induction on `hz' using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨y, rfl⟩` from `hz`. Conclude with `h x y`.

Consider the case `zero => simp`. Consider the case `add _ _ _ _ h1 h2`. Simplify using `only [star_add, mulVec_add, dotProduct_add, Complex.add_im, map_add, h1, h2, mul_add, Finset.sum_add_distrib]`. Consider the case `smul c _ _ h1`. Simplify using `only [star_smul, star_trivial, mulVec_smul, dotProduct_smul, Complex.smul_im, map_smul, h1, smul_eq_mul, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Consider the case `zero => simp`. Consider the case `add _ _ _ _ h1 h2`. Simplify using `only [add_dotProduct, Complex.add_im, map_add, h1, h2, mul_add, Finset.sum_add_distrib]`. Consider the case `smul c _ _ h1`.

Simplify using `only [smul_dotProduct, Complex.smul_im, map_smul, h1, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem im_form_eq (A : ι → Matrix (Fin r) (Fin r) ℂ) (s : ι → ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ x y, (hermForm Hm (P x) (P y)).im =
      ∑ t, -2 * s t * (blockOf idx q t (P x) ⬝ᵥ A t *ᵥ star (blockOf idx q t (P y))).im)
    (z z' : Fin g → ℂ) : (hermForm Hm z z').im =
      ∑ t, -2 * s t * (blockOf idx q t z ⬝ᵥ A t *ᵥ star (blockOf idx q t z')).im := by
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by rw [hspan]; trivial
  have hz' : z' ∈ Submodule.span ℝ (Set.range P) := by rw [hspan]; trivial
  unfold hermForm at *
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, rfl⟩ := hz
    induction hz' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, rfl⟩ := hz
      exact h x y
    | zero => simp
    | add _ _ _ _ h1 h2 =>
      simp only [star_add, mulVec_add, dotProduct_add, Complex.add_im, map_add, h1, h2, mul_add,
        Finset.sum_add_distrib]
    | smul c _ _ h1 =>
      simp only [star_smul, star_trivial, mulVec_smul, dotProduct_smul, Complex.smul_im, map_smul, h1,
        smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
  | zero => simp
  | add _ _ _ _ h1 h2 =>
    simp only [add_dotProduct, Complex.add_im, map_add, h1, h2, mul_add, Finset.sum_add_distrib]
  | smul c _ _ h1 =>
    simp only [smul_dotProduct, Complex.smul_im, map_smul, h1, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Establish `h1 : ∀ w w', (hermForm Hm (ofBlock idx q t w) (ofBlock idx q t w')).im = -2 * s t * (w ⬝ᵥ A t *ᵥ star w').im`. Introduce `w w'`. Rewrite using `[h, Finset.sum_eq_single t]`. Simplify using `[blockOf_ofBlock]`. Introduce `b _ hb`.

Simplify using `[blockOf_ofBlock, hb]`. Simplify using the standard rewrite rules. Establish `hI : ∀ z z' : Fin g → ℂ, hermForm Hm (Complex.I • z) (Complex.I • z') = hermForm Hm z z'`. Introduce `z z'`. Simplify using `[hermForm, star_smul, mulVec_smul, mulVec_neg, ← mul_assoc]`.

Establish `hI' : ∀ z z' : Fin g → ℂ, (hermForm Hm (Complex.I • z) z').im = (hermForm Hm z z').re`. Introduce `z z'`. Simplify using `[hermForm]`. Establish `hc : sgnMat r q * A t = A t * sgnMat r q`. Rewrite using `[comm_sgnMat_iff]`.

Introduce `a b hab`. Establish `h2 : ∀ c : ℂ, (c * A t a b).im = 0`. Introduce `c`. Establish `h3` using `h1 (Pi.single a c) (Pi.single b 1)`. Rewrite `h3` using `[← hI, I_smul_ofBlock, I_smul_ofBlock, h1]`.

Establish `h4` using `mul_left_cancel₀ (by have := hs t; linarith : -2 * s t ≠ 0) h3`. Establish `h5 : star (Pi.single b 1 : Fin r → ℂ) = Pi.single b 1`. Rewrite using `[← Pi.single_star]`. Simplify using the standard rewrite rules. Establish `h6 : ∀ (a : Fin r) (c : ℂ), sgnMat r q *ᵥ (Pi.single a c) = ((FD.sgn q a : ℝ) : ℂ) • Pi.single a c`.

Introduce `a c`. Use extensionality with `k`. Apply the tactic sequence `by_cases hk : k = a <;> simp [sgnMat, mulVec_diagonal, hk]`. Rewrite `h4` using `[h6, h6]`. Simplify using `only [star_smul, h5, mulVec_smul, smul_dotProduct, dotProduct_smul, single_dotProduct, mulVec_single_one, FD.sgn] at h4`.

Apply the tactic sequence `by_cases ha : (a : ℕ) < q <;> by_cases hb : (b : ℕ) < q <;> simp [ha, hb] at hab h4 ⊢ <;>`. Combine the linear equalities and inequalities to obtain the conclusion. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `using h2 Complex.I`. Simplify using `using h2 1`.

Establish `hS : (sgnMat r q).IsHermitian`. Apply `isHermitian_diagonal_of_self_adjoint` to reduce the goal to its premises. Use extensionality with `a`. Simplify using the standard rewrite rules. Establish `hH : (sgnMat r q * A t).IsHermitian`.

Unfold `IsHermitian`. Rewrite using `[conjTranspose_mul, hS.eq, (hA t).eq, hc]`. Use `⟨hc, PosDef.of_dotProduct_mulVec_pos hH fun u hu => ?_⟩` and prove the remaining obligations. Establish `hz : ofBlock idx q t (star u) ≠ 0`. Introduce `h0`.

Use `blockOf_ofBlock idx q t t (star u)` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `only [map_zero, if_true] at this`. Conclude with `hu (star_eq_zero.mp this.symm)`. Establish `h2` using `hpos _ hz`.

Rewrite `h2` using `[← hI', I_smul_ofBlock, h1]`. Establish `h3 : (sgnMat r q *ᵥ star u) ⬝ᵥ A t *ᵥ u = star u ⬝ᵥ (sgnMat r q * A t) *ᵥ u`. Rewrite using `[← mulVec_mulVec]`. Simplify using `only [dotProduct, sgnMat, mulVec_diagonal]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.

Rewrite `h2` using `[smul_dotProduct, star_star, h3]`. Use `Complex.pos_iff.mpr ⟨?_, (hH.im_star_dotProduct_mulVec_self u).symm⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul, neg_mul, Complex.neg_im, Complex.I_mul, mul_neg, neg_neg] at h2`. Use `hs t` as an intermediate fact. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem block_sign (A : ι → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ t, (A t).IsHermitian) (s : ι → ℝ)
    (hs : ∀ t, 0 < s t) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (h : ∀ z z', (hermForm Hm z z').im =
      ∑ t, -2 * s t * (blockOf idx q t z ⬝ᵥ A t *ᵥ star (blockOf idx q t z')).im) (t : ι) :
    sgnMat r q * A t = A t * sgnMat r q ∧ (sgnMat r q * A t).PosDef := by
  classical
  have h1 : ∀ w w', (hermForm Hm (ofBlock idx q t w) (ofBlock idx q t w')).im =
      -2 * s t * (w ⬝ᵥ A t *ᵥ star w').im := by
    intro w w'
    rw [h, Finset.sum_eq_single t]
    · simp [blockOf_ofBlock]
    · intro b _ hb; simp [blockOf_ofBlock, hb]
    · simp
  have hI : ∀ z z' : Fin g → ℂ, hermForm Hm (Complex.I • z) (Complex.I • z') = hermForm Hm z z' := by
    intro z z'
    simp [hermForm, star_smul, mulVec_smul, mulVec_neg, ← mul_assoc]
  have hI' : ∀ z z' : Fin g → ℂ, (hermForm Hm (Complex.I • z) z').im = (hermForm Hm z z').re := by
    intro z z'
    simp [hermForm]
  have hc : sgnMat r q * A t = A t * sgnMat r q := by
    rw [comm_sgnMat_iff]
    intro a b hab
    have h2 : ∀ c : ℂ, (c * A t a b).im = 0 := by
      intro c
      have h3 := h1 (Pi.single a c) (Pi.single b 1)
      rw [← hI, I_smul_ofBlock, I_smul_ofBlock, h1] at h3
      have h4 := mul_left_cancel₀ (by have := hs t; linarith : -2 * s t ≠ 0) h3
      have h5 : star (Pi.single b 1 : Fin r → ℂ) = Pi.single b 1 := by
        rw [← Pi.single_star]; simp
      have h6 : ∀ (a : Fin r) (c : ℂ), sgnMat r q *ᵥ (Pi.single a c) =
          ((FD.sgn q a : ℝ) : ℂ) • Pi.single a c := by
        intro a c
        ext k
        by_cases hk : k = a <;> simp [sgnMat, mulVec_diagonal, hk]
      rw [h6, h6] at h4
      simp only [star_smul, h5, mulVec_smul, smul_dotProduct, dotProduct_smul, single_dotProduct,
        mulVec_single_one, FD.sgn] at h4
      by_cases ha : (a : ℕ) < q <;> by_cases hb : (b : ℕ) < q <;> simp [ha, hb] at hab h4 ⊢ <;>
        linarith
    apply Complex.ext
    · simpa using h2 Complex.I
    · simpa using h2 1
  have hS : (sgnMat r q).IsHermitian := by
    apply isHermitian_diagonal_of_self_adjoint
    ext a; simp
  have hH : (sgnMat r q * A t).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, hS.eq, (hA t).eq, hc]
  refine ⟨hc, PosDef.of_dotProduct_mulVec_pos hH fun u hu => ?_⟩
  have hz : ofBlock idx q t (star u) ≠ 0 := by
    intro h0
    have := blockOf_ofBlock idx q t t (star u)
    rw [h0] at this
    simp only [map_zero, if_true] at this
    exact hu (star_eq_zero.mp this.symm)
  have h2 := hpos _ hz
  rw [← hI', I_smul_ofBlock, h1] at h2
  have h3 : (sgnMat r q *ᵥ star u) ⬝ᵥ A t *ᵥ u = star u ⬝ᵥ (sgnMat r q * A t) *ᵥ u := by
    rw [← mulVec_mulVec]
    simp only [dotProduct, sgnMat, mulVec_diagonal]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [smul_dotProduct, star_star, h3] at h2
  refine Complex.pos_iff.mpr ⟨?_, (hH.im_star_dotProduct_mulVec_self u).symm⟩
  simp only [smul_eq_mul, neg_mul, Complex.neg_im, Complex.I_mul, mul_neg, neg_neg] at h2
  have := hs t
  by_contra hcon
  push Not at hcon
  nlinarith

end Block

/- English proof (translation)
Establish `hex : ∀ t, ∃ Mi : Matrix (Fin r) (Fin r) ℂ, M t * Mi = 1` using `fun t => (isUnit_block idx q P hspan e M hM t).exists_right_inv`. Use `choose Mi hMi using hex`. Establish `he : ∀ v t, e t v = Mi t *ᵥ blockOf idx q t (P v)`. Introduce `v t`. Rewrite using `[hM, mulVec_mulVec, mul_eq_one_comm.mp (hMi t), one_mulVec]`.

Set `A : ι → Matrix (Fin r) (Fin r) ℂ` to `fun t => (Mi t)ᵀ * G t * (Mi t).map conj`. Establish `hAH : ∀ t, (A t).IsHermitian`. Introduce `t`. Establish `: (Mi t)ᵀ = ((Mi t).map conj)ᴴ` using `by ext a b; simp [conjTranspose_apply]`. Simplify using `only [A]`.

Rewrite using `[this]`. Conclude with `isHermitian_conjTranspose_mul_mul _ (hGH t)`. Establish `hform : ∀ (t : ι) (u w : Fin r → ℂ), (Mi t *ᵥ u) ⬝ᵥ G t *ᵥ star (Mi t *ᵥ w) = u ⬝ᵥ A t *ᵥ star w`. Introduce `t u w`. Establish `: star (Mi t *ᵥ w) = (Mi t).map conj *ᵥ star w`.

Use extensionality with `a`. Simplify using `[mulVec, dotProduct]`. Simplify using `only [A]`. Rewrite using `[this, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u, vecMul_transpose]`. Establish `hmain : ∀ x y, (hermForm Hm (P x) (P y)).im = ∑ t, -2 * s t * (blockOf idx q t (P x) ⬝ᵥ A t *ᵥ star (blockOf idx q t (P y))).im`.

Introduce `x y`. Rewrite using `[h]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[he x, he y, hform]`. Establish `hsign` using `block_sign idx q A hAH s hs Hm hpos (im_form_eq idx q P hspan A s Hm hmain) t`.

Take `⟨x, hx0, hx1, hx2⟩` from `exists_frame (G t) (M t) (Mi t) (hMi t) hsign.1 hsign.2`. Use `⟨x, hx0, hx1, fun v a => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun (hM v t) a`. Rewrite `h1` using `[blockOf_apply, kap_apply]`. Distinguish the cases in `ha : (a : ℕ) < q`.

Rewrite `h1`, the goal using `[if_pos ha]`. Rewrite using `[(hx2 (e t v) a).1 ha, ← h1, Complex.conj_conj]`. Rewrite `h1`, the goal using `[if_neg ha]`. Rewrite using `[(hx2 (e t v) a).2 ha, h1]`.
-/
theorem exists_frames {ι : Type} [Fintype ι] {g r : ℕ} (idx : Fin g ≃ ι × Fin r) (q : ℕ) {Λ : Type}
    (P : Λ → Fin g → ℂ) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (e : ι → Λ → Fin r → ℂ) (M : ι → Matrix (Fin r) (Fin r) ℂ)
    (hM : ∀ v t, blockOf idx q t (P v) = M t *ᵥ e t v) (G : ι → Matrix (Fin r) (Fin r) ℂ)
    (hGH : ∀ t, (G t).IsHermitian) (s : ι → ℝ) (hs : ∀ t, 0 < s t) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (h : ∀ x y, (hermForm Hm (P x) (P y)).im = ∑ t, -2 * s t * (e t x ⬝ᵥ G t *ᵥ star (e t y)).im)
    (t : ι) :
    ∃ x : Matrix (Fin r) (Fin r) ℂ, x.det ≠ 0 ∧ (sgnMat r q * (xᵀ * G t * x.map conj)).PosDef ∧
      ∀ (v : Λ) (a : Fin r), P v (idx.symm (t, a)) =
        if (a : ℕ) < q then conj ((e t v ᵥ* (G t * x.map conj)) a) else (x⁻¹ *ᵥ e t v) a := by
  have hex : ∀ t, ∃ Mi : Matrix (Fin r) (Fin r) ℂ, M t * Mi = 1 := fun t =>
    (isUnit_block idx q P hspan e M hM t).exists_right_inv
  choose Mi hMi using hex
  have he : ∀ v t, e t v = Mi t *ᵥ blockOf idx q t (P v) := by
    intro v t
    rw [hM, mulVec_mulVec, mul_eq_one_comm.mp (hMi t), one_mulVec]
  let A : ι → Matrix (Fin r) (Fin r) ℂ := fun t => (Mi t)ᵀ * G t * (Mi t).map conj
  have hAH : ∀ t, (A t).IsHermitian := by
    intro t
    have : (Mi t)ᵀ = ((Mi t).map conj)ᴴ := by ext a b; simp [conjTranspose_apply]
    simp only [A]
    rw [this]
    exact isHermitian_conjTranspose_mul_mul _ (hGH t)
  have hform : ∀ (t : ι) (u w : Fin r → ℂ),
      (Mi t *ᵥ u) ⬝ᵥ G t *ᵥ star (Mi t *ᵥ w) = u ⬝ᵥ A t *ᵥ star w := by
    intro t u w
    have : star (Mi t *ᵥ w) = (Mi t).map conj *ᵥ star w := by
      ext a; simp [mulVec, dotProduct]
    simp only [A]
    rw [this, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u, vecMul_transpose]
  have hmain : ∀ x y, (hermForm Hm (P x) (P y)).im = ∑ t, -2 * s t *
      (blockOf idx q t (P x) ⬝ᵥ A t *ᵥ star (blockOf idx q t (P y))).im := by
    intro x y
    rw [h]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [he x, he y, hform]
  have hsign := block_sign idx q A hAH s hs Hm hpos (im_form_eq idx q P hspan A s Hm hmain) t
  obtain ⟨x, hx0, hx1, hx2⟩ := exists_frame (G t) (M t) (Mi t) (hMi t) hsign.1 hsign.2
  refine ⟨x, hx0, hx1, fun v a => ?_⟩
  have h1 := congrFun (hM v t) a
  rw [blockOf_apply, kap_apply] at h1
  by_cases ha : (a : ℕ) < q
  · rw [if_pos ha] at h1 ⊢
    rw [(hx2 (e t v) a).1 ha, ← h1, Complex.conj_conj]
  · rw [if_neg ha] at h1 ⊢
    rw [(hx2 (e t v) a).2 ha, h1]

section Field

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs`. Consider the case `exact _root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs`. Consider the case `(apply _root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs ..)`.
-/
theorem exists_row {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {r : ℕ} (φ : Λ →ₗ[𝓞 E] (Fin r → E))
    (hinj : Function.Injective φ) (hsp : Submodule.span E (Set.range φ) = ⊤) (σ : E →+* ℂ) (f : Λ →+ ℂ)
    (hf : ∀ (a : 𝓞 E) x, f (a • x) = σ (a : E) * f x) :
    ∃ c : Fin r → ℂ, ∀ v, f v = ∑ j, c j * σ (φ v j) := by
  first
  | exact @_root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs
  | exact _root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs
  | (apply _root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExistsSmulMemRange.exists_coeffs ..)

/- English proof (translation)
Establish `h1 : algebraMap ℚ ℂ (Algebra.trace ℚ E z) = ∑ σ : E →ₐ[ℚ] ℂ, σ z` using `trace_eq_sum_embeddings (K := ℚ) (E := ℂ) (x := z)`. Establish `h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ z = ∑ σ : E →+* ℂ, σ z` using `(Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)) (fun σ : E →+* ℂ => σ z) (fun σ => σ z) (fun σ => rfl)).symm`. Establish `h3 : ∑ σ ∈ Ψᶜ, σ z = ∑ σ ∈ Ψ, conj (σ z)`. Use `Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ) (fun σ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `σ hσ`.

Use `hΨ (ComplexEmbedding.conjugate σ)` as an intermediate fact. Rewrite `this` using `[ComplexEmbedding.involutive_conjugate E σ]`. Simplify using `only [Finset.mem_compl] at hσ`. Conclude with `this.mpr hσ`. Introduce `σ hσ`.

Simplify using `only [Finset.mem_compl]`. Conclude with `(hΨ σ).mp hσ`. Introduce `σ _`. Conclude with `ComplexEmbedding.involutive_conjugate E σ`. Introduce `σ _`.

Conclude with `ComplexEmbedding.involutive_conjugate E σ`. Introduce `σ _`. Simplify using `[ComplexEmbedding.conjugate_coe_eq]`. Establish `h4 : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ σ ∈ Ψ, (σ z + conj (σ z))`. Rewrite using `[← eq_ratCast (algebraMap ℚ ℂ) (Algebra.trace ℚ E z), h1, h2, ← Finset.sum_add_sum_compl Ψ, h3, Finset.sum_add_distrib]`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[Complex.ofReal_ratCast, h4, ← Finset.sum_coe_sort Ψ, Complex.ofReal_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.add_conj]`.
-/
theorem trace_eq_sum_re (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : Ψ, 2 * (τ.1 z).re := by
  classical
  have h1 : algebraMap ℚ ℂ (Algebra.trace ℚ E z) = ∑ σ : E →ₐ[ℚ] ℂ, σ z :=
    trace_eq_sum_embeddings (K := ℚ) (E := ℂ) (x := z)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ z = ∑ σ : E →+* ℂ, σ z :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)) (fun σ : E →+* ℂ => σ z)
      (fun σ => σ z) (fun σ => rfl)).symm
  have h3 : ∑ σ ∈ Ψᶜ, σ z = ∑ σ ∈ Ψ, conj (σ z) := by
    refine Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ)
      (fun σ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      have := hΨ (ComplexEmbedding.conjugate σ)
      rw [ComplexEmbedding.involutive_conjugate E σ] at this
      simp only [Finset.mem_compl] at hσ
      exact this.mpr hσ
    · intro σ hσ
      simp only [Finset.mem_compl]
      exact (hΨ σ).mp hσ
    · intro σ _; exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _; exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _; simp [ComplexEmbedding.conjugate_coe_eq]
  have h4 : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ σ ∈ Ψ, (σ z + conj (σ z)) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ) (Algebra.trace ℚ E z), h1, h2,
      ← Finset.sum_add_sum_compl Ψ, h3, Finset.sum_add_distrib]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, h4, ← Finset.sum_coe_sort Ψ, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Complex.add_conj]

variable [IsCMField E]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem`. Consider the case `exact _root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem`. Consider the case `(apply _root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem ..)`.
-/
theorem cmType_host (H : Host E) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0)
    (τ : E →+* ℂ) : τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  first
  | exact @_root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem
  | exact _root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem
  | (apply _root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem ..)

/- English proof (translation)
Simplify using `[FD.hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hermC_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    FD.hermC τ G u v = u ⬝ᵥ G.map τ *ᵥ star v := by
  simp [FD.hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [FD.gram, FD.hermC, FD.col, of_apply, Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem gram_eq' {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ G x = xᵀ * G.map τ * x.map conj := by
  ext a b
  simp only [FD.gram, FD.hermC, FD.col, of_apply, Matrix.mul_apply, transpose_apply, map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Establish `hcc : ∀ a b, conj (τ (G a b)) = τ (G b a)` using `fun a b => by`. Rewrite using `[← hG a b]`. Conclude with `(IsCMField.complexEmbedding_complexConj E τ _).symm`. Simplify using `only [FD.hermC, FD.col, vecMul, dotProduct, Matrix.mul_apply, map_apply, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum, hcc]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem hermC_col {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, FD.cc (G a b) = G b a) (x : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) (a : Fin r) :
    conj ((v ᵥ* (G.map τ * x.map conj)) a) = FD.hermC τ G (FD.col x a) v := by
  have hcc : ∀ a b, conj (τ (G a b)) = τ (G b a) := fun a b => by
    rw [← hG a b]
    exact (IsCMField.complexEmbedding_complexConj E τ _).symm
  simp only [FD.hermC, FD.col, vecMul, dotProduct, Matrix.mul_apply, map_apply,
    map_sum, map_mul, Complex.conj_conj, Finset.mul_sum, hcc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Field

end GlobalTheory.PeriodOnto

namespace GlobalTheory

open PeriodOnto

/- English proof (translation)
Introduce `E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hξpos ⟨hinj, hsp, hG, _, hEF⟩ _ P ⟨hlin, _, _, hspan, Hm, _, hpos, hIm⟩`. Establish `hcc : ∀ (τ : E →+* ℂ) (z : E), τ (FD.cc z) = conj (τ z)` using `fun τ z => IsCMField.complexEmbedding_complexConj E τ z`. Establish `hex : ∀ k, ∃ c : Fin r → ℂ, ∀ v, P v k = ∑ j, c j * ty k (φ v j)` using `fun k => exists_row φ hinj hsp (ty k) ((Pi.evalAddMonoidHom (fun _ => ℂ) k).comp P) (fun a x => hlin a x k)`. Use `choose C hC using hex`. Establish `hM : ∀ v (t : Ψ), blockOf idx D.q t (P v) = (Matrix.of fun (a : Fin r) j => kap D.q a (C (idx.symm (t, a)) j)) *ᵥ FD.Data.emb t.1 (φ v)`.

Introduce `v t`. Use extensionality with `a`. Rewrite using `[blockOf_apply, hC, hty]`. Simplify using `only [mulVec, dotProduct, of_apply, FD.Data.emb, kap_apply, Equiv.apply_symm_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hGH : ∀ t : Ψ, (Gm.map t.1).IsHermitian`. Introduce `t`. Use extensionality with `a b`. Rewrite using `[conjTranspose_apply, map_apply, map_apply, ← hG b a, hcc]`. Both sides reduce to the same expression.

Establish `hmain : ∀ x y, (hermForm Hm (P x) (P y)).im = ∑ t : Ψ, -2 * (t.1 ξ).im * (FD.Data.emb t.1 (φ x) ⬝ᵥ Gm.map t.1 *ᵥ star (FD.Data.emb t.1 (φ y))).im`. Introduce `x y`. Establish `h1 : ((D.EF x y : ℤ) : ℝ) = ((Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)) : ℚ) : ℝ)`. Rewrite using `[← hEF]`. Simplify using the standard rewrite rules.

Rewrite using `[hIm, h1, trace_eq_sum_re Ψ (cmType_host H Ψ hΨ)]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Establish `h2 : t.1 (FD.herm Gm (φ x) (φ y)) = FD.hermC t.1 Gm (FD.Data.emb t.1 (φ x)) (FD.Data.emb t.1 (φ y))`. Simplify using `[FD.hermC, FD.herm, FD.Data.emb, hcc]`. Establish `h3 : (t.1 ξ).re = 0`.

Use `congrArg (fun z => (t.1 z).re) hξ` as an intermediate fact. Simplify using `only [hcc, map_neg, Complex.conj_re, Complex.neg_re] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[map_mul, h2, hermC_eq, Complex.mul_re, h3]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hfr` using `exists_frames idx D.q P hspan (fun t v => FD.Data.emb t.1 (φ v)) _ hM (fun t => Gm.map t.1) hGH (fun t => (t.1 ξ).im) (fun t => hξpos t.1 t.2) Hm hpos hmain`. Use `choose x hx0 hx1 hx2 using hfr`. Use `⟨fun t => x t, fun t => ⟨hx0 t, fun i => ?_⟩, fun v k => ?_⟩` and prove the remaining obligations. Apply `lminor_sign` to reduce the goal to its premises. Rewrite using `[gram_eq']`.

Conclude with `hx1 t`. Take `⟨⟨t, a⟩, rfl⟩` from `idx.symm.surjective k`. Rewrite using `[hx2, hermC_col _ _ hG, Equiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem exists_frame_of_isPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (_hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (_hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = D.p + D.q → ∀ P : D.La →+ (Fin g → ℂ), IsPeriod D ty P → ∃ x ∈ FD.GG Ψ Gm D.q, (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) := by
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hξpos ⟨hinj, hsp, hG, _, hEF⟩ _ P
    ⟨hlin, _, _, hspan, Hm, _, hpos, hIm⟩
  have hcc : ∀ (τ : E →+* ℂ) (z : E), τ (FD.cc z) = conj (τ z) := fun τ z =>
    IsCMField.complexEmbedding_complexConj E τ z
  have hex : ∀ k, ∃ c : Fin r → ℂ, ∀ v, P v k = ∑ j, c j * ty k (φ v j) := fun k =>
    exists_row φ hinj hsp (ty k) ((Pi.evalAddMonoidHom (fun _ => ℂ) k).comp P) (fun a x => hlin a x k)
  choose C hC using hex
  have hM : ∀ v (t : Ψ), blockOf idx D.q t (P v) =
      (Matrix.of fun (a : Fin r) j => kap D.q a (C (idx.symm (t, a)) j)) *ᵥ FD.Data.emb t.1 (φ v) := by
    intro v t
    ext a
    rw [blockOf_apply, hC, hty]
    simp only [mulVec, dotProduct, of_apply, FD.Data.emb, kap_apply, Equiv.apply_symm_apply]
    split_ifs <;> simp
  have hGH : ∀ t : Ψ, (Gm.map t.1).IsHermitian := by
    intro t
    ext a b
    rw [conjTranspose_apply, map_apply, map_apply, ← hG b a, hcc]
    rfl
  have hmain : ∀ x y, (hermForm Hm (P x) (P y)).im = ∑ t : Ψ, -2 * (t.1 ξ).im *
      (FD.Data.emb t.1 (φ x) ⬝ᵥ Gm.map t.1 *ᵥ star (FD.Data.emb t.1 (φ y))).im := by
    intro x y
    have h1 : ((D.EF x y : ℤ) : ℝ) = ((Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)) : ℚ) : ℝ) := by
      rw [← hEF]; simp
    rw [hIm, h1, trace_eq_sum_re Ψ (cmType_host H Ψ hΨ)]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h2 : t.1 (FD.herm Gm (φ x) (φ y)) =
        FD.hermC t.1 Gm (FD.Data.emb t.1 (φ x)) (FD.Data.emb t.1 (φ y)) := by
      simp [FD.hermC, FD.herm, FD.Data.emb, hcc]
    have h3 : (t.1 ξ).re = 0 := by
      have := congrArg (fun z => (t.1 z).re) hξ
      simp only [hcc, map_neg, Complex.conj_re, Complex.neg_re] at this
      linarith
    rw [map_mul, h2, hermC_eq, Complex.mul_re, h3]
    ring
  have hfr := exists_frames idx D.q P hspan (fun t v => FD.Data.emb t.1 (φ v)) _ hM
    (fun t => Gm.map t.1) hGH (fun t => (t.1 ξ).im) (fun t => hξpos t.1 t.2) Hm hpos hmain
  choose x hx0 hx1 hx2 using hfr
  refine ⟨fun t => x t, fun t => ⟨hx0 t, fun i => ?_⟩, fun v k => ?_⟩
  · apply lminor_sign
    rw [gram_eq']
    exact hx1 t
  · obtain ⟨⟨t, a⟩, rfl⟩ := idx.symm.surjective k
    rw [hx2, hermC_col _ _ hG, Equiv.apply_symm_apply]
    rfl

end GlobalTheory
