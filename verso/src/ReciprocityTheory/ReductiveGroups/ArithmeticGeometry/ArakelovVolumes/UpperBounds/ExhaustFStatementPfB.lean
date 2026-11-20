import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SignTypeCancelIdentity

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Take `⟨P, hPdet, hPgram⟩` from `X.signature τ`. Establish `hG` using `X.Gm_herm`. Establish `hg : ∀ a b, hermC τ.1 X.Gm (FD.col P a) (FD.col P b) = Matrix.diagonal (fun a : Fin r => ((sgn X.p0 a : ℝ) : ℂ)) a b` using `fun a b => by`. Rewrite using `[← hPgram]`. Both sides reduce to the same expression.

Establish `hPu : IsUnit P.det` using `isUnit_iff_ne_zero.2 hPdet`. Establish `hcoord : ∀ u : Fin r → ℂ, ∑ a, (P⁻¹ *ᵥ u) a • FD.col P a = u`. Introduce `u`. Establish `h1 : P *ᵥ (P⁻¹ *ᵥ u) = u`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]`.

Use `conv_rhs => rw [← h1]`. Use function extensionality and compare the values at `k`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FD.col, Matrix.mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hquad : ∀ y : Fin r → ℂ, hermC τ.1 X.Gm (∑ a, y a • FD.col P a) (∑ b, y b • FD.col P b) = ∑ a, y a * conj (y a) * ((sgn X.p0 a : ℝ) : ℂ)`. Introduce `y`. Rewrite using `[hermC_sum_left]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hermC_smul_left, hermC_sum_right]`.

Repeatedly rewrite using `[hermC_smul_right, hg, Matrix.diagonal_apply]`. Simplify using `only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Set `Q : Matrix (Fin r) (Option (Fin X.p0)) ℂ` to `fun k o => Option.elim o (e k) (fun b => X.colP x τ b k)`. Set `R : Matrix (Fin X.p0) (Option (Fin X.p0)) ℂ` to `(P⁻¹ * Q).submatrix (Fin.castLE X.p0_le) id`. Establish `hker : LinearMap.ker (Matrix.mulVecLin R) ≠ ⊥`. Apply `LinearMap.ker_ne_bot_of_finrank_lt` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Take `⟨z, hz, hz0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hker`. Rewrite `hz` using `[LinearMap.mem_ker, Matrix.mulVecLin_apply]`. Establish `hQv : Q *ᵥ z = ∑ b, z (some b) • X.colP x τ b + z none • e`. Use function extensionality and compare the values at `k`. Simplify using `only [Q, Matrix.mulVec, dotProduct, Fintype.sum_option, Option.elim, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[add_comm]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun b _ => mul_comm _ _`. Conclude with `mul_comm _ _`. Establish `hy0 : ∀ a : Fin X.p0, (P⁻¹ *ᵥ (∑ b, z (some b) • X.colP x τ b + z none • e)) (Fin.castLE X.p0_le a) = 0`.

Introduce `a`. Establish `h3 : ((P⁻¹ * Q) *ᵥ z) (Fin.castLE X.p0_le a) = 0` using `congrFun hz a`. Rewrite `h3` using `[← Matrix.mulVec_mulVec, hQv]`. Then use the resulting hypothesis. Use `set w : Fin r → ℂ := ∑ b, z (some b) • X.colP x τ b with hwdef`. Use `set v : Fin r → ℂ := w + z none • e with hvdef`.

Use `set y : Fin r → ℂ := P⁻¹ *ᵥ v with hydef`. Establish `hvP : v = ∑ k, y k • FD.col P k` using `(hcoord v).symm`. Establish `hsg : ∀ k, y k * conj (y k) * ((sgn X.p0 k : ℝ) : ℂ) = -((Complex.normSq (y k) : ℝ) : ℂ)`. Introduce `k`. Distinguish the cases in `hk : (k : ℕ) < X.p0`.

Establish `: y k = 0` using `hy0 ⟨k, hk⟩`. Simplify using `[this]`. Simplify using `[sgn, hk, Complex.mul_conj]`. Establish `hvv1 : hermC τ.1 X.Gm v v = -∑ k, ((Complex.normSq (y k) : ℝ) : ℂ)`. Rewrite using `[hvP, hquad]`.

Simplify using `only [hsg, Finset.sum_neg_distrib]`. Establish `hwe : hermC τ.1 X.Gm w e = 0`. Rewrite using `[hwdef, hermC_sum_left]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hermC_smul_left, ← hermC_conj τ.1 hG, hperp b, map_zero, mul_zero]`.

Establish `hew : hermC τ.1 X.Gm e w = 0`. Rewrite using `[hwdef, hermC_sum_right]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hermC_smul_right, hperp b, mul_zero]`. Establish `hvv2 : hermC τ.1 X.Gm v v = hermC τ.1 X.Gm w w + z none * conj (z none) * hermC τ.1 X.Gm e e`.

Rewrite using `[hvdef]`. Simplify using `only [hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right, hwe, hew]`. Expand and normalize the polynomial expressions, which then agree. Establish `hwq : hermC τ.1 X.Gm w w = ∑ a, ∑ b, z (some a) * X.gramPos x τ a b * conj (z (some b))`. Rewrite using `[hwdef, hermC_sum_left]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hermC_smul_left, hermC_sum_right, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hermC_smul_right, Data.gramPos_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hre : (hermC τ.1 X.Gm v v).re = (hermC τ.1 X.Gm w w).re + Complex.normSq (z none) * (hermC τ.1 X.Gm e e).re`. Rewrite using `[hvv2, Complex.mul_conj, Complex.add_re, Complex.re_ofReal_mul]`. Establish `hre2 : (hermC τ.1 X.Gm v v).re = -∑ k, Complex.normSq (y k)`. Rewrite using `[hvv1]`. Simplify using the standard rewrite rules.

Establish `hww : 0 ≤ (hermC τ.1 X.Gm w w).re`. Distinguish the cases in `hz1 : (fun b => z (some b)) = 0`. Establish `hw0 : w = 0`. Rewrite using `[hwdef]`. Simplify using `[show ∀ b, z (some b) = 0 from fun b => congrFun hz1 b]`.

Rewrite using `[hw0]`. Simplify using `[hermC]`. Rewrite using `[hwq]`. Conclude with `(quad_re_pos hA hz1).le`. Establish `hnn : 0 ≤ (hermC τ.1 X.Gm v v).re`.

Rewrite using `[hre]`. Conclude with `add_nonneg hww (mul_nonneg (Complex.normSq_nonneg _) hcon)`. Establish `hy : ∀ k, y k = 0`. Establish `hs : ∑ k, Complex.normSq (y k) = 0`. Use `Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (y k))` as an intermediate fact.

Rewrite `hnn` using `[hre2]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `k`. Use `(Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg (y k))).1 hs k (Finset.mem_univ _)` as an intermediate fact. Conclude with `Complex.normSq_eq_zero.1 this`.

Establish `hv0 : v = 0`. Rewrite using `[hvP]`. Simplify using `[hy]`. Establish `hzs : (fun b => z (some b)) = 0`. Assume the negation of the conclusion as `hz1`.

Establish `h1` using `quad_re_pos hA hz1`. Rewrite `h1` using `[← hwq]`. Establish `h0 : (hermC τ.1 X.Gm v v).re = 0` using `by rw [hv0]; simp [hermC]`. Rewrite `h0` using `[hre]`. Use polynomial arithmetic with `[mul_nonneg (Complex.normSq_nonneg (z none)) hcon]`.

Establish `hw0 : w = 0`. Rewrite using `[hwdef]`. Simplify using `[show ∀ b, z (some b) = 0 from fun b => congrFun hzs b]`. Establish `ht0 : z none = 0`. Establish `h` using `hv0`.

Rewrite `h` using `[hvdef, hw0, zero_add]`. Conclude with `(smul_eq_zero.1 h).resolve_right he`. Apply `hz0` to reduce the goal to its premises. Use function extensionality and compare the values at `o`. Consider the cases of `o with`.

Consider the case `none => exact ht0`. Consider the case `some b => exact congrFun hzs b`.
-/
theorem neg_of_perp' {x : Frame X.Ψ r} (τ : X.Ψ) (hA : (X.gramPos x τ).PosDef) {e : Fin r → ℂ}
    (he : e ≠ 0) (hperp : ∀ b, hermC τ.1 X.Gm e (X.colP x τ b) = 0) :
    (hermC τ.1 X.Gm e e).re < 0 := by
  classical
  obtain ⟨P, hPdet, hPgram⟩ := X.signature τ
  have hG := X.Gm_herm
  have hg : ∀ a b, hermC τ.1 X.Gm (FD.col P a) (FD.col P b) =
      Matrix.diagonal (fun a : Fin r => ((sgn X.p0 a : ℝ) : ℂ)) a b := fun a b => by
    rw [← hPgram]; rfl
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hPdet
  have hcoord : ∀ u : Fin r → ℂ, ∑ a, (P⁻¹ *ᵥ u) a • FD.col P a = u := by
    intro u
    have h1 : P *ᵥ (P⁻¹ *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
    conv_rhs => rw [← h1]
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FD.col, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hquad : ∀ y : Fin r → ℂ, hermC τ.1 X.Gm (∑ a, y a • FD.col P a) (∑ b, y b • FD.col P b) =
      ∑ a, y a * conj (y a) * ((sgn X.p0 a : ℝ) : ℂ) := by
    intro y
    rw [hermC_sum_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hermC_smul_left, hermC_sum_right]
    simp_rw [hermC_smul_right, hg, Matrix.diagonal_apply]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  by_contra hcon
  push_neg at hcon
  let Q : Matrix (Fin r) (Option (Fin X.p0)) ℂ :=
    fun k o => Option.elim o (e k) (fun b => X.colP x τ b k)
  let R : Matrix (Fin X.p0) (Option (Fin X.p0)) ℂ := (P⁻¹ * Q).submatrix (Fin.castLE X.p0_le) id
  have hker : LinearMap.ker (Matrix.mulVecLin R) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz
  have hQv : Q *ᵥ z = ∑ b, z (some b) • X.colP x τ b + z none • e := by
    funext k
    simp only [Q, Matrix.mulVec, dotProduct, Fintype.sum_option, Option.elim, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    · exact mul_comm _ _
  have hy0 : ∀ a : Fin X.p0,
      (P⁻¹ *ᵥ (∑ b, z (some b) • X.colP x τ b + z none • e)) (Fin.castLE X.p0_le a) = 0 := by
    intro a
    have h3 : ((P⁻¹ * Q) *ᵥ z) (Fin.castLE X.p0_le a) = 0 := congrFun hz a
    rwa [← Matrix.mulVec_mulVec, hQv] at h3
  set w : Fin r → ℂ := ∑ b, z (some b) • X.colP x τ b with hwdef
  set v : Fin r → ℂ := w + z none • e with hvdef
  set y : Fin r → ℂ := P⁻¹ *ᵥ v with hydef
  have hvP : v = ∑ k, y k • FD.col P k := (hcoord v).symm
  have hsg : ∀ k, y k * conj (y k) * ((sgn X.p0 k : ℝ) : ℂ) =
      -((Complex.normSq (y k) : ℝ) : ℂ) := by
    intro k
    by_cases hk : (k : ℕ) < X.p0
    · have : y k = 0 := hy0 ⟨k, hk⟩
      simp [this]
    · simp [sgn, hk, Complex.mul_conj]
  have hvv1 : hermC τ.1 X.Gm v v = -∑ k, ((Complex.normSq (y k) : ℝ) : ℂ) := by
    rw [hvP, hquad]
    simp only [hsg, Finset.sum_neg_distrib]
  have hwe : hermC τ.1 X.Gm w e = 0 := by
    rw [hwdef, hermC_sum_left]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [hermC_smul_left, ← hermC_conj τ.1 hG, hperp b, map_zero, mul_zero]
  have hew : hermC τ.1 X.Gm e w = 0 := by
    rw [hwdef, hermC_sum_right]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [hermC_smul_right, hperp b, mul_zero]
  have hvv2 : hermC τ.1 X.Gm v v =
      hermC τ.1 X.Gm w w + z none * conj (z none) * hermC τ.1 X.Gm e e := by
    rw [hvdef]
    simp only [hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right, hwe, hew]
    ring
  have hwq : hermC τ.1 X.Gm w w =
      ∑ a, ∑ b, z (some a) * X.gramPos x τ a b * conj (z (some b)) := by
    rw [hwdef, hermC_sum_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hermC_smul_right, Data.gramPos_apply]
    ring
  have hre : (hermC τ.1 X.Gm v v).re =
      (hermC τ.1 X.Gm w w).re + Complex.normSq (z none) * (hermC τ.1 X.Gm e e).re := by
    rw [hvv2, Complex.mul_conj, Complex.add_re, Complex.re_ofReal_mul]
  have hre2 : (hermC τ.1 X.Gm v v).re = -∑ k, Complex.normSq (y k) := by
    rw [hvv1]; simp
  have hww : 0 ≤ (hermC τ.1 X.Gm w w).re := by
    by_cases hz1 : (fun b => z (some b)) = 0
    · have hw0 : w = 0 := by
        rw [hwdef]
        simp [show ∀ b, z (some b) = 0 from fun b => congrFun hz1 b]
      rw [hw0]; simp [hermC]
    · rw [hwq]; exact (quad_re_pos hA hz1).le
  have hnn : 0 ≤ (hermC τ.1 X.Gm v v).re := by
    rw [hre]; exact add_nonneg hww (mul_nonneg (Complex.normSq_nonneg _) hcon)
  have hy : ∀ k, y k = 0 := by
    have hs : ∑ k, Complex.normSq (y k) = 0 := by
      have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (y k))
      rw [hre2] at hnn
      linarith
    intro k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg (y k))).1 hs k
      (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  have hv0 : v = 0 := by
    rw [hvP]; simp [hy]
  have hzs : (fun b => z (some b)) = 0 := by
    by_contra hz1
    have h1 := quad_re_pos hA hz1
    rw [← hwq] at h1
    have h0 : (hermC τ.1 X.Gm v v).re = 0 := by rw [hv0]; simp [hermC]
    rw [hre] at h0
    nlinarith [mul_nonneg (Complex.normSq_nonneg (z none)) hcon]
  have hw0 : w = 0 := by
    rw [hwdef]
    simp [show ∀ b, z (some b) = 0 from fun b => congrFun hzs b]
  have ht0 : z none = 0 := by
    have h := hv0
    rw [hvdef, hw0, zero_add] at h
    exact (smul_eq_zero.1 h).resolve_right he
  apply hz0
  funext o
  cases o with
  | none => exact ht0
  | some b => exact congrFun hzs b

/- English proof (translation)
Establish `hG` using `X.Gm_herm`. Set `gr : Fin k → Fin r` to `fun j => ⟨X.p0 + j, by have := j.isLt; omega⟩`. Set `d : Fin k → Fin r → ℂ` to `fun j => FD.col (mat x τ) (gr j)`. Set `A : Matrix (Fin X.p0) (Fin X.p0) ℂ` to `X.gramPos x τ`. Set `B : Matrix (Fin X.p0) (Fin k) ℂ` to `fun a l => hermC τ.1 X.Gm (X.colP x τ a) (d l)`.

Set `C : Matrix (Fin k) (Fin X.p0) ℂ` to `fun j b => hermC τ.1 X.Gm (d j) (X.colP x τ b)`. Set `D : Matrix (Fin k) (Fin k) ℂ` to `fun j l => hermC τ.1 X.Gm (d j) (d l)`. Establish `hApos : 0 < A.det` using `Matrix.PosDef.det_pos hA`. Establish `hAu : IsUnit A.det` using `isUnit_iff_ne_zero.2 hApos.ne'`. Use `haveI : Invertible A := Matrix.invertibleOfIsUnitDet A hAu`.

Establish `hdm : dmin X.Gm x τ i = (Matrix.fromBlocks A B C D).det`. Set `e : Fin X.p0 ⊕ Fin k ≃ Fin (i : ℕ)` to `finSumFinEquiv.trans (finCongr hik.symm)`. Unfold `dmin lminor`. Rewrite using `[← Matrix.det_submatrix_equiv_self e]`. Use `congr 1`.

Use extensionality with `s t`. Apply the tactic sequence `rcases s with a | j <;> rcases t with b | l <;> rfl`. Rewrite using `[hdm, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]`. Use `set α : Matrix (Fin k) (Fin X.p0) ℂ := C * A⁻¹ with hαdef`. Establish `hαA : α * A = C`.

Rewrite using `[hαdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]`. Establish `hAab : ∀ a b, A a b = hermC τ.1 X.Gm (X.colP x τ a) (X.colP x τ b)` using `fun a b => by show X.gramPos x τ a b = _`. Rewrite using `[Data.gramPos_apply]`. Set `wv : Fin k → Fin r → ℂ` to `fun j => d j + ∑ a, (-α j a) • X.colP x τ a`. Establish `hwc : ∀ j b, hermC τ.1 X.Gm (wv j) (X.colP x τ b) = 0`.

Introduce `j b`. Use `show hermC τ.1 X.Gm (d j + ∑ a, (-α j a) • X.colP x τ a) (X.colP x τ b) = 0`. Rewrite using `[hermC_add_left, hermC_sum_left]`. Simplify using `only [hermC_smul_left]`. Establish `h1 : ∑ a, -α j a * hermC τ.1 X.Gm (X.colP x τ a) (X.colP x τ b) = -(α * A) j b`.

Rewrite using `[Matrix.mul_apply, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hAab]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, hαA]`.

Conclude with `add_neg_cancel _`. Establish `hSw : ∀ j l, (D - α * B) j l = hermC τ.1 X.Gm (wv j) (wv l)`. Introduce `j l`. Establish `h2 : hermC τ.1 X.Gm (wv j) (wv l) = hermC τ.1 X.Gm (wv j) (d l)` using `by show hermC τ.1 X.Gm (wv j) (d l + ∑ a, (-α l a) • X.colP x τ a) = _`. Rewrite using `[hermC_add_right, hermC_sum_right]`.

Simplify using `only [hermC_smul_right, hwc, mul_zero, Finset.sum_const_zero, add_zero]`. Establish `h3 : hermC τ.1 X.Gm (wv j) (d l) = D j l - (α * B) j l` using `by show hermC τ.1 X.Gm (d j + ∑ a, (-α j a) • X.colP x τ a) (d l) = _`. Rewrite using `[hermC_add_left, hermC_sum_left, Matrix.mul_apply, sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Simplify using `only [hermC_smul_left]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun a _ => neg_mul _ _`. Rewrite using `[Matrix.sub_apply, h2, h3]`. Establish `hSH : (D - α * B).IsHermitian` using `Matrix.IsHermitian.ext fun j l => by`. Rewrite using `[hSw, hSw]`. Conclude with `hermC_conj τ.1 hG _ _`.

Establish `hli0 : LinearIndependent ℂ (fun m => FD.col (mat x τ) m)` using `Matrix.linearIndependent_cols_of_det_ne_zero hdet`. Establish `hg : Function.Injective (Sum.elim (Fin.castLE X.p0_le) gr)`. Introduce `s t hst`. Apply the tactic sequence `rcases s with a | j <;> rcases t with b | l`. Conclude with `congrArg Sum.inl (Fin.castLE_injective X.p0_le hst)`.

It suffices to derive a contradiction. Establish `h1` using `congrArg Fin.val hst`. Use `a.isLt` as an intermediate fact. Simplify using `only [Sum.elim_inl, Sum.elim_inr, gr, Fin.coe_castLE, Fin.val_mk] at h1`. Use linear arithmetic over natural numbers and integers.

It suffices to derive a contradiction. Establish `h1` using `congrArg Fin.val hst`. Use `b.isLt` as an intermediate fact. Simplify using `only [Sum.elim_inl, Sum.elim_inr, gr, Fin.coe_castLE, Fin.val_mk] at h1`. Use linear arithmetic over natural numbers and integers.

Establish `h1` using `congrArg Fin.val hst`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, gr, Fin.coe_castLE, Fin.val_mk] at h1`. Conclude with `congrArg Sum.inr (Fin.ext (by omega))`. Establish `hli` using `hli0.comp _ hg`. Establish `hS : (-(D - α * B)).PosDef`.

Use `Matrix.PosDef.of_dotProduct_mulVec_pos hSH.neg fun xv hxv => ?_` and prove the remaining obligations. Use `set W : Fin r → ℂ := ∑ j, conj (xv j) • wv j with hWdef`. Establish `hq : star xv ⬝ᵥ ((-(D - α * B)) *ᵥ xv) = -hermC τ.1 X.Gm W W`. Rewrite using `[hWdef, hermC_sum_left]`. Simplify using `only [hermC_smul_left, hermC_sum_right, hermC_smul_right, Complex.conj_conj, dotProduct, Matrix.mulVec, Matrix.neg_apply, hSw, Pi.star_apply, Finset.mul_sum]`.

Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hWc : ∀ b, hermC τ.1 X.Gm W (X.colP x τ b) = 0`. Introduce `b`. Rewrite using `[hWdef, hermC_sum_left]`. Conclude with `Finset.sum_eq_zero fun j _ => by rw [hermC_smul_left, hwc j b, mul_zero]`.

Establish `hW0 : W ≠ 0`. Introduce `hW`. Set `coef : Fin X.p0 ⊕ Fin k → ℂ` to `Sum.elim (fun a => ∑ j, conj (xv j) * -α j a) (fun j => conj (xv j))`. Establish `hsum : ∑ s, coef s • FD.col (mat x τ) (Sum.elim (Fin.castLE X.p0_le) gr s) = W`. Rewrite using `[Fintype.sum_sum_type, hWdef]`.

Simplify using `only [coef, Sum.elim_inl, Sum.elim_inr, wv, d, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul, Finset.sum_smul]`. Rewrite using `[add_comm, Finset.sum_comm]`. Both sides reduce to the same expression. Establish `h0 : ∑ s, coef s • ((fun m => FD.col (mat x τ) m) ∘ Sum.elim (Fin.castLE X.p0_le) gr) s = 0` using `hsum.trans hW`. Establish `hcoef` using `Fintype.linearIndependent_iff.1 hli coef h0`.

Apply `hxv` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Use `hcoef (Sum.inr j)` as an intermediate fact. Simplify `this` using `[coef]`. Establish `hneg` using `neg_of_perp' X τ hA hW0 hWc`.

Establish `him : (hermC τ.1 X.Gm W W).im = 0` using `Complex.conj_eq_iff_im.1 (hermC_conj τ.1 hG W W)`. Rewrite using `[hq, Complex.lt_def]`. Prove the components needed by the constructor for the conclusion. Simplify using `only [Complex.zero_re, Complex.neg_re]`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `[him]`. Establish `hSpos : 0 < (-(D - α * B)).det` using `Matrix.PosDef.det_pos hS`. Establish `hdetS : (D - α * B).det = (-1) ^ k * (-(D - α * B)).det`. Rewrite using `[Matrix.det_neg, Fintype.card_fin, ← mul_assoc, ← mul_pow]`. Evaluate the numerical expressions.

Rewrite using `[hdetS, hik, OrthonormalChartBounds.psgn_add]`. Establish `hz : A.det * ((-1) ^ k * (-(D - α * B)).det) = (((-1 : ℝ) ^ k : ℝ) : ℂ) * (A.det * (-(D - α * B)).det)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hre : 0 < (A.det * (-(D - α * B)).det).re`.

Use `(Complex.lt_def.1 (mul_pos hApos hSpos)).1` as an intermediate fact. Simplify using `using this`. Establish `h1 : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1`. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions.

Rewrite using `[hz, Complex.re_ofReal_mul, ← mul_assoc, h1, one_mul]`. Conclude with `hre`.
-/
theorem psgn_dmin_gt {x : Frame X.Ψ r} (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0)
    (hA : (X.gramPos x τ).PosDef) (k : ℕ) (hk : X.p0 + k ≤ r) (i : Fin (r + 1))
    (hik : (i : ℕ) = X.p0 + k) : 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
  classical
  have hG := X.Gm_herm
  let gr : Fin k → Fin r := fun j => ⟨X.p0 + j, by have := j.isLt; omega⟩
  let d : Fin k → Fin r → ℂ := fun j => FD.col (mat x τ) (gr j)
  let A : Matrix (Fin X.p0) (Fin X.p0) ℂ := X.gramPos x τ
  let B : Matrix (Fin X.p0) (Fin k) ℂ := fun a l => hermC τ.1 X.Gm (X.colP x τ a) (d l)
  let C : Matrix (Fin k) (Fin X.p0) ℂ := fun j b => hermC τ.1 X.Gm (d j) (X.colP x τ b)
  let D : Matrix (Fin k) (Fin k) ℂ := fun j l => hermC τ.1 X.Gm (d j) (d l)
  have hApos : 0 < A.det := Matrix.PosDef.det_pos hA
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hApos.ne'
  haveI : Invertible A := Matrix.invertibleOfIsUnitDet A hAu
  have hdm : dmin X.Gm x τ i = (Matrix.fromBlocks A B C D).det := by
    let e : Fin X.p0 ⊕ Fin k ≃ Fin (i : ℕ) := finSumFinEquiv.trans (finCongr hik.symm)
    unfold dmin lminor
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext s t
    rcases s with a | j <;> rcases t with b | l <;> rfl
  rw [hdm, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  set α : Matrix (Fin k) (Fin X.p0) ℂ := C * A⁻¹ with hαdef
  have hαA : α * A = C := by
    rw [hαdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]
  have hAab : ∀ a b, A a b = hermC τ.1 X.Gm (X.colP x τ a) (X.colP x τ b) := fun a b => by
    show X.gramPos x τ a b = _
    rw [Data.gramPos_apply]
  let wv : Fin k → Fin r → ℂ := fun j => d j + ∑ a, (-α j a) • X.colP x τ a
  have hwc : ∀ j b, hermC τ.1 X.Gm (wv j) (X.colP x τ b) = 0 := by
    intro j b
    show hermC τ.1 X.Gm (d j + ∑ a, (-α j a) • X.colP x τ a) (X.colP x τ b) = 0
    rw [hermC_add_left, hermC_sum_left]
    simp only [hermC_smul_left]
    have h1 : ∑ a, -α j a * hermC τ.1 X.Gm (X.colP x τ a) (X.colP x τ b) = -(α * A) j b := by
      rw [Matrix.mul_apply, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hAab]
      ring
    rw [h1, hαA]
    exact add_neg_cancel _
  have hSw : ∀ j l, (D - α * B) j l = hermC τ.1 X.Gm (wv j) (wv l) := by
    intro j l
    have h2 : hermC τ.1 X.Gm (wv j) (wv l) = hermC τ.1 X.Gm (wv j) (d l) := by
      show hermC τ.1 X.Gm (wv j) (d l + ∑ a, (-α l a) • X.colP x τ a) = _
      rw [hermC_add_right, hermC_sum_right]
      simp only [hermC_smul_right, hwc, mul_zero, Finset.sum_const_zero, add_zero]
    have h3 : hermC τ.1 X.Gm (wv j) (d l) = D j l - (α * B) j l := by
      show hermC τ.1 X.Gm (d j + ∑ a, (-α j a) • X.colP x τ a) (d l) = _
      rw [hermC_add_left, hermC_sum_left, Matrix.mul_apply, sub_eq_add_neg,
        ← Finset.sum_neg_distrib]
      simp only [hermC_smul_left]
      congr 1
      exact Finset.sum_congr rfl fun a _ => neg_mul _ _
    rw [Matrix.sub_apply, h2, h3]
  have hSH : (D - α * B).IsHermitian := Matrix.IsHermitian.ext fun j l => by
    rw [hSw, hSw]
    exact hermC_conj τ.1 hG _ _
  have hli0 : LinearIndependent ℂ (fun m => FD.col (mat x τ) m) :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hg : Function.Injective (Sum.elim (Fin.castLE X.p0_le) gr) := by
    intro s t hst
    rcases s with a | j <;> rcases t with b | l
    · exact congrArg Sum.inl (Fin.castLE_injective X.p0_le hst)
    · exfalso
      have h1 := congrArg Fin.val hst
      have := a.isLt
      simp only [Sum.elim_inl, Sum.elim_inr, gr, Fin.coe_castLE, Fin.val_mk] at h1
      omega
    · exfalso
      have h1 := congrArg Fin.val hst
      have := b.isLt
      simp only [Sum.elim_inl, Sum.elim_inr, gr, Fin.coe_castLE, Fin.val_mk] at h1
      omega
    · have h1 := congrArg Fin.val hst
      simp only [Sum.elim_inl, Sum.elim_inr, gr, Fin.coe_castLE, Fin.val_mk] at h1
      exact congrArg Sum.inr (Fin.ext (by omega))
  have hli := hli0.comp _ hg
  have hS : (-(D - α * B)).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hSH.neg fun xv hxv => ?_
    set W : Fin r → ℂ := ∑ j, conj (xv j) • wv j with hWdef
    have hq : star xv ⬝ᵥ ((-(D - α * B)) *ᵥ xv) = -hermC τ.1 X.Gm W W := by
      rw [hWdef, hermC_sum_left]
      simp only [hermC_smul_left, hermC_sum_right, hermC_smul_right, Complex.conj_conj,
        dotProduct, Matrix.mulVec, Matrix.neg_apply, hSw, Pi.star_apply, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Complex.star_def]
      ring
    have hWc : ∀ b, hermC τ.1 X.Gm W (X.colP x τ b) = 0 := by
      intro b
      rw [hWdef, hermC_sum_left]
      exact Finset.sum_eq_zero fun j _ => by rw [hermC_smul_left, hwc j b, mul_zero]
    have hW0 : W ≠ 0 := by
      intro hW
      let coef : Fin X.p0 ⊕ Fin k → ℂ :=
        Sum.elim (fun a => ∑ j, conj (xv j) * -α j a) (fun j => conj (xv j))
      have hsum : ∑ s, coef s • FD.col (mat x τ) (Sum.elim (Fin.castLE X.p0_le) gr s) = W := by
        rw [Fintype.sum_sum_type, hWdef]
        simp only [coef, Sum.elim_inl, Sum.elim_inr, wv, d, smul_add, Finset.sum_add_distrib,
          Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [add_comm, Finset.sum_comm]
        rfl
      have h0 : ∑ s, coef s • ((fun m => FD.col (mat x τ) m) ∘ Sum.elim (Fin.castLE X.p0_le) gr) s
          = 0 := hsum.trans hW
      have hcoef := Fintype.linearIndependent_iff.1 hli coef h0
      apply hxv
      funext j
      have := hcoef (Sum.inr j)
      simpa [coef] using this
    have hneg := neg_of_perp' X τ hA hW0 hWc
    have him : (hermC τ.1 X.Gm W W).im = 0 :=
      Complex.conj_eq_iff_im.1 (hermC_conj τ.1 hG W W)
    rw [hq, Complex.lt_def]
    constructor
    · simp only [Complex.zero_re, Complex.neg_re]
      linarith
    · simp [him]
  have hSpos : 0 < (-(D - α * B)).det := Matrix.PosDef.det_pos hS
  have hdetS : (D - α * B).det = (-1) ^ k * (-(D - α * B)).det := by
    rw [Matrix.det_neg, Fintype.card_fin, ← mul_assoc, ← mul_pow]
    norm_num
  rw [hdetS, hik, OrthonormalChartBounds.psgn_add]
  have hz : A.det * ((-1) ^ k * (-(D - α * B)).det) =
      (((-1 : ℝ) ^ k : ℝ) : ℂ) * (A.det * (-(D - α * B)).det) := by
    push_cast
    ring
  have hre : 0 < (A.det * (-(D - α * B)).det).re := by
    have := (Complex.lt_def.1 (mul_pos hApos hSpos)).1
    simpa using this
  have h1 : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hz, Complex.re_ofReal_mul, ← mul_assoc, h1, one_mul]
  exact hre

/- English proof (translation)
Rewrite using `[psgn_eq_one hip, one_mul]`. Establish `hsub : ((X.gramPos x τ).submatrix (Fin.castLE hip) (Fin.castLE hip)).PosDef` using `hA.submatrix (Fin.castLE_injective hip)`. Establish `heq : dmin X.Gm x τ i = ((X.gramPos x τ).submatrix (Fin.castLE hip) (Fin.castLE hip)).det`. Unfold `dmin lminor Data.gramPos`. Rewrite using `[Matrix.submatrix_submatrix]`.

Both sides reduce to the same expression. Rewrite using `[heq]`. Conclude with `OrthonormalChartBounds.pos_re_of_posDef hsub`.
-/
theorem psgn_dmin_le {x : Frame X.Ψ r} (τ : X.Ψ) (hA : (X.gramPos x τ).PosDef) (i : Fin (r + 1))
    (hip : (i : ℕ) ≤ X.p0) : 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
  rw [psgn_eq_one hip, one_mul]
  have hsub : ((X.gramPos x τ).submatrix (Fin.castLE hip) (Fin.castLE hip)).PosDef :=
    hA.submatrix (Fin.castLE_injective hip)
  have heq : dmin X.Gm x τ i =
      ((X.gramPos x τ).submatrix (Fin.castLE hip) (Fin.castLE hip)).det := by
    unfold dmin lminor Data.gramPos
    rw [Matrix.submatrix_submatrix]
    rfl
  rw [heq]
  exact OrthonormalChartBounds.pos_re_of_posDef hsub

/- English proof (translation)
Rewrite using `[Data.mem_dom_iff]`. Introduce `τ`. Use `⟨(h τ).1, fun i => ?_⟩` and prove the remaining obligations. Establish `hir` using `i.isLt`. Distinguish the cases in `hip : (i : ℕ) ≤ X.p0`.

Conclude with `psgn_dmin_le X τ (h τ).2 i hip`. Take `⟨k, hk⟩ : ∃ k, (i : ℕ) = X.p0 + k` from `⟨(i : ℕ) - X.p0, by omega⟩`. Conclude with `psgn_dmin_gt X τ (h τ).1 (h τ).2 k (by omega) i hk`.
-/
theorem mem_dom_of_gramPos {x : Frame X.Ψ r}
    (h : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ (X.gramPos x τ).PosDef) : x ∈ X.dom := by
  rw [Data.mem_dom_iff]
  intro τ
  refine ⟨(h τ).1, fun i => ?_⟩
  have hir := i.isLt
  by_cases hip : (i : ℕ) ≤ X.p0
  · exact psgn_dmin_le X τ (h τ).2 i hip
  · obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = X.p0 + k := ⟨(i : ℕ) - X.p0, by omega⟩
    exact psgn_dmin_gt X τ (h τ).1 (h τ).2 k (by omega) i hk

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
