import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix MvPolynomial Filter Topology
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.FockGauss

section Mat

open scoped MatrixOrder in

/- English proof (translation)
Take `⟨B, rfl⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg`. Establish `: ∑ k, ∑ l, (star B * B) k l * inner ℂ (u k) (u l) = ∑ m, inner ℂ (∑ k, B m k • u k) (∑ l, B m l • u l)`. Simplify using `only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Matrix.mul_apply, Finset.sum_mul, Matrix.star_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[Finset.sum_comm (γ := n) (s := Finset.univ) (t := Finset.univ) (f := fun x m => star (B m x) * B m _ * inner ℂ (u x) (u _))]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [RCLike.star_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Complex.re_sum]`.

Conclude with `Finset.sum_nonneg fun m _ => inner_self_nonneg (𝕜 := ℂ)`.
-/
theorem re_sum_inner_nonneg {n H : Type} [Fintype n] [DecidableEq n] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) (u : n → H) :
    0 ≤ (∑ k, ∑ l, M k l * inner ℂ (u k) (u l)).re := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  have : ∑ k, ∑ l, (star B * B) k l * inner ℂ (u k) (u l) =
      ∑ m, inner ℂ (∑ k, B m k • u k) (∑ l, B m l • u l) := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Matrix.mul_apply, Finset.sum_mul,
      Matrix.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (γ := n) (s := Finset.univ) (t := Finset.univ)
      (f := fun x m => star (B m x) * B m _ * inner ℂ (u x) (u _))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [RCLike.star_def]; ring
  rw [this, Complex.re_sum]
  exact Finset.sum_nonneg fun m _ => inner_self_nonneg (𝕜 := ℂ)

/- English proof (translation)
Establish `h` using `re_sum_inner_nonneg hM u`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Complex.sub_re, sub_nonneg] at h`. Use `h.trans_eq ?_` and prove the remaining obligations. Rewrite using `[Complex.re_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.re_ofReal_mul, ← inner_self_eq_norm_sq (𝕜 := ℂ)]`. Both sides reduce to the same expression.
-/
theorem re_sum_inner_le {n H : Type} [Fintype n] [DecidableEq n] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {M : Matrix n n ℂ} {r : ℝ} (hM : ((r : ℂ) • (1 : Matrix n n ℂ) - M).PosSemidef) (u : n → H) :
    (∑ k, ∑ l, M k l * inner ℂ (u k) (u l)).re ≤ r * ∑ k, ‖u k‖ ^ 2 := by
  have h := re_sum_inner_nonneg hM u
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Complex.sub_re,
    sub_nonneg] at h
  refine h.trans_eq ?_
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.re_ofReal_mul, ← inner_self_eq_norm_sq (𝕜 := ℂ)]; rfl

open scoped MatrixOrder in

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ, h1⟩ : ∃ δ : ℝ, 0 < δ ∧ (1 - Aᴴ * A - (δ : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ)).PosSemidef := by`. Break down `Nat.eq_zero_or_pos Q with rfl | hN` into its components or cases. Conclude with `⟨1, one_pos, by rw [Subsingleton.elim (_ - _) 0]; exact PosSemidef.zero⟩`. Use `haveI : Nonempty (Fin Q) := ⟨⟨0, hN⟩⟩`. Take `⟨r, hr, hle⟩` from `(CFC.exists_pos_algebraMap_le_iff (A := Matrix (Fin Q) (Fin Q) ℂ) h.isStrictlyPositive.isSelfAdjoint).2 fun x hx => h.isStrictlyPositive.spectrum_pos hx`.

Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Use `Matrix.le_iff.mp hle` as an intermediate fact. Rewrite `this` using `[Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]`. Then use the resulting hypothesis. Use `set r : ℝ := max (1 - δ) (1 / 2) with hr`. Establish `hr0 : 0 < r` using `lt_max_of_lt_right (by norm_num)`.

Establish `hr0' : (0 : ℂ) < r` using `by exact_mod_cast hr0`. Establish `h2 : ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ) - Aᴴ * A).PosSemidef`. Establish `h3 : (((r - (1 - δ) : ℝ) : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ)).PosSemidef` using `PosSemidef.one.smul (by exact_mod_cast sub_nonneg.2 (le_max_left _ _))`. Use `h1.add h3 using 1` and compare the differences between its conclusion and the goal. Use `push_cast`.

Use `module`. Use `⟨r, hr0, max_lt (by linarith) (by norm_num), h2, ?_⟩` and prove the remaining obligations. Establish `hD : ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ)).PosDef` using `PosDef.one.smul hr0'`. Use `letI := hD.isUnit.invertible`. Use `letI : Invertible (1 : Matrix (Fin P) (Fin P) ℂ) := invertibleOne`.

Establish `h4` using `(PosDef.fromBlocks₁₁ A ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ)) PosDef.one).2 (by simpa using h2)`. Establish `h5` using `((PosDef.fromBlocks₂₂ 1 A hD).1 h4).smul hr0'.le`. Establish `h6 : ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ))⁻¹ = (r : ℂ)⁻¹ • 1` using `Matrix.inv_eq_right_inv (by rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hr0'.ne', one_smul])`. Rewrite `h5` using `[h6, smul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul, mul_inv_cancel₀ hr0'.ne', one_smul]`. Then use the resulting hypothesis.
-/
theorem exists_bound {P Q : ℕ} {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ) - Aᴴ * A).PosSemidef ∧
      ((r : ℂ) • (1 : Matrix (Fin P) (Fin P) ℂ) - A * Aᴴ).PosSemidef := by
  obtain ⟨δ, hδ, h1⟩ : ∃ δ : ℝ, 0 < δ ∧ (1 - Aᴴ * A - (δ : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ)).PosSemidef := by
    rcases Nat.eq_zero_or_pos Q with rfl | hN
    · exact ⟨1, one_pos, by rw [Subsingleton.elim (_ - _) 0]; exact PosSemidef.zero⟩
    haveI : Nonempty (Fin Q) := ⟨⟨0, hN⟩⟩
    obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff (A := Matrix (Fin Q) (Fin Q) ℂ)
      h.isStrictlyPositive.isSelfAdjoint).2 fun x hx => h.isStrictlyPositive.spectrum_pos hx
    refine ⟨r, hr, ?_⟩
    have := Matrix.le_iff.mp hle
    rwa [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] at this
  set r : ℝ := max (1 - δ) (1 / 2) with hr
  have hr0 : 0 < r := lt_max_of_lt_right (by norm_num)
  have hr0' : (0 : ℂ) < r := by exact_mod_cast hr0
  have h2 : ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ) - Aᴴ * A).PosSemidef := by
    have h3 : (((r - (1 - δ) : ℝ) : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ)).PosSemidef :=
      PosSemidef.one.smul (by exact_mod_cast sub_nonneg.2 (le_max_left _ _))
    convert h1.add h3 using 1
    push_cast
    module
  refine ⟨r, hr0, max_lt (by linarith) (by norm_num), h2, ?_⟩
  have hD : ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ)).PosDef := PosDef.one.smul hr0'
  letI := hD.isUnit.invertible
  letI : Invertible (1 : Matrix (Fin P) (Fin P) ℂ) := invertibleOne
  have h4 := (PosDef.fromBlocks₁₁ A ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ)) PosDef.one).2 (by simpa using h2)
  have h5 := ((PosDef.fromBlocks₂₂ 1 A hD).1 h4).smul hr0'.le
  have h6 : ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ))⁻¹ = (r : ℂ)⁻¹ • 1 :=
    Matrix.inv_eq_right_inv (by rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hr0'.ne', one_smul])
  rwa [h6, smul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul, mul_inv_cancel₀ hr0'.ne',
    one_smul] at h5

end Mat

section General

variable {σ : Type} [DecidableEq σ] (F : Fock σ)

/- English proof (translation)
Introduce `α β` and use `by convert F.fockIP α β`.
-/
theorem isFockIP : GlobalTheory.FockAlg.IsFockIP F.ι := fun α β => by convert F.fockIP α β

def DegLt (k : ℕ) (f : MvPolynomial σ ℂ) : Prop := ∀ α : σ →₀ ℕ, k ≤ α.degree → coeff α f = 0

omit [DecidableEq σ] in
/- English proof (translation)
Use extensionality with `α`. Simplify using `using h α (Nat.zero_le _)`.
-/
theorem DegLt.eq_zero {f : MvPolynomial σ ℂ} (h : DegLt 0 f) : f = 0 := by
  ext α; simpa using h α (Nat.zero_le _)

omit [DecidableEq σ] in
/- English proof (translation)
Introduce `α hα` and use `h α (hk.trans hα)`.
-/
theorem DegLt.mono {k k' : ℕ} {f : MvPolynomial σ ℂ} (h : DegLt k f) (hk : k ≤ k') : DegLt k' f :=
  fun α hα => h α (hk.trans hα)

omit [DecidableEq σ] in
/- English proof (translation)
Introduce `α hα` and use `by rw [coeff_pderiv, h _ (by rw [map_add, Finsupp.degree_single]; omega), zero_mul]`.
-/
theorem DegLt.pderiv {k : ℕ} {f : MvPolynomial σ ℂ} (h : DegLt (k + 1) f) (l : σ) : DegLt k (pderiv l f) :=
  fun α hα => by rw [coeff_pderiv, h _ (by rw [map_add, Finsupp.degree_single]; omega), zero_mul]

/- English proof (translation)
Introduce `α hα` and use `by rw [coeff_X_mul'] split_ifs with hl · refine h _ ?_ have e : α - Finsupp.single l 1 + Finsupp.single l 1 = α := tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hl))) have := congrArg Finsupp.degree e rw [map_add, Finsupp.degree_sin …`.
-/
theorem DegLt.X_mul {k : ℕ} {f : MvPolynomial σ ℂ} (h : DegLt k f) (l : σ) : DegLt (k + 1) (X l * f) :=
  fun α hα => by
    rw [coeff_X_mul']
    split_ifs with hl
    · refine h _ ?_
      have e : α - Finsupp.single l 1 + Finsupp.single l 1 = α :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hl)))
      have := congrArg Finsupp.degree e
      rw [map_add, Finsupp.degree_single] at this
      omega
    · rfl

omit [DecidableEq σ] in
/- English proof (translation)
Introduce `α hα` and use `by rw [coeff_smul, h α hα, smul_zero]`.
-/
theorem DegLt.smul {k : ℕ} {f : MvPolynomial σ ℂ} (h : DegLt k f) (c : ℂ) : DegLt k (c • f) :=
  fun α hα => by rw [coeff_smul, h α hα, smul_zero]

omit [DecidableEq σ] in
/- English proof (translation)
Introduce `α hα` and use `by rw [coeff_add, h α hα, h' α hα, add_zero]`.
-/
theorem DegLt.add {k : ℕ} {f g : MvPolynomial σ ℂ} (h : DegLt k f) (h' : DegLt k g) : DegLt k (f + g) :=
  fun α hα => by rw [coeff_add, h α hα, h' α hα, add_zero]

omit [DecidableEq σ] in
/- English proof (translation)
Introduce `α hα` and use `by rw [coeff_sum]; exact Finset.sum_eq_zero fun i _ => h i α hα`.
-/
theorem DegLt.sum {k : ℕ} {I : Type} [Fintype I] {f : I → MvPolynomial σ ℂ} (h : ∀ i, DegLt k (f i)) :
    DegLt k (∑ i, f i) :=
  fun α hα => by rw [coeff_sum]; exact Finset.sum_eq_zero fun i _ => h i α hα

/- English proof (translation)
Use `conv_lhs => rw [f.as_sum]`. Rewrite using `[map_sum, sum_inner]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Establish `e : (monomial α (coeff α f) : MvPolynomial σ ℂ) = coeff α f • monomial α 1` using `by simp [smul_monomial]`. Rewrite using `[e, map_smul, inner_smul_left, hasCoeff_coe F g α, GlobalTheory.FockSeq.mfact_cast, MvPolynomial.coeff_coe]`.
-/
theorem inner_eq_sum (f g : MvPolynomial σ ℂ) :
    inner ℂ (F.ι f) (F.ι g) =
      ∑ α ∈ f.support, (starRingEnd ℂ) (coeff α f) * ((GlobalTheory.FockSeq.mfact α : ℂ) * coeff α g) := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun α _ => ?_
  have e : (monomial α (coeff α f) : MvPolynomial σ ℂ) = coeff α f • monomial α 1 := by simp [smul_monomial]
  rw [e, map_smul, inner_smul_left, hasCoeff_coe F g α, GlobalTheory.FockSeq.mfact_cast, MvPolynomial.coeff_coe]

/- English proof (translation)
Rewrite using `[coeff_X_mul']`. Use `split_ifs with hl`. Establish `h0` using `Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hl)`. Rewrite using `[coeff_pderiv, tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h0), mul_comm]`. Simplify using `[Nat.cast_sub h0]`.

Simplify using `[Finsupp.notMem_support_iff.1 hl]`.
-/
theorem coeff_X_mul_pderiv (l : σ) (f : MvPolynomial σ ℂ) (α : σ →₀ ℕ) :
    coeff α (X l * pderiv l f) = (α l : ℂ) * coeff α f := by
  rw [coeff_X_mul']
  split_ifs with hl
  · have h0 := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hl)
    rw [coeff_pderiv, tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h0), mul_comm]
    simp [Nat.cast_sub h0]
  · simp [Finsupp.notMem_support_iff.1 hl]

/- English proof (translation)
Establish `h1 : ∀ l, ‖F.ι (pderiv l f)‖ ^ 2 = ∑ α ∈ f.support, (α l : ℝ) * (GlobalTheory.FockSeq.mfact α * Complex.normSq (coeff α f))` using `fun l => by`. Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ), GlobalTheory.Oscillator.inner_pderiv (isFockIP F), inner_eq_sum, map_sum]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_X_mul_pderiv]`. Simplify using `[Complex.normSq_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ‖F.ι f‖ ^ 2 = ∑ α ∈ f.support, (GlobalTheory.FockSeq.mfact α * Complex.normSq (coeff α f))`. Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ), inner_eq_sum, map_sum]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Simplify using `[Complex.normSq_apply]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h1, h2]`. Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_le_sum fun α hα => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul]`.

Use `mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))` and prove the remaining obligations. Rewrite using `[← Nat.cast_sum, ← Finsupp.degree_eq_sum, Nat.cast_le]`. Conclude with `le_of_not_ge fun hk => mem_support_iff.1 hα (h α hk)`.
-/
theorem sum_sq_pderiv_le [Fintype σ] {k : ℕ} {f : MvPolynomial σ ℂ} (h : DegLt k f) :
    ∑ l, ‖F.ι (pderiv l f)‖ ^ 2 ≤ k * ‖F.ι f‖ ^ 2 := by
  have h1 : ∀ l, ‖F.ι (pderiv l f)‖ ^ 2 =
      ∑ α ∈ f.support, (α l : ℝ) * (GlobalTheory.FockSeq.mfact α * Complex.normSq (coeff α f)) := fun l => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), GlobalTheory.Oscillator.inner_pderiv (isFockIP F), inner_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [coeff_X_mul_pderiv]
    simp [Complex.normSq_apply]; ring
  have h2 : ‖F.ι f‖ ^ 2 = ∑ α ∈ f.support, (GlobalTheory.FockSeq.mfact α * Complex.normSq (coeff α f)) := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp [Complex.normSq_apply]; ring
  simp only [h1, h2]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun α hα => ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
  rw [← Nat.cast_sum, ← Finsupp.degree_eq_sum, Nat.cast_le]
  exact le_of_not_ge fun hk => mem_support_iff.1 hα (h α hk)

/- English proof (translation)
Rewrite using `[GlobalTheory.Oscillator.inner_X_mul (isFockIP F), GlobalTheory.Oscillator.inner_pderiv (isFockIP F), Derivation.leibniz, map_add, inner_add_right, smul_eq_mul, smul_eq_mul, pderiv_X, Pi.single_apply]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.
-/
theorem inner_X_X (a b : σ) (f g : MvPolynomial σ ℂ) :
    inner ℂ (F.ι (X a * f)) (F.ι (X b * g)) =
      inner ℂ (F.ι (pderiv b f)) (F.ι (pderiv a g)) + if a = b then inner ℂ (F.ι f) (F.ι g) else 0 := by
  rw [GlobalTheory.Oscillator.inner_X_mul (isFockIP F), GlobalTheory.Oscillator.inner_pderiv (isFockIP F), Derivation.leibniz,
    map_add, inner_add_right, smul_eq_mul, smul_eq_mul, pderiv_X, Pi.single_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

/- English proof (translation)
Establish `h1 : ‖F.ι (X l * f)‖ ^ 2 = ‖F.ι (pderiv l f)‖ ^ 2 + ‖F.ι f‖ ^ 2`. Simplify using `only [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_X_X, if_true, map_add]`. Establish `h2 : ‖F.ι (pderiv l f)‖ ^ 2 ≤ k * ‖F.ι f‖ ^ 2` using `(Finset.single_le_sum (f := fun l => ‖F.ι (pderiv l f)‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ l)).trans (sum_sq_pderiv_le F h)`. Use `(abs_le_of_sq_le_sq' ?_ (by positivity)).2` and prove the remaining obligations. Rewrite using `[mul_pow, Real.sq_sqrt (by positivity)]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_X_mul_le [Fintype σ] {k : ℕ} {f : MvPolynomial σ ℂ} (h : DegLt k f) (l : σ) :
    ‖F.ι (X l * f)‖ ≤ √(k + 1) * ‖F.ι f‖ := by
  have h1 : ‖F.ι (X l * f)‖ ^ 2 = ‖F.ι (pderiv l f)‖ ^ 2 + ‖F.ι f‖ ^ 2 := by
    simp only [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_X_X, if_true, map_add]
  have h2 : ‖F.ι (pderiv l f)‖ ^ 2 ≤ k * ‖F.ι f‖ ^ 2 :=
    (Finset.single_le_sum (f := fun l => ‖F.ι (pderiv l f)‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ l)).trans (sum_sq_pderiv_le F h)
  refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  linarith

end General

section Quad

variable {P Q : ℕ} (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ)

def quadMul (f : MvPolynomial (Ix P Q) ℂ) : MvPolynomial (Ix P Q) ℂ :=
  ∑ i, ∑ j, A i j • (X (Sum.inl i) * (X (Sum.inr j) * f))

def quadDer (f : MvPolynomial (Ix P Q) ℂ) : MvPolynomial (Ix P Q) ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (A i j) • pderiv (Sum.inr j) (pderiv (Sum.inl i) f)

/- English proof (translation)
Simplify using `only [quadMul, quadDer, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, GlobalTheory.Oscillator.inner_X_mul (isFockIP F)]`.
-/
theorem inner_quadMul (f g : MvPolynomial (Ix P Q) ℂ) :
    inner ℂ (F.ι (quadMul A f)) (F.ι g) = inner ℂ (F.ι f) (F.ι (quadDer A g)) := by
  simp only [quadMul, quadDer, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    GlobalTheory.Oscillator.inner_X_mul (isFockIP F)]

/- English proof (translation)
Establish `e : ∀ (a : Fin P) (b : Fin Q), pderiv (Sum.inl a : Ix P Q) ((X (Sum.inr b) : MvPolynomial (Ix P Q) ℂ) * f) = X (Sum.inr b) * pderiv (Sum.inl a) f` using `fun a b => by`. Rewrite using `[Derivation.leibniz, pderiv_X_of_ne (by simp)]; simp`. Rewrite using `[inner_X_X, e, e, inner_X_X, inner_X_X]`. Simplify using `only [Sum.inl.injEq, Sum.inr.injEq]`. Apply the tactic sequence `split_ifs <;> simp [add_assoc]`.
-/
theorem inner_XX_XX (i k : Fin P) (j l : Fin Q) (f : MvPolynomial (Ix P Q) ℂ) :
    inner ℂ (F.ι (X (Sum.inl i) * (X (Sum.inr j) * f))) (F.ι (X (Sum.inl k) * (X (Sum.inr l) * f))) =
      inner ℂ (F.ι (pderiv (Sum.inr l) (pderiv (Sum.inl k) f))) (F.ι (pderiv (Sum.inr j) (pderiv (Sum.inl i) f))) +
      (if j = l then inner ℂ (F.ι (pderiv (Sum.inl k) f)) (F.ι (pderiv (Sum.inl i) f)) else 0) +
      (if i = k then inner ℂ (F.ι (pderiv (Sum.inr l) f)) (F.ι (pderiv (Sum.inr j) f)) else 0) +
      (if i = k then if j = l then inner ℂ (F.ι f) (F.ι f) else 0 else 0) := by
  have e : ∀ (a : Fin P) (b : Fin Q), pderiv (Sum.inl a : Ix P Q) ((X (Sum.inr b) : MvPolynomial (Ix P Q) ℂ) * f) =
      X (Sum.inr b) * pderiv (Sum.inl a) f := fun a b => by
    rw [Derivation.leibniz, pderiv_X_of_ne (by simp)]; simp
  rw [inner_X_X, e, e, inner_X_X, inner_X_X]
  simp only [Sum.inl.injEq, Sum.inr.injEq]
  split_ifs <;> simp [add_assoc]

/- English proof (translation)
Simplify using `only [quadMul, quadDer, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, inner_XX_XX, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_c …`. Use `congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_` and prove the remaining obligations. Repeatedly rewrite using `[← Fintype.sum_prod_type']`. Conclude with `Fintype.sum_bijective (fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1)) (Function.Involutive.bijective fun _ => rfl) _ _ fun _ => mul_left_comm _ _ _`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, Complex.mul_conj]`.
-/
theorem inner_quadMul_self (f : MvPolynomial (Ix P Q) ℂ) :
    inner ℂ (F.ι (quadMul A f)) (F.ι (quadMul A f)) = inner ℂ (F.ι (quadDer A f)) (F.ι (quadDer A f)) +
      ∑ k, ∑ i, (A * Aᴴ) k i * inner ℂ (F.ι (pderiv (Sum.inl k) f)) (F.ι (pderiv (Sum.inl i) f)) +
      ∑ l, ∑ j, (Aᴴ * A)ᵀ l j * inner ℂ (F.ι (pderiv (Sum.inr l) f)) (F.ι (pderiv (Sum.inr j) f)) +
      ((∑ i, ∑ j, Complex.normSq (A i j) : ℝ) : ℂ) * inner ℂ (F.ι f) (F.ι f) := by
  simp only [quadMul, quadDer, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    inner_XX_XX, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Complex.ofReal_sum, Complex.conj_conj,
    RCLike.star_def]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · simp_rw [← Fintype.sum_prod_type']
    exact Fintype.sum_bijective (fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1))
      (Function.Involutive.bijective fun _ => rfl) _ _ fun _ => mul_left_comm _ _ _
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    rw [← mul_assoc, Complex.mul_conj]

/- English proof (translation)
Use `set T : ℝ := ∑ i, ∑ j, Complex.normSq (A i j) with hT`. Establish `hT0 : 0 ≤ T` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _`. Proceed by induction on `n with`. Consider the case `zero => intro f hf`. Simplify using `[hf.eq_zero, quadMul]`.

Consider the case `succ n ih`. Introduce `f hf`. Establish `hD : DegLt (2 * n) (quadDer A f)` using `DegLt.sum fun i => DegLt.sum fun j => ((DegLt.pderiv (k := 2 * n + 1) hf _).pderiv _).smul _`. Establish `hc : 0 ≤ n * T + r * (n * (n + 1))` using `by positivity`. Establish `e1 : ‖F.ι (quadDer A f)‖ ≤ √(n * T + r * (n * (n + 1))) * ‖F.ι f‖`.

It suffices to establish `h : ‖F.ι (quadDer A f)‖ * ‖F.ι (quadDer A f)‖ ≤ √(n * T + r * (n * (n + 1))) * ‖F.ι f‖ * ‖F.ι (quadDer A f)‖ by`. Break down `(norm_nonneg (F.ι (quadDer A f))).eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0]`. Check the signs of the components of the expression. Conclude with `le_of_mul_le_mul_right h h0`.

Rewrite using `[← inner_self_eq_norm_mul_norm (𝕜 := ℂ), ← inner_quadMul]`. Use `(re_inner_le_norm _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : ‖F.ι (quadDer A f)‖ ^ 2 ≤ (n * T + r * (n * (n + 1))) * ‖F.ι f‖ ^ 2`. Use `pow_le_pow_left₀ (norm_nonneg _) e1 2` as an intermediate fact.

Rewrite `this` using `[mul_pow, Real.sq_sqrt hc]`. Then use the resulting hypothesis. Establish `e3` using `re_sum_inner_le h2 fun k => F.ι (pderiv (Sum.inl k) f)`. Establish `e4` using `re_sum_inner_le (M := (Aᴴ * A)ᵀ) (r := r) (by simpa using h1.transpose) fun k => F.ι (pderiv (Sum.inr k) f)`. Establish `e5` using `mul_le_mul_of_nonneg_left (sum_sq_pderiv_le F hf) hr`. Rewrite `e5` using `[Fintype.sum_sum_type]`.

Establish `e6` using `congrArg Complex.re (inner_quadMul_self F A f)`. Establish `e7 : ∀ v : F.H, (inner ℂ v v).re = ‖v‖ ^ 2` using `fun v => inner_self_eq_norm_sq (𝕜 := ℂ) v`. Rewrite `e6` using `[Complex.add_re, Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, e7, e7, e7, ← hT]`. Use `(abs_le_of_sq_le_sq' ?_ (by positivity)).2` and prove the remaining obligations. Rewrite using `[mul_pow, Real.sq_sqrt (by positivity), e6]`.

Move the coercions through the operations in `at e5 ⊢`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_quadMul_le {r : ℝ} (hr : 0 ≤ r)
    (h1 : ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ) - Aᴴ * A).PosSemidef)
    (h2 : ((r : ℂ) • (1 : Matrix (Fin P) (Fin P) ℂ) - A * Aᴴ).PosSemidef) (n : ℕ) :
    ∀ f, DegLt (2 * n) f →
      ‖F.ι (quadMul A f)‖ ≤ √(n * (∑ i, ∑ j, Complex.normSq (A i j)) + r * (n * (n + 1))) * ‖F.ι f‖ := by
  set T : ℝ := ∑ i, ∑ j, Complex.normSq (A i j) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  induction n with
  | zero => intro f hf; simp [hf.eq_zero, quadMul]
  | succ n ih =>
    intro f hf
    have hD : DegLt (2 * n) (quadDer A f) :=
      DegLt.sum fun i => DegLt.sum fun j => ((DegLt.pderiv (k := 2 * n + 1) hf _).pderiv _).smul _
    have hc : 0 ≤ n * T + r * (n * (n + 1)) := by positivity
    have e1 : ‖F.ι (quadDer A f)‖ ≤ √(n * T + r * (n * (n + 1))) * ‖F.ι f‖ := by
      suffices h : ‖F.ι (quadDer A f)‖ * ‖F.ι (quadDer A f)‖ ≤
          √(n * T + r * (n * (n + 1))) * ‖F.ι f‖ * ‖F.ι (quadDer A f)‖ by
        rcases (norm_nonneg (F.ι (quadDer A f))).eq_or_lt with h0 | h0
        · rw [← h0]; positivity
        · exact le_of_mul_le_mul_right h h0
      rw [← inner_self_eq_norm_mul_norm (𝕜 := ℂ), ← inner_quadMul]
      refine (re_inner_le_norm _ _).trans ?_
      calc _ ≤ √(n * T + r * (n * (n + 1))) * ‖F.ι (quadDer A f)‖ * ‖F.ι f‖ :=
            mul_le_mul_of_nonneg_right (ih _ hD) (norm_nonneg _)
        _ = _ := by ring
    have e2 : ‖F.ι (quadDer A f)‖ ^ 2 ≤ (n * T + r * (n * (n + 1))) * ‖F.ι f‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) e1 2
      rwa [mul_pow, Real.sq_sqrt hc] at this
    have e3 := re_sum_inner_le h2 fun k => F.ι (pderiv (Sum.inl k) f)
    have e4 := re_sum_inner_le (M := (Aᴴ * A)ᵀ) (r := r) (by simpa using h1.transpose)
      fun k => F.ι (pderiv (Sum.inr k) f)
    have e5 := mul_le_mul_of_nonneg_left (sum_sq_pderiv_le F hf) hr
    rw [Fintype.sum_sum_type] at e5
    have e6 := congrArg Complex.re (inner_quadMul_self F A f)
    have e7 : ∀ v : F.H, (inner ℂ v v).re = ‖v‖ ^ 2 := fun v => inner_self_eq_norm_sq (𝕜 := ℂ) v
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, e7, e7, e7, ← hT] at e6
    refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
    rw [mul_pow, Real.sq_sqrt (by positivity), e6]
    push_cast at e5 ⊢
    nlinarith

variable (x : Ix P Q → ℂ)

/- English proof (translation)
Simplify using `only [gaussPoly, quadMul, add_mul, Finset.sum_mul, smul_eq_C_mul, mul_assoc]`.
-/
theorem gaussPoly_mul (f : MvPolynomial (Ix P Q) ℂ) :
    gaussPoly A x * f = quadMul A f + ∑ l, x l • (X l * f) := by
  simp only [gaussPoly, quadMul, add_mul, Finset.sum_mul, smul_eq_C_mul, mul_assoc]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `α hα`. Rewrite using `[pow_zero, coeff_one, if_neg]`. Introduce and unpack `rfl`.

Simplify using `at hα`. Consider the case `succ n ih`. Rewrite using `[pow_succ', gaussPoly_mul]`. Conclude with `(DegLt.sum fun i => DegLt.sum fun j => ((ih.X_mul _).X_mul _).smul _).add (DegLt.sum fun l => ((ih.X_mul _).mono (by omega)).smul _)`.
-/
theorem degLt_pow (n : ℕ) : DegLt (2 * n + 1) (gaussPoly A x ^ n) := by
  induction n with
  | zero =>
    intro α hα
    rw [pow_zero, coeff_one, if_neg]
    rintro rfl
    simp at hα
  | succ n ih =>
    rw [pow_succ', gaussPoly_mul]
    exact (DegLt.sum fun i => DegLt.sum fun j => ((ih.X_mul _).X_mul _).smul _).add
      (DegLt.sum fun l => ((ih.X_mul _).mono (by omega)).smul _)

/- English proof (translation)
Take `⟨r, hr0, hr1, h1, h2⟩` from `exists_bound h`. Use `set T : ℝ := ∑ i, ∑ j, Complex.normSq (A i j) with hT`. Establish `hT0 : 0 ≤ T` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _`. Use `set C : ℝ := ∑ l, ‖x l‖ with hC`. Set `g : ℝ → ℝ` to `fun u => √(u * T + r * (1 + u)) + C * √(2 * u + u ^ 2)`.

Establish `hg : Continuous g` using `by fun_prop`. Establish `hg0 : g 0 < 1` using `by simpa [g, Real.sqrt_lt' one_pos] using hr1`. Take `⟨s, hs0, hs1⟩` from `exists_between hg0`. Establish `hev` using `((hg.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat).eventually_lt_const hs0`. Use `summable_of_ratio_norm_eventually_le hs1 (hev.mono fun n hn => ?_)` and prove the remaining obligations.

Establish `hd : DegLt (2 * (n + 1)) (gaussPoly A x ^ n)` using `(degLt_pow A x n).mono (by omega)`. Establish `hm : (0 : ℝ) < n + 1` using `by positivity`. Establish `b1` using `norm_quadMul_le F A hr0.le h1 h2 (n + 1) _ hd`. Establish `b2 : ‖F.ι (∑ l, x l • (X l * gaussPoly A x ^ n))‖ ≤ C * (√(((2 * (n + 1) : ℕ) : ℝ) + 1) * ‖F.ι (gaussPoly A x ^ n)‖)`. Rewrite using `[map_sum, hC, Finset.sum_mul]`.

Use `norm_sum_le_of_le _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, norm_smul]`. Conclude with `mul_le_mul_of_nonneg_left (norm_X_mul_le F hd l) (norm_nonneg _)`. Establish `s1 : √(((n + 1 : ℕ) : ℝ) * T + r * (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))) = (n + 1) * √(1 / (n + 1) * T + r * (1 + 1 / (n + 1)))`. Rewrite using `[← Real.sqrt_sq hm.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm.le]`.

Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `s2 : √(((2 * (n + 1) : ℕ) : ℝ) + 1) = (n + 1) * √(2 * (1 / (n + 1)) + (1 / (n + 1)) ^ 2)`. Rewrite using `[← Real.sqrt_sq hm.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm.le]`.

Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `b3 : ‖F.ι (gaussPoly A x ^ (n + 1))‖ ≤ (n + 1) * (s * ‖F.ι (gaussPoly A x ^ n)‖)`. Rewrite using `[pow_succ', gaussPoly_mul, map_add]`.

Use `(norm_add_le_of_le b1 b2).trans ?_` and prove the remaining obligations. Rewrite using `[← hT, s1, s2]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_smul, norm_smul, norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast, Nat.factorial_succ]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem summable_pow (h : (1 - Aᴴ * A).PosDef) :
    Summable fun n : ℕ => (n.factorial : ℂ)⁻¹ • F.ι (gaussPoly A x ^ n) := by
  obtain ⟨r, hr0, hr1, h1, h2⟩ := exists_bound h
  set T : ℝ := ∑ i, ∑ j, Complex.normSq (A i j) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  set C : ℝ := ∑ l, ‖x l‖ with hC
  let g : ℝ → ℝ := fun u => √(u * T + r * (1 + u)) + C * √(2 * u + u ^ 2)
  have hg : Continuous g := by fun_prop
  have hg0 : g 0 < 1 := by simpa [g, Real.sqrt_lt' one_pos] using hr1
  obtain ⟨s, hs0, hs1⟩ := exists_between hg0
  have hev := ((hg.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat).eventually_lt_const hs0
  refine summable_of_ratio_norm_eventually_le hs1 (hev.mono fun n hn => ?_)
  have hd : DegLt (2 * (n + 1)) (gaussPoly A x ^ n) := (degLt_pow A x n).mono (by omega)
  have hm : (0 : ℝ) < n + 1 := by positivity
  have b1 := norm_quadMul_le F A hr0.le h1 h2 (n + 1) _ hd
  have b2 : ‖F.ι (∑ l, x l • (X l * gaussPoly A x ^ n))‖ ≤
      C * (√(((2 * (n + 1) : ℕ) : ℝ) + 1) * ‖F.ι (gaussPoly A x ^ n)‖) := by
    rw [map_sum, hC, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun l _ => ?_
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_X_mul_le F hd l) (norm_nonneg _)
  have s1 : √(((n + 1 : ℕ) : ℝ) * T + r * (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))) =
      (n + 1) * √(1 / (n + 1) * T + r * (1 + 1 / (n + 1))) := by
    rw [← Real.sqrt_sq hm.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm.le]
    congr 1; push_cast; field_simp
  have s2 : √(((2 * (n + 1) : ℕ) : ℝ) + 1) = (n + 1) * √(2 * (1 / (n + 1)) + (1 / (n + 1)) ^ 2) := by
    rw [← Real.sqrt_sq hm.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm.le]
    congr 1; push_cast; field_simp
  have b3 : ‖F.ι (gaussPoly A x ^ (n + 1))‖ ≤ (n + 1) * (s * ‖F.ι (gaussPoly A x ^ n)‖) := by
    rw [pow_succ', gaussPoly_mul, map_add]
    refine (norm_add_le_of_le b1 b2).trans ?_
    rw [← hT, s1, s2]
    calc _ = (n + 1) * (g (1 / (n + 1)) * ‖F.ι (gaussPoly A x ^ n)‖) := by simp only [g]; ring
      _ ≤ _ := by gcongr; exact hn.le
  rw [norm_smul, norm_smul, norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast, Nat.factorial_succ]
  calc _ ≤ ((((n + 1) * n.factorial : ℕ) : ℝ))⁻¹ * ((n + 1) * (s * ‖F.ι (gaussPoly A x ^ n)‖)) := by gcongr
    _ = _ := by push_cast; field_simp

end Quad

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro α hα`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`. Introduce `α hα`.

Rewrite using `[pow_succ, coeff_mul]`. Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations. Establish `e` using `congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.1 hp)`. Rewrite `e` using `[map_add]`. Distinguish the cases in `h0 : p.2 = 0`.

Rewrite using `[h0, hq, mul_zero]`. Establish `: p.2.degree ≠ 0` using `fun h => h0 ((Finsupp.degree_eq_zero_iff _).1 h)`. Rewrite using `[ih _ (by omega), zero_mul]`.
-/
theorem coeff_pow_eq_zero {σ : Type} {q : MvPolynomial σ ℂ} (hq : coeff 0 q = 0) (n : ℕ) :
    ∀ α : σ →₀ ℕ, α.degree < n → coeff α (q ^ n) = 0 := by
  classical
  induction n with
  | zero => intro α hα; omega
  | succ n ih =>
    intro α hα
    rw [pow_succ, coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    have e := congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.1 hp)
    rw [map_add] at e
    by_cases h0 : p.2 = 0
    · rw [h0, hq, mul_zero]
    · have : p.2.degree ≠ 0 := fun h => h0 ((Finsupp.degree_eq_zero_iff _).1 h)
      rw [ih _ (by omega), zero_mul]

/- English proof (translation)
Use `F.dense.eq_of_inner_right (𝕜 := ℂ) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, rfl⟩`. Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `add f g hf hg => simp only [map_add, inner_add_left, hf, hg]`. Consider the case `monomial α a`.

Establish `e : (monomial α a : MvPolynomial σ ℂ) = a • monomial α 1` using `by simp [smul_monomial]`. Rewrite using `[e, map_smul, inner_smul_left, inner_smul_left, hv α, hw α]`.
-/
theorem hasCoeff_unique {σ : Type} [DecidableEq σ] (F : Fock σ) {v w : F.H} {c : MvPowerSeries σ ℂ}
    (hv : HasCoeff F v c) (hw : HasCoeff F w c) : v = w := by
  refine F.dense.eq_of_inner_right (𝕜 := ℂ) ?_
  rintro _ ⟨f, rfl⟩
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, inner_add_left, hf, hg]
  | monomial α a =>
    have e : (monomial α a : MvPolynomial σ ℂ) = a • monomial α 1 := by simp [smul_monomial]
    rw [e, map_smul, inner_smul_left, inner_smul_left, hv α, hw α]

/- English proof (translation)
Introduce `P Q F A x h`. Use `existsUnique_of_exists_of_unique ⟨∑' n : ℕ, (n.factorial : ℂ)⁻¹ • F.ι (gaussPoly A x ^ n), fun α => ?_⟩ fun v w hv hw => hasCoeff_unique F hv hw` and prove the remaining obligations. Establish `e` using `(innerSL ℂ (F.ι (monomial α 1))).map_tsum (summable_pow F A x h)`. Simplify using `only [innerSL_apply_apply, inner_smul_right, hasCoeff_coe F _ α, MvPolynomial.coeff_coe] at e`. Rewrite using `[e, tsum_eq_sum (s := Finset.range (α.degree + 1)), MvPowerSeries.coeff_apply, expPS, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun n _ => by ring`. Introduce `n hn`. Rewrite using `[coeff_pow_eq_zero (coeff_zero_gaussPoly A x) n α (by simpa using hn), mul_zero, mul_zero]`.
-/
theorem existsUnique_gauss : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ),
    (1 - Aᴴ * A).PosDef → ∃! v : F.H, HasCoeff F v (expPS (gaussPoly A x)) := by
  intro P Q F A x h
  refine existsUnique_of_exists_of_unique ⟨∑' n : ℕ, (n.factorial : ℂ)⁻¹ • F.ι (gaussPoly A x ^ n), fun α => ?_⟩
    fun v w hv hw => hasCoeff_unique F hv hw
  have e := (innerSL ℂ (F.ι (monomial α 1))).map_tsum (summable_pow F A x h)
  simp only [innerSL_apply_apply, inner_smul_right, hasCoeff_coe F _ α, MvPolynomial.coeff_coe] at e
  rw [e, tsum_eq_sum (s := Finset.range (α.degree + 1)), MvPowerSeries.coeff_apply, expPS, Finset.mul_sum]
  · exact Finset.sum_congr rfl fun n _ => by ring
  · intro n hn
    rw [coeff_pow_eq_zero (coeff_zero_gaussPoly A x) n α (by simpa using hn), mul_zero, mul_zero]

end GlobalTheory.FockGauss

end
