import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Development
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
The claim follows from `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X`.
-/
lemma tst_exp_hasSum_linfty {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    HasSum (fun j : ℕ => ((j.factorial : ℂ)⁻¹) • X ^ j) (NormedSpace.exp X) :=
  NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X

end Linfty

/- English proof (translation)
Conclude with `tst_exp_hasSum_linfty X`.
-/
lemma tst_exp_hasSum {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    HasSum (fun j : ℕ => ((j.factorial : ℂ)⁻¹) • X ^ j) (NormedSpace.exp X) := by
  exact tst_exp_hasSum_linfty X

/- English proof (translation)
Use `letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra`. Establish `hE` using `hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ)`. Set `L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ` to `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) l).comp (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin n → ℂ) j)`. Establish `h2` using `(L.hasFDerivAt.comp_hasDerivAt _ hE).comp_ofReal`.

Simplify using `only [L, Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul] at h2`. Conclude with `h2`.
-/
private theorem exp_entry_lemma_2 {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (j l : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) j l) (X j l) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hE := hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) l).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin n → ℂ) j)
  have h2 := (L.hasFDerivAt.comp_hasDerivAt _ hE).comp_ofReal
  simp only [L, Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

/- English proof (translation)
Use extensionality with `x`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`.
-/
private theorem smul_mulVec_lemma {n : ℕ} (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    (c • M) *ᵥ v = c • (M *ᵥ v) := by
  ext x
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Establish `hc : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => M *ᵥ v` using `Continuous.matrix_mulVec continuous_id continuous_const`. Establish `h1` using `(tst_exp_hasSum X).map (AddMonoidHom.mk' (fun M : Matrix (Fin n) (Fin n) ℂ => M *ᵥ v) (fun A B => Matrix.add_mulVec A B v)) hc`. Establish `h2 : HasSum (fun j : ℕ => ((j.factorial : ℂ)⁻¹ • X ^ j) *ᵥ v) v`. Establish `h` using `hasSum_single (f := fun j : ℕ => ((j.factorial : ℂ)⁻¹ • X ^ j) *ᵥ v) 0 (by`. Introduce `j hj`.

Take `⟨m, rfl⟩ : ∃ m, j = m + 1` from `⟨j - 1, by omega⟩`. Use `show ((((m + 1).factorial : ℕ) : ℂ)⁻¹ • X ^ (m + 1)) *ᵥ v = 0`. Rewrite using `[smul_mulVec_lemma, pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, smul_zero])`. Simplify using `using h`. Conclude with `h1.unique h2`.
-/
lemma tst_exp_mulVec {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (hv : X *ᵥ v = 0) :
    NormedSpace.exp X *ᵥ v = v := by
  have hc : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => M *ᵥ v :=
    Continuous.matrix_mulVec continuous_id continuous_const
  have h1 := (tst_exp_hasSum X).map (AddMonoidHom.mk' (fun M : Matrix (Fin n) (Fin n) ℂ => M *ᵥ v)
    (fun A B => Matrix.add_mulVec A B v)) hc
  have h2 : HasSum (fun j : ℕ => ((j.factorial : ℂ)⁻¹ • X ^ j) *ᵥ v) v := by
    have h := hasSum_single (f := fun j : ℕ => ((j.factorial : ℂ)⁻¹ • X ^ j) *ᵥ v) 0 (by
      intro j hj
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      show ((((m + 1).factorial : ℕ) : ℂ)⁻¹ • X ^ (m + 1)) *ᵥ v = 0
      rw [smul_mulVec_lemma, pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, smul_zero])
    simpa using h
  exact h1.unique h2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Use `⟨?_, fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `h1 : gᴴ * Hpk k r * g = Hpk k r` using `hg.1`. Establish `h2 : hᴴ * Hpk k r * h = Hpk k r` using `hh.1`. Use `show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r`. Rewrite using `[Matrix.conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by simp only [Matrix.mul_assoc], h1, h2]`.

Rewrite using `[← Matrix.mulVec_mulVec, (hh.2 a ha).1, (hg.2 a ha).1]`. Rewrite using `[← Matrix.mulVec_mulVec, (hh.2 a ha).2, (hg.2 a ha).2]`.
-/
lemma tst_mul_mem {k r : ℕ} {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · have h1 : gᴴ * Hpk k r * g = Hpk k r := hg.1
    have h2 : hᴴ * Hpk k r * h = Hpk k r := hh.1
    show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    rw [Matrix.conjTranspose_mul,
      show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by simp only [Matrix.mul_assoc],
      h1, h2]
  · rw [← Matrix.mulVec_mulVec, (hh.2 a ha).1, (hg.2 a ha).1]
  · rw [← Matrix.mulVec_mulVec, (hh.2 a ha).2, (hg.2 a ha).2]

/- English proof (translation)
Take `⟨hLie, hfix⟩` from `hX`. Establish `hI` using `Formalism.QuantumDeterminants.GBasic.Hpk_sq k r`. Establish `hunitH : IsUnit (Hpk k r)` using `(Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hI)`. Establish `hinv : (Hpk k r)⁻¹ = Hpk k r` using `Matrix.inv_eq_left_inv hI`. Establish `hst : star ((t : ℂ)) = (t : ℂ)` using `Complex.conj_ofReal t`.

Use `⟨?_, fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `hXc : Xᴴ = Hpk k r * (-X) * Hpk k r`. Establish `h1 : Xᴴ * Hpk k r = -(Hpk k r * X)` using `eq_neg_of_add_eq_zero_left hLie`. Combine the equalities or inequalities in the displayed calculation. Establish `hYc : ((t : ℂ) • X)ᴴ = Hpk k r * (-((t : ℂ) • X)) * (Hpk k r)⁻¹`.

Rewrite using `[hinv, Matrix.conjTranspose_smul, hst, hXc, ← smul_neg, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hE : (NormedSpace.exp ((t : ℂ) • X))ᴴ = Hpk k r * NormedSpace.exp (-((t : ℂ) • X)) * (Hpk k r)⁻¹`. Rewrite using `[← Matrix.exp_conjTranspose, hYc, Matrix.exp_conj _ _ hunitH]`. Establish `hEE : NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) = 1`. Rewrite using `[Matrix.exp_neg]`.

Conclude with `Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))`. Use `show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r`. Rewrite using `[hE, hinv, Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-((t : ℂ) • X))) (Hpk k r) (Hpk k r), hI, Matrix.mul_one, Matrix.mul_assoc, hEE, Matrix.mul_one]`. Conclude with `tst_exp_mulVec _ _ (by rw [smul_mulVec_lemma, (hfix a ha).1, smul_zero])`. Conclude with `tst_exp_mulVec _ _ (by rw [smul_mulVec_lemma, (hfix a ha).2, smul_zero])`.
-/
lemma tst_exp_mem {k r : ℕ} {i : Fin (r + 1)} {X : Mx k r} (hX : inLieLev k r i X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  obtain ⟨hLie, hfix⟩ := hX
  have hI := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hunitH : IsUnit (Hpk k r) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hI)
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hI
  have hst : star ((t : ℂ)) = (t : ℂ) := Complex.conj_ofReal t
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · have hXc : Xᴴ = Hpk k r * (-X) * Hpk k r := by
      have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hLie
      calc Xᴴ = Xᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc, hI, Matrix.mul_one]
        _ = Hpk k r * (-X) * Hpk k r := by rw [h1, Matrix.mul_neg]
    have hYc : ((t : ℂ) • X)ᴴ = Hpk k r * (-((t : ℂ) • X)) * (Hpk k r)⁻¹ := by
      rw [hinv, Matrix.conjTranspose_smul, hst, hXc, ← smul_neg, Matrix.mul_smul, Matrix.smul_mul]
    have hE : (NormedSpace.exp ((t : ℂ) • X))ᴴ =
        Hpk k r * NormedSpace.exp (-((t : ℂ) • X)) * (Hpk k r)⁻¹ := by
      rw [← Matrix.exp_conjTranspose, hYc, Matrix.exp_conj _ _ hunitH]
    have hEE : NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) = 1 := by
      rw [Matrix.exp_neg]
      exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))
    show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r
    rw [hE, hinv, Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-((t : ℂ) • X))) (Hpk k r) (Hpk k r), hI,
      Matrix.mul_one, Matrix.mul_assoc, hEE, Matrix.mul_one]
  · exact tst_exp_mulVec _ _ (by rw [smul_mulVec_lemma, (hfix a ha).1, smul_zero])
  · exact tst_exp_mulVec _ _ (by rw [smul_mulVec_lemma, (hfix a ha).2, smul_zero])

/- English proof (translation)
Establish `hq : q.val < 2 * (r - i.val) + k + 1` using `q.isLt`. Establish `hi` using `i.isLt`. Establish `hp : (posL k r i q).val = q.val + i.val` using `rfl`. Establish `he : (eI k r a).val = a.val` using `rfl`. Establish `hs : (esI k r a).val = 2 * r + k - a.val` using `rfl`.

Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `simp only [Hpk, Fin.ext_iff, hp, he] split_ifs <;> first | rfl | (exfalso; omega)`. Apply the tactic sequence `simp only [Hpk, Fin.ext_iff, hp, hs] split_ifs <;> first | rfl | (exfalso; omega)`.
-/
lemma tst_H_zero {k r : ℕ} (i : Fin (r + 1)) (q : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    Hpk k r (posL k r i q) (eI k r a) = 0 ∧ Hpk k r (posL k r i q) (esI k r a) = 0 := by
  have hq : q.val < 2 * (r - i.val) + k + 1 := q.isLt
  have hi := i.isLt
  have hp : (posL k r i q).val = q.val + i.val := rfl
  have he : (eI k r a).val = a.val := rfl
  have hs : (esI k r a).val = 2 * r + k - a.val := rfl
  constructor
  · simp only [Hpk, Fin.ext_iff, hp, he]
    split_ifs <;> first | rfl | (exfalso; omega)
  · simp only [Hpk, Fin.ext_iff, hp, hs]
    split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Use extensionality with `x`. Simplify using `[bvec, Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, h]`.
-/
lemma tst_Z_fix {n : ℕ} (a' b' p : Fin n) (h : b' ≠ p) : Matrix.single a' b' (1 : ℂ) *ᵥ bvec p = 0 := by
  ext x
  simp [bvec, Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, h]

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Establish `h0 : (Matrix.single a' b' (1 : ℂ))ᴴ *ᵥ (H *ᵥ bvec p) = 0`. Use extensionality with `x`. Simplify using `[bvec, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.single_apply, Pi.single_apply, h]`. Apply the tactic sequence `by_cases hb : b' = x <;> simp [hb, h]`.

Rewrite using `[h0, Matrix.mulVec_zero]`.
-/
lemma tst_ZH_fix {n : ℕ} (W H : Matrix (Fin n) (Fin n) ℂ) (a' b' p : Fin n) (h : H a' p = 0) :
    (W * (Matrix.single a' b' (1 : ℂ))ᴴ * H) *ᵥ bvec p = 0 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h0 : (Matrix.single a' b' (1 : ℂ))ᴴ *ᵥ (H *ᵥ bvec p) = 0 := by
    ext x
    simp [bvec, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.single_apply, Pi.single_apply, h]
    by_cases hb : b' = x <;> simp [hb, h]
  rw [h0, Matrix.mulVec_zero]

/- English proof (translation)
Establish `hHH : ∀ Y : Matrix (Fin n) (Fin n) ℂ, H * (H * Y) = Y` using `fun Y => by`. Rewrite using `[← Matrix.mul_assoc, hH2, Matrix.one_mul]`. Rewrite using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH]`. Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hH2, hHH, Matrix.mul_one]`. Normalize the expressions using the abelian group laws.
-/
lemma tst_core1 {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hH2 : H * H = 1) :
    (Z - H * Zᴴ * H)ᴴ * H + H * (Z - H * Zᴴ * H) = 0 := by
  have hHH : ∀ Y : Matrix (Fin n) (Fin n) ℂ, H * (H * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hH2, Matrix.one_mul]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hH2, hHH, Matrix.mul_one]
  abel

/- English proof (translation)
Establish `hHH : ∀ Y : Matrix (Fin n) (Fin n) ℂ, H * (H * Y) = Y` using `fun Y => by`. Rewrite using `[← Matrix.mul_assoc, hH2, Matrix.one_mul]`. Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hH2, hHH, Matrix.mul_one]`. Normalize the expressions using the abelian group laws.
-/
lemma tst_core2 {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hH2 : H * H = 1) :
    (Z + H * Zᴴ * H)ᴴ * H = H * (Z + H * Zᴴ * H) := by
  have hHH : ∀ Y : Matrix (Fin n) (Fin n) ℂ, H * (H * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hH2, Matrix.one_mul]
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hH2, hHH, Matrix.mul_one]
  abel

/- English proof (translation)
Establish `hH` using `Formalism.QuantumDeterminants.GBasic.Hpk_herm k r`. Establish `hI` using `Formalism.QuantumDeterminants.GBasic.Hpk_sq k r`. Establish `hinv : (Hpk k r)⁻¹ = Hpk k r` using `Matrix.inv_eq_left_inv hI`. Establish `hfx : ∀ a' : Fin r, a'.val < i.val → ∀ p : Fin (2 * r + k + 1), (p = eI k r a' ∨ p = esI k r a') → Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) *ᵥ bvec p = 0 ∧ (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r) *ᵥ bvec p = 0`. Introduce `a' ha' p hp`.

Establish `hb : b.val < 2 * (r - i.val) + k + 1` using `b.isLt`. Establish `hi` using `i.isLt`. Establish `hpb : (posL k r i b).val = b.val + i.val` using `rfl`. Establish `hne : posL k r i b ≠ p`. Introduce `e`.

Break down `hp with rfl | rfl` into its components or cases. Use `congrArg Fin.val e` as an intermediate fact. Rewrite `this` using `[hpb]`. Establish `h2 : (eI k r a').val = a'.val` using `rfl`. Use linear arithmetic over natural numbers and integers.

Use `congrArg Fin.val e` as an intermediate fact. Rewrite `this` using `[hpb]`. Establish `h2 : (esI k r a').val = 2 * r + k - a'.val` using `rfl`. Use linear arithmetic over natural numbers and integers. Establish `hz : Hpk k r (posL k r i a) p = 0`.

Break down `hp with rfl | rfl` into its components or cases. Conclude with `(tst_H_zero i a a' ha').1`. Conclude with `(tst_H_zero i a a' ha').2`. Conclude with `⟨tst_Z_fix _ _ _ hne, tst_ZH_fix _ _ _ _ _ hz⟩`. Establish `hs : star (1 / 2 : ℂ) = 1 / 2`.

Rewrite using `[show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]`. Conclude with `Complex.conj_ofReal _`. Establish `hs2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I))`. Rewrite using `[star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.

Prove the components needed by the constructor for the conclusion. Use `⟨?_, fun a' ha' => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [hpart1, hinv]`. Rewrite using `[Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, tst_core1 _ _ hH hI, smul_zero]`. Take `⟨h1, h2⟩` from `hfx a' ha' _ (Or.inl rfl)`.

Simplify using `only [hpart1, hinv]`. Rewrite using `[smul_mulVec_lemma, Matrix.sub_mulVec, h1, h2, sub_zero, smul_zero]`. Take `⟨h1, h2⟩` from `hfx a' ha' _ (Or.inr rfl)`. Simplify using `only [hpart1, hinv]`. Rewrite using `[smul_mulVec_lemma, Matrix.sub_mulVec, h1, h2, sub_zero, smul_zero]`.

Use `⟨?_, fun a' ha' => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [hpart2, hinv]`. Rewrite using `[Matrix.conjTranspose_smul, hs2, Matrix.smul_mul, Matrix.mul_smul, tst_core2 _ _ hH hI, neg_smul, neg_add_cancel]`. Take `⟨h1, h2⟩` from `hfx a' ha' _ (Or.inl rfl)`. Simplify using `only [hpart2, hinv]`.

Rewrite using `[smul_mulVec_lemma, Matrix.add_mulVec, h1, h2, add_zero, smul_zero]`. Take `⟨h1, h2⟩` from `hfx a' ha' _ (Or.inr rfl)`. Simplify using `only [hpart2, hinv]`. Rewrite using `[smul_mulVec_lemma, Matrix.add_mulVec, h1, h2, add_zero, smul_zero]`.
-/
lemma tst_lie {k r : ℕ} (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) ∧
    inLieLev k r i (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  have hH := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  have hI := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hI
  have hfx : ∀ a' : Fin r, a'.val < i.val → ∀ p : Fin (2 * r + k + 1), (p = eI k r a' ∨ p = esI k r a') →
      Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) *ᵥ bvec p = 0 ∧
      (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r) *ᵥ bvec p = 0 := by
    intro a' ha' p hp
    have hb : b.val < 2 * (r - i.val) + k + 1 := b.isLt
    have hi := i.isLt
    have hpb : (posL k r i b).val = b.val + i.val := rfl
    have hne : posL k r i b ≠ p := by
      intro e
      rcases hp with rfl | rfl
      · have := congrArg Fin.val e
        rw [hpb] at this
        have h2 : (eI k r a').val = a'.val := rfl
        omega
      · have := congrArg Fin.val e
        rw [hpb] at this
        have h2 : (esI k r a').val = 2 * r + k - a'.val := rfl
        omega
    have hz : Hpk k r (posL k r i a) p = 0 := by
      rcases hp with rfl | rfl
      · exact (tst_H_zero i a a' ha').1
      · exact (tst_H_zero i a a' ha').2
    exact ⟨tst_Z_fix _ _ _ hne, tst_ZH_fix _ _ _ _ _ hz⟩
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.conj_ofReal _
  have hs2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I, map_ofNat]
    ring
  constructor
  · refine ⟨?_, fun a' ha' => ⟨?_, ?_⟩⟩
    · simp only [hpart1, hinv]
      rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, tst_core1 _ _ hH hI,
        smul_zero]
    · obtain ⟨h1, h2⟩ := hfx a' ha' _ (Or.inl rfl)
      simp only [hpart1, hinv]
      rw [smul_mulVec_lemma, Matrix.sub_mulVec, h1, h2, sub_zero, smul_zero]
    · obtain ⟨h1, h2⟩ := hfx a' ha' _ (Or.inr rfl)
      simp only [hpart1, hinv]
      rw [smul_mulVec_lemma, Matrix.sub_mulVec, h1, h2, sub_zero, smul_zero]
  · refine ⟨?_, fun a' ha' => ⟨?_, ?_⟩⟩
    · simp only [hpart2, hinv]
      rw [Matrix.conjTranspose_smul, hs2, Matrix.smul_mul, Matrix.mul_smul, tst_core2 _ _ hH hI, neg_smul,
        neg_add_cancel]
    · obtain ⟨h1, h2⟩ := hfx a' ha' _ (Or.inl rfl)
      simp only [hpart2, hinv]
      rw [smul_mulVec_lemma, Matrix.add_mulVec, h1, h2, add_zero, smul_zero]
    · obtain ⟨h1, h2⟩ := hfx a' ha' _ (Or.inr rfl)
      simp only [hpart2, hinv]
      rw [smul_mulVec_lemma, Matrix.add_mulVec, h1, h2, add_zero, smul_zero]

/- English proof (translation)
Use `hasDerivAt_pi.2 fun m => hasDerivAt_pi.2 fun l => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply]`. Establish `hs` using `HasDerivAt.sum (u := Finset.univ) fun j _ => (exp_entry_lemma_2 X j l).const_mul (g m j)`. Use `hs using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`.

Simplify using `[Finset.sum_apply]`.
-/
private theorem gamma_lemma_3 {k r : ℕ} (g X : Mx k r) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
  refine hasDerivAt_pi.2 fun m => hasDerivAt_pi.2 fun l => ?_
  simp only [Matrix.mul_apply]
  have hs := HasDerivAt.sum (u := Finset.univ) fun j _ => (exp_entry_lemma_2 X j l).const_mul (g m j)
  convert hs using 1
  ext y
  simp [Finset.sum_apply]

/- English proof (translation)
Establish `hγ` using `gamma_lemma_3 g X`. Establish `hFd : HasFDerivAt F (fderiv ℝ F g) g` using `((hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)).hasFDerivAt`. Establish `h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g` using `by simp`. Establish `hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0] (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))`. Establish `hmem : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' U ∈ nhds (0 : ℝ)`.

Apply `hγ.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Use `show U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))`. Rewrite using `[h0]`. Conclude with `hU.mem_nhds hg`. Use `filter_upwards [hmem] with t ht`.

Conclude with `hfF _ ht (tst_mul_mem hgG (tst_exp_mem hX t))`. Establish `hcomp` using `HasFDerivAt.comp_hasDerivAt_of_eq 0 hFd hγ h0.symm`. Use `show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 = fderiv ℝ F g (g * X)`. Conclude with `(hcomp.congr_of_eventuallyEq hev).deriv`.
-/
lemma tst_rdV_eq {k r : ℕ} {i : Fin (r + 1)} (f F : Mx k r → ℂ) (U : Set (Mx k r)) (g X : Mx k r)
    (hU : IsOpen U) (hg : g ∈ U) (hgG : g ∈ Glev k r i) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ h ∈ U, h ∈ Glev k r i → f h = F h) (hX : inLieLev k r i X) :
    RdV X f g = fderiv ℝ F g (g * X) := by
  have hγ := gamma_lemma_3 g X
  have hFd : HasFDerivAt F (fderiv ℝ F g) g :=
    ((hF.differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hg)).hasFDerivAt
  have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' U ∈ nhds (0 : ℝ) := by
      apply hγ.continuousAt.preimage_mem_nhds
      show U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))
      rw [h0]
      exact hU.mem_nhds hg
    filter_upwards [hmem] with t ht
    exact hfF _ ht (tst_mul_mem hgG (tst_exp_mem hX t))
  have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq 0 hFd hγ h0.symm
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 = fderiv ℝ F g (g * X)
  exact (hcomp.congr_of_eventuallyEq hev).deriv

/- English proof (translation)
Establish `hγ` using `gamma_lemma_3 g X`. Establish `hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0] fun _ => (0 : ℂ)`. Establish `h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g` using `by simp`. Establish `hmem : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' Kᶜ ∈ nhds (0 : ℝ)`. Apply `hγ.continuousAt.preimage_mem_nhds` to reduce the goal to its premises.

Use `show Kᶜ ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))`. Rewrite using `[h0]`. Conclude with `hK.isOpen_compl.mem_nhds hgK`. Use `filter_upwards [hmem] with t ht`. Conclude with `hKf _ (tst_mul_mem hg (tst_exp_mem hX t)) ht`.

Use `show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 = 0`. Rewrite using `[hev.deriv_eq, deriv_const]`.
-/
lemma tst_rdV_zero {k r : ℕ} {i : Fin (r + 1)} (f : Mx k r → ℂ) (K : Set (Mx k r)) (hK : IsClosed K)
    (hKf : ∀ g ∈ Glev k r i, g ∉ K → f g = 0) (X : Mx k r) (hX : inLieLev k r i X) (g : Mx k r)
    (hg : g ∈ Glev k r i) (hgK : g ∉ K) : RdV X f g = 0 := by
  have hγ := gamma_lemma_3 g X
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0] fun _ => (0 : ℂ) := by
    have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
    have hmem : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' Kᶜ ∈ nhds (0 : ℝ) := by
      apply hγ.continuousAt.preimage_mem_nhds
      show Kᶜ ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))
      rw [h0]
      exact hK.isOpen_compl.mem_nhds hgK
    filter_upwards [hmem] with t ht
    exact hKf _ (tst_mul_mem hg (tst_exp_mem hX t)) ht
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 = 0
  rw [hev.deriv_eq, deriv_const]

/- English proof (translation)
Introduce `k r i a b f hf`. Unfold `TestF CptOn at hf ⊢`. Take `⟨hs, K, hK, hKf⟩` from `hf`. Take `⟨h1, h2⟩` from `tst_lie (k := k) i a b`. Use `⟨?_, K, hK, ?_⟩` and prove the remaining obligations.

Introduce `g₀ hg₀`. Take `⟨U, F, hU, hg₀U, hF, hfF⟩` from `hs g₀ hg₀`. Establish `hd` using `hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty`. Use `⟨U, fun g => fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) + Complex.I • fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)), hU, hg₀U, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hd.clm_apply (mulRightRealCLM _).contDiff.contDiffOn).add ((hd.clm_apply (mulRightRealCLM _).contDiff.contDiffOn).const_smul Complex.I)`.

Introduce `g hg hgG show RdV _ f g + Complex.I • RdV _ f g = _`. Rewrite using `[tst_rdV_eq f F U g _ hU hg hgG hF hfF h1, tst_rdV_eq f F U g _ hU hg hgG hF hfF h2]`. Introduce `g hg hgK show RdV _ f g + Complex.I • RdV _ f g = 0`. Rewrite using `[tst_rdV_zero f K hK.isClosed hKf _ h1 g hg hgK, tst_rdV_zero f K hK.isClosed hKf _ h2 g hg hgK, smul_zero, add_zero]`.
-/
theorem elementary_generator_preserves_test : EabTest := by
  intro k r i a b f hf
  unfold TestF CptOn at hf ⊢
  obtain ⟨hs, K, hK, hKf⟩ := hf
  obtain ⟨h1, h2⟩ := tst_lie (k := k) i a b
  refine ⟨?_, K, hK, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hs g₀ hg₀
    have hd := hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
    refine ⟨U, fun g => fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) +
      Complex.I • fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)),
      hU, hg₀U, ?_, ?_⟩
    · exact (hd.clm_apply (mulRightRealCLM _).contDiff.contDiffOn).add
        ((hd.clm_apply (mulRightRealCLM _).contDiff.contDiffOn).const_smul Complex.I)
    · intro g hg hgG
      show RdV _ f g + Complex.I • RdV _ f g = _
      rw [tst_rdV_eq f F U g _ hU hg hgG hF hfF h1, tst_rdV_eq f F U g _ hU hg hgG hF hfF h2]
  · intro g hg hgK
    show RdV _ f g + Complex.I • RdV _ f g = 0
    rw [tst_rdV_zero f K hK.isClosed hKf _ h1 g hg hgK, tst_rdV_zero f K hK.isClosed hKf _ h2 g hg hgK,
      smul_zero, add_zero]

/- English proof (translation)
Establish `h2` using `(Complex.conjCLE.contDiff (n := ∞)).comp h`. Simplify `h2` using `[Function.comp_def]`.
-/
lemma tst_cd_star {k r : ℕ} {φ : Mx k r → ℂ} (h : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (fun g => star (φ g)) := by
  have h2 := (Complex.conjCLE.contDiff (n := ∞)).comp h
  simpa [Function.comp_def] using h2

/- English proof (translation)
Unfold `TestF SmoothLev CptOn at *`. Take `⟨hs, K, hK, hKf⟩` from `hf`. Use `⟨fun g₀ hg₀ => ?_, K, hK, fun g hg hgK => by show ψ g * f g = 0` and prove the remaining obligations. Rewrite using `[hKf g hg hgK, mul_zero]⟩`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hs g₀ hg₀`.

Use `⟨U, fun g => φ g * F g, hU, hgU, hφ.contDiffOn.mul hF, fun g hgU' hgG => ?_⟩` and prove the remaining obligations. Use `show ψ g * f g = φ g * F g`. Rewrite using `[hψ g hgG, hfF g hgU' hgG]`.
-/
lemma tst_mul_test {k r : ℕ} {i : Fin (r + 1)} (φ ψ : Mx k r → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hψ : ∀ g ∈ Glev k r i, ψ g = φ g) (f : Mx k r → ℂ) (hf : TestF k r i f) :
    TestF k r i (fun g => ψ g * f g) := by
  unfold TestF SmoothLev CptOn at *
  obtain ⟨hs, K, hK, hKf⟩ := hf
  refine ⟨fun g₀ hg₀ => ?_, K, hK, fun g hg hgK => by
    show ψ g * f g = 0
    rw [hKf g hg hgK, mul_zero]⟩
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hs g₀ hg₀
  refine ⟨U, fun g => φ g * F g, hU, hgU, hφ.contDiffOn.mul hF, fun g hgU' hgG => ?_⟩
  show ψ g * f g = φ g * F g
  rw [hψ g hgG, hfF g hgU' hgG]

def yExt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) (g : Mx k r) : ℂ :=
  ∑ l, Hpk k r (posL k r i c) l * star (∑ m, star ((Hpk k r *ᵥ fvec k r z i) m) * g m l)

def bExt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) (g : Mx k r) : ℂ :=
  ∑ j, star (fvec k r z i j) * ∑ l, Hpk k r j l * g l (posL k r i c)

/- English proof (translation)
Unfold `yExt`. Conclude with `ContDiff.sum fun l _ => contDiff_const.mul (tst_cd_star (ContDiff.sum fun m _ => contDiff_const.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id m) l)))`.
-/
lemma tst_yExt_cd (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) :
    ContDiff ℝ ∞ (yExt k r z i c) := by
  unfold yExt
  exact ContDiff.sum fun l _ => contDiff_const.mul
    (tst_cd_star (ContDiff.sum fun m _ => contDiff_const.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id m) l)))

/- English proof (translation)
Unfold `bExt`. Conclude with `ContDiff.sum fun j _ => contDiff_const.mul (ContDiff.sum fun l _ => contDiff_const.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id l) (posL k r i c)))`.
-/
lemma tst_bExt_cd (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) :
    ContDiff ℝ ∞ (bExt k r z i c) := by
  unfold bExt
  exact ContDiff.sum fun j _ => contDiff_const.mul
    (ContDiff.sum fun l _ => contDiff_const.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id l) (posL k r i c)))

/- English proof (translation)
Establish `hI` using `Formalism.QuantumDeterminants.GBasic.Hpk_sq k r`. Establish `hU : gᴴ * Hpk k r * g = Hpk k r` using `hg.1`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.mul_assoc (Hpk k r * gᴴ), Matrix.mul_assoc (Hpk k r), ← Matrix.mul_assoc gᴴ, hU, hI]`.
-/
lemma tst_inv_eq {k r : ℕ} {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hI := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc (Hpk k r * gᴴ), Matrix.mul_assoc (Hpk k r), ← Matrix.mul_assoc gᴴ, hU, hI]

/- English proof (translation)
Use `show (g⁻¹ *ᵥ fvec k r z i) (posL k r i c) = yExt k r z i c g`. Rewrite using `[tst_inv_eq hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Simplify using `only [yExt, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, star_mul, star_star]`.
-/
lemma tst_yv_eq {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) {g : Mx k r}
    (hg : g ∈ Glev k r i) : yv k r z i g c = yExt k r z i c g := by
  show (g⁻¹ *ᵥ fvec k r z i) (posL k r i c) = yExt k r z i c g
  rw [tst_inv_eq hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [yExt, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, star_mul, star_star]

/- English proof (translation)
Establish `hcol : g *ᵥ bvec (posL k r i c) = fun l => g l (posL k r i c)`. Use extensionality with `l`. Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`. Use `show herm (Hpk k r) (g *ᵥ bvec (posL k r i c)) (fvec k r z i) = bExt k r z i c g`. Rewrite using `[hcol]`.

Simplify using `only [herm, bExt, dotProduct, Matrix.mulVec, Pi.star_apply]`.
-/
lemma tst_ybv_eq {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) (g : Mx k r) :
    ybv k r z i g c = bExt k r z i c g := by
  have hcol : g *ᵥ bvec (posL k r i c) = fun l => g l (posL k r i c) := by
    ext l
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  show herm (Hpk k r) (g *ᵥ bvec (posL k r i c)) (fvec k r z i) = bExt k r z i c g
  rw [hcol]
  simp only [herm, bExt, dotProduct, Matrix.mulVec, Pi.star_apply]

/- English proof (translation)
Introduce `k r z i c f hf`. Conclude with `⟨tst_mul_test (yExt k r z i c) (fun g => yv k r z i g c) (tst_yExt_cd k r z i c) (fun g hg => tst_yv_eq z i c hg) f hf, tst_mul_test (fun g => star (yExt k r z i c g)) (fun g => star (yv k r z i g c)) (tst_cd_star (tst_yExt_cd k r z i c)) (fun g hg => congrArg star (tst_yv_eq z i …`.
-/
theorem multiplication_preserves_test : MulTest := by
  intro k r z i c f hf
  exact ⟨tst_mul_test (yExt k r z i c) (fun g => yv k r z i g c) (tst_yExt_cd k r z i c)
      (fun g hg => tst_yv_eq z i c hg) f hf,
    tst_mul_test (fun g => star (yExt k r z i c g)) (fun g => star (yv k r z i g c))
      (tst_cd_star (tst_yExt_cd k r z i c)) (fun g hg => congrArg star (tst_yv_eq z i c hg)) f hf,
    tst_mul_test (bExt k r z i c) (fun g => ybv k r z i g c) (tst_bExt_cd k r z i c)
      (fun g _ => tst_ybv_eq z i c g) f hf,
    tst_mul_test (fun g => star (bExt k r z i c g)) (fun g => star (ybv k r z i g c))
      (tst_cd_star (tst_bExt_cd k r z i c)) (fun g _ => congrArg star (tst_ybv_eq z i c g)) f hf⟩

/- English proof (translation)
Establish `h1 : IsClosed {g : Mx k r | gᴴ * Hpk k r * g = Hpk k r}` using `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`. Establish `h2 : ∀ a : Fin r, IsClosed {g : Mx k r | a.val < i.val → g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}`. Introduce `a`. Distinguish the cases in `ha : a.val < i.val`. Simplify using `only [ha, true_implies, Set.setOf_and]`.

Conclude with `(isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)`. Simplify using `only [ha, false_implies, Set.setOf_true]`. Conclude with `isClosed_univ`. Establish `e : Glev k r i = {g : Mx k r | gᴴ * Hpk k r * g = Hpk k r} ∩ ⋂ a : Fin r, {g : Mx k r | a.val < i.val → g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}`. Use extensionality with `g`.

Simplify using `[Glev, UH]`. Rewrite using `[e]`. Conclude with `h1.inter (isClosed_iInter h2)`.
-/
lemma tst_glev_closed (k r : ℕ) (i : Fin (r + 1)) : IsClosed (Glev k r i) := by
  have h1 : IsClosed {g : Mx k r | gᴴ * Hpk k r * g = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  have h2 : ∀ a : Fin r, IsClosed {g : Mx k r | a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)} := by
    intro a
    by_cases ha : a.val < i.val
    · simp only [ha, true_implies, Set.setOf_and]
      exact (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
    · simp only [ha, false_implies, Set.setOf_true]
      exact isClosed_univ
  have e : Glev k r i = {g : Mx k r | gᴴ * Hpk k r * g = Hpk k r} ∩ ⋂ a : Fin r, {g : Mx k r | a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)} := by
    ext g
    simp [Glev, UH]
  rw [e]
  exact h1.inter (isClosed_iInter h2)

/- English proof (translation)
Unfold `SmoothLev at hf`. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hg₀U, hF, hfF⟩` from `hf g₀ ⟨hg₀, Set.mem_univ _⟩`. Establish `hFc : ContinuousAt F g₀` using `hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)`. Use `hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hg₀U hg₀)` and prove the remaining obligations.

Use `filter_upwards [inter_mem_nhdsWithin (Glev k r i) (hU.mem_nhds hg₀U)] with g hg`. Conclude with `hfF g hg.2 hg.1`.
-/
lemma tst_contOn {k r : ℕ} {i : Fin (r + 1)} (f : Mx k r → ℂ) (hf : SmoothLev k r i Set.univ f) :
    ContinuousOn f (Glev k r i) := by
  unfold SmoothLev at hf
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ ⟨hg₀, Set.mem_univ _⟩
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hg₀U hg₀)
  filter_upwards [inter_mem_nhdsWithin (Glev k r i) (hU.mem_nhds hg₀U)] with g hg
  exact hfF g hg.2 hg.1

/- English proof (translation)
Introduce `k r i μ hμ f h hf hh`. Unfold `TestF CptOn at hf hh`. Take `⟨hfs, Kf, hKf, hKf0⟩` from `hf`. Take `⟨hhs, -, -, -⟩` from `hh`. Establish `: IsFiniteMeasureOnCompacts μ` using `⟨fun K hK => hμ.finite_compact K hK⟩`.

Set `S : Set (Mt k r)` to `Glev k r i`. Set `K : Set (Mt k r)` to `Kf`. Establish `hSc : IsClosed S` using `tst_glev_closed k r i`. Establish `hKc : IsCompact K` using `hKf`. Establish `hfo : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) S` using `tst_contOn f hfs`.

Establish `hho : ContinuousOn (fun x : Mt k r => h (Matrix.of x)) S` using `tst_contOn h hhs`. Establish `hφc : ContinuousOn (fun x : Mt k r => f (Matrix.of x) * star (h (Matrix.of x))) S` using `hfo.mul (Complex.continuous_conj.comp_continuousOn hho)`. Establish `hint : IntegrableOn (fun x : Mt k r => f (Matrix.of x) * star (h (Matrix.of x))) (S ∩ K) μ` using `(hφc.mono Set.inter_subset_left).integrableOn_compact (hKc.inter_left hSc)`. Establish `hind` using `hint.integrable_indicator (hSc.inter hKc.isClosed).measurableSet`. Use `hind.congr ?_` and prove the remaining obligations.

Establish `hae : ∀ᵐ x ∂μ, x ∈ S`. Rewrite using `[ae_iff]`. Conclude with `hμ.conc`. Use `filter_upwards [hae] with x hx`. Distinguish the cases in `hxK : x ∈ K`.

Rewrite using `[Set.indicator_of_mem (show x ∈ S ∩ K from ⟨hx, hxK⟩)]`. Establish `e : f (Matrix.of x) * star (h (Matrix.of x)) = 0`. Rewrite using `[hKf0 (Matrix.of x) hx hxK, zero_mul]`. Rewrite using `[e]`. Conclude with `Set.indicator_apply_eq_zero.mpr (fun _ => e)`.
-/
theorem test_function_pairing_integral : TestInt := by
  intro k r i μ hμ f h hf hh
  unfold TestF CptOn at hf hh
  obtain ⟨hfs, Kf, hKf, hKf0⟩ := hf
  obtain ⟨hhs, -, -, -⟩ := hh
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hμ.finite_compact K hK⟩
  let S : Set (Mt k r) := Glev k r i
  let K : Set (Mt k r) := Kf
  have hSc : IsClosed S := tst_glev_closed k r i
  have hKc : IsCompact K := hKf
  have hfo : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) S := tst_contOn f hfs
  have hho : ContinuousOn (fun x : Mt k r => h (Matrix.of x)) S := tst_contOn h hhs
  have hφc : ContinuousOn (fun x : Mt k r => f (Matrix.of x) * star (h (Matrix.of x))) S :=
    hfo.mul (Complex.continuous_conj.comp_continuousOn hho)
  have hint : IntegrableOn (fun x : Mt k r => f (Matrix.of x) * star (h (Matrix.of x))) (S ∩ K) μ :=
    (hφc.mono Set.inter_subset_left).integrableOn_compact (hKc.inter_left hSc)
  have hind := hint.integrable_indicator (hSc.inter hKc.isClosed).measurableSet
  refine hind.congr ?_
  have hae : ∀ᵐ x ∂μ, x ∈ S := by
    rw [ae_iff]
    exact hμ.conc
  filter_upwards [hae] with x hx
  by_cases hxK : x ∈ K
  · rw [Set.indicator_of_mem (show x ∈ S ∩ K from ⟨hx, hxK⟩)]
  · have e : f (Matrix.of x) * star (h (Matrix.of x)) = 0 := by
      rw [hKf0 (Matrix.of x) hx hxK, zero_mul]
    rw [e]
    exact Set.indicator_apply_eq_zero.mpr (fun _ => e)

end PI.QnHermHaar
