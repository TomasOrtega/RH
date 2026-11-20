import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyTransformMemRationalUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinBasisCoeffsEmbeddingsEvalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormOneCmFieldDetOneAddNeZeroCharZeroStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.UnitaryDense

open Matrix

noncomputable def cayMat {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K :=
  (1 - M) * (1 + M)⁻¹

/- English proof (translation)
Establish `h1 : (A.adjugate).map f = (A.map f).adjugate` using `RingHom.map_adjugate f A`. Establish `h2 : f A.det = (A.map f).det` using `RingHom.map_det f A`. Rewrite using `[Matrix.inv_def, Matrix.inv_def, ← h1, ← h2]`. Use extensionality with `i j`. Simplify using `[Ring.inverse_eq_inv']`.
-/
theorem map_inv_fieldHom {F E : Type} [Field F] [Field E] (f : F →+* E) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) : (A⁻¹).map f = (A.map f)⁻¹ := by
  have h1 : (A.adjugate).map f = (A.map f).adjugate := RingHom.map_adjugate f A
  have h2 : f A.det = (A.map f).det := RingHom.map_det f A
  rw [Matrix.inv_def, Matrix.inv_def, ← h1, ← h2]
  ext i j
  simp [Ring.inverse_eq_inv']

/- English proof (translation)
Unfold `cayMat`. Rewrite using `[Matrix.map_mul, map_inv_fieldHom, Matrix.map_sub f (map_sub f), Matrix.map_add f (map_add f), Matrix.map_one _ (map_zero f) (map_one f)]`.
-/
theorem cayMat_map {F E : Type} [Field F] [Field E] (f : F →+* E) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) : (cayMat A).map f = cayMat (A.map f) := by
  unfold cayMat
  rw [Matrix.map_mul, map_inv_fieldHom, Matrix.map_sub f (map_sub f), Matrix.map_add f (map_add f),
    Matrix.map_one _ (map_zero f) (map_one f)]

/- English proof (translation)
Use `MvPolynomial.funext_set (p := q) (q := 0) (fun _ => Set.range (Rat.cast : ℚ → K)) (fun _ => Set.infinite_range_of_injective Rat.cast_injective) ?_` and prove the remaining obligations. Introduce `x hx`. Use `choose y hy using fun v => hx v (Set.mem_univ v)`. Rewrite using `[map_zero]`. Establish `hxy : x = fun v => (y v : K)` using `funext fun v => (hy v).symm`.

Substitute `hxy` using the available equality. Conclude with `h y`.
-/
theorem eq_zero_of_rat_points {V K : Type} [Field K] [CharZero K] (q : MvPolynomial V K)
    (h : ∀ x : V → ℚ, MvPolynomial.eval (fun v => (x v : K)) q = 0) : q = 0 := by
  refine MvPolynomial.funext_set (p := q) (q := 0) (fun _ => Set.range (Rat.cast : ℚ → K))
    (fun _ => Set.infinite_range_of_injective Rat.cast_injective) ?_
  intro x hx
  choose y hy using fun v => hx v (Set.mem_univ v)
  rw [map_zero]
  have hxy : x = fun v => (y v : K) := funext fun v => (hy v).symm
  subst hxy
  exact h y

/- English proof (translation)
Establish `hTN : Mᵀ * N = 1` using `mul_eq_one_comm.mp hNM`. Establish `hdT : (1 + Mᵀ).det ≠ 0`. Rewrite using `[← transpose_one, ← transpose_add, det_transpose]`. Conclude with `hM`. Establish `key : (1 + Mᵀ) * (1 - N) = -((1 - Mᵀ) * (1 + N))`.

Simplify using `only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hTN]`. Normalize the expressions using the abelian group laws. Establish `hu1 : IsUnit (1 + Mᵀ).det` using `isUnit_iff_ne_zero.mpr hdT`. Establish `hu2 : IsUnit (1 + N).det` using `isUnit_iff_ne_zero.mpr hN`. Unfold `cayMat`.

Rewrite using `[transpose_mul, transpose_nonsing_inv, transpose_add, transpose_sub, transpose_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, nonsing_inv_mul _ hu1, Matrix.one_mul]`. Use `_ = -((1 + Mᵀ)⁻¹ * (1 - Mᵀ)) := by`. Rewrite using `[key]`.

Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, mul_nonsing_inv _ hu2, Matrix.mul_one]`.
-/
theorem cayMat_transpose {K : Type} [Field K] {n : ℕ} (M N : Matrix (Fin n) (Fin n) K)
    (hNM : N * Mᵀ = 1) (hM : (1 + M).det ≠ 0) (hN : (1 + N).det ≠ 0) :
    cayMat N = -(cayMat M)ᵀ := by
  have hTN : Mᵀ * N = 1 := mul_eq_one_comm.mp hNM
  have hdT : (1 + Mᵀ).det ≠ 0 := by
    rw [← transpose_one, ← transpose_add, det_transpose]; exact hM
  have key : (1 + Mᵀ) * (1 - N) = -((1 - Mᵀ) * (1 + N)) := by
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hTN]
    abel
  have hu1 : IsUnit (1 + Mᵀ).det := isUnit_iff_ne_zero.mpr hdT
  have hu2 : IsUnit (1 + N).det := isUnit_iff_ne_zero.mpr hN
  unfold cayMat
  rw [transpose_mul, transpose_nonsing_inv, transpose_add, transpose_sub, transpose_one]
  calc (1 - N) * (1 + N)⁻¹ = (1 + Mᵀ)⁻¹ * ((1 + Mᵀ) * (1 - N)) * (1 + N)⁻¹ := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu1, Matrix.one_mul]
    _ = -((1 + Mᵀ)⁻¹ * (1 - Mᵀ)) := by
        rw [key]
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, mul_nonsing_inv _ hu2, Matrix.mul_one]

section
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (K : Type) [Field K] [CharZero K] (n : ℕ)

noncomputable def linPoly (σ : L →+* K) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin (Module.finrank ℚ L) × Fin n × Fin n) K) :=
  Matrix.of fun a b => ∑ i, MvPolynomial.C (σ (Module.finBasis ℚ L i)) * MvPolynomial.X (i, a, b)

noncomputable def skewPoly (σ : L →+* K) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin (Module.finrank ℚ L) × Fin n × Fin n) K) :=
  linPoly L K n σ - (linPoly L K n (σ.comp (IsCMField.complexConj L : L →+* L)))ᵀ

noncomputable def skewRat (x : Fin (Module.finrank ℚ L) × Fin n × Fin n → ℚ) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun a b => (∑ i, (x (i, a, b) : L) * Module.finBasis ℚ L i) -
    (IsCMField.complexConj L : L →+* L) (∑ i, (x (i, b, a) : L) * Module.finBasis ℚ L i)

/- English proof (translation)
Simplify using `[skewPoly, linPoly, Matrix.sub_apply, Matrix.transpose_apply, map_sum]`.
-/
theorem eval_skewPoly (σ : L →+* K) (x : Fin (Module.finrank ℚ L) × Fin n × Fin n → K) (a b : Fin n) :
    MvPolynomial.eval x (skewPoly L K n σ a b) =
      ∑ i, σ (Module.finBasis ℚ L i) * x (i, a, b) -
        ∑ i, σ ((IsCMField.complexConj L : L →+* L) (Module.finBasis ℚ L i)) * x (i, b, a) := by
  simp [skewPoly, linPoly, Matrix.sub_apply, Matrix.transpose_apply, map_sum]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.map_apply, Matrix.map_apply, eval_skewPoly]`. Simplify using `[skewRat, map_sum, map_sub, mul_comm]`.
-/
theorem skewRat_map (σ : L →+* K) (x : Fin (Module.finrank ℚ L) × Fin n × Fin n → ℚ) :
    (skewRat L n x).map σ = (skewPoly L K n σ).map (MvPolynomial.eval (fun v => (x v : K))) := by
  ext a b
  rw [Matrix.map_apply, Matrix.map_apply, eval_skewPoly]
  simp [skewRat, map_sum, map_sub, mul_comm]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[skewRat, Matrix.add_apply, Matrix.transpose_apply, map_sub, complexConj_invol]`.
-/
theorem skewRat_skew (x : Fin (Module.finrank ℚ L) × Fin n × Fin n → ℚ) :
    skewRat L n x + ((skewRat L n x).map (IsCMField.complexConj L : L →+* L))ᵀ = 0 := by
  ext a b
  simp [skewRat, Matrix.add_apply, Matrix.transpose_apply, map_sub, complexConj_invol]

end
end GlobalTheory.UnitaryDense

namespace GlobalTheory.UnitaryDense

/- English proof (translation)
Introduce `V W K _ g f P`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨MvPolynomial.C a, 0, fun x _ => by simp⟩`. Consider the case `add p q hp hq`. Take `⟨q1, k1, h1⟩` from `hp`.

Take `⟨q2, k2, h2⟩` from `hq`. Use `⟨q1 * g ^ k2 + q2 * g ^ k1, k1 + k2, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, map_mul, map_mul, map_pow, map_pow, ← h1 x hx, ← h2 x hx]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p w hp`.

Take `⟨q1, k1, h1⟩` from `hp`. Use `⟨q1 * f w, k1 + 1, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, ← h1 x hx, MvPolynomial.eval_X]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem clear_denom : ∀ {V W K : Type} [Field K] (g : MvPolynomial V K) (f : W → MvPolynomial V K) (P : MvPolynomial W K), ∃ (q : MvPolynomial V K) (k : ℕ), ∀ x : V → K, MvPolynomial.eval x g ≠ 0 → MvPolynomial.eval (fun w => MvPolynomial.eval x (f w) / MvPolynomial.eval x g) P * (MvPolynomial.eval x g) ^ k = MvPolynomial.eval x q := by
  intro V W K _ g f P
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, 0, fun x _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨q1, k1, h1⟩ := hp
    obtain ⟨q2, k2, h2⟩ := hq
    refine ⟨q1 * g ^ k2 + q2 * g ^ k1, k1 + k2, fun x hx => ?_⟩
    rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, ← h1 x hx, ← h2 x hx]
    ring
  | mul_X p w hp =>
    obtain ⟨q1, k1, h1⟩ := hp
    refine ⟨q1 * f w, k1 + 1, fun x hx => ?_⟩
    rw [map_mul, map_mul, ← h1 x hx, MvPolynomial.eval_X]
    field_simp
    ring

/- English proof (translation)
Introduce `K _ _ n M hM`. Establish `hu : IsUnit (1 + M).det` using `isUnit_iff_ne_zero.mpr hM`. Establish `hc : (1 - M) * (1 + M)⁻¹ = (1 + M)⁻¹ * (1 - M)`. Establish `h1 : (1 + M) * (1 - M) = (1 - M) * (1 + M)`. Simplify using `only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]`.

Normalize the expressions using the abelian group laws. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]`. Use `_ = (1 + M)⁻¹ * (1 - M) := by`. Rewrite using `[h1, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]`.

Establish `hp : 1 + (1 - M) * (1 + M)⁻¹ = (2 : K) • (1 + M)⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.add_mul, Matrix.mul_nonsing_inv _ hu]`. Use `_ = (2 : K) • (1 + M)⁻¹ := by`. Rewrite using `[show (1 + M) + (1 - M) = (2 : K) • (1 : Matrix (Fin n) (Fin n) K) by`.

Rewrite using `[two_smul]`. Use the proof step `abel, Matrix.smul_mul, Matrix.one_mul]`. Establish `hm : 1 - (1 - M) * (1 + M)⁻¹ = (2 : K) • (M * (1 + M)⁻¹)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.sub_mul (1 + M) (1 - M), Matrix.mul_nonsing_inv _ hu]`.

Use `_ = (2 : K) • (M * (1 + M)⁻¹) := by`. Rewrite using `[show (1 + M) - (1 - M) = (2 : K) • M by rw [two_smul]; abel, Matrix.smul_mul]`. Establish `h2 : (2 : K) ≠ 0` using `two_ne_zero`. Establish `hdinv : ((1 + M)⁻¹).det ≠ 0`. Rewrite using `[Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`.

Conclude with `inv_ne_zero hM`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hp, Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ h2) hdinv`. Establish `hinv : ((2 : K) • (1 + M)⁻¹)⁻¹ = (2 : K)⁻¹ • (1 + M)`.

Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ h2, one_smul, Matrix.mul_nonsing_inv _ hu]`. Rewrite using `[hp, hm, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ h2, one_smul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]`.
-/
theorem cay_invol : ∀ {K : Type} [Field K] [CharZero K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K), (1 + M).det ≠ 0 → (1 + (1 - M) * (1 + M)⁻¹).det ≠ 0 ∧ (1 - (1 - M) * (1 + M)⁻¹) * (1 + (1 - M) * (1 + M)⁻¹)⁻¹ = M := by
  intro K _ _ n M hM
  have hu : IsUnit (1 + M).det := isUnit_iff_ne_zero.mpr hM
  have hc : (1 - M) * (1 + M)⁻¹ = (1 + M)⁻¹ * (1 - M) := by
    have h1 : (1 + M) * (1 - M) = (1 - M) * (1 + M) := by
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel
    calc (1 - M) * (1 + M)⁻¹ = (1 + M)⁻¹ * ((1 + M) * (1 - M)) * (1 + M)⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = (1 + M)⁻¹ * (1 - M) := by
          rw [h1, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have hp : 1 + (1 - M) * (1 + M)⁻¹ = (2 : K) • (1 + M)⁻¹ := by
    calc 1 + (1 - M) * (1 + M)⁻¹ = ((1 + M) + (1 - M)) * (1 + M)⁻¹ := by
          rw [Matrix.add_mul, Matrix.mul_nonsing_inv _ hu]
      _ = (2 : K) • (1 + M)⁻¹ := by
          rw [show (1 + M) + (1 - M) = (2 : K) • (1 : Matrix (Fin n) (Fin n) K) by
            rw [two_smul]; abel, Matrix.smul_mul, Matrix.one_mul]
  have hm : 1 - (1 - M) * (1 + M)⁻¹ = (2 : K) • (M * (1 + M)⁻¹) := by
    calc 1 - (1 - M) * (1 + M)⁻¹ = ((1 + M) - (1 - M)) * (1 + M)⁻¹ := by
          rw [Matrix.sub_mul (1 + M) (1 - M), Matrix.mul_nonsing_inv _ hu]
      _ = (2 : K) • (M * (1 + M)⁻¹) := by
          rw [show (1 + M) - (1 - M) = (2 : K) • M by rw [two_smul]; abel, Matrix.smul_mul]
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hdinv : ((1 + M)⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hM
  refine ⟨?_, ?_⟩
  · rw [hp, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ h2) hdinv
  · have hinv : ((2 : K) • (1 + M)⁻¹)⁻¹ = (2 : K)⁻¹ • (1 + M) := by
      apply Matrix.inv_eq_left_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ h2, one_smul,
        Matrix.mul_nonsing_inv _ hu]
    rw [hp, hm, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ h2, one_smul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
end GlobalTheory.UnitaryDense

namespace GlobalTheory.UnitaryDense
open Matrix

section
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (K : Type) [Field K] [CharZero K] (n : ℕ)

/- English proof (translation)
Use `choose y hy using fun ab : Fin n × Fin n => GlobalTheory.T.exists_finBasis_coeffs_embeddings_eval L K (fun σ => Wf σ ab.1 ab.2 / 2)`. Use `⟨fun v => y (v.2.1, v.2.2) v.1, fun σ => ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Rewrite using `[Matrix.map_apply, eval_skewPoly]`. Establish `h1` using `hy (a, b) σ`.

Establish `h2` using `hy (b, a) (σ.comp (IsCMField.complexConj L : L →+* L))`. Simplify using `only [RingHom.comp_apply] at h2`. Simplify using `only`. Rewrite using `[h1, h2, hW σ]`. Simplify using `only [Matrix.neg_apply, Matrix.transpose_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem family_surj (Wf : (L →+* K) → Matrix (Fin n) (Fin n) K)
    (hW : ∀ σ, Wf (σ.comp (IsCMField.complexConj L : L →+* L)) = -(Wf σ)ᵀ) :
    ∃ x : Fin (Module.finrank ℚ L) × Fin n × Fin n → K,
      ∀ σ, (skewPoly L K n σ).map (MvPolynomial.eval x) = Wf σ := by
  choose y hy using fun ab : Fin n × Fin n => GlobalTheory.T.exists_finBasis_coeffs_embeddings_eval L K (fun σ => Wf σ ab.1 ab.2 / 2)
  refine ⟨fun v => y (v.2.1, v.2.2) v.1, fun σ => ?_⟩
  ext a b
  rw [Matrix.map_apply, eval_skewPoly]
  have h1 := hy (a, b) σ
  have h2 := hy (b, a) (σ.comp (IsCMField.complexConj L : L →+* L))
  simp only [RingHom.comp_apply] at h2
  simp only
  rw [h1, h2, hW σ]
  simp only [Matrix.neg_apply, Matrix.transpose_apply]
  ring

/- English proof (translation)
Set `d : (L →+* K) → MvPolynomial (Fin (Module.finrank ℚ L) × Fin n × Fin n) K` to `fun σ => (1 + skewPoly L K n σ).det`. Set `g` to `∏ σ, d σ`. Set `f : (L →+* K) × Fin n × Fin n → MvPolynomial (Fin (Module.finrank ℚ L) × Fin n × Fin n) K` to `fun p => ((1 - skewPoly L K n p.1) * (1 + skewPoly L K n p.1).adjugate) p.2.1 p.2.2 * ∏ τ ∈ Finset.univ.erase p.1, d τ`. Establish `hd : ∀ y σ, MvPolynomial.eval y (d σ) = (1 + (skewPoly L K n σ).map (MvPolynomial.eval y)).det`. Introduce `y σ`.

Simplify using `only [d]`. Rewrite using `[RingHom.map_det, map_add, map_one, RingHom.mapMatrix_apply]`. Establish `hg : ∀ y, MvPolynomial.eval y g = ∏ σ, MvPolynomial.eval y (d σ)` using `fun y => map_prod _ _ _`. Establish `hev : ∀ y, (∀ σ, MvPolynomial.eval y (d σ) ≠ 0) → ∀ p : (L →+* K) × Fin n × Fin n, MvPolynomial.eval y (f p) / MvPolynomial.eval y g = cayMat ((skewPoly L K n p.1).map (MvPolynomial.eval y)) p.2.1 p.2.2`. Introduce `y hy p`.

Establish `hE : MvPolynomial.eval y (∏ τ ∈ Finset.univ.erase p.1, d τ) ≠ 0`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun τ _ => hy τ`. Establish `hsplit : MvPolynomial.eval y g = MvPolynomial.eval y (d p.1) * MvPolynomial.eval y (∏ τ ∈ Finset.univ.erase p.1, d τ)`. Simplify using `only [g]`.

Rewrite using `[← map_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ _)]`. Establish `hN : MvPolynomial.eval y (((1 - skewPoly L K n p.1) * (1 + skewPoly L K n p.1).adjugate) p.2.1 p.2.2) = ((1 - (skewPoly L K n p.1).map (MvPolynomial.eval y)) * (1 + (skewPoly L K n p.1).map (MvPolynomial.eval y)).adjugate) p.2.1 p.2.2`. Establish `e : (MvPolynomial.eval y).mapMatrix ((1 - skewPoly L K n p.1) * (1 + skewPoly L K n p.1).adjugate) = (1 - (skewPoly L K n p.1).map (MvPolynomial.eval y)) * (1 + (skewPoly L K n p.1).map (MvPolynomial.eval y)).adjugate`. Rewrite using `[map_mul, map_sub, map_one, RingHom.map_adjugate, map_add, map_one]`. Both sides reduce to the same expression.

Conclude with `congrFun (congrFun e _) _`. Simplify using `only [f]`. Rewrite using `[map_mul, hN, hsplit, mul_div_mul_right _ _ hE, hd]`. Unfold `cayMat`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Take `⟨q, k, hq⟩` from `clear_denom g f P`. Establish `h0 : ∀ σ, skewPoly L K n σ = skewPoly L K n σ` using `fun _ => rfl`. Establish `hq0 : q * g = 0`. Apply `eq_zero_of_rat_points` to reduce the goal to its premises.

Introduce `xr`. Use `set y : Fin (Module.finrank ℚ L) × Fin n × Fin n → K := fun v => (xr v : K)`. Rewrite using `[map_mul]`. Distinguish the cases in `hgy : MvPolynomial.eval y g = 0`. Rewrite using `[hgy, mul_zero]`.

Establish `hy : ∀ σ, MvPolynomial.eval y (d σ) ≠ 0`. Rewrite `hgy` using `[hg]`. Conclude with `fun σ => (Finset.prod_ne_zero_iff.mp hgy) σ (Finset.mem_univ σ)`. Rewrite using `[← hq y hgy]`. Apply `mul_eq_zero_of_left` to reduce the goal to its premises.

Apply `mul_eq_zero_of_left` to reduce the goal to its premises. Establish `hfun : (fun w => MvPolynomial.eval y (f w) / MvPolynomial.eval y g) = fun p : (L →+* K) × Fin n × Fin n => p.1 ((cayMat (skewRat L n xr)) p.2.1 p.2.2)`. Use function extensionality and compare the values at `p`. Rewrite using `[hev y hy p, ← Matrix.map_apply (f := p.1), cayMat_map, skewRat_map]`. Rewrite using `[hfun]`.

Use `set A := skewRat L n xr`. Take `σ₀` from `Classical.arbitrary (L →+* K)`. Establish `hA : (1 - -A).det ≠ 0`. Rewrite using `[sub_neg_eq_add]`. Introduce `h`.

Apply `hy σ₀` to reduce the goal to its premises. Rewrite using `[hd, ← skewRat_map, ← Matrix.map_one σ₀ (map_zero σ₀) (map_one σ₀), ← Matrix.map_add σ₀ (map_add σ₀), ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]`. Establish `hskew : -A + ((-A).map (IsCMField.complexConj L : L →+* L))ᵀ = 0`. Use `skewRat_skew L n xr` as an intermediate fact. Rewrite using `[Matrix.map_neg _ (map_neg _), transpose_neg, ← neg_add, this, neg_zero]`.

Take `⟨γ₀, hγ, hγe⟩` from `GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian L n (-A) hskew hA`. Establish `: cayMat A = (γ₀ : Matrix (Fin n) (Fin n) L)`. Rewrite using `[hγe, cayMat, sub_neg_eq_add, ← sub_eq_add_neg]`. Rewrite using `[this]`. Conclude with `hP γ₀ hγ`.

Establish `hgne : g ≠ 0`. Introduce `h`. Use `congrArg (MvPolynomial.eval (0 : Fin (Module.finrank ℚ L) × Fin n × Fin n → K)) h` as an intermediate fact. Rewrite `this` using `[hg, map_zero]`. Use `Finset.prod_ne_zero_iff.mpr (fun σ _ => ?_) this` and prove the remaining obligations.

Rewrite using `[hd]`. Establish `: (skewPoly L K n σ).map (MvPolynomial.eval 0) = 0`. Use extensionality with `a b`. Rewrite using `[Matrix.map_apply, eval_skewPoly]`. Simplify using the standard rewrite rules.

Rewrite using `[this, add_zero, det_one]`. Conclude with `one_ne_zero`. Establish `hq' : q = 0` using `(mul_eq_zero.mp hq0).resolve_right hgne`. Establish `hxd : ∀ σ, MvPolynomial.eval x (d σ) ≠ 0` using `fun σ => by rw [hd]; exact hx σ`. Establish `hgx : MvPolynomial.eval x g ≠ 0`.

Rewrite using `[hg]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun σ _ => hxd σ`. Use `hq x hgx` as an intermediate fact. Rewrite `this` using `[hq', map_zero]`. Establish `h2` using `(mul_eq_zero.mp this).resolve_right (pow_ne_zero _ hgx)`.

Establish `hfun : (fun w => MvPolynomial.eval x (f w) / MvPolynomial.eval x g) = fun p : (L →+* K) × Fin n × Fin n => cayMat ((skewPoly L K n p.1).map (MvPolynomial.eval x)) p.2.1 p.2.2`. Use function extensionality and compare the values at `(hev x hxd)`. Rewrite `h2` using `[hfun]`. Conclude with `h2`.
-/
theorem generic_vanish [Nonempty (L →+* K)] (P : MvPolynomial ((L →+* K) × Fin n × Fin n) K)
    (hP : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) P = 0)
    (x : Fin (Module.finrank ℚ L) × Fin n × Fin n → K)
    (hx : ∀ σ, (1 + (skewPoly L K n σ).map (MvPolynomial.eval x)).det ≠ 0) :
    MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n =>
      cayMat ((skewPoly L K n p.1).map (MvPolynomial.eval x)) p.2.1 p.2.2) P = 0 := by
  classical
  let d : (L →+* K) → MvPolynomial (Fin (Module.finrank ℚ L) × Fin n × Fin n) K :=
    fun σ => (1 + skewPoly L K n σ).det
  let g := ∏ σ, d σ
  let f : (L →+* K) × Fin n × Fin n → MvPolynomial (Fin (Module.finrank ℚ L) × Fin n × Fin n) K :=
    fun p => ((1 - skewPoly L K n p.1) * (1 + skewPoly L K n p.1).adjugate) p.2.1 p.2.2 *
      ∏ τ ∈ Finset.univ.erase p.1, d τ
  have hd : ∀ y σ, MvPolynomial.eval y (d σ) = (1 + (skewPoly L K n σ).map (MvPolynomial.eval y)).det := by
    intro y σ
    simp only [d]
    rw [RingHom.map_det, map_add, map_one, RingHom.mapMatrix_apply]
  have hg : ∀ y, MvPolynomial.eval y g = ∏ σ, MvPolynomial.eval y (d σ) := fun y => map_prod _ _ _
  have hev : ∀ y, (∀ σ, MvPolynomial.eval y (d σ) ≠ 0) → ∀ p : (L →+* K) × Fin n × Fin n,
      MvPolynomial.eval y (f p) / MvPolynomial.eval y g =
        cayMat ((skewPoly L K n p.1).map (MvPolynomial.eval y)) p.2.1 p.2.2 := by
    intro y hy p
    have hE : MvPolynomial.eval y (∏ τ ∈ Finset.univ.erase p.1, d τ) ≠ 0 := by
      rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun τ _ => hy τ
    have hsplit : MvPolynomial.eval y g = MvPolynomial.eval y (d p.1) *
        MvPolynomial.eval y (∏ τ ∈ Finset.univ.erase p.1, d τ) := by
      simp only [g]; rw [← map_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ _)]
    have hN : MvPolynomial.eval y (((1 - skewPoly L K n p.1) * (1 + skewPoly L K n p.1).adjugate) p.2.1 p.2.2) =
        ((1 - (skewPoly L K n p.1).map (MvPolynomial.eval y)) *
          (1 + (skewPoly L K n p.1).map (MvPolynomial.eval y)).adjugate) p.2.1 p.2.2 := by
      have e : (MvPolynomial.eval y).mapMatrix ((1 - skewPoly L K n p.1) * (1 + skewPoly L K n p.1).adjugate) =
          (1 - (skewPoly L K n p.1).map (MvPolynomial.eval y)) *
            (1 + (skewPoly L K n p.1).map (MvPolynomial.eval y)).adjugate := by
        rw [map_mul, map_sub, map_one, RingHom.map_adjugate, map_add, map_one]; rfl
      exact congrFun (congrFun e _) _
    simp only [f]
    rw [map_mul, hN, hsplit, mul_div_mul_right _ _ hE, hd]
    unfold cayMat
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    field_simp
  obtain ⟨q, k, hq⟩ := clear_denom g f P
  have h0 : ∀ σ, skewPoly L K n σ = skewPoly L K n σ := fun _ => rfl
  have hq0 : q * g = 0 := by
    apply eq_zero_of_rat_points
    intro xr
    set y : Fin (Module.finrank ℚ L) × Fin n × Fin n → K := fun v => (xr v : K)
    rw [map_mul]
    by_cases hgy : MvPolynomial.eval y g = 0
    · rw [hgy, mul_zero]
    · have hy : ∀ σ, MvPolynomial.eval y (d σ) ≠ 0 := by
        rw [hg] at hgy; exact fun σ => (Finset.prod_ne_zero_iff.mp hgy) σ (Finset.mem_univ σ)
      rw [← hq y hgy]
      apply mul_eq_zero_of_left
      apply mul_eq_zero_of_left
      have hfun : (fun w => MvPolynomial.eval y (f w) / MvPolynomial.eval y g) =
          fun p : (L →+* K) × Fin n × Fin n => p.1 ((cayMat (skewRat L n xr)) p.2.1 p.2.2) := by
        funext p
        rw [hev y hy p, ← Matrix.map_apply (f := p.1), cayMat_map, skewRat_map]
      rw [hfun]
      set A := skewRat L n xr
      obtain σ₀ := Classical.arbitrary (L →+* K)
      have hA : (1 - -A).det ≠ 0 := by
        rw [sub_neg_eq_add]
        intro h
        apply hy σ₀
        rw [hd, ← skewRat_map, ← Matrix.map_one σ₀ (map_zero σ₀) (map_one σ₀),
          ← Matrix.map_add σ₀ (map_add σ₀), ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
      have hskew : -A + ((-A).map (IsCMField.complexConj L : L →+* L))ᵀ = 0 := by
        have := skewRat_skew L n xr
        rw [Matrix.map_neg _ (map_neg _), transpose_neg, ← neg_add, this, neg_zero]
      obtain ⟨γ₀, hγ, hγe⟩ := GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian L n (-A) hskew hA
      have : cayMat A = (γ₀ : Matrix (Fin n) (Fin n) L) := by
        rw [hγe, cayMat, sub_neg_eq_add, ← sub_eq_add_neg]
      rw [this]
      exact hP γ₀ hγ
  have hgne : g ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval (0 : Fin (Module.finrank ℚ L) × Fin n × Fin n → K)) h
    rw [hg, map_zero] at this
    refine Finset.prod_ne_zero_iff.mpr (fun σ _ => ?_) this
    rw [hd]
    have : (skewPoly L K n σ).map (MvPolynomial.eval 0) = 0 := by
      ext a b; rw [Matrix.map_apply, eval_skewPoly]; simp
    rw [this, add_zero, det_one]; exact one_ne_zero
  have hq' : q = 0 := (mul_eq_zero.mp hq0).resolve_right hgne
  have hxd : ∀ σ, MvPolynomial.eval x (d σ) ≠ 0 := fun σ => by rw [hd]; exact hx σ
  have hgx : MvPolynomial.eval x g ≠ 0 := by
    rw [hg]; exact Finset.prod_ne_zero_iff.mpr fun σ _ => hxd σ
  have := hq x hgx
  rw [hq', map_zero] at this
  have h2 := (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ hgx)
  have hfun : (fun w => MvPolynomial.eval x (f w) / MvPolynomial.eval x g) =
      fun p : (L →+* K) × Fin n × Fin n => cayMat ((skewPoly L K n p.1).map (MvPolynomial.eval x)) p.2.1 p.2.2 :=
    funext (hev x hxd)
  rw [hfun] at h2
  exact h2

/- English proof (translation)
Establish `hW : ∀ σ, cayMat (B (σ.comp (IsCMField.complexConj L : L →+* L))) = -(cayMat (B σ))ᵀ` using `fun σ => cayMat_transpose (B σ) _ (hB σ) (hB1 σ) (hB1 _)`. Take `⟨x, hx⟩` from `family_surj L K n (fun σ => cayMat (B σ)) hW`. Establish `h` using `generic_vanish L K n P hP x (fun σ => by rw [hx σ]; exact (cay_invol (B σ) (hB1 σ)).1)`. Establish `hfun : (fun p : (L →+* K) × Fin n × Fin n => cayMat ((skewPoly L K n p.1).map (MvPolynomial.eval x)) p.2.1 p.2.2) = fun p : (L →+* K) × Fin n × Fin n => B p.1 p.2.1 p.2.2`. Use function extensionality and compare the values at `p`.

Rewrite using `[hx p.1]`. Conclude with `congrFun (congrFun (cay_invol (B p.1) (hB1 p.1)).2 _) _`. Rewrite `h` using `[hfun]`. Conclude with `h`.
-/
theorem vanish_good [Nonempty (L →+* K)] (P : MvPolynomial ((L →+* K) × Fin n × Fin n) K)
    (hP : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) P = 0)
    (B : (L →+* K) → Matrix (Fin n) (Fin n) K)
    (hB : ∀ σ, B (σ.comp (IsCMField.complexConj L : L →+* L)) * (B σ)ᵀ = 1)
    (hB1 : ∀ σ, (1 + B σ).det ≠ 0) :
    MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => B p.1 p.2.1 p.2.2) P = 0 := by
  have hW : ∀ σ, cayMat (B (σ.comp (IsCMField.complexConj L : L →+* L))) = -(cayMat (B σ))ᵀ :=
    fun σ => cayMat_transpose (B σ) _ (hB σ) (hB1 σ) (hB1 _)
  obtain ⟨x, hx⟩ := family_surj L K n (fun σ => cayMat (B σ)) hW
  have h := generic_vanish L K n P hP x (fun σ => by rw [hx σ]; exact (cay_invol (B σ) (hB1 σ)).1)
  have hfun : (fun p : (L →+* K) × Fin n × Fin n =>
      cayMat ((skewPoly L K n p.1).map (MvPolynomial.eval x)) p.2.1 p.2.2) =
      fun p : (L →+* K) × Fin n × Fin n => B p.1 p.2.1 p.2.2 := by
    funext p
    rw [hx p.1]
    exact congrFun (congrFun (cay_invol (B p.1) (hB1 p.1)).2 _) _
  rw [hfun] at h
  exact h

end

/- English proof (translation)
Introduce `L _ _ _ n K _ _ P hP B hB`. Break down `isEmpty_or_nonempty (L →+* K) with hS | hS` into its components or cases. Establish `h1` using `hP 1 (one_mem _)`. Establish `hfun : (fun p : (L →+* K) × Fin n × Fin n => ((B p.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.2.1 p.2.2) = fun p : (L →+* K) × Fin n × Fin n => p.1 (((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)`. Use function extensionality and compare the values at `p`.

Conclude with `(hS.false p.1).elim`. Rewrite using `[hfun]`. Conclude with `h1`. Use `set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc`. Set `Bm : (L →+* K) → Matrix (Fin n) (Fin n) K` to `fun σ => ((B σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)`.

Establish `hBm : ∀ σ, Bm (σ.comp c) * (Bm σ)ᵀ = 1`. Introduce `σ`. Simplify using `only [Bm]`. Rewrite using `[hB σ, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]`. Take `⟨u, hu, hdet⟩` from `GlobalTheory.T.exists_normOne_cmField_det_one_add_ne_zero_charZero L K n Bm`.

Establish `hσu : ∀ σ : L →+* K, σ (c u) * σ u = 1` using `fun σ => by`. Rewrite using `[← map_mul, mul_comm, hu, map_one]`. Set `B' : (L →+* K) → Matrix (Fin n) (Fin n) K` to `fun σ => σ u • Bm σ`. Establish `hB' : ∀ σ, B' (σ.comp c) * (B' σ)ᵀ = 1`. Introduce `σ`.

Simplify using `only [B', RingHom.comp_apply, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hBm σ, smul_smul]`. Rewrite using `[mul_comm, hσu, one_smul]`. Set `P'` to `MvPolynomial.bind₁ (fun p : (L →+* K) × Fin n × Fin n => MvPolynomial.C (p.1 (c u)) * MvPolynomial.X p) P`. Establish `hP' : ∀ y, MvPolynomial.eval y P' = MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 (c u) * y p) P`. Introduce `y`.

Simplify using `only [P']`. Express the relevant statement in the definitionally equal form `MvPolynomial.eval₂Hom (RingHom.id K) y _ = MvPolynomial.eval₂Hom (RingHom.id K) _ P`. Rewrite using `[MvPolynomial.eval₂Hom_bind₁]`. Simplify using the standard rewrite rules. Establish `hcu : c u * u = 1` using `by rw [mul_comm]; exact hu`.

Set `s : GL (Fin n) L` to `⟨Matrix.scalar (Fin n) (c u), Matrix.scalar (Fin n) u, by rw [← map_mul, hcu, map_one], by rw [← map_mul, hu, map_one]⟩`. Establish `hs : s ∈ GQ0 L n` using `by show Matrix.scalar (Fin n) (c u) * conjT c (Matrix.scalar (Fin n) (c u)) = 1`. Establish `: conjT c (Matrix.scalar (Fin n) (c u)) = Matrix.scalar (Fin n) u`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `[conjT, hc, complexConj_invol]`. Simplify using `[conjT, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]`. Rewrite using `[this, ← map_mul, hcu, map_one]`. Establish `hQ : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) P' = 0`.

Introduce `γ₀ hγ`. Rewrite using `[hP']`. Use `hP (s * γ₀) (mul_mem hs hγ)` as an intermediate fact. Establish `e : (fun p : (L →+* K) × Fin n × Fin n => p.1 (c u) * p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) = fun p : (L →+* K) × Fin n × Fin n => p.1 (((s * γ₀ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)`. Use function extensionality and compare the values at `p`.

Simplify using `[s, Matrix.scalar_apply, Matrix.diagonal_mul, map_mul]`. Rewrite using `[e]`. Conclude with `this`. Establish `h` using `vanish_good L K n P' hQ B' hB' hdet`. Rewrite `h` using `[hP']`.

Establish `e : (fun p : (L →+* K) × Fin n × Fin n => p.1 (c u) * B' p.1 p.2.1 p.2.2) = fun p : (L →+* K) × Fin n × Fin n => ((B p.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.2.1 p.2.2`. Use function extensionality and compare the values at `p`. Simplify using `only [B', Bm, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hσu, one_mul]`. Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem unitary_points_dense : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] [CharZero K]
    (P : MvPolynomial ((L →+* K) × Fin n × Fin n) K),
    (∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) P = 0) →
    ∀ B : (L →+* K) → GL (Fin n) K,
      (∀ σ : L →+* K, ((B (σ.comp (IsCMField.complexConj L : L →+* L)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Matrix.transpose (((B σ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) →
      MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => ((B p.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.2.1 p.2.2) P = 0 := by
  intro L _ _ _ n K _ _ P hP B hB
  classical
  rcases isEmpty_or_nonempty (L →+* K) with hS | hS
  · have h1 := hP 1 (one_mem _)
    have hfun : (fun p : (L →+* K) × Fin n × Fin n => ((B p.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.2.1 p.2.2) =
        fun p : (L →+* K) × Fin n × Fin n => p.1 (((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2) := by
      funext p; exact (hS.false p.1).elim
    rw [hfun]; exact h1
  · set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
    let Bm : (L →+* K) → Matrix (Fin n) (Fin n) K := fun σ => ((B σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    have hBm : ∀ σ, Bm (σ.comp c) * (Bm σ)ᵀ = 1 := by
      intro σ
      simp only [Bm]
      rw [hB σ, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]
    obtain ⟨u, hu, hdet⟩ := GlobalTheory.T.exists_normOne_cmField_det_one_add_ne_zero_charZero L K n Bm
    have hσu : ∀ σ : L →+* K, σ (c u) * σ u = 1 := fun σ => by
      rw [← map_mul, mul_comm, hu, map_one]
    let B' : (L →+* K) → Matrix (Fin n) (Fin n) K := fun σ => σ u • Bm σ
    have hB' : ∀ σ, B' (σ.comp c) * (B' σ)ᵀ = 1 := by
      intro σ
      simp only [B', RingHom.comp_apply, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hBm σ, smul_smul]
      rw [mul_comm, hσu, one_smul]
    let P' := MvPolynomial.bind₁ (fun p : (L →+* K) × Fin n × Fin n =>
      MvPolynomial.C (p.1 (c u)) * MvPolynomial.X p) P
    have hP' : ∀ y, MvPolynomial.eval y P' = MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 (c u) * y p) P := by
      intro y
      simp only [P']
      change MvPolynomial.eval₂Hom (RingHom.id K) y _ = MvPolynomial.eval₂Hom (RingHom.id K) _ P
      rw [MvPolynomial.eval₂Hom_bind₁]
      simp
    have hcu : c u * u = 1 := by rw [mul_comm]; exact hu
    let s : GL (Fin n) L := ⟨Matrix.scalar (Fin n) (c u), Matrix.scalar (Fin n) u,
      by rw [← map_mul, hcu, map_one], by rw [← map_mul, hu, map_one]⟩
    have hs : s ∈ GQ0 L n := by
      show Matrix.scalar (Fin n) (c u) * conjT c (Matrix.scalar (Fin n) (c u)) = 1
      have : conjT c (Matrix.scalar (Fin n) (c u)) = Matrix.scalar (Fin n) u := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [conjT, hc, complexConj_invol]
        · simp [conjT, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]
      rw [this, ← map_mul, hcu, map_one]
    have hQ : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
        MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) P' = 0 := by
      intro γ₀ hγ
      rw [hP']
      have := hP (s * γ₀) (mul_mem hs hγ)
      have e : (fun p : (L →+* K) × Fin n × Fin n => p.1 (c u) * p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) =
          fun p : (L →+* K) × Fin n × Fin n => p.1 (((s * γ₀ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2) := by
        funext p
        simp [s, Matrix.scalar_apply, Matrix.diagonal_mul, map_mul]
      rw [e]; exact this
    have h := vanish_good L K n P' hQ B' hB' hdet
    rw [hP'] at h
    have e : (fun p : (L →+* K) × Fin n × Fin n => p.1 (c u) * B' p.1 p.2.1 p.2.2) =
        fun p : (L →+* K) × Fin n × Fin n => ((B p.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.2.1 p.2.2 := by
      funext p
      simp only [B', Bm, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hσu, one_mul]
    rw [e] at h; exact h

end GlobalTheory.UnitaryDense
