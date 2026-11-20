import Formalism.HermitianCurvature.FrameExists2

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

namespace HermitianFormRankFour

section L2

open scoped Matrix.Norms.L2Operator

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hfin : (spectrum ℂ A).Finite`. Rewrite using `[← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) ℂ ≃ₐ[ℂ] _) A]`. Conclude with `Module.End.finite_spectrum _`.

Use `Set.Icc_infinite Real.pi_pos (Set.Finite.of_finite_image (f := fun θ : ℝ => -Complex.exp (θ * Complex.I)) (hfin.subset ?_) ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨θ, _, rfl⟩`. Conclude with `h θ`. Introduce `θ1 h1 θ2 h2 he`. Apply `Real.injOn_cos h1 h2` to reduce the goal to its premises.

Use `congrArg Complex.re he` as an intermediate fact. Simplify `this` using `[Complex.exp_ofReal_mul_I_re]`.
-/
theorem exists_theta {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ∃ θ : ℝ, -Complex.exp (θ * Complex.I) ∉ spectrum ℂ A := by
  by_contra h
  push_neg at h
  have hfin : (spectrum ℂ A).Finite := by
    rw [← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) ℂ ≃ₐ[ℂ] _) A]
    exact Module.End.finite_spectrum _
  refine Set.Icc_infinite Real.pi_pos
    (Set.Finite.of_finite_image (f := fun θ : ℝ => -Complex.exp (θ * Complex.I)) (hfin.subset ?_) ?_)
  · rintro _ ⟨θ, _, rfl⟩
    exact h θ
  · intro θ1 h1 θ2 h2 he
    apply Real.injOn_cos h1 h2
    have := congrArg Complex.re he
    simpa [Complex.exp_ofReal_mul_I_re] using this

/- English proof (translation)
Take `⟨θ, hθ⟩` from `exists_theta A`. Establish `hA' : A * Aᴴ = 1` using `mul_eq_one_comm.1 hA`. Use `set c : ℂ := Complex.exp (-(θ * Complex.I)) with hc`. Establish `hc0 : c ≠ 0` using `Complex.exp_ne_zero _`. Establish `hcc : star c * c = 1`.

Rewrite using `[hc, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]`. Simplify using the standard rewrite rules. Establish `hu : c • A ∈ unitary (Matrix (Fin k) (Fin k) ℂ)`. Rewrite using `[Unitary.mem_iff, star_smul, Matrix.star_eq_conjTranspose]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[smul_mul_smul_comm, hA, hcc, one_smul]`. Rewrite using `[smul_mul_smul_comm, hA', mul_comm, hcc, one_smul]`. Establish `hsp : (-1 : ℂ) ∉ spectrum ℂ (c • A)`. Introduce `h`. Apply `hθ` to reduce the goal to its premises.

Establish `h2` using `(spectrum.smul_mem_smul_iff (a := A) (s := -Complex.exp (θ * Complex.I)) (r := Units.mk0 c hc0)).1`. Apply `h2` to reduce the goal to its premises. Establish `e1 : (Units.mk0 c hc0) • (-Complex.exp (θ * Complex.I)) = (-1 : ℂ)` using `by show c * (-Complex.exp (θ * Complex.I)) = -1`. Rewrite using `[hc, mul_neg, ← Complex.exp_add]`. Simplify using the standard rewrite rules.

Rewrite using `[e1]`. Conclude with `h`. Establish `hn` using `(Unitary.norm_sub_one_lt_two_iff hu).2 hsp`. Establish `he` using `expUnitary_argSelfAdjoint (u := ⟨c • A, hu⟩) hn`. Establish `he2 : NormedSpace.exp (Complex.I • (Unitary.argSelfAdjoint ⟨c • A, hu⟩ : Matrix (Fin k) (Fin k) ℂ)) = c • A`.

Use `congrArg Subtype.val he` as an intermediate fact. Rewrite `this` using `[selfAdjoint.expUnitary_coe]`. Then use the resulting hypothesis. Use `set S : Matrix (Fin k) (Fin k) ℂ := (Unitary.argSelfAdjoint ⟨c • A, hu⟩ : Matrix (Fin k) (Fin k) ℂ) with hS`. Establish `hSs : Sᴴ = S` using `(Unitary.argSelfAdjoint ⟨c • A, hu⟩).2`. Use `⟨algebraMap ℂ _ (θ * Complex.I) + Complex.I • S, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hSs, Algebra.algebraMap_eq_smul_one, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]`. Simplify using `[add_comm]`. Set `: NormedAlgebra ℚ (Matrix (Fin k) (Fin k) ℂ)` to `.restrictScalars ℚ ℂ _`. Rewrite using `[NormedSpace.exp_add_of_commute (Algebra.commutes _ _), he2, ← NormedSpace.algebraMap_exp_comm, ← Complex.exp_eq_exp_ℂ, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul, hc, ← Complex.exp_add]`. Simplify using the standard rewrite rules.
-/
theorem exists_skew_hermitian_log_unitary {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (hA : Aᴴ * A = 1) :
    ∃ B : Matrix (Fin k) (Fin k) ℂ, Bᴴ = -B ∧ NormedSpace.exp B = A := by
  obtain ⟨θ, hθ⟩ := exists_theta A
  have hA' : A * Aᴴ = 1 := mul_eq_one_comm.1 hA
  set c : ℂ := Complex.exp (-(θ * Complex.I)) with hc
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hcc : star c * c = 1 := by
    rw [hc, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  have hu : c • A ∈ unitary (Matrix (Fin k) (Fin k) ℂ) := by
    rw [Unitary.mem_iff, star_smul, Matrix.star_eq_conjTranspose]
    constructor
    · rw [smul_mul_smul_comm, hA, hcc, one_smul]
    · rw [smul_mul_smul_comm, hA', mul_comm, hcc, one_smul]
  have hsp : (-1 : ℂ) ∉ spectrum ℂ (c • A) := by
    intro h
    apply hθ
    have h2 := (spectrum.smul_mem_smul_iff (a := A) (s := -Complex.exp (θ * Complex.I)) (r := Units.mk0 c hc0)).1
    apply h2
    have e1 : (Units.mk0 c hc0) • (-Complex.exp (θ * Complex.I)) = (-1 : ℂ) := by
      show c * (-Complex.exp (θ * Complex.I)) = -1
      rw [hc, mul_neg, ← Complex.exp_add]
      simp
    rw [e1]
    exact h
  have hn := (Unitary.norm_sub_one_lt_two_iff hu).2 hsp
  have he := expUnitary_argSelfAdjoint (u := ⟨c • A, hu⟩) hn
  have he2 : NormedSpace.exp (Complex.I • (Unitary.argSelfAdjoint ⟨c • A, hu⟩ : Matrix (Fin k) (Fin k) ℂ)) = c • A := by
    have := congrArg Subtype.val he
    rwa [selfAdjoint.expUnitary_coe] at this
  set S : Matrix (Fin k) (Fin k) ℂ := (Unitary.argSelfAdjoint ⟨c • A, hu⟩ : Matrix (Fin k) (Fin k) ℂ) with hS
  have hSs : Sᴴ = S := (Unitary.argSelfAdjoint ⟨c • A, hu⟩).2
  refine ⟨algebraMap ℂ _ (θ * Complex.I) + Complex.I • S, ?_, ?_⟩
  · rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hSs, Algebra.algebraMap_eq_smul_one,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp [add_comm]
  · let : NormedAlgebra ℚ (Matrix (Fin k) (Fin k) ℂ) := .restrictScalars ℚ ℂ _
    rw [NormedSpace.exp_add_of_commute (Algebra.commutes _ _), he2, ← NormedSpace.algebraMap_exp_comm,
      ← Complex.exp_eq_exp_ℂ, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul, hc, ← Complex.exp_add]
    simp

end L2

/- English proof (translation)
The claim follows from `exists_skew_hermitian_log_unitary A hA`.
-/
theorem unitary_log {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (hA : Aᴴ * A = 1) :
    ∃ B : Matrix (Fin k) (Fin k) ℂ, Bᴴ = -B ∧ NormedSpace.exp B = A := exists_skew_hermitian_log_unitary A hA

section Core

variable {N K J : Type} [Fintype N] [Fintype K] [Fintype J] [DecidableEq N] [DecidableEq K] [DecidableEq J]

/- English proof (translation)
Use `letI : NormedRing (Matrix N N ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix N N ℂ) := Matrix.linftyOpNormedAlgebra`. Use `letI : NormedRing (Matrix K K ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix K K ℂ) := Matrix.linftyOpNormedAlgebra`. Establish `hp : ∀ n : ℕ, X ^ n * V = V * B ^ n`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]`. Set `fL : Matrix N N ℂ →+ Matrix N K ℂ` to `⟨⟨fun M => M * V, Matrix.zero_mul V⟩, fun a b => Matrix.add_mul a b V⟩`.

Set `fR : Matrix K K ℂ →+ Matrix N K ℂ` to `⟨⟨fun M => V * M, Matrix.mul_zero V⟩, fun a b => Matrix.mul_add V a b⟩`. Establish `h1` using `(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X).map fL (show Continuous (fun M : Matrix N N ℂ => M * V) from continuous_id.matrix_mul continuous_const)`. Establish `h2` using `(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B).map fR (show Continuous (fun M : Matrix K K ℂ => V * M) from continuous_const.matrix_mul continuous_id)`. Establish `e : (⇑fL ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • X ^ n) = (⇑fR ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • B ^ n)`. Use function extensionality and compare the values at `n`.

Simplify using `only [Function.comp_apply, fL, fR, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.smul_mul, Matrix.mul_smul, hp]`. Rewrite `h1` using `[e]`. Conclude with `h1.unique h2`.
-/
theorem exp_semiconj (X : Matrix N N ℂ) (B : Matrix K K ℂ) (V : Matrix N K ℂ) (h : X * V = V * B) :
    NormedSpace.exp X * V = V * NormedSpace.exp B := by
  letI : NormedRing (Matrix N N ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix N N ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix K K ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix K K ℂ) := Matrix.linftyOpNormedAlgebra
  have hp : ∀ n : ℕ, X ^ n * V = V * B ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  let fL : Matrix N N ℂ →+ Matrix N K ℂ := ⟨⟨fun M => M * V, Matrix.zero_mul V⟩, fun a b => Matrix.add_mul a b V⟩
  let fR : Matrix K K ℂ →+ Matrix N K ℂ := ⟨⟨fun M => V * M, Matrix.mul_zero V⟩, fun a b => Matrix.mul_add V a b⟩
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X).map fL
    (show Continuous (fun M : Matrix N N ℂ => M * V) from continuous_id.matrix_mul continuous_const)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B).map fR
    (show Continuous (fun M : Matrix K K ℂ => V * M) from continuous_const.matrix_mul continuous_id)
  have e : (⇑fL ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • X ^ n) = (⇑fR ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • B ^ n) := by
    funext n
    simp only [Function.comp_apply, fL, fR, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.smul_mul, Matrix.mul_smul, hp]
  rw [e] at h1
  exact h1.unique h2

variable {V : Matrix N K ℂ} {C : Matrix N J ℂ} {Vd : Matrix K N ℂ} {Cd : Matrix J N ℂ}

/- English proof (translation)
Establish `hQP : fromRows Vd Cd * fromCols V C = 1`. Rewrite using `[fromRows_mul_fromCols, h1, h2, h3, h4, fromBlocks_one]`. Use `(mul_eq_one_comm_of_equiv e).mpr hQP` as an intermediate fact. Rewrite `this` using `[fromCols_mul_fromRows]`. Then use the resulting hypothesis.
-/
theorem complete (e : N ≃ K ⊕ J) (h1 : Vd * V = 1) (h2 : Vd * C = 0) (h3 : Cd * V = 0) (h4 : Cd * C = 1) :
    V * Vd + C * Cd = 1 := by
  have hQP : fromRows Vd Cd * fromCols V C = 1 := by
    rw [fromRows_mul_fromCols, h1, h2, h3, h4, fromBlocks_one]
  have := (mul_eq_one_comm_of_equiv e).mpr hQP
  rwa [fromCols_mul_fromRows] at this

/- English proof (translation)
Establish `e1 : V * B * Vd * V = V * B` using `by rw [Matrix.mul_assoc, h1, Matrix.mul_one]`. Establish `e2 : V * B * Vd * C = C * (0 : Matrix J J ℂ)` using `by rw [Matrix.mul_assoc, h2, Matrix.mul_zero, Matrix.mul_zero]`. Establish `s1` using `exp_semiconj (V * B * Vd) B V e1`. Establish `s2` using `exp_semiconj (V * B * Vd) (0 : Matrix J J ℂ) C e2`. Rewrite `s2` using `[NormedSpace.exp_zero, Matrix.mul_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hc, Matrix.mul_one]`. Use `_ = V * NormedSpace.exp B * Vd + C * Cd := by`. Rewrite using `[Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, s1, s2]`.
-/
theorem exp_lift (hc : V * Vd + C * Cd = 1) (h1 : Vd * V = 1) (h2 : Vd * C = 0) (B : Matrix K K ℂ) :
    NormedSpace.exp (V * B * Vd) = V * NormedSpace.exp B * Vd + C * Cd := by
  have e1 : V * B * Vd * V = V * B := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have e2 : V * B * Vd * C = C * (0 : Matrix J J ℂ) := by rw [Matrix.mul_assoc, h2, Matrix.mul_zero, Matrix.mul_zero]
  have s1 := exp_semiconj (V * B * Vd) B V e1
  have s2 := exp_semiconj (V * B * Vd) (0 : Matrix J J ℂ) C e2
  rw [NormedSpace.exp_zero, Matrix.mul_one] at s2
  calc NormedSpace.exp (V * B * Vd) = NormedSpace.exp (V * B * Vd) * (V * Vd + C * Cd) := by
        rw [hc, Matrix.mul_one]
    _ = V * NormedSpace.exp B * Vd + C * Cd := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, s1, s2]

/- English proof (translation)
Establish `e1 : h * V = V * (Vd * h * V)`. Combine the equalities or inequalities in the displayed calculation. Use `⟨e1, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem decomp (hc : V * Vd + C * Cd = 1) (h3 : Cd * V = 0) (h : Matrix N N ℂ) (hC : h * C = C) (hCd : Cd * h = Cd) :
    h * V = V * (Vd * h * V) ∧ h = V * (Vd * h * V) * Vd + C * Cd := by
  have e1 : h * V = V * (Vd * h * V) := by
    calc h * V = (V * Vd + C * Cd) * (h * V) := by rw [hc, Matrix.one_mul]
      _ = V * (Vd * h * V) + C * (Cd * h * V) := by simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = V * (Vd * h * V) := by rw [hCd, h3, Matrix.mul_zero, add_zero]
  refine ⟨e1, ?_⟩
  calc h = h * (V * Vd + C * Cd) := by rw [hc, Matrix.mul_one]
    _ = h * V * Vd + h * C * Cd := by simp only [Matrix.mul_add, Matrix.mul_assoc]
    _ = V * (Vd * h * V) * Vd + C * Cd := by rw [e1, hC]

def colM (U : J → N → ℂ) : Matrix N J ℂ := Matrix.of fun p j => U j p

/- English proof (translation)
Simplify using `only [herm, colM, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, dotProduct, mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem gramM_apply (H : Matrix N N ℂ) (U : J → N → ℂ) (W : K → N → ℂ) (i : J) (j : K) :
    ((colM U)ᴴ * H * colM W) i j = herm H (W j) (U i) := by
  simp only [herm, colM, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mul_colM (h : Matrix N N ℂ) (U : J → N → ℂ) : h * colM U = colM fun j => h *ᵥ U j := rfl

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem dual_fix {H h : Matrix N N ℂ} (hh : hᴴ * H * h = H) {C' : Matrix N J ℂ} (hC : h * C' = C') :
    C'ᴴ * H * h = C'ᴴ * H := by
  calc C'ᴴ * H * h = (h * C')ᴴ * H * h := by rw [hC]
    _ = C'ᴴ * (hᴴ * H * h) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = C'ᴴ * H := by rw [hh]

/- English proof (translation)
Establish `k1 : (h * V)ᴴ * H * (h * V) = 1`. Rewrite using `[conjTranspose_mul, show Vᴴ * hᴴ * H * (h * V) = Vᴴ * (hᴴ * H * h) * V by simp only [Matrix.mul_assoc], hh, h1]`. Rewrite `k1` using `[e1, conjTranspose_mul, show (Vᴴ * H * h * V)ᴴ * Vᴴ * H * (V * (Vᴴ * H * h * V)) = (Vᴴ * H * h * V)ᴴ * (Vᴴ * H * V) * (Vᴴ * H * h * V) by simp only [Matrix.mul_assoc], h1, Matrix.mul_one]`. Conclude with `k1`.
-/
theorem unitary_of {H h : Matrix N N ℂ} (hH : Hᴴ = H) (hh : hᴴ * H * h = H) (h1 : Vᴴ * H * V = 1)
    (e1 : h * V = V * (Vᴴ * H * h * V)) : (Vᴴ * H * h * V)ᴴ * (Vᴴ * H * h * V) = 1 := by
  have k1 : (h * V)ᴴ * H * (h * V) = 1 := by
    rw [conjTranspose_mul, show Vᴴ * hᴴ * H * (h * V) = Vᴴ * (hᴴ * H * h) * V by simp only [Matrix.mul_assoc],
      hh, h1]
  rw [e1, conjTranspose_mul,
    show (Vᴴ * H * h * V)ᴴ * Vᴴ * H * (V * (Vᴴ * H * h * V)) =
      (Vᴴ * H * h * V)ᴴ * (Vᴴ * H * V) * (Vᴴ * H * h * V) by simp only [Matrix.mul_assoc],
    h1, Matrix.mul_one] at k1
  exact k1

/- English proof (translation)
Simplify using `[conjTranspose_mul, hH, hB, Matrix.mul_assoc]`.
-/
theorem skew_of {H : Matrix N N ℂ} (hH : Hᴴ = H) {B : Matrix K K ℂ} (hB : Bᴴ = -B) :
    (V * B * (Vᴴ * H))ᴴ * H + H * (V * B * (Vᴴ * H)) = 0 := by
  simp [conjTranspose_mul, hH, hB, Matrix.mul_assoc]

end Core

section Geo

variable {k r : ℕ}

abbrev JJ (r : ℕ) := Fin r ⊕ (Fin r ⊕ Unit)

def cvec (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : JJ r → Fin (2 * r + k + 1) → ℂ
  | Sum.inl a => bvec (eI k r a)
  | Sum.inr (Sum.inl a) => bvec (esI k r a)
  | Sum.inr (Sum.inr _) => z

def cvec' (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : JJ r → Fin (2 * r + k + 1) → ℂ
  | Sum.inl a => bvec (esI k r a)
  | Sum.inr (Sum.inl a) => bvec (eI k r a)
  | Sum.inr (Sum.inr _) => (star (herm (Hpk k r) z z))⁻¹ • z

/- English proof (translation)
Use `c.isLt` as an intermediate fact. Use `t.isLt` as an intermediate fact. Simplify using `only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
private theorem hpk_col_e_lemma (k r : ℕ) (c : Fin r) (t : Fin (2 * r + k + 1)) :
    Hpk k r t (eI k r c) = if t = esI k r c then 1 else 0 := by
  have := c.isLt
  have := t.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Use `c.isLt` as an intermediate fact. Use `t.isLt` as an intermediate fact. Simplify using `only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
private theorem hpk_col_es_lemma_2 (k r : ℕ) (c : Fin r) (t : Fin (2 * r + k + 1)) :
    Hpk k r t (esI k r c) = if t = eI k r c then 1 else 0 := by
  have := c.isLt
  have := t.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Simplify using `only [herm, dotProduct, mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.star_apply, hpk_col_e_lemma]`.
-/
theorem herm_e_left (w : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    herm (Hpk k r) (bvec (eI k r c)) w = star (w (esI k r c)) := by
  simp only [herm, dotProduct, mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Pi.star_apply, hpk_col_e_lemma]

/- English proof (translation)
Simplify using `only [herm, dotProduct, mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.star_apply, hpk_col_es_lemma_2]`.
-/
theorem herm_es_left (w : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    herm (Hpk k r) (bvec (esI k r c)) w = star (w (eI k r c)) := by
  simp only [herm, dotProduct, mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Pi.star_apply, hpk_col_es_lemma_2]

/- English proof (translation)
Use `c.isLt` as an intermediate fact. Use `c'.isLt` as an intermediate fact. Simplify using `only [bvec, Pi.single_apply, eI, esI, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `all_goals (split_ifs <;> first | rfl | omega)`.
-/
theorem bvec_ee (c c' : Fin r) : bvec (eI k r c') (eI k r c) = if c = c' then 1 else 0 := by
  have := c.isLt
  have := c'.isLt
  simp only [bvec, Pi.single_apply, eI, esI, Fin.ext_iff, Fin.val_mk]
  all_goals (split_ifs <;> first | rfl | omega)

/- English proof (translation)
Use `c.isLt` as an intermediate fact. Use `c'.isLt` as an intermediate fact. Simplify using `only [bvec, Pi.single_apply, eI, esI, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `all_goals (split_ifs <;> first | rfl | omega)`.
-/
theorem bvec_ss (c c' : Fin r) : bvec (esI k r c') (esI k r c) = if c = c' then 1 else 0 := by
  have := c.isLt
  have := c'.isLt
  simp only [bvec, Pi.single_apply, eI, esI, Fin.ext_iff, Fin.val_mk]
  all_goals (split_ifs <;> first | rfl | omega)

/- English proof (translation)
Use `c.isLt` as an intermediate fact. Use `c'.isLt` as an intermediate fact. Simplify using `only [bvec, Pi.single_apply, eI, esI, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `all_goals (split_ifs <;> first | rfl | omega)`.
-/
theorem bvec_es (c c' : Fin r) : bvec (eI k r c') (esI k r c) = 0 := by
  have := c.isLt
  have := c'.isLt
  simp only [bvec, Pi.single_apply, eI, esI, Fin.ext_iff, Fin.val_mk]
  all_goals (split_ifs <;> first | rfl | omega)

/- English proof (translation)
Use `c.isLt` as an intermediate fact. Use `c'.isLt` as an intermediate fact. Simplify using `only [bvec, Pi.single_apply, eI, esI, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `all_goals (split_ifs <;> first | rfl | omega)`.
-/
theorem bvec_se (c c' : Fin r) : bvec (esI k r c') (eI k r c) = 0 := by
  have := c.isLt
  have := c'.isLt
  simp only [bvec, Pi.single_apply, eI, esI, Fin.ext_iff, Fin.val_mk]
  all_goals (split_ifs <;> first | rfl | omega)

/- English proof (translation)
Use `t.isLt` as an intermediate fact. Use `u.isLt` as an intermediate fact. Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
private theorem hpk_symm_lemma_3 (k r : ℕ) (t u : Fin (2 * r + k + 1)) : Hpk k r u t = Hpk k r t u := by
  have := t.isLt
  have := u.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Simplify using `only [Hpk]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem hpk_star_lemma_4 (k r : ℕ) (t u : Fin (2 * r + k + 1)) : star (Hpk k r t u) = Hpk k r t u := by
  simp only [Hpk]
  split_ifs <;> simp

/- English proof (translation)
Simplify using `only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, hpk_star_lemma_4, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[hpk_symm_lemma_3]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem herm_symm_lemma_5 (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, hpk_star_lemma_4, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
  rw [hpk_symm_lemma_3]
  ring

/- English proof (translation)
Simplify using `only [herm, star_smul, smul_dotProduct, smul_eq_mul]`.
-/
private theorem herm_smul_right_lemma_6 (v w : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    herm (Hpk k r) v (c • w) = star c * herm (Hpk k r) v w := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
The claim follows from `hv _ (Or.inr (by have := c.isLt; show r + k < 2 * r + k - c.val; omega))`.
-/
private theorem wb_es_lemma_7 {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (c : Fin r) : v (esI k r c) = 0 :=
  hv _ (Or.inr (by have := c.isLt; show r + k < 2 * r + k - c.val; omega))

/- English proof (translation)
The claim follows from `hv _ (Or.inl c.isLt)`.
-/
private theorem wb_e_lemma_8 {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (c : Fin r) : v (eI k r c) = 0 :=
  hv _ (Or.inl c.isLt)

/- English proof (translation)
Apply the tactic sequence `rcases i with a | a | u <;> rcases j with b | b | v <;> simp only [cvec, cvec']`. Apply the tactic sequence `rw [herm_e_left, bvec_ss] split_ifs <;> simp_all`. Rewrite using `[herm_es_left, bvec_se, star_zero]`. Simplify using the standard rewrite rules. Rewrite using `[herm_symm_lemma_5, herm_es_left, wb_e_lemma_8 hz a, star_zero, star_zero]`.

Simplify using the standard rewrite rules. Rewrite using `[herm_e_left, bvec_es, star_zero]`. Simplify using the standard rewrite rules. Apply the tactic sequence `rw [herm_es_left, bvec_ee] split_ifs <;> simp_all`. Rewrite using `[herm_symm_lemma_5, herm_e_left, wb_es_lemma_7 hz a, star_zero, star_zero]`.

Simplify using the standard rewrite rules. Rewrite using `[herm_smul_right_lemma_6, herm_e_left, wb_es_lemma_7 hz b, star_zero, mul_zero]`. Simplify using the standard rewrite rules. Rewrite using `[herm_smul_right_lemma_6, herm_es_left, wb_e_lemma_8 hz b, star_zero, mul_zero]`. Simplify using the standard rewrite rules.

Simplify using `[herm_smul_right_lemma_6, hzz]`.
-/
theorem gram_CC {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hzz : herm (Hpk k r) z z ≠ 0) (i j : JJ r) :
    herm (Hpk k r) (cvec k r z j) (cvec' k r z i) = if i = j then 1 else 0 := by
  rcases i with a | a | u <;> rcases j with b | b | v <;> simp only [cvec, cvec']
  · rw [herm_e_left, bvec_ss]
    split_ifs <;> simp_all
  · rw [herm_es_left, bvec_se, star_zero]
    simp
  · rw [herm_symm_lemma_5, herm_es_left, wb_e_lemma_8 hz a, star_zero, star_zero]
    simp
  · rw [herm_e_left, bvec_es, star_zero]
    simp
  · rw [herm_es_left, bvec_ee]
    split_ifs <;> simp_all
  · rw [herm_symm_lemma_5, herm_e_left, wb_es_lemma_7 hz a, star_zero, star_zero]
    simp
  · rw [herm_smul_right_lemma_6, herm_e_left, wb_es_lemma_7 hz b, star_zero, mul_zero]
    simp
  · rw [herm_smul_right_lemma_6, herm_es_left, wb_e_lemma_8 hz b, star_zero, mul_zero]
    simp
  · simp [herm_smul_right_lemma_6, hzz]

/- English proof (translation)
Take `⟨hw, _, ho⟩` from `hB`. Apply the tactic sequence `rcases j with c | c | u <;> simp only [cvec]`. Rewrite using `[herm_e_left, wb_es_lemma_7 (hw a) c, star_zero]`. Rewrite using `[herm_es_left, wb_e_lemma_8 (hw a) c, star_zero]`. Rewrite using `[herm_symm_lemma_5, ho a z (by simp), star_zero]`.
-/
theorem gram_VC {z : Fin (2 * r + k + 1) → ℂ} {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z] Bs) (a : Fin m) (j : JJ r) : herm (Hpk k r) (cvec k r z j) (Bs a) = 0 := by
  obtain ⟨hw, _, ho⟩ := hB
  rcases j with c | c | u <;> simp only [cvec]
  · rw [herm_e_left, wb_es_lemma_7 (hw a) c, star_zero]
  · rw [herm_es_left, wb_e_lemma_8 (hw a) c, star_zero]
  · rw [herm_symm_lemma_5, ho a z (by simp), star_zero]

/- English proof (translation)
Take `⟨hw, _, ho⟩` from `hB`. Apply the tactic sequence `rcases j with c | c | u <;> simp only [cvec']`. Rewrite using `[herm_symm_lemma_5, herm_es_left, wb_e_lemma_8 (hw a) c, star_zero, star_zero]`. Rewrite using `[herm_symm_lemma_5, herm_e_left, wb_es_lemma_7 (hw a) c, star_zero, star_zero]`. Rewrite using `[herm_smul_right_lemma_6, ho a z (by simp), mul_zero]`.
-/
theorem gram_CV {z : Fin (2 * r + k + 1) → ℂ} {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z] Bs) (a : Fin m) (j : JJ r) : herm (Hpk k r) (Bs a) (cvec' k r z j) = 0 := by
  obtain ⟨hw, _, ho⟩ := hB
  rcases j with c | c | u <;> simp only [cvec']
  · rw [herm_symm_lemma_5, herm_es_left, wb_e_lemma_8 (hw a) c, star_zero, star_zero]
  · rw [herm_symm_lemma_5, herm_e_left, wb_es_lemma_7 (hw a) c, star_zero, star_zero]
  · rw [herm_smul_right_lemma_6, ho a z (by simp), mul_zero]

/- English proof (translation)
Take `⟨_, he, hz⟩` from `hh`. Break down `j with a | a | u` into its components or cases. Conclude with `(he a).1`. Conclude with `(he a).2`. Conclude with `hz`.
-/
theorem fix_c {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (j : JJ r) :
    h *ᵥ cvec k r z j = cvec k r z j := by
  obtain ⟨_, he, hz⟩ := hh
  rcases j with a | a | u
  · exact (he a).1
  · exact (he a).2
  · exact hz

/- English proof (translation)
Take `⟨_, he, hz⟩` from `hh`. Break down `j with a | a | u` into its components or cases. Conclude with `(he a).2`. Conclude with `(he a).1`. Simplify using `only [cvec']`.

Rewrite using `[mulVec_smul, hz]`.
-/
theorem fix_c' {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (j : JJ r) :
    h *ᵥ cvec' k r z j = cvec' k r z j := by
  obtain ⟨_, he, hz⟩ := hh
  rcases j with a | a | u
  · exact (he a).2
  · exact (he a).1
  · simp only [cvec']
    rw [mulVec_smul, hz]

end Geo

end HermitianFormRankFour

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open HermitianFormRankFour in
/- English proof (translation)
Introduce `k r z hz hT Pr h1 hstep h hh`. Take `⟨Bs, hB⟩` from `Qx8.frame_exists hz hT`. Establish `hzz : herm (Hpk k r) z z ≠ 0`. Introduce `e`. Unfold `Tz at hT`.

Rewrite `hT` using `[e]`. Simplify using `at hT`. Establish `g1 : (colM Bs)ᴴ * Hpk k r * colM Bs = 1`. Use extensionality with `a b`. Rewrite using `[gramM_apply, hB.2.1, Matrix.one_apply]`.

Simplify using `[eq_comm]`. Establish `g2 : (colM Bs)ᴴ * Hpk k r * colM (cvec k r z) = 0`. Use extensionality with `a j`. Rewrite using `[gramM_apply]`. Conclude with `gram_VC hB a j`.

Establish `g3 : (colM (cvec' k r z))ᴴ * Hpk k r * colM Bs = 0`. Use extensionality with `j a`. Rewrite using `[gramM_apply]`. Conclude with `gram_CV hB a j`. Establish `g4 : (colM (cvec' k r z))ᴴ * Hpk k r * colM (cvec k r z) = 1`.

Use extensionality with `i j`. Rewrite using `[gramM_apply, Matrix.one_apply]`. Conclude with `gram_CC hz hzz i j`. Establish `hc` using `complete (Fintype.equivOfCardEq (by simp; omega)) g1 g2 g3 g4`. Establish `hC : h * colM (cvec k r z) = colM (cvec k r z)`.

Rewrite using `[mul_colM]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `fix_c hh j`. Establish `hC' : h * colM (cvec' k r z) = colM (cvec' k r z)`.

Rewrite using `[mul_colM]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `fix_c' hh j`. Establish `hCd` using `dual_fix hh.1 hC'`.

Take `⟨e1, e2⟩` from `decomp hc g3 h hC hCd`. Take `⟨B, hBs, hBe⟩` from `unitary_log _ (unitary_of Qx8.hpk_herm hh.1 g1 e1)`. Establish `hXC : colM Bs * B * ((colM Bs)ᴴ * Hpk k r) * colM (cvec k r z) = 0`. Rewrite using `[Matrix.mul_assoc, g2, Matrix.mul_zero]`. Establish `col : ∀ j, (colM Bs * B * ((colM Bs)ᴴ * Hpk k r)) *ᵥ cvec k r z j = 0`.

Introduce `j`. Use function extensionality and compare the values at `p`. Conclude with `congrFun (congrFun hXC p) j`. Establish `hX : InLieW k r z (colM Bs * B * ((colM Bs)ᴴ * Hpk k r))` using `⟨⟨skew_of Qx8.hpk_herm hBs, fun a _ => ⟨col (Sum.inl a), col (Sum.inr (Sum.inl a))⟩⟩, col (Sum.inr (Sum.inr ()))⟩`. Establish `hfin` using `hstep _ 1 hX h1`.

Rewrite `hfin` using `[Matrix.mul_one, exp_lift hc g1 g2 B, hBe, ← e2]`. Conclude with `hfin`.
-/
theorem exp_generates : Formalism.FourierDecayAlt.Qr.ExpGen := by
  intro k r z hz hT Pr h1 hstep h hh
  obtain ⟨Bs, hB⟩ := Qx8.frame_exists hz hT
  have hzz : herm (Hpk k r) z z ≠ 0 := by
    intro e
    unfold Tz at hT
    rw [e] at hT
    simp at hT
  have g1 : (colM Bs)ᴴ * Hpk k r * colM Bs = 1 := by
    ext a b
    rw [gramM_apply, hB.2.1, Matrix.one_apply]
    simp [eq_comm]
  have g2 : (colM Bs)ᴴ * Hpk k r * colM (cvec k r z) = 0 := by
    ext a j
    rw [gramM_apply]
    exact gram_VC hB a j
  have g3 : (colM (cvec' k r z))ᴴ * Hpk k r * colM Bs = 0 := by
    ext j a
    rw [gramM_apply]
    exact gram_CV hB a j
  have g4 : (colM (cvec' k r z))ᴴ * Hpk k r * colM (cvec k r z) = 1 := by
    ext i j
    rw [gramM_apply, Matrix.one_apply]
    exact gram_CC hz hzz i j
  have hc := complete (Fintype.equivOfCardEq (by simp; omega)) g1 g2 g3 g4
  have hC : h * colM (cvec k r z) = colM (cvec k r z) := by
    rw [mul_colM]
    congr 1
    funext j
    exact fix_c hh j
  have hC' : h * colM (cvec' k r z) = colM (cvec' k r z) := by
    rw [mul_colM]
    congr 1
    funext j
    exact fix_c' hh j
  have hCd := dual_fix hh.1 hC'
  obtain ⟨e1, e2⟩ := decomp hc g3 h hC hCd
  obtain ⟨B, hBs, hBe⟩ := unitary_log _ (unitary_of Qx8.hpk_herm hh.1 g1 e1)
  have hXC : colM Bs * B * ((colM Bs)ᴴ * Hpk k r) * colM (cvec k r z) = 0 := by
    rw [Matrix.mul_assoc, g2, Matrix.mul_zero]
  have col : ∀ j, (colM Bs * B * ((colM Bs)ᴴ * Hpk k r)) *ᵥ cvec k r z j = 0 := by
    intro j
    funext p
    exact congrFun (congrFun hXC p) j
  have hX : InLieW k r z (colM Bs * B * ((colM Bs)ᴴ * Hpk k r)) :=
    ⟨⟨skew_of Qx8.hpk_herm hBs, fun a _ => ⟨col (Sum.inl a), col (Sum.inr (Sum.inl a))⟩⟩,
      col (Sum.inr (Sum.inr ()))⟩
  have hfin := hstep _ 1 hX h1
  rw [Matrix.mul_one, exp_lift hc g1 g2 B, hBe, ← e2] at hfin
  exact hfin

end Formalism.FourierDecayAlt.P
