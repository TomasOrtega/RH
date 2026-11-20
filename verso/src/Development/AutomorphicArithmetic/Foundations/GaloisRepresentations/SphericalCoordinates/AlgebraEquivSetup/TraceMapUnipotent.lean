import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.VecCoord
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

/- English proof (translation)
Break down `InfinitePlace.mk_eq_iff.mp h with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `A.c_neg`. Establish `h1` using `A.c_neg`. Rewrite `h1` using `[← h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]`.

Conclude with `h1`.
-/
private lemma c_re_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (τ : E →+* ℂ)
    (h : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀) : (τ (A.c : E)).re < 0 := by
  rcases InfinitePlace.mk_eq_iff.mp h with h | h
  · rw [h]; exact A.c_neg
  · have h1 := A.c_neg
    rw [← h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at h1
    exact h1

/- English proof (translation)
Use `A.c_ne` as an intermediate fact. Unfold `Arith.dg`. Apply the tactic sequence `split_ifs <;> simp [this]`.
-/
private lemma dg_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    ((A.dg n i : 𝓞 E) : E) ≠ 0 := by
  have := A.c_ne
  unfold Arith.dg
  split_ifs <;> simp [this]

/- English proof (translation)
Establish `h : A.bar (A.dg n i) = A.dg n i`. Unfold `Arith.dg`. Apply the tactic sequence `split_ifs <;> simp [A.c_real]`. Conclude with `(A.bar_eq _).symm.trans (congrArg _ h)`.
-/
private lemma dg_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    cj E ((A.dg n i : 𝓞 E) : E) = ((A.dg n i : 𝓞 E) : E) := by
  have h : A.bar (A.dg n i) = A.dg n i := by
    unfold Arith.dg
    split_ifs <;> simp [A.c_real]
  exact (A.bar_eq _).symm.trans (congrArg _ h)

/- English proof (translation)
Establish `h : A.bar (A.hd n i) = A.hd n i`. Unfold `Arith.hd Arith.dg`. Apply the tactic sequence `split_ifs <;> simp [A.c_real]`. Conclude with `(A.bar_eq _).symm.trans (congrArg _ h)`.
-/
private lemma hd_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    cj E ((A.hd n i : 𝓞 E) : E) = ((A.hd n i : 𝓞 E) : E) := by
  have h : A.bar (A.hd n i) = A.hd n i := by
    unfold Arith.hd Arith.dg
    split_ifs <;> simp [A.c_real]
  exact (A.bar_eq _).symm.trans (congrArg _ h)

/- English proof (translation)
Simplify using `[Arith.hd]`.
-/
private lemma hd_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    ((A.hd n i : 𝓞 E) : E) = -(A.c : E) * ((A.dg n i : 𝓞 E) : E) := by
  simp [Arith.hd]

/- English proof (translation)
Simplify using `only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h : star (x i) * (a * x i) = a * ((Complex.normSq (x i) : ℝ) : ℂ)`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Simplify using `only [Complex.star_def]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, Complex.re_mul_ofReal]`.
-/
private lemma re_form {n : ℕ} (a : ℂ) (x : Fin n → ℂ) :
    (star x ⬝ᵥ ((Matrix.diagonal fun _ => a) *ᵥ x)).re = a.re * ∑ i, Complex.normSq (x i) := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star (x i) * (a * x i) = a * ((Complex.normSq (x i) : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [h, Complex.re_mul_ofReal]

/- English proof (translation)
Take `⟨i, hi⟩` from `Function.ne_iff.mp hx`. Conclude with `Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩`.
-/
private lemma sum_pos' {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) : 0 < ∑ i, Complex.normSq (x i) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

/- English proof (translation)
Unfold `Arith.H`. Rewrite using `[Matrix.diagonal_map (map_zero _), Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[hd_eq, map_mul, map_neg, map_inv₀, mul_assoc, mul_inv_cancel₀ ((map_ne_zero e).2 (dg_ne A n i)), mul_one]`.
-/
private lemma form_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (e : E →+* ℂ) :
    ((A.H n).map e)ᵀ * (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)⁻¹).map e =
      Matrix.diagonal fun _ => -e (A.c : E) := by
  unfold Arith.H
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [hd_eq, map_mul, map_neg, map_inv₀, mul_assoc, mul_inv_cancel₀ ((map_ne_zero e).2 (dg_ne A n i)), mul_one]

/- English proof (translation)
Unfold `Arith.H`. Rewrite using `[Matrix.diagonal_map (map_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hd_cj A n i`.
-/
private lemma H_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    (A.H n).map (cj E) = A.H n := by
  unfold Arith.H
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact hd_cj A n i

private abbrev Dm {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) : Matrix (Fin n) (Fin n) E :=
  Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)

/- English proof (translation)
Unfold `Arith.H`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[hd_eq]`.

Simplify using `[h]`.
-/
private lemma H_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    A.H n = (-(A.c : E)) • Dm A n := by
  unfold Arith.H
  ext i j
  by_cases h : i = j
  · subst h; simp [hd_eq]
  · simp [h]

/- English proof (translation)
Establish `hc : -(A.c : E) ≠ 0` using `neg_ne_zero.2 A.c_ne`. Establish `hu : IsUnit (A.H n).det` using `(A.det_ne n).isUnit`. Establish `hD : Dm A n = (-(A.c : E))⁻¹ • A.H n`. Rewrite using `[H_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Rewrite using `[hermStar_apply, show (A.H n).map (IsCMField.complexConj E : E →+* E) = A.H n from H_cj A n, hD]`.

Rewrite using `[smul_mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_smul]`.
-/
private lemma D_star {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (M : Matrix (Fin n) (Fin n) E) :
    Dm A n * (hermStar (A.H n) (A.det_ne n) M).unop = (M.map (cj E))ᵀ * Dm A n := by
  have hc : -(A.c : E) ≠ 0 := neg_ne_zero.2 A.c_ne
  have hu : IsUnit (A.H n).det := (A.det_ne n).isUnit
  have hD : Dm A n = (-(A.c : E))⁻¹ • A.H n := by
    rw [H_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hermStar_apply, show (A.H n).map (IsCMField.complexConj E : E →+* E) = A.H n from H_cj A n, hD]
  rw [smul_mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_smul]

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]

private def βS (S : Setup A n p) : S.G.Cˣ :=
  (⟨Dm A n, Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)⁻¹, by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (dg_ne A n i), by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (dg_ne A n i)⟩ : (Matrix (Fin n) (Fin n) E)ˣ)

/- English proof (translation)
Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]`. Conclude with `(Finset.prod_ne_zero_iff.2 fun i _ => dg_ne A n i).isUnit`.
-/
private lemma hU (A : Arith E) (n : ℕ) : IsUnit (Dm A n) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  exact (Finset.prod_ne_zero_iff.2 fun i _ => dg_ne A n i).isUnit

/- English proof (translation)
Establish `h` using `D_star A n (Dm A n)`. Establish `hD : (Dm A n).map (cj E) = Dm A n`. Rewrite using `[Matrix.diagonal_map (map_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `dg_cj A n i`. Rewrite `h` using `[hD, Matrix.diagonal_transpose]`. Conclude with `(hU A n).mul_right_inj.1 h`.
-/
private lemma βS_sym (S : Setup A n p) : sh S.G (βS S : S.G.Cˣ) = (βS S : S.G.Cˣ) := by
  have h := D_star A n (Dm A n)
  have hD : (Dm A n).map (cj E) = Dm A n := by
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact dg_cj A n i
  rw [hD, Matrix.diagonal_transpose] at h
  exact (hU A n).mul_right_inj.1 h

/- English proof (translation)
Establish `hs : sigPosH (S.G.gram_herm v) = sigPos (A.herm n) v.embedding` using `rfl`. Establish `hf : S.G.gram v * S.G.psi v (((βS S)⁻¹ : S.G.Cˣ) : S.G.C) = Matrix.diagonal fun _ => -v.embedding (A.c : E)` using `form_eq A n v.embedding`. Establish `hP` using `sum_pos' hx`. Rewrite using `[hf, re_form, hs, Complex.neg_re]`. Distinguish the cases in `hm : InfinitePlace.mk v.embedding = InfinitePlace.mk A.τ₀`.

Establish `hc` using `c_re_neg A v.embedding hm`. Establish `h1'` using `((S.sig v.embedding).1 hm).1`. Conclude with `⟨fun _ => mul_pos (neg_pos.2 hc) hP, fun h => absurd h1' h⟩`. Establish `hc` using `A.c_pos v.embedding hm`. Establish `h0` using `((S.sig v.embedding).2 hm).1`.

Use `⟨fun h => ?_, fun _ => mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hP⟩` and prove the remaining obligations. Rewrite `h` using `[h0]`. Conclude with `absurd h (by norm_num)`.
-/
private lemma βS_pos (S : Setup A n p) (v : InfinitePlace S.G.F) (x : Fin S.G.n → ℂ) (hx : x ≠ 0) :
    (sigPosH (S.G.gram_herm v) = 1 → 0 < (star x ⬝ᵥ ((S.G.gram v * S.G.psi v (((βS S)⁻¹ : S.G.Cˣ) : S.G.C)) *ᵥ x)).re) ∧
      (sigPosH (S.G.gram_herm v) ≠ 1 → (star x ⬝ᵥ ((S.G.gram v * S.G.psi v (((βS S)⁻¹ : S.G.Cˣ) : S.G.C)) *ᵥ x)).re < 0) := by
  have hs : sigPosH (S.G.gram_herm v) = sigPos (A.herm n) v.embedding := rfl
  have hf : S.G.gram v * S.G.psi v (((βS S)⁻¹ : S.G.Cˣ) : S.G.C) = Matrix.diagonal fun _ => -v.embedding (A.c : E) :=
    form_eq A n v.embedding
  have hP := sum_pos' hx
  rw [hf, re_form, hs, Complex.neg_re]
  by_cases hm : InfinitePlace.mk v.embedding = InfinitePlace.mk A.τ₀
  · have hc := c_re_neg A v.embedding hm
    have h1' := ((S.sig v.embedding).1 hm).1
    exact ⟨fun _ => mul_pos (neg_pos.2 hc) hP, fun h => absurd h1' h⟩
  · have hc := A.c_pos v.embedding hm
    have h0 := ((S.sig v.embedding).2 hm).1
    refine ⟨fun h => ?_, fun _ => mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hP⟩
    rw [h0] at h
    exact absurd h (by norm_num)

/- English proof (translation)
Establish `h1 : Y * (s⁻¹ • Z) = 1` using `by rw [Matrix.mul_smul, h, smul_smul, inv_mul_cancel₀ hs, one_smul]`. Establish `h2` using `mul_eq_one_comm.1 h1`. Rewrite `h2` using `[smul_mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma sim_comm {Y Z : Matrix (Fin n) (Fin n) E} {s : E} (hs : s ≠ 0) (h : Y * Z = s • 1) : Z * Y = s • 1 := by
  have h1 : Y * (s⁻¹ • Z) = 1 := by rw [Matrix.mul_smul, h, smul_smul, inv_mul_cancel₀ hs, one_smul]
  have h2 := mul_eq_one_comm.1 h1
  rw [smul_mul_assoc] at h2
  calc Z * Y = s • (s⁻¹ • (Z * Y)) := by rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
    _ = s • 1 := by rw [h2]

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one, algebraMap_smul]`.
-/
private lemma alg_mat (q : ℚ) : algebraMap ℚ (Matrix (Fin n) (Fin n) E) q = algebraMap ℚ E q • (1 : Matrix (Fin n) (Fin n) E) := by
  rw [Algebra.algebraMap_eq_smul_one, algebraMap_smul]

/- English proof (translation)
Establish `hs (q : ℚˣ) : algebraMap ℚ E q ≠ 0` using `by simp`. Establish `key : (y.1.val * Dm A n) * (hermStar (A.H n) (A.det_ne n) y.1.val).unop = y.1.val * (y.1.val.map (cj E))ᵀ * Dm A n`. Rewrite using `[Matrix.mul_assoc, D_star, Matrix.mul_assoc]`. Establish `hg : y ∈ GlobalTheory.LKCx.grp S.G (βS S) ↔ (y.1.val * (y.1.val.map (cj E))ᵀ = algebraMap ℚ E y.2 • (1 : Matrix (Fin n) (Fin n) E)) ∧ 0 < (y.2 : ℚ)`. Use `and_congr_left' ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(y.1.val * Dm A n) * (hermStar (A.H n) (A.det_ne n) y.1.val).unop = algebraMap ℚ (Matrix (Fin n) (Fin n) E) y.2 * Dm A n ↔ _`. Rewrite using `[key, alg_mat]`. Conclude with `(hU A n).mul_left_inj`. Establish `hG : y ∈ Gam0 E n ↔ ((y.1.val.map (cj E))ᵀ * y.1.val = algebraMap ℚ E y.2 • (1 : Matrix (Fin n) (Fin n) E)) ∧ 0 < (y.2 : ℚ)` using `Iff.rfl`. Rewrite using `[hg, hG]`.

Conclude with `and_congr_left' ⟨sim_comm (hs _), sim_comm (hs _)⟩`.
-/
private lemma mem_iff (S : Setup A n p) (y : GL (Fin n) E × ℚˣ) : y ∈ GlobalTheory.LKCx.grp S.G (βS S) ↔ y ∈ Gam0 E n := by
  have hs (q : ℚˣ) : algebraMap ℚ E q ≠ 0 := by simp
  have key : (y.1.val * Dm A n) * (hermStar (A.H n) (A.det_ne n) y.1.val).unop =
      y.1.val * (y.1.val.map (cj E))ᵀ * Dm A n := by
    rw [Matrix.mul_assoc, D_star, Matrix.mul_assoc]
  have hg : y ∈ GlobalTheory.LKCx.grp S.G (βS S) ↔
      (y.1.val * (y.1.val.map (cj E))ᵀ = algebraMap ℚ E y.2 • (1 : Matrix (Fin n) (Fin n) E)) ∧ 0 < (y.2 : ℚ) := by
    refine and_congr_left' ?_
    change (y.1.val * Dm A n) * (hermStar (A.H n) (A.det_ne n) y.1.val).unop = algebraMap ℚ (Matrix (Fin n) (Fin n) E) y.2 * Dm A n ↔ _
    rw [key, alg_mat]
    exact (hU A n).mul_left_inj
  have hG : y ∈ Gam0 E n ↔
      ((y.1.val.map (cj E))ᵀ * y.1.val = algebraMap ℚ E y.2 • (1 : Matrix (Fin n) (Fin n) E)) ∧ 0 < (y.2 : ℚ) := Iff.rfl
  rw [hg, hG]
  exact and_congr_left' ⟨sim_comm (hs _), sim_comm (hs _)⟩

private noncomputable def xOf {S : Setup A n p} (T : Tr S) : (AfP p ⊗[ℚ] S.G.C)ˣ :=
  Units.map (RingHom.toMonoidHom T.μ.symm.toRingHom) (GeneralLinearGroup.map T.Φ T.a)

private noncomputable def xv {S : Setup A n p} (T : Tr S) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E := (xOf T).val

private noncomputable def xiv {S : Setup A n p} (T : Tr S) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E := ((xOf T)⁻¹).val

/- English proof (translation)
The claim follows from `T.μ.apply_symm_apply _`.
-/
private lemma traceMap_unipotent {S : Setup A n p} (T : Tr S) : T.μ (xv T) = T.a.val.map T.Φ :=
  T.μ.apply_symm_apply _

/- English proof (translation)
The claim follows from `T.μ.apply_symm_apply _`.
-/
private lemma mu_xi {S : Setup A n p} (T : Tr S) : T.μ (xiv T) = (T.a⁻¹).val.map T.Φ :=
  T.μ.apply_symm_apply _

/- English proof (translation)
Use extensionality with `i k`. Conclude with `T.mu 1 M i k`.
-/
private lemma mu_one {S : Setup A n p} (T : Tr S) (M : Matrix (Fin n) (Fin n) E) :
    T.μ ((1 : AfP p) ⊗ₜ[ℚ] M) = M.map fun e => (1 : AfP p) ⊗ₜ[ℚ] e := by
  ext i k
  exact T.mu 1 M i k

/- English proof (translation)
Establish `hst` using `hM (AfP p) E A n T.μ T.mu (xv T)`. Rewrite `hst` using `[traceMap_unipotent]`. Establish `hD : (Dm A n).map (fun e => (1 : AfP p) ⊗ₜ[ℚ] e) = Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] ((A.dg n i : 𝓞 E) : E))`. Use extensionality with `i k`. Distinguish the cases in `h : i = k`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Establish `h0` using `congrArg (fun M => M.map T.Φ) T.iso.1`. Simplify using `only [Matrix.map_mul] at h0`.

Establish `h1 : ((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ * Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] ((A.dg n i : 𝓞 E) : E)) * T.a.val.map T.Φ = 1`. Establish `e1 : ((T.a.val.map (conjFin (GlobalTheory.SplitPts.conjE E)))ᵀ).map T.Φ = ((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ`. Use extensionality with `i k`. Conclude with `T.Φ_conj _`. Establish `e2 : (Matrix.diagonal fun i => algebraMap E (Af E) ((A.dg n i : 𝓞 E) : E)).map T.Φ = Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] ((A.dg n i : 𝓞 E) : E))`.

Use extensionality with `i k`. Distinguish the cases in `h : i = k`. Substitute `h` using the available equality. Simplify using `[T.Φ_E]`. Simplify using `[h]`.

Rewrite `h0` using `[e1, e2, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `h0`. Establish `h2 : T.a.val.map T.Φ * (((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ * Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] ((A.dg n i : 𝓞 E) : E))) = 1` using `mul_eq_one_comm.1 h1`. Establish `e : xv T * ((1 : AfP p) ⊗ₜ[ℚ] Dm A n) * (starT (hermStar (A.H n) (A.det_ne n)) (AfP p) (xv T)).unop = 1`. Apply `T.μ.injective` to reduce the goal to its premises.

Rewrite using `[map_mul, map_mul, map_one, traceMap_unipotent, mu_one, hD, Matrix.mul_assoc, hst]`. Conclude with `h2`. Conclude with `e.trans (map_one _).symm`.
-/
private lemma triv_xOf_of_muStar (hM : MuStar) {S : Setup A n p} (T : Tr S) : Triv S.G (AfP p) (βS S : S.G.Cˣ) (xOf T) 1 := by
  have hst := hM (AfP p) E A n T.μ T.mu (xv T)
  rw [traceMap_unipotent] at hst
  have hD : (Dm A n).map (fun e => (1 : AfP p) ⊗ₜ[ℚ] e) =
      Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] ((A.dg n i : 𝓞 E) : E)) := by
    ext i k
    by_cases h : i = k
    · subst h; simp
    · simp [h]
  have h0 := congrArg (fun M => M.map T.Φ) T.iso.1
  simp only [Matrix.map_mul] at h0
  have h1 : ((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ *
      Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] ((A.dg n i : 𝓞 E) : E)) * T.a.val.map T.Φ = 1 := by
    have e1 : ((T.a.val.map (conjFin (GlobalTheory.SplitPts.conjE E)))ᵀ).map T.Φ = ((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ := by
      ext i k
      exact T.Φ_conj _
    have e2 : (Matrix.diagonal fun i => algebraMap E (Af E) ((A.dg n i : 𝓞 E) : E)).map T.Φ =
        Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] ((A.dg n i : 𝓞 E) : E)) := by
      ext i k
      by_cases h : i = k
      · subst h; simp [T.Φ_E]
      · simp [h]
    rw [e1, e2, Matrix.map_one _ (map_zero _) (map_one _)] at h0
    exact h0
  have h2 : T.a.val.map T.Φ * (((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ *
      Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] ((A.dg n i : 𝓞 E) : E))) = 1 := mul_eq_one_comm.1 h1
  have e : xv T * ((1 : AfP p) ⊗ₜ[ℚ] Dm A n) * (starT (hermStar (A.H n) (A.det_ne n)) (AfP p) (xv T)).unop = 1 := by
    apply T.μ.injective
    rw [map_mul, map_mul, map_one, traceMap_unipotent, mu_one, hD, Matrix.mul_assoc, hst]
    exact h2
  exact e.trans (map_one _).symm

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Apply `T.μ.injective` to reduce the goal to its premises. Use `Eq.trans ?_ (T.j_mx (rat ⟨y, h'⟩)).symm` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `T.μ (xv T * ((1 : AfP p) ⊗ₜ[ℚ] y.1.val) * xiv T) = _`. Rewrite using `[map_mul, map_mul, traceMap_unipotent, mu_xi, mu_one, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]`. Use `congr 2`. Use extensionality with `i k`. Conclude with `(T.Φ_E _).symm`.

Apply `Units.ext` to reduce the goal to its premises. Use `Eq.trans ?_ (T.j_sim (rat ⟨y, h'⟩)).symm` and prove the remaining obligations. Conclude with `RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ (AfP p)) (T.ρ.comp (algebraMap ℚ AfQ))) _`.
-/
private lemma emb_eq {S : Setup A n p} (T : Tr S) (hx : Triv S.G (AfP p) (βS S : S.G.Cˣ) (xOf T) 1) (y : GL (Fin n) E × ℚˣ)
    (h : y ∈ GlobalTheory.LKCx.grp S.G (βS S)) (h' : y ∈ Gam0 E n) :
    GlobalTheory.LKCx.toAfF S.G (βS S) (xOf T) 1 hx ⟨y, h⟩ = T.j (rat ⟨y, h'⟩) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    apply T.μ.injective
    refine Eq.trans ?_ (T.j_mx (rat ⟨y, h'⟩)).symm
    change T.μ (xv T * ((1 : AfP p) ⊗ₜ[ℚ] y.1.val) * xiv T) = _
    rw [map_mul, map_mul, traceMap_unipotent, mu_xi, mu_one, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
    congr 2
    ext i k
    exact (T.Φ_E _).symm
  · apply Units.ext
    refine Eq.trans ?_ (T.j_sim (rat ⟨y, h'⟩)).symm
    exact RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ (AfP p)) (T.ρ.comp (algebraMap ℚ AfQ))) _

end
/- English proof (translation)
Introduce `hM E _ _ _ A n p _ S T`. Establish `hx` using `triv_xOf_of_muStar hM T`. Use `⟨⟨βS S, βS_sym S, ⟨xOf T, 1, hx⟩, βS_pos S⟩, xOf T, hx, fun y => mem_iff S y, fun y h h' => emb_eq T hx y h h'⟩` and prove the remaining obligations.
-/
theorem UpperTheory.Gal.W2.Seed.pStdForm2 :
    MuStar → StdForm2 := by
  intro hM E _ _ _ A n p _ S T
  have hx := triv_xOf_of_muStar hM T
  refine ⟨⟨βS S, βS_sym S, ⟨xOf T, 1, hx⟩, βS_pos S⟩, xOf T, hx, fun y => mem_iff S y, fun y h h' => emb_eq T hx y h h'⟩
