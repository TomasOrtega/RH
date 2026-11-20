import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CayleyTransformUnitarySkewInvolutiveStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdempotentAdelesAndSmallAdelicMatricesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdelicUnitaryScalingUnitStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseOneAddPreservingAdelicCompletionStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalMatrixApproxAdeleLinearMapStatement

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.WeakApprox

/- English proof (translation)
Establish `h1 : ∀ x y : Fin n → R, ∑ a, ∑ b, x a * G a b * σ (y b) = x ⬝ᵥ (G *ᵥ (σ ∘ y))`. Introduce `x y`. Simplify using `[dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`. Establish `h2 : ∀ x y : Fin n → R, (g *ᵥ x) ⬝ᵥ (G *ᵥ (σ ∘ (g *ᵥ y))) = x ⬝ᵥ ((gᵀ * G * g.map σ) *ᵥ (σ ∘ y))`. Introduce `x y`.

Establish `: σ ∘ (g *ᵥ y) = g.map σ *ᵥ (σ ∘ y)`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec σ g y i`. Rewrite using `[this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]`. Simplify using `only [h1, h2]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `a b`. Use `h (Pi.single a 1) (Pi.single b 1)` as an intermediate fact. Establish `e : σ ∘ (Pi.single b 1 : Fin n → R) = Pi.single b 1`.

Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = b`. Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hi]`.

Simplify `this` using `[e]`. Introduce `h x y`. Rewrite using `[h]`.
-/
theorem preserves_iff {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (G g : Matrix (Fin n) (Fin n) R) :
    (∀ x y : Fin n → R, ∑ a, ∑ b, (g *ᵥ x) a * G a b * σ ((g *ᵥ y) b) = ∑ a, ∑ b, x a * G a b * σ (y b)) ↔
      gᵀ * G * g.map σ = G := by
  have h1 : ∀ x y : Fin n → R, ∑ a, ∑ b, x a * G a b * σ (y b) = x ⬝ᵥ (G *ᵥ (σ ∘ y)) := by
    intro x y
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h2 : ∀ x y : Fin n → R, (g *ᵥ x) ⬝ᵥ (G *ᵥ (σ ∘ (g *ᵥ y))) =
      x ⬝ᵥ ((gᵀ * G * g.map σ) *ᵥ (σ ∘ y)) := by
    intro x y
    have : σ ∘ (g *ᵥ y) = g.map σ *ᵥ (σ ∘ y) := by
      funext i
      exact RingHom.map_mulVec σ g y i
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x,
      Matrix.vecMul_transpose]
  simp only [h1, h2]
  constructor
  · intro h
    ext a b
    have := h (Pi.single a 1) (Pi.single b 1)
    have e : σ ∘ (Pi.single b 1 : Fin n → R) = Pi.single b 1 := by
      funext i
      by_cases hi : i = b
      · subst hi; simp
      · simp [hi]
    simpa [e] using this
  · intro h x y
    rw [h]

/- English proof (translation)
Use `Matrix.inv_eq_right_inv ?_` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero ι) (map_one ι)]`.
-/
theorem map_inv' {K R : Type} [CommRing K] [CommRing R] (ι : K →+* R) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A.det) : (A.map ι)⁻¹ = A⁻¹.map ι := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero ι) (map_one ι)]

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_smul'' {K R : Type} [CommRing K] [CommRing R] (ι : K →+* R) {n : ℕ} (r : K)
    (A : Matrix (Fin n) (Fin n) K) : (r • A).map ι = ι r • A.map ι := by
  ext i j
  simp

/- English proof (translation)
Establish `: (1 + e • (-((S - T) * U))) * (1 + S) = (1 + S) - e • (S - T)`. Rewrite using `[add_mul, one_mul, smul_mul_assoc, neg_mul, mul_assoc, hU, mul_one, smul_neg, sub_eq_add_neg (1 + S)]`. Rewrite using `[this, smul_sub e (1 + S), smul_smul, he, ← smul_sub]`. Use `congr 1`. Normalize the expressions using the abelian group laws.
-/
theorem idem_factor {R M : Type} [CommRing R] [Ring M] [Algebra R M] (e : R) (he : e * e = e)
    (S T U : M) (hU : U * (1 + S) = 1) :
    e • (1 + T) = e • ((1 + e • (-((S - T) * U))) * (1 + S)) := by
  have : (1 + e • (-((S - T) * U))) * (1 + S) = (1 + S) - e • (S - T) := by
    rw [add_mul, one_mul, smul_mul_assoc, neg_mul, mul_assoc, hU, mul_one, smul_neg, sub_eq_add_neg (1 + S)]
  rw [this, smul_sub e (1 + S), smul_smul, he, ← smul_sub]
  congr 1
  abel

/- English proof (translation)
Establish `h1 : V - U = V * (S - T) * U`. Establish `: S - T = (1 + S) - (1 + T)` using `by abel`. Rewrite using `[this, mul_sub, sub_mul, mul_assoc V, hU', hV, mul_one, one_mul]`. Establish `h2 : e • (U * W) = e • V`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_smul_comm, smul_mul_assoc, mul_assoc (U * W), hV', mul_one]`. Use `_ = e • (U * (W * (1 + e • (-((S - T) * U)))) * (1 + S) * V) := by`. Rewrite using `[idem_factor e he S T U hU, mul_smul_comm, smul_mul_assoc]`. Simplify using `only [mul_assoc]`. Use `_ = e • V := by rw [hW, mul_one, hU, one_mul]`.

Rewrite using `[h1, ← smul_mul_assoc, ← smul_mul_assoc, ← h2, smul_mul_assoc, smul_mul_assoc]`.
-/
theorem idem_diff {R M : Type} [CommRing R] [Ring M] [Algebra R M] (e : R) (he : e * e = e)
    (S T U V W : M) (hU : U * (1 + S) = 1) (hU' : (1 + S) * U = 1) (hV : V * (1 + T) = 1)
    (hV' : (1 + T) * V = 1) (hW : W * (1 + e • (-((S - T) * U))) = 1) :
    e • (V - U) = e • (U * W * (S - T) * U) := by
  have h1 : V - U = V * (S - T) * U := by
    have : S - T = (1 + S) - (1 + T) := by abel
    rw [this, mul_sub, sub_mul, mul_assoc V, hU', hV, mul_one, one_mul]
  have h2 : e • (U * W) = e • V := by
    calc e • (U * W) = U * W * (e • (1 + T)) * V := by
          rw [mul_smul_comm, smul_mul_assoc, mul_assoc (U * W), hV', mul_one]
      _ = e • (U * (W * (1 + e • (-((S - T) * U)))) * (1 + S) * V) := by
          rw [idem_factor e he S T U hU, mul_smul_comm, smul_mul_assoc]
          simp only [mul_assoc]
      _ = e • V := by rw [hW, mul_one, hU, one_mul]
  rw [h1, ← smul_mul_assoc, ← smul_mul_assoc, ← h2, smul_mul_assoc, smul_mul_assoc]

/- English proof (translation)
Establish `h0 : e * (1 - e) = 0` using `by rw [mul_sub, he, mul_one, sub_self]`. Establish `h0' : (1 - e) * e = 0` using `by rw [mul_comm, h0]`. Establish `h1 : (1 - e) * (1 - e) = 1 - e` using `by rw [mul_sub, h0', mul_one, sub_zero]`. Rewrite using `[map_smul'', Matrix.map_add _ (map_add σ), map_smul'', map_smul'', Matrix.map_one _ (map_zero σ) (map_one σ), map_sub, map_one, hσ, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one, smul_mul_assoc, smul_mul_assoc, mul …`. Simplify using `only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, he, h0, h0', h1, hh, zero_smul, one_mul, mul_one, add_zero, zero_add]`.

Rewrite using `[← add_smul]`. Simplify using the standard rewrite rules.
-/
theorem preserves_form_smul_idempotent_glue {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (G h : Matrix (Fin n) (Fin n) R)
    (e l : R) (he : e * e = e) (hσ : σ e = e) (hl : l * σ l = 1) (hh : hᵀ * G * h.map σ = G) :
    (l • (e • h + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)))ᵀ * G *
      (l • (e • h + (1 - e) • (1 : Matrix (Fin n) (Fin n) R))).map σ = G := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, h0', mul_one, sub_zero]
  rw [map_smul'', Matrix.map_add _ (map_add σ), map_smul'', map_smul'',
    Matrix.map_one _ (map_zero σ) (map_one σ), map_sub, map_one, hσ, Matrix.transpose_smul,
    Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one,
    smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, hl, one_smul]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, he, h0, h0', h1, hh,
    zero_smul, one_mul, mul_one, add_zero, zero_add]
  rw [← add_smul]
  simp

/- English proof (translation)
Establish `hmm : ∀ A : Matrix (Fin n) (Fin n) K, (A.map ι).map σ = (A.map c).map ι`. Introduce `A`. Use extensionality with `i j`. Simplify using `[hσι]`. Establish `cay : ∀ A B : Matrix (Fin n) (Fin n) R, (1 + A) * B = 1 → (1 - A) * B = (2 : R) • B - 1`.

Introduce `A B hAB`. Rewrite `hAB` using `[add_mul, one_mul]`. Rewrite using `[sub_mul, one_mul, two_smul, ← hAB]`. Normalize the expressions using the abelian group laws. Establish `hdu : IsUnit G.det` using `hdet.isUnit`.

Establish `hG' : ((G.map ι).map σ)ᵀ = G.map ι`. Rewrite using `[hmm, ← Matrix.transpose_map, hG]`. Establish `hdet' : IsUnit (G.map ι).det`. Use `hdu.map ι` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis.

Establish `h2' : IsUnit (2 : R)`. Use `h2.isUnit.map ι` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Take `⟨cR1, cR2, -, -⟩` from `GlobalTheory.T.cayleyTransform_unitary_skew_involutive R σ n (G.map ι) hσ hG' hdet' h2'`. Take `⟨-, -, cK3, cK4⟩` from `GlobalTheory.T.cayleyTransform_unitary_skew_involutive K c n G hc hG hdu h2.isUnit`.

Establish `hl : ι lam * σ (ι lam) = 1` using `by rw [hσι, ← map_mul, hlam, map_one]`. Use `set k : Matrix (Fin n) (Fin n) R := ι lam • (e • h + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) with hk`. Establish `hku : kᵀ * G.map ι * k.map σ = G.map ι` using `preserves_form_smul_idempotent_glue σ _ h e _ he hσe hl hh`. Take `⟨hS, hSu⟩` from `cR1 k hku hu`. Establish `hkS` using `cR2 k hu`.

Use `set S : Matrix (Fin n) (Fin n) R := (1 - k) * (1 + k)⁻¹ with hSdef`. Use `set U : Matrix (Fin n) (Fin n) R := (1 + S)⁻¹ with hUdef`. Establish `hU : U * (1 + S) = 1` using `Matrix.nonsing_inv_mul _ hSu`. Establish `hU' : (1 + S) * U = 1` using `Matrix.mul_nonsing_inv _ hSu`. Take `⟨d1, hd1, hO1⟩` from `hb U`.

Take `⟨d2, hd2, hO2⟩` from `hb ((2 * σ (ι lam)) • U)`. Take `⟨d3, hd3, hO3⟩` from `hb (U * g)`. Take `⟨M₀, X, hX, hδ⟩` from `hapx (ι 2⁻¹ • S) (N * d1 * d2 * d3 * D) (by positivity)`. Establish `hu2 : ι 2⁻¹ + ι 2⁻¹ = 1`. Rewrite using `[← map_add, ← two_mul, mul_inv_cancel₀ h2, map_one]`.

Establish `hSS : ι 2⁻¹ • S - (G.map ι * (ι 2⁻¹ • S).map σ * (G.map ι)⁻¹)ᵀ = S`. Establish `e1 : G.map ι * S.map σ = -(Sᵀ * G.map ι)` using `eq_neg_of_add_eq_zero_right hS`. Rewrite using `[map_smul'', hσι, map_inv₀ c, map_ofNat c, mul_smul_comm, e1, smul_mul_assoc, neg_mul, mul_assoc, Matrix.mul_nonsing_inv _ hdet', mul_one, Matrix.transpose_smul, Matrix.transpose_neg, Matrix.transpose_transpose, smul_neg, sub_neg_eq_add, ← add_smul, hu2, one_smul]`. Use `set S₀ : Matrix (Fin n) (Fin n) K := M₀ - (G * M₀.map c * G⁻¹)ᵀ with hS₀`. Establish `hS₀s` using `cK4 M₀`.

Rewrite `hS₀s` using `[← hS₀]`. Establish `hT : M₀.map ι - (G.map ι * (M₀.map ι).map σ * (G.map ι)⁻¹)ᵀ = S₀.map ι`. Rewrite using `[hS₀, Matrix.map_sub _ (map_sub ι), Matrix.transpose_map, Matrix.map_mul, Matrix.map_mul, hmm, map_inv' ι G hdu]`. Rewrite `hδ` using `[hSS, hT]`. Use `set T : Matrix (Fin n) (Fin n) R := S₀.map ι with hTdef`.

Establish `hY : -(((d2 * d3 * D) • X) * (d1 • U)) ∈ O` using `neg_mem (mul_mem (nsmul_mem hX _) hO1)`. Take `⟨W, hWO, hW'⟩` from `hnak _ hY`. Establish `hNY : N • (-(((d2 * d3 * D) • X) * (d1 • U))) = -((S - T) * U)`. Rewrite using `[hδ, smul_neg]`. Simplify using `only [smul_mul_assoc, mul_smul_comm, smul_smul]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hW'` using `[hNY]`. Establish `hW : W * (1 + e • (-((S - T) * U))) = 1` using `mul_eq_one_comm.1 hW'`. Establish `h1T : (1 + S₀).map ι = 1 + T`.

Rewrite using `[Matrix.map_add _ (map_add ι), Matrix.map_one _ (map_zero ι) (map_one ι)]`. Establish `hS₀u : IsUnit (1 + S₀).det`. Use `Ne.isUnit fun h0 => he0 ?_` and prove the remaining obligations. Establish `e1` using `congrArg Matrix.det (idem_factor e he S T U hU)`. Establish `e2 : (1 + T).det = 0`.

Rewrite using `[← h1T]`. Use `RingHom.map_det ι (1 + S₀)` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `this.symm`. Establish `e3 : IsUnit ((1 + e • (-((S - T) * U))) * (1 + S)).det`.

Rewrite using `[Matrix.det_mul]`. Conclude with `(Matrix.isUnit_det_of_left_inverse hW).mul hSu`. Rewrite `e1` using `[Matrix.det_smul, Matrix.det_smul, e2, mul_zero]`. Establish `e4` using `e3.mul_left_eq_zero.1 e1.symm`. Establish `e5` using `IsIdempotentElem.pow_succ_eq (Fintype.card (Fin n)) (show IsIdempotentElem e from he)`.

Rewrite using `[← e5, pow_succ, e4, zero_mul]`. Use `set V : Matrix (Fin n) (Fin n) R := (1 + S₀)⁻¹.map ι with hVdef`. Establish `hV : V * (1 + T) = 1`. Rewrite using `[← h1T, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hS₀u, Matrix.map_one _ (map_zero ι) (map_one ι)]`. Establish `hV' : (1 + T) * V = 1` using `mul_eq_one_comm.1 hV`.

Establish `hγ` using `cK3 S₀ hS₀s hS₀u`. Use `⟨c lam • ((1 - S₀) * (1 + S₀)⁻¹), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul'', hc, Matrix.transpose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm, hlam, one_smul, hγ]`. Use `⟨(N * d1) • (e • ((d2 • ((2 * σ (ι lam)) • U)) * W * X * (d3 • (U * g)))), nsmul_mem (heO _ (mul_mem (mul_mem (mul_mem hO2 hWO) hX) hO3)) _, ?_⟩` and prove the remaining obligations. Establish `e1 : (c lam • ((1 - S₀) * (1 + S₀)⁻¹)).map ι = σ (ι lam) • ((2 : R) • V - 1)`.

Rewrite using `[map_smul'', hσι, Matrix.map_mul, Matrix.map_sub _ (map_sub ι), Matrix.map_one _ (map_zero ι) (map_one ι), ← hVdef, ← hTdef, cay _ _ hV']`. Establish `e2 : k = (2 : R) • U - 1`. Rewrite using `[← hkS, cay _ _ hU']`. Establish `e3 : e • (1 : Matrix (Fin n) (Fin n) R) = e • (σ (ι lam) • (k * g))`. Rewrite using `[hk, smul_mul_assoc, smul_smul (σ _), mul_comm, hl, one_smul, ← smul_mul_assoc, smul_add, smul_smul, smul_smul, he, mul_sub, he, mul_one, sub_self, zero_smul, add_zero, smul_mul_assoc, hg]`.

Establish `e4` using `idem_diff e he S T U V W hU hU' hV hV' hW`. Establish `e5 : e • ((c lam • ((1 - S₀) * (1 + S₀)⁻¹)).map ι * g - 1) = (2 * σ (ι lam)) • ((e • (V - U)) * g)`. Rewrite using `[smul_sub, e3, e1, e2]`. Simplify using `only [smul_mul_assoc, sub_mul, one_mul]`. Use `module`.

Rewrite using `[e5, e4, hδ]`. Simplify using `only [smul_mul_assoc, mul_smul_comm, mul_assoc]`. Use `module`.
-/
theorem core {K R : Type} [Field K] [CommRing R] (ι : K →+* R) (c : K →+* K) (σ : R →+* R)
    (hσι : ∀ x, σ (ι x) = ι (c x)) (hc : ∀ x, c (c x) = x) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (hG : (G.map c)ᵀ = G) (hdet : G.det ≠ 0) (h2 : (2 : K) ≠ 0)
    (O : Subring (Matrix (Fin n) (Fin n) R)) (hb : ∀ M, ∃ d : ℕ, 0 < d ∧ d • M ∈ O)
    (e : R) (he : e * e = e) (hσe : σ e = e) (he0 : e ≠ 0) (heO : ∀ X ∈ O, e • X ∈ O)
    (N : ℕ) (hN : 0 < N) (hnak : ∀ X ∈ O, ∃ W ∈ O, (1 + e • (N • X)) * W = 1)
    (hapx : ∀ (M : Matrix (Fin n) (Fin n) R) (D : ℕ), 0 < D → ∃ M₀ : Matrix (Fin n) (Fin n) K, ∃ X ∈ O,
      (M - (G.map ι * M.map σ * (G.map ι)⁻¹)ᵀ) -
        (M₀.map ι - (G.map ι * (M₀.map ι).map σ * (G.map ι)⁻¹)ᵀ) = D • X)
    (g h : Matrix (Fin n) (Fin n) R) (hg : h * g = 1) (hh : hᵀ * G.map ι * h.map σ = G.map ι)
    (lam : K) (hlam : lam * c lam = 1)
    (hu : IsUnit (1 + ι lam • (e • h + (1 - e) • (1 : Matrix (Fin n) (Fin n) R))).det)
    (D : ℕ) (hD : 0 < D) :
    ∃ γ : Matrix (Fin n) (Fin n) K, γᵀ * G * γ.map c = G ∧
      ∃ X ∈ O, e • (γ.map ι * g - 1) = D • X := by
  have hmm : ∀ A : Matrix (Fin n) (Fin n) K, (A.map ι).map σ = (A.map c).map ι := by
    intro A
    ext i j
    simp [hσι]
  have cay : ∀ A B : Matrix (Fin n) (Fin n) R, (1 + A) * B = 1 → (1 - A) * B = (2 : R) • B - 1 := by
    intro A B hAB
    rw [add_mul, one_mul] at hAB
    rw [sub_mul, one_mul, two_smul, ← hAB]
    abel
  have hdu : IsUnit G.det := hdet.isUnit
  have hG' : ((G.map ι).map σ)ᵀ = G.map ι := by
    rw [hmm, ← Matrix.transpose_map, hG]
  have hdet' : IsUnit (G.map ι).det := by
    have := hdu.map ι
    rwa [RingHom.map_det] at this
  have h2' : IsUnit (2 : R) := by
    have := h2.isUnit.map ι
    rwa [map_ofNat] at this
  obtain ⟨cR1, cR2, -, -⟩ := GlobalTheory.T.cayleyTransform_unitary_skew_involutive R σ n (G.map ι) hσ hG' hdet' h2'
  obtain ⟨-, -, cK3, cK4⟩ := GlobalTheory.T.cayleyTransform_unitary_skew_involutive K c n G hc hG hdu h2.isUnit
  have hl : ι lam * σ (ι lam) = 1 := by rw [hσι, ← map_mul, hlam, map_one]
  set k : Matrix (Fin n) (Fin n) R := ι lam • (e • h + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) with hk
  have hku : kᵀ * G.map ι * k.map σ = G.map ι := preserves_form_smul_idempotent_glue σ _ h e _ he hσe hl hh
  obtain ⟨hS, hSu⟩ := cR1 k hku hu
  have hkS := cR2 k hu
  set S : Matrix (Fin n) (Fin n) R := (1 - k) * (1 + k)⁻¹ with hSdef
  set U : Matrix (Fin n) (Fin n) R := (1 + S)⁻¹ with hUdef
  have hU : U * (1 + S) = 1 := Matrix.nonsing_inv_mul _ hSu
  have hU' : (1 + S) * U = 1 := Matrix.mul_nonsing_inv _ hSu
  obtain ⟨d1, hd1, hO1⟩ := hb U
  obtain ⟨d2, hd2, hO2⟩ := hb ((2 * σ (ι lam)) • U)
  obtain ⟨d3, hd3, hO3⟩ := hb (U * g)
  obtain ⟨M₀, X, hX, hδ⟩ := hapx (ι 2⁻¹ • S) (N * d1 * d2 * d3 * D) (by positivity)
  have hu2 : ι 2⁻¹ + ι 2⁻¹ = 1 := by
    rw [← map_add, ← two_mul, mul_inv_cancel₀ h2, map_one]
  have hSS : ι 2⁻¹ • S - (G.map ι * (ι 2⁻¹ • S).map σ * (G.map ι)⁻¹)ᵀ = S := by
    have e1 : G.map ι * S.map σ = -(Sᵀ * G.map ι) := eq_neg_of_add_eq_zero_right hS
    rw [map_smul'', hσι, map_inv₀ c, map_ofNat c, mul_smul_comm, e1, smul_mul_assoc, neg_mul, mul_assoc,
      Matrix.mul_nonsing_inv _ hdet', mul_one, Matrix.transpose_smul, Matrix.transpose_neg,
      Matrix.transpose_transpose, smul_neg, sub_neg_eq_add, ← add_smul, hu2, one_smul]
  set S₀ : Matrix (Fin n) (Fin n) K := M₀ - (G * M₀.map c * G⁻¹)ᵀ with hS₀
  have hS₀s := cK4 M₀
  rw [← hS₀] at hS₀s
  have hT : M₀.map ι - (G.map ι * (M₀.map ι).map σ * (G.map ι)⁻¹)ᵀ = S₀.map ι := by
    rw [hS₀, Matrix.map_sub _ (map_sub ι), Matrix.transpose_map, Matrix.map_mul, Matrix.map_mul, hmm,
      map_inv' ι G hdu]
  rw [hSS, hT] at hδ
  set T : Matrix (Fin n) (Fin n) R := S₀.map ι with hTdef
  have hY : -(((d2 * d3 * D) • X) * (d1 • U)) ∈ O := neg_mem (mul_mem (nsmul_mem hX _) hO1)
  obtain ⟨W, hWO, hW'⟩ := hnak _ hY
  have hNY : N • (-(((d2 * d3 * D) • X) * (d1 • U))) = -((S - T) * U) := by
    rw [hδ, smul_neg]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 2
    ring
  rw [hNY] at hW'
  have hW : W * (1 + e • (-((S - T) * U))) = 1 := mul_eq_one_comm.1 hW'
  have h1T : (1 + S₀).map ι = 1 + T := by
    rw [Matrix.map_add _ (map_add ι), Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hS₀u : IsUnit (1 + S₀).det := by
    refine Ne.isUnit fun h0 => he0 ?_
    have e1 := congrArg Matrix.det (idem_factor e he S T U hU)
    have e2 : (1 + T).det = 0 := by
      rw [← h1T]
      have := RingHom.map_det ι (1 + S₀)
      rw [h0, map_zero] at this
      exact this.symm
    have e3 : IsUnit ((1 + e • (-((S - T) * U))) * (1 + S)).det := by
      rw [Matrix.det_mul]
      exact (Matrix.isUnit_det_of_left_inverse hW).mul hSu
    rw [Matrix.det_smul, Matrix.det_smul, e2, mul_zero] at e1
    have e4 := e3.mul_left_eq_zero.1 e1.symm
    have e5 := IsIdempotentElem.pow_succ_eq (Fintype.card (Fin n)) (show IsIdempotentElem e from he)
    rw [← e5, pow_succ, e4, zero_mul]
  set V : Matrix (Fin n) (Fin n) R := (1 + S₀)⁻¹.map ι with hVdef
  have hV : V * (1 + T) = 1 := by
    rw [← h1T, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hS₀u,
      Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hV' : (1 + T) * V = 1 := mul_eq_one_comm.1 hV
  have hγ := cK3 S₀ hS₀s hS₀u
  refine ⟨c lam • ((1 - S₀) * (1 + S₀)⁻¹), ?_, ?_⟩
  · rw [map_smul'', hc, Matrix.transpose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_comm, hlam, one_smul, hγ]
  · refine ⟨(N * d1) • (e • ((d2 • ((2 * σ (ι lam)) • U)) * W * X * (d3 • (U * g)))),
      nsmul_mem (heO _ (mul_mem (mul_mem (mul_mem hO2 hWO) hX) hO3)) _, ?_⟩
    have e1 : (c lam • ((1 - S₀) * (1 + S₀)⁻¹)).map ι = σ (ι lam) • ((2 : R) • V - 1) := by
      rw [map_smul'', hσι, Matrix.map_mul, Matrix.map_sub _ (map_sub ι),
        Matrix.map_one _ (map_zero ι) (map_one ι), ← hVdef, ← hTdef, cay _ _ hV']
    have e2 : k = (2 : R) • U - 1 := by
      rw [← hkS, cay _ _ hU']
    have e3 : e • (1 : Matrix (Fin n) (Fin n) R) = e • (σ (ι lam) • (k * g)) := by
      rw [hk, smul_mul_assoc, smul_smul (σ _), mul_comm, hl, one_smul, ← smul_mul_assoc, smul_add,
        smul_smul, smul_smul, he, mul_sub, he, mul_one, sub_self, zero_smul, add_zero,
        smul_mul_assoc, hg]
    have e4 := idem_diff e he S T U V W hU hU' hV hV' hW
    have e5 : e • ((c lam • ((1 - S₀) * (1 + S₀)⁻¹)).map ι * g - 1) =
        (2 * σ (ι lam)) • ((e • (V - U)) * g) := by
      rw [smul_sub, e3, e1, e2]
      simp only [smul_mul_assoc, sub_mul, one_mul]
      module
    rw [e5, e4, hδ]
    simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
    module

def stab {R : Type} [CommRing R] {n : ℕ} (Λ : AddSubgroup (Fin n → R)) :
    Subring (Matrix (Fin n) (Fin n) R) where
  carrier := {M | ∀ z ∈ Λ, M *ᵥ z ∈ Λ}
  mul_mem' := fun {a b} ha hb z hz => by
    rw [← Matrix.mulVec_mulVec]; exact ha _ (hb z hz)
  one_mem' := fun z hz => by rwa [Matrix.one_mulVec]
  add_mem' := fun {a b} ha hb z hz => by
    rw [Matrix.add_mulVec]; exact add_mem (ha z hz) (hb z hz)
  zero_mem' := fun z _ => by rw [Matrix.zero_mulVec]; exact zero_mem _
  neg_mem' := fun {a} ha z hz => by rw [Matrix.neg_mulVec]; exact neg_mem (ha z hz)

/- English proof (translation)
Take `⟨u, hu⟩` from `hD.exists_left_inv`. Use `⟨u • M, fun z hz => ?_, ?_⟩` and prove the remaining obligations. Take `⟨w, hw, e⟩` from `h z hz`. Rewrite using `[Matrix.smul_mulVec, e, ← Nat.cast_smul_eq_nsmul R, smul_smul, hu, one_smul]` and apply the resulting hypothesis. Rewrite using `[← Nat.cast_smul_eq_nsmul R, smul_smul, mul_comm, hu, one_smul]`.
-/
theorem exists_stab {R : Type} [CommRing R] {n : ℕ} (Λ : AddSubgroup (Fin n → R))
    (M : Matrix (Fin n) (Fin n) R) (D : ℕ) (hD : IsUnit (D : R))
    (h : ∀ z ∈ Λ, ∃ w ∈ Λ, M *ᵥ z = D • w) : ∃ X ∈ stab Λ, M = D • X := by
  obtain ⟨u, hu⟩ := hD.exists_left_inv
  refine ⟨u • M, fun z hz => ?_, ?_⟩
  · obtain ⟨w, hw, e⟩ := h z hz
    rwa [Matrix.smul_mulVec, e, ← Nat.cast_smul_eq_nsmul R, smul_smul, hu, one_smul]
  · rw [← Nat.cast_smul_eq_nsmul R, smul_smul, mul_comm, hu, one_smul]

noncomputable def skewPart {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (G : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R →+ Matrix (Fin n) (Fin n) R :=
  AddMonoidHom.mk' (fun A => A - (G * A.map σ * G⁻¹)ᵀ) fun A B => by
    rw [Matrix.map_add _ (map_add σ), mul_add, add_mul, Matrix.transpose_add]
    abel

/- English proof (translation)
Express the relevant statement in the definitionally equal form `a • A - (G * (a • A).map σ * G⁻¹)ᵀ = a • (A - (G * A.map σ * G⁻¹)ᵀ)`. Rewrite using `[map_smul'', ha, mul_smul_comm, smul_mul_assoc, Matrix.transpose_smul, smul_sub]`.
-/
theorem skewPart_smul {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (G : Matrix (Fin n) (Fin n) R)
    (a : R) (ha : σ a = a) (A : Matrix (Fin n) (Fin n) R) :
    skewPart σ G (a • A) = a • skewPart σ G A := by
  change a • A - (G * (a • A).map σ * G⁻¹)ᵀ = a • (A - (G * A.map σ * G⁻¹)ᵀ)
  rw [map_smul'', ha, mul_smul_comm, smul_mul_assoc, Matrix.transpose_smul, smul_sub]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.transpose_mul, Matrix.map_mul]`. Simplify using `only [mul_assoc]`. Use `_ = G := by rw [hgh, Matrix.map_one _ (map_zero σ) (map_one σ)]; simp`.
-/
theorem unitary_inv {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (G g h : Matrix (Fin n) (Fin n) R)
    (hgh : g * h = 1) (hg : gᵀ * G * g.map σ = G) : hᵀ * G * h.map σ = G := by
  calc hᵀ * G * h.map σ = hᵀ * (gᵀ * G * g.map σ) * h.map σ := by rw [hg]
    _ = (g * h)ᵀ * G * (g * h).map σ := by
      rw [Matrix.transpose_mul, Matrix.map_mul]
      simp only [mul_assoc]
    _ = G := by rw [hgh, Matrix.map_one _ (map_zero σ) (map_one σ)]; simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ c n G hG hr L hfg hsp g N D hg hN hD`. Take `⟨hcc, hc1, hGc, hdet⟩` from `hG`. Take `⟨i1, i2, -, i4, i5⟩` from `GlobalTheory.T.idempotent_adeles_and_small_adelic_matrices F E n L hfg hsp`. Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | (N : 𝓞 F) ∈ v.asIdeal}.Finite`. Establish `hne : Ideal.span {(N : 𝓞 F)} ≠ 0`.

Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `Nat.cast_ne_zero.2 hN.ne'`. Use `(Ideal.finite_factors hne).subset fun v hv => ?_` and prove the remaining obligations. Conclude with `Ideal.dvd_span_singleton.2 hv`. Take `⟨e, he1, he0⟩` from `i1 hfin.toFinset`.

Establish `he1' : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 1` using `fun v hv => he1 v (hfin.mem_toFinset.2 hv)`. Establish `he0' : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∉ v.asIdeal → e v = 0` using `fun v hv => he0 v fun h => hv (hfin.mem_toFinset.1 h)`. Establish `hee : e * e = e`. Use `FiniteAdeleRing.ext F fun v => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e v * e v = e v`.

Distinguish the cases in `hv : (N : 𝓞 F) ∈ v.asIdeal`. Rewrite using `[he1' v hv, mul_one]`. Rewrite using `[he0' v hv, mul_zero]`. Establish `heI : ∀ v, e v ∈ v.adicCompletionIntegers F`. Introduce `v`.

Distinguish the cases in `hv : (N : 𝓞 F) ∈ v.asIdeal`. Rewrite using `[he1' v hv]`. Conclude with `one_mem _`. Rewrite using `[he0' v hv]`. Conclude with `zero_mem _`.

Establish `hsupp : {v | e v ≠ 0}.Finite` using `hfin.subset fun v hv => by`. Assume the negation of the conclusion as `h`. Conclude with `hv (he0' v h)`. Establish `hsub : ((1 - e) ⊗ₜ[F] (1 : E) : RA F E) = 1 - e ⊗ₜ[F] (1 : E)`. Rewrite using `[TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]`.

Establish `key : ∀ k : Matrix (Fin n) (Fin n) (RA F E), (∃ X ∈ stab (hat F (L : Set (Fin n → E))), (e ⊗ₜ[F] (1 : E) : RA F E) • (k - 1) = D • X) → CongAtA F L N D k`. Introduce and unpack `k ⟨X, hX, hk⟩`. Take `⟨t, ht, H⟩` from `i4 N D (1 - e) (k - 1) hD fun v hv => by`. Express the relevant statement in the definitionally equal form `1 - e v = 0`. Rewrite using `[he1' v hv, sub_self]`.

Use `⟨t, ht, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, hwz⟩` from `H z hz`. Use `⟨w + t • (X *ᵥ z), add_mem hw (nsmul_mem (hX z hz) t), ?_⟩` and prove the remaining obligations. Establish `: k *ᵥ z - z = (((1 - e) ⊗ₜ[F] (1 : E) : RA F E) • (k - 1)) *ᵥ z + D • (X *ᵥ z)`. Rewrite using `[← Matrix.smul_mulVec D, ← hk, ← Matrix.add_mulVec, ← add_smul, hsub, sub_add_cancel, one_smul, Matrix.sub_mulVec, Matrix.one_mulVec]`.

Rewrite using `[this, smul_add, hwz, smul_add, smul_comm t D]`. Distinguish the cases in `hz : (e ⊗ₜ[F] (1 : E) : RA F E) = 0`. Use `⟨1, fun x y => by simp, key _ ⟨0, zero_mem _, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hz, zero_smul, smul_zero]`. Set `ι : E →+* RA F E` to `(Algebra.TensorProduct.includeRight : E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E).toRingHom`.

Set `σ : RA F E →+* RA F E` to `(sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom`. Set `c' : E →+* E` to `(c : E →ₐ[F] E).toRingHom`. Establish `hσt : ∀ (a : FiniteAdeleRing (𝓞 F) F) (x : E), σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] c x` using `fun a x => rfl`. Establish `hσσ : ∀ x, σ (σ x) = x`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y => rw [hσt, hσt, hcc]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Establish `hσ1 : ∀ a : FiniteAdeleRing (𝓞 F) F, σ (a ⊗ₜ[F] (1 : E)) = a ⊗ₜ[F] (1 : E)`.

Introduce `a`. Rewrite using `[hσt, map_one]`. Establish `hunit : ∀ d : ℕ, 0 < d → IsUnit (d : RA F E)`. Introduce `d hd`. Use `(Nat.cast_ne_zero.2 hd.ne' : (d : E) ≠ 0).isUnit.map ι` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hgu : g.1ᵀ * G.map ι * g.1.map σ = G.map ι` using `(preserves_iff σ (G.map ι) g.1).1 hg`. Take `⟨lam, hlam, hu⟩` from `GlobalTheory.T.adelic_unitary_scaling_unit F E c hr hcc hc1 n (g⁻¹).1 e hee hsupp`. Rewrite `hu` using `[hsub]`. Take `⟨γ, hγ, hcong⟩` from `core ι c' σ (fun x => hσt 1 x) hcc hσσ G (by ext a b; exact hGc b a) hdet two_ne_zero (stab (hat F (L : Set (Fin n → E)))) (fun M => by`.

Take `⟨d, hd, H⟩` from `i2 M`. Conclude with `⟨d, hd, fun z hz => by rw [Matrix.smul_mulVec]; exact H z hz⟩)`. Use the proof step `(e ⊗ₜ[F] (1 : E)) (by rw [Algebra.TensorProduct.tmul_mul_tmul, hee, mul_one]) (hσ1 e) hz`. Use the proof step `(fun X hX z hz => by rw [Matrix.smul_mulVec]; exact i5 e heI _ (hX z hz))`. Use `N hN (fun X hX => by`.

Take `⟨W, hW, hW'⟩` from `GlobalTheory.T.exists_inverse_one_add_preserving_adelicCompletion F E n L hfg hsp N e heI he0' X hX`. Conclude with `⟨W, hW', hW⟩)`. Use the proof step `(fun M D' hD' => by`. Take `⟨M₀, H⟩` from `GlobalTheory.T.exists_rational_matrix_approx_adele_linear_map F E n L hfg hsp (skewPart σ (G.map ι)) (fun a M => skewPart_smul σ _ _ (hσ1 a) M) M D' hD'`. Take `⟨X, hX, hX'⟩` from `exists_stab _ _ D' (hunit D' hD') H`.

Rewrite `hX'` using `[map_sub]`. Conclude with `⟨M₀, X, hX, hX'⟩)`. Use the proof step `g.1 (g⁻¹).1 g.inv_mul (unitary_inv σ _ g.1 _ g.mul_inv hgu) lam hlam hu D hD`. Establish `hγdet : γ.det ≠ 0`. Introduce `h0`.

Use `congrArg Matrix.det hγ` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul]`. Conclude with `hdet this.symm`. Conclude with `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero γ hγdet, (preserves_iff c' G γ).2 hγ, key _ hcong⟩`.
-/
theorem weak_approximation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N D : ℕ), IsUnA c G g.1 → 0 < N → 0 < D → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAtA F L N D (fm F γ.1 * g.1) := by
  intro F E _ _ _ _ _ c n G hG hr L hfg hsp g N D hg hN hD
  classical
  obtain ⟨hcc, hc1, hGc, hdet⟩ := hG
  obtain ⟨i1, i2, -, i4, i5⟩ := GlobalTheory.T.idempotent_adeles_and_small_adelic_matrices F E n L hfg hsp
  have hfin : {v : HeightOneSpectrum (𝓞 F) | (N : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have hne : Ideal.span {(N : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 hN.ne'
    refine (Ideal.finite_factors hne).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  obtain ⟨e, he1, he0⟩ := i1 hfin.toFinset
  have he1' : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 1 :=
    fun v hv => he1 v (hfin.mem_toFinset.2 hv)
  have he0' : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∉ v.asIdeal → e v = 0 :=
    fun v hv => he0 v fun h => hv (hfin.mem_toFinset.1 h)
  have hee : e * e = e := by
    refine FiniteAdeleRing.ext F fun v => ?_
    change e v * e v = e v
    by_cases hv : (N : 𝓞 F) ∈ v.asIdeal
    · rw [he1' v hv, mul_one]
    · rw [he0' v hv, mul_zero]
  have heI : ∀ v, e v ∈ v.adicCompletionIntegers F := by
    intro v
    by_cases hv : (N : 𝓞 F) ∈ v.asIdeal
    · rw [he1' v hv]; exact one_mem _
    · rw [he0' v hv]; exact zero_mem _
  have hsupp : {v | e v ≠ 0}.Finite := hfin.subset fun v hv => by
    by_contra h
    exact hv (he0' v h)
  have hsub : ((1 - e) ⊗ₜ[F] (1 : E) : RA F E) = 1 - e ⊗ₜ[F] (1 : E) := by
    rw [TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]

  have key : ∀ k : Matrix (Fin n) (Fin n) (RA F E),
      (∃ X ∈ stab (hat F (L : Set (Fin n → E))), (e ⊗ₜ[F] (1 : E) : RA F E) • (k - 1) = D • X) →
      CongAtA F L N D k := by
    rintro k ⟨X, hX, hk⟩
    obtain ⟨t, ht, H⟩ := i4 N D (1 - e) (k - 1) hD fun v hv => by
      change 1 - e v = 0
      rw [he1' v hv, sub_self]
    refine ⟨t, ht, fun z hz => ?_⟩
    obtain ⟨w, hw, hwz⟩ := H z hz
    refine ⟨w + t • (X *ᵥ z), add_mem hw (nsmul_mem (hX z hz) t), ?_⟩
    have : k *ᵥ z - z = (((1 - e) ⊗ₜ[F] (1 : E) : RA F E) • (k - 1)) *ᵥ z + D • (X *ᵥ z) := by
      rw [← Matrix.smul_mulVec D, ← hk, ← Matrix.add_mulVec, ← add_smul, hsub, sub_add_cancel, one_smul,
        Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [this, smul_add, hwz, smul_add, smul_comm t D]
  by_cases hz : (e ⊗ₜ[F] (1 : E) : RA F E) = 0
  · refine ⟨1, fun x y => by simp, key _ ⟨0, zero_mem _, ?_⟩⟩
    rw [hz, zero_smul, smul_zero]
  let ι : E →+* RA F E := (Algebra.TensorProduct.includeRight :
    E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E).toRingHom
  let σ : RA F E →+* RA F E := (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom
  let c' : E →+* E := (c : E →ₐ[F] E).toRingHom
  have hσt : ∀ (a : FiniteAdeleRing (𝓞 F) F) (x : E), σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] c x := fun a x => rfl
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => rw [hσt, hσt, hcc]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hσ1 : ∀ a : FiniteAdeleRing (𝓞 F) F, σ (a ⊗ₜ[F] (1 : E)) = a ⊗ₜ[F] (1 : E) := by
    intro a; rw [hσt, map_one]
  have hunit : ∀ d : ℕ, 0 < d → IsUnit (d : RA F E) := by
    intro d hd
    have := (Nat.cast_ne_zero.2 hd.ne' : (d : E) ≠ 0).isUnit.map ι
    rwa [map_natCast] at this
  have hgu : g.1ᵀ * G.map ι * g.1.map σ = G.map ι := (preserves_iff σ (G.map ι) g.1).1 hg
  obtain ⟨lam, hlam, hu⟩ := GlobalTheory.T.adelic_unitary_scaling_unit F E c hr hcc hc1 n (g⁻¹).1 e hee hsupp
  rw [hsub] at hu
  obtain ⟨γ, hγ, hcong⟩ := core ι c' σ (fun x => hσt 1 x) hcc hσσ G
    (by ext a b; exact hGc b a) hdet two_ne_zero (stab (hat F (L : Set (Fin n → E))))
    (fun M => by
      obtain ⟨d, hd, H⟩ := i2 M
      exact ⟨d, hd, fun z hz => by rw [Matrix.smul_mulVec]; exact H z hz⟩)
    (e ⊗ₜ[F] (1 : E)) (by rw [Algebra.TensorProduct.tmul_mul_tmul, hee, mul_one]) (hσ1 e) hz
    (fun X hX z hz => by rw [Matrix.smul_mulVec]; exact i5 e heI _ (hX z hz))
    N hN (fun X hX => by
      obtain ⟨W, hW, hW'⟩ := GlobalTheory.T.exists_inverse_one_add_preserving_adelicCompletion F E n L hfg hsp N e heI he0' X hX
      exact ⟨W, hW', hW⟩)
    (fun M D' hD' => by
      obtain ⟨M₀, H⟩ := GlobalTheory.T.exists_rational_matrix_approx_adele_linear_map F E n L hfg hsp (skewPart σ (G.map ι))
        (fun a M => skewPart_smul σ _ _ (hσ1 a) M) M D' hD'
      obtain ⟨X, hX, hX'⟩ := exists_stab _ _ D' (hunit D' hD') H
      rw [map_sub] at hX'
      exact ⟨M₀, X, hX, hX'⟩)
    g.1 (g⁻¹).1 g.inv_mul (unitary_inv σ _ g.1 _ g.mul_inv hgu) lam hlam hu D hD
  have hγdet : γ.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hγ
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at this
    exact hdet this.symm
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero γ hγdet, (preserves_iff c' G γ).2 hγ, key _ hcong⟩

end GlobalTheory.UnRep.WeakApprox
