import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount

open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Introduce `V _ _ B r f x'`. Prove the components needed by the constructor for the conclusion. Introduce `a`. Establish `h` using `congrArg (fun M => M a (Fin.last r)) (Matrix.mul_adjugate (C7.zhat B f x'))`. Simplify using `only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at h`.

Unfold `C7.cofX'`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[← h]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `b _`.

Rewrite using `[mul_comm]`. Both sides reduce to the same expression. Introduce `b`. Establish `h` using `congrArg (fun M => M (Fin.last r) b) (Matrix.adjugate_mul (C7.zhat B f x'))`. Simplify using `only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at h`.

Unfold `C7.cofX`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, smul_eq_mul, Complex.conj_conj]`. Establish `e : (if b = Fin.last r then (C7.zhat B f x').det else 0) = (if Fin.last r = b then (C7.zhat B f x').det else 0)`. Apply the tactic sequence `by_cases hb : b = Fin.last r <;> simp [hb, eq_comm]`. Rewrite using `[e, ← h]`.

Both sides reduce to the same expression.
-/
theorem cofactorPair_statement : C7.CofactorPair := by
  intro V _ _ B r f x'
  constructor
  · intro a
    have h := congrArg (fun M => M a (Fin.last r)) (Matrix.mul_adjugate (C7.zhat B f x'))
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero] at h
    unfold C7.cofX'
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← h]
    apply Finset.sum_congr rfl; intro b _; rw [mul_comm]; rfl
  · intro b
    have h := congrArg (fun M => M (Fin.last r) b) (Matrix.adjugate_mul (C7.zhat B f x'))
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero] at h
    unfold C7.cofX
    simp only [map_sum, LinearMap.map_smulₛₗ, smul_eq_mul, Complex.conj_conj]
    have e : (if b = Fin.last r then (C7.zhat B f x').det else 0) =
        (if Fin.last r = b then (C7.zhat B f x').det else 0) := by
      by_cases hb : b = Fin.last r <;> simp [hb, eq_comm]
    rw [e, ← h]
    rfl

/- English proof (translation)
Introduce `r Z`. Rewrite using `[Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]`. Unfold `C7.minorR`. Establish `: ((-1 : ℂ)) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1`. Rewrite using `[← two_mul, pow_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[this, one_mul]`.
-/
theorem cofactor_corner_identity : C7.CofactorCorner := by
  intro r Z
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  unfold C7.minorR
  have : ((-1 : ℂ)) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1 := by
    rw [← two_mul, pow_mul]; simp
  rw [this, one_mul]

/- English proof (translation)
Introduce `r Z l u hl1 hl2 hu1 hu2 b`. Establish `hdl : l.det = 1`. Rewrite using `[Matrix.det_of_lowerTriangular l (fun i j h => hl1 i j h)]`. Simplify using `[hl2]`. Establish `hdu : u.det = 1`.

Rewrite using `[Matrix.det_of_upperTriangular (fun i j h => hu1 i j h)]`. Simplify using `[hu2]`. Establish `hadj : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, M.det = 1 → adjugate M = M⁻¹`. Introduce `M hM`. Rewrite using `[Matrix.inv_def, hM]`.

Simplify using the standard rewrite rules. Establish `hcol : ∀ d, l d (Fin.last r) = if d = Fin.last r then 1 else 0`. Introduce `d`. Distinguish the cases in `hd : d = Fin.last r`. Substitute `hd` using the available equality.

Simplify using `[hl2]`. Rewrite using `[if_neg hd]`. Conclude with `hl1 d _ (Fin.lt_last_iff_ne_last.2 hd)`. Establish `hinv : ∀ d, l⁻¹ d (Fin.last r) = if d = Fin.last r then 1 else 0`. Introduce `d`.

Establish `e : l⁻¹ * l = 1` using `Matrix.nonsing_inv_mul l (by rw [hdl]; exact isUnit_one)`. Use `congrArg (fun M => M d (Fin.last r)) e` as an intermediate fact. Simplify using `only [Matrix.mul_apply, hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.one_apply] at this`. Rewrite using `[this]`. Rewrite using `[Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hadj u hdu, hadj l hdl, Matrix.mul_apply]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `c _`. Use `congr 1`. Rewrite using `[Matrix.mul_apply]`. Simplify using `[hinv]`.
-/
theorem adjLastCol_statement : C7.AdjLastCol := by
  intro r Z l u hl1 hl2 hu1 hu2 b
  have hdl : l.det = 1 := by
    rw [Matrix.det_of_lowerTriangular l (fun i j h => hl1 i j h)]; simp [hl2]
  have hdu : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j h => hu1 i j h)]; simp [hu2]
  have hadj : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, M.det = 1 → adjugate M = M⁻¹ := by
    intro M hM; rw [Matrix.inv_def, hM]; simp
  have hcol : ∀ d, l d (Fin.last r) = if d = Fin.last r then 1 else 0 := by
    intro d
    by_cases hd : d = Fin.last r
    · subst hd; simp [hl2]
    · rw [if_neg hd]; exact hl1 d _ (Fin.lt_last_iff_ne_last.2 hd)
  have hinv : ∀ d, l⁻¹ d (Fin.last r) = if d = Fin.last r then 1 else 0 := by
    intro d
    have e : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l (by rw [hdl]; exact isUnit_one)
    have := congrArg (fun M => M d (Fin.last r)) e
    simp only [Matrix.mul_apply, hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Matrix.one_apply] at this
    rw [this]
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hadj u hdu, hadj l hdl, Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro c _
  congr 1
  rw [Matrix.mul_apply]
  simp [hinv]

/- English proof (translation)
Introduce `V _ _ B r f x' T' h`. Unfold `C7.cofX'`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.map_smulₛₗ, h]`. Simplify using `only [mul_ite, mul_zero, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]`. Rewrite using `[cofactor_corner_identity r (C7.zhat B f x')]`.

Rewrite using `[← Complex.mul_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_cofactor_identity : C7.GramCofactor := by
  intro V _ _ B r f x' T' h
  unfold C7.cofX'
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.map_smulₛₗ, h]
  simp only [mul_ite, mul_zero, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  rw [cofactor_corner_identity r (C7.zhat B f x')]
  rw [← Complex.mul_conj]
  ring

/- English proof (translation)
Introduce `V _ _ B x ω z T T' D Dr hH hT hxx hxω hxz hωz hzz hv`. Establish `hωx : B ω x = 0` using `by rw [hH x ω, hxω, map_zero]`. Establish `hzx : B z x = 0` using `by rw [hH x z, hxz, map_zero]`. Establish `hzω : B z ω = 0` using `by rw [hH ω z, hωz, map_zero]`. Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hxx, hxω, hxz, hωx, hωz, hzx, hzω, hzz] at hv`.

Establish `hT0 : (T : ℂ) ≠ 0` using `by exact_mod_cast hT.ne'`. Establish `hc : (-D / T) * (starRingEnd ℂ) (-D / T) = (Complex.normSq D : ℂ) / T ^ 2`. Rewrite using `[map_div₀, map_neg, Complex.conj_ofReal, ← Complex.mul_conj]`. Clear the denominators using the available nonvanishing facts. Establish `e : B ω ω = -(T' : ℂ) * Complex.normSq Dr + (Complex.normSq D : ℂ) / T ^ 2 * T`.

Rewrite using `[← hc]`. Take the linear combination `hv`. Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem omega_norm_identity : C7.OmNorm := by
  intro V _ _ B x ω z T T' D Dr hH hT hxx hxω hxz hωz hzz hv
  have hωx : B ω x = 0 := by rw [hH x ω, hxω, map_zero]
  have hzx : B z x = 0 := by rw [hH x z, hxz, map_zero]
  have hzω : B z ω = 0 := by rw [hH ω z, hωz, map_zero]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
    hxx, hxω, hxz, hωx, hωz, hzx, hzω, hzz] at hv
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hc : (-D / T) * (starRingEnd ℂ) (-D / T) = (Complex.normSq D : ℂ) / T ^ 2 := by
    rw [map_div₀, map_neg, Complex.conj_ofReal, ← Complex.mul_conj]; field_simp
  have e : B ω ω = -(T' : ℂ) * Complex.normSq Dr + (Complex.normSq D : ℂ) / T ^ 2 * T := by
    rw [← hc]; linear_combination hv
  rw [e]; field_simp; ring

/- English proof (translation)
Introduce `V _ _ B r f x' x ω z T T' hH hT hG hxx hxω hxz hωz hzz hcof`. Establish `hv` using `gram_cofactor_identity V B r f x' T' hG`. Rewrite `hv` using `[hcof]`. Conclude with `omega_norm_identity V B x ω z T T' _ _ hH hT hxx hxω hxz hωz hzz hv`.
-/
theorem omNormCofactor_statement : C7.OmNormCofactor := by
  intro V _ _ B r f x' x ω z T T' hH hT hG hxx hxω hxz hωz hzz hcof
  have hv := gram_cofactor_identity V B r f x' T' hG
  rw [hcof] at hv
  exact omega_norm_identity V B x ω z T T' _ _ hH hT hxx hxω hxz hωz hzz hv

/- English proof (translation)
Introduce `_ _` and use `omNormCofactor_statement`.
-/
theorem omNormCofactorOfParts_statement : C7.OmNormCofactorOfParts := fun _ _ => omNormCofactor_statement

/- English proof (translation)
Introduce `V _ _ B V' _ _ ω₁ ω₂ ω₁' ω₂' D₁ D₂ Dr₁ Dr₂ T T' hD1 hD2 hT hT' h2 h2' hn1 hn2`. Establish `hcD1 : (starRingEnd ℂ) D₁ ≠ 0` using `(map_ne_zero _).2 hD1`. Establish `hcD2 : (starRingEnd ℂ) D₂ ≠ 0` using `(map_ne_zero _).2 hD2`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, smul_smul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h2', smul_smul]`. Use `congr 1`. Rewrite using `[map_div₀]`.

Clear the denominators using the available nonvanishing facts. Establish `hu : (D₂ / D₁) * (starRingEnd ℂ) (D₂ / D₁) = (Complex.normSq D₂ : ℂ) / Complex.normSq D₁`. Rewrite using `[map_div₀, div_mul_div_comm, Complex.mul_conj, Complex.mul_conj]`. Rewrite `hn2` using `[h2]`. Simplify using `only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at hn2`.

Establish `hN1 : (Complex.normSq D₁ : ℂ) ≠ 0` using `by exact_mod_cast (Complex.normSq_pos.2 hD1).ne'`. Establish `e : (T : ℂ) * ((starRingEnd ℂ) (D₂ / D₁) * (D₂ / D₁ * B ω₁ ω₁)) = ((D₂ / D₁) * (starRingEnd ℂ) (D₂ / D₁)) * (T * B ω₁ ω₁)` using `by ring`. Rewrite `hn2` using `[e, hu, hn1]`. Establish `hTT : ((T : ℂ) * T') ≠ 0`. Establish `: (T : ℂ) ≠ 0` using `by exact_mod_cast hT.ne'`.

Establish `: (T' : ℂ) ≠ 0` using `by exact_mod_cast hT'.ne'`. Conclude with `mul_ne_zero (by assumption) (by assumption)`. Establish `key : (Complex.normSq D₂ : ℂ) * Complex.normSq Dr₁ = Complex.normSq D₁ * Complex.normSq Dr₂`. Establish `h3 : ((T : ℂ) * T') * ((Complex.normSq D₂ : ℂ) * Complex.normSq Dr₁ - Complex.normSq D₁ * Complex.normSq Dr₂) = 0`. Clear denominators, using `at hn2` for the nonvanishing conditions.

Take the linear combination `(-1 : ℂ) * hn2`. Use `(mul_eq_zero.1 h3).resolve_left hTT` as an intermediate fact. Take the linear combination `this`. Establish `keyR : Complex.normSq D₂ * Complex.normSq Dr₁ = Complex.normSq D₁ * Complex.normSq Dr₂`. Conclude with `key` after adjusting the coercions.

Establish `p1` using `Complex.normSq_pos.2 hD1`. Establish `p2` using `Complex.normSq_pos.2 hD2`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `keyR` using `[h, Complex.normSq_zero, mul_zero]`.

Establish `: Complex.normSq Dr₂ = 0`. Break down `mul_eq_zero.1 keyR.symm with h' | h'` into its components or cases. Conclude with `absurd h' p1.ne'`. Conclude with `h'`. Conclude with `Complex.normSq_eq_zero.1 this`.

Introduce `h`. Rewrite `keyR` using `[h, Complex.normSq_zero, mul_zero]`. Establish `: Complex.normSq Dr₁ = 0`. Break down `mul_eq_zero.1 keyR with h' | h'` into its components or cases. Conclude with `absurd h' p2.ne'`.

Conclude with `h'`. Conclude with `Complex.normSq_eq_zero.1 this`.
-/
theorem scalar_pair_common_factor : C7.ScalarPairCommon := by
  intro V _ _ B V' _ _ ω₁ ω₂ ω₁' ω₂' D₁ D₂ Dr₁ Dr₂ T T' hD1 hD2 hT hT' h2 h2' hn1 hn2
  have hcD1 : (starRingEnd ℂ) D₁ ≠ 0 := (map_ne_zero _).2 hD1
  have hcD2 : (starRingEnd ℂ) D₂ ≠ 0 := (map_ne_zero _).2 hD2
  refine ⟨?_, ?_, ?_⟩
  · rw [h2, smul_smul]; congr 1; field_simp
  · rw [h2', smul_smul]; congr 1; rw [map_div₀]; field_simp
  · have hu : (D₂ / D₁) * (starRingEnd ℂ) (D₂ / D₁) = (Complex.normSq D₂ : ℂ) / Complex.normSq D₁ := by
      rw [map_div₀, div_mul_div_comm, Complex.mul_conj, Complex.mul_conj]
    rw [h2] at hn2
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at hn2
    have hN1 : (Complex.normSq D₁ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 hD1).ne'
    have e : (T : ℂ) * ((starRingEnd ℂ) (D₂ / D₁) * (D₂ / D₁ * B ω₁ ω₁)) =
        ((D₂ / D₁) * (starRingEnd ℂ) (D₂ / D₁)) * (T * B ω₁ ω₁) := by ring
    rw [e, hu, hn1] at hn2
    have hTT : ((T : ℂ) * T') ≠ 0 := by
      have : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
      have : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
      exact mul_ne_zero (by assumption) (by assumption)
    have key : (Complex.normSq D₂ : ℂ) * Complex.normSq Dr₁ = Complex.normSq D₁ * Complex.normSq Dr₂ := by
      have h3 : ((T : ℂ) * T') * ((Complex.normSq D₂ : ℂ) * Complex.normSq Dr₁ -
          Complex.normSq D₁ * Complex.normSq Dr₂) = 0 := by
        field_simp at hn2
        linear_combination (-1 : ℂ) * hn2
      have := (mul_eq_zero.1 h3).resolve_left hTT
      linear_combination this
    have keyR : Complex.normSq D₂ * Complex.normSq Dr₁ = Complex.normSq D₁ * Complex.normSq Dr₂ := by
      exact_mod_cast key
    have p1 := Complex.normSq_pos.2 hD1
    have p2 := Complex.normSq_pos.2 hD2
    constructor
    · intro h; rw [h, Complex.normSq_zero, mul_zero] at keyR
      have : Complex.normSq Dr₂ = 0 := by
        rcases mul_eq_zero.1 keyR.symm with h' | h'
        · exact absurd h' p1.ne'
        · exact h'
      exact Complex.normSq_eq_zero.1 this
    · intro h; rw [h, Complex.normSq_zero, mul_zero] at keyR
      have : Complex.normSq Dr₁ = 0 := by
        rcases mul_eq_zero.1 keyR with h' | h'
        · exact absurd h' p2.ne'
        · exact h'
      exact Complex.normSq_eq_zero.1 this

end Formalism.FourierDecayAlt.P
