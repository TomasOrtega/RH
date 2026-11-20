import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsGlobalApproxOfLocalModPPowConj
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsBoundedDenominatorOfLocalIntegralityConj
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsFinsetSpanOfIntegralMultiples

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.HermitianFrame

variable {F K : Type} [Field F] [Field K] {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`.
-/
private theorem map_mulVec' (τ : F →+* K) (M : Matrix (Fin n) (Fin n) F) (v : Fin n → F) :
    (fun i => τ ((M *ᵥ v) i)) = M.map τ *ᵥ (fun i => τ (v i)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

/- English proof (translation)
Establish `hu : IsUnit S.det` using `isUnit_iff_ne_zero.mpr hS`. Establish `h1 : S⁻¹ * R = M * S⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.transpose_mul, ← Matrix.transpose_mul, h1]`.
-/
private theorem transpose_conj {R M S : Matrix (Fin n) (Fin n) K} (hS : S.det ≠ 0) (h : R * S = S * M) :
    Rᵀ * (S⁻¹)ᵀ = (S⁻¹)ᵀ * Mᵀ := by
  have hu : IsUnit S.det := isUnit_iff_ne_zero.mpr hS
  have h1 : S⁻¹ * R = M * S⁻¹ := by
    calc S⁻¹ * R = S⁻¹ * R * (S * S⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = S⁻¹ * (R * S) * S⁻¹ := by simp only [Matrix.mul_assoc]
      _ = S⁻¹ * (S * M) * S⁻¹ := by rw [h]
      _ = M * S⁻¹ := by rw [← Matrix.mul_assoc S⁻¹ S M, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, h1]

/- English proof (translation)
Rewrite using `[← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h, ← map_mulVec']`. Simplify using `[dotProduct, map_sum, map_mul]`.
-/
private theorem pair_eval (τ : F →+* K) (j : F →+* F) (S B : Matrix (Fin n) (Fin n) K) (Q : Matrix (Fin n) (Fin n) F)
    (h : Bᵀ * S = Q.map τ) (y z : Fin n → F) :
    (B *ᵥ (fun i => τ (j (y i)))) ⬝ᵥ (S *ᵥ (fun i => τ (z i))) = τ ((fun i => j (y i)) ⬝ᵥ (Q *ᵥ z)) := by
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h, ← map_mulVec']
  simp [dotProduct, map_sum, map_mul]

/- English proof (translation)
Establish `hQ' : ∀ i k, j (Q i k) = - Q k i` using `fun i k => by`. Use `congrFun (congrFun hQ k) i` as an intermediate fact. Simplify using `using this`. Simplify using `only [dotProduct, Matrix.mulVec, map_sum, map_mul, hj, hQ', Finset.mul_sum, ← Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem conj_form (j : F →+* F) (hj : ∀ x, j (j x) = x) (Q : Matrix (Fin n) (Fin n) F) (hQ : (Q.map j)ᵀ = -Q)
    (y z : Fin n → F) :
    j ((fun i => j (y i)) ⬝ᵥ (Q *ᵥ z)) = -((fun i => j (z i)) ⬝ᵥ (Q *ᵥ y)) := by
  have hQ' : ∀ i k, j (Q i k) = - Q k i := fun i k => by
    have := congrFun (congrFun hQ k) i
    simpa using this
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hj, hQ', Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end UpperTheory.Gal.W2.HermitianFrame

open UpperTheory.Gal.W2.HermitianFrame in
/- English proof (translation)
Introduce `hMat hForm hSN hTr hInt hApp p _ D G L hm β hβ`. Take `⟨kp, σ, hkp⟩` from `hMat p D G L hm`. Take `⟨A, hAdet, hAc, hAf, hAsh⟩` from `hForm p D G L kp σ hkp`. Establish `hS : ∀ w : Fin G.m, ∃ S : Matrix (Fin G.n) (Fin G.n) (G.Fw w), S.det ≠ 0 ∧ ∀ c : G.C, G.rho w c * S = S * (σ c).map (G.embW w)`. Introduce `w`.

Take `⟨S, hS0, hS1⟩` from `hSN G.F (G.Fw w) G.n (G.embW w) ((G.rho w).comp σ.symm.toAlgHom.toRingHom) (by`. Introduce `x`. Establish `hx : Matrix.scalar (Fin G.n) x = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) G.F) x`. Use extensionality with `i k`. Simplify using `[Matrix.scalar_apply, Matrix.algebraMap_matrix_apply, Matrix.diagonal_apply]`.

Establish `hσ : σ.symm (algebraMap G.F (Matrix (Fin G.n) (Fin G.n) G.F) x) = algebraMap G.F G.C x` using `σ.symm.commutes x`. Rewrite using `[hx]`. Conclude with `(congrArg (G.rho w) hσ).trans (G.rho_F w x))`. Conclude with `⟨S, hS0, fun c => by simpa using hS1 (σ c)⟩`. Use `choose S hSdet hSrho using hS`.

Establish `hsh : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x`. Introduce `x y`. Simplify using `[sh, map_mul]`. Establish `hβi : sh G ↑β⁻¹ = ↑β⁻¹`. Establish `h1 : sh G ↑β⁻¹ * ↑β = 1`.

Rewrite using `[← hβ, ← hsh, Units.mul_inv, sh_one_eq]`. Combine the equalities or inequalities in the displayed calculation. Establish `hAsh' : ∀ c, Aᵀ * (σ c).map (IsCMField.complexConj G.F) = (σ (sh G c))ᵀ * Aᵀ`. Introduce `c`. Use `congrArg Matrix.transpose (hAsh c)` as an intermediate fact.

Simplify `this.symm` using `[Matrix.transpose_mul]`. Establish `K1 : ∀ w c, (G.rho w c)ᵀ * ((S w)⁻¹)ᵀ = ((S w)⁻¹)ᵀ * ((σ c).map (G.embW w))ᵀ` using `fun w c => transpose_conj (hSdet w) (hSrho w c)`. Establish `hrinv : ∀ w, (G.rho w ↑β)ᵀ * (G.rho w ↑β⁻¹)ᵀ = 1`. Introduce `w`. Rewrite using `[← Matrix.transpose_mul, ← map_mul, Units.inv_mul, map_one, Matrix.transpose_one]`.

Use `set B : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w) := fun w => (G.rho w ↑β⁻¹)ᵀ * ((S w)⁻¹)ᵀ * (A.map (G.embW w))ᵀ with hB`. Establish `K2 : ∀ w c, B w * ((σ c).map (IsCMField.complexConj G.F)).map (G.embW w) = (G.rho w (↑β * sh G c * ↑β⁻¹))ᵀ * B w`. Introduce `w c`. Establish `e1 : (A.map (G.embW w))ᵀ * ((σ c).map (IsCMField.complexConj G.F)).map (G.embW w) = ((σ (sh G c)).map (G.embW w))ᵀ * (A.map (G.embW w))ᵀ`. Rewrite using `[← Matrix.transpose_map, ← Matrix.map_mul, hAsh', Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]`.

Simplify using `only [hB, map_mul, Matrix.transpose_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc _ _ (Matrix.map _ _), e1]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (G.rho w ↑β⁻¹)ᵀ * (G.rho w (sh G c))ᵀ * ((G.rho w ↑β)ᵀ * (G.rho w ↑β⁻¹)ᵀ) * ((S w)⁻¹)ᵀ * (A.map (G.embW w))ᵀ := by`.

Rewrite using `[← K1, hrinv]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`. Establish `hkp' : ∀ c v, kp (L.rep c v) = σ c *ᵥ kp v` using `hkp`. Establish `hcm : ∀ w (M : Matrix (Fin G.n) (Fin G.n) G.F) (v : Fin G.n → G.F), (fun i => G.embW w (IsCMField.complexConj G.F ((M *ᵥ v) i))) = (M.map (IsCMField.complexConj G.F)).map (G.embW w) *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (v i)))`.

Introduce `w M v`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`. Establish `hc1 : ∀ (M : Matrix (Fin G.n) (Fin G.n) G.F) (v : Fin G.n → G.F), (fun i => IsCMField.complexConj G.F ((M *ᵥ v) i)) = M.map (IsCMField.complexConj G.F) *ᵥ (fun i => IsCMField.complexConj G.F (v i))`. Introduce `M v`.

Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`. Establish `hdetS : ∀ w, ((S w)⁻¹).det ≠ 0`. Introduce `w`. Establish `: ((S w)⁻¹).det * (S w).det = 1`.

Rewrite using `[← Matrix.det_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hSdet w)), Matrix.det_one]`. Conclude with `left_ne_zero_of_mul_eq_one this`. Establish `hBdet : ∀ w, (B w).det ≠ 0`. Introduce `w`. Establish `h1 : (G.rho w ↑β⁻¹).det * (G.rho w ↑β).det = 1`.

Rewrite using `[← Matrix.det_mul, ← map_mul, Units.inv_mul, map_one, Matrix.det_one]`. Establish `h3 : (A.map (G.embW w)).det ≠ 0`. Use `(RingHom.map_det (G.embW w) A).symm` as an intermediate fact. Rewrite `this` using `[RingHom.mapMatrix_apply]`. Rewrite using `[this]`.

Conclude with `(_root_.map_ne_zero _).mpr hAdet`. Simplify using `only [hB, Matrix.det_mul, Matrix.det_transpose]`. Conclude with `mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul_eq_one h1) (hdetS w)) h3`. Establish `hBS : ∀ w, (B w)ᵀ * S w = (A * σ ↑β⁻¹).map (G.embW w)`. Introduce `w`.

Simplify using `only [hB, Matrix.transpose_mul, Matrix.transpose_transpose]`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, hSrho, ← Matrix.mul_assoc (S w)⁻¹, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hSdet w)), Matrix.one_mul, Matrix.map_mul]`. Establish `hsw : ∀ v z : Fin G.n → G.F, (fun i => IsCMField.complexConj G.F ((σ ↑β⁻¹ *ᵥ v) i)) ⬝ᵥ (A *ᵥ z) = (fun i => IsCMField.complexConj G.F (v i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ z)`. Introduce `v z`. Rewrite using `[hc1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← hAsh, hβi]`.

Set `j : G.F →+* G.F` to `(IsCMField.complexConj G.F).toRingEquiv.toRingHom`. Establish `hjj : ∀ x, j (j x) = x` using `fun x => by simp [j]`. Establish `hjA : (A.map j)ᵀ = -A` using `hAc`. Set `T : VQ D →+ Loc G` to `AddMonoidHom.mk' (fun x w => S w *ᵥ (fun i => G.embW w (kp x i))) (by`. Introduce `x y`.

Use function extensionality and compare the values at `w`. Rewrite using `[show (fun i => G.embW w (kp (x + y) i)) = (fun i => G.embW w (kp x i)) + (fun i => G.embW w (kp y i)) from by`. Use function extensionality and compare the values at `i`. Use the proof step `simp, Matrix.mulVec_add]`. Use the proof step `rfl)`.

Set `T' : VQ D →+ Loc G` to `AddMonoidHom.mk' (fun x w => B w *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (kp x i)))) (by`. Introduce `x y`. Use function extensionality and compare the values at `w`. Rewrite using `[show (fun i => G.embW w (IsCMField.complexConj G.F (kp (x + y) i))) = (fun i => G.embW w (IsCMField.complexConj G.F (kp x i))) + (fun i => G.embW w (IsCMField.complexConj G.F (kp y i))) from by`. Use function extensionality and compare the values at `i`.

Use the proof step `simp, Matrix.mulVec_add]`. Use the proof step `rfl)`. Establish `hT : ∀ x w, T x w = S w *ᵥ (fun i => G.embW w (kp x i))` using `fun _ _ => rfl`. Establish `hT' : ∀ x w, T' x w = B w *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (kp x i)))` using `fun _ _ => rfl`. Use `⟨⟨T, T', ?_, ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations.

Introduce `c x w`. Rewrite using `[hT, hT, hkp', map_mulVec', Matrix.mulVec_mulVec, ← hSrho, ← Matrix.mulVec_mulVec]`. Introduce `c x w`. Rewrite using `[hT', hT', hkp', hcm, Matrix.mulVec_mulVec, K2, ← Matrix.mulVec_mulVec]`. Introduce `u x`.

Establish `e0 : formB L β u x = Algebra.trace ℚ G.F ((fun i => IsCMField.complexConj G.F (kp x i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ kp u))`. Unfold `formB`. Rewrite using `[hAf, hkp', Matrix.mulVec_mulVec]`. Establish `hpe : ∀ w (y z : Fin G.n → G.F), (B w *ᵥ fun i => G.embW w (IsCMField.complexConj G.F (y i))) ⬝ᵥ (S w *ᵥ fun i => G.embW w (z i)) = G.embW w ((fun i => IsCMField.complexConj G.F (y i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ z))` using `fun w y z => pair_eval (G.embW w) j (S w) (B w) _ (hBS w) y z`. Establish `hneg : IsCMField.complexConj G.F ((fun i => IsCMField.complexConj G.F (kp x i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ kp u)) = -((fun i => IsCMField.complexConj G.F (kp u i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ kp x))`.

Rewrite using `[← Matrix.mulVec_mulVec]`. Establish `h4` using `conj_form j hjj A hjA (kp x) (σ ↑β⁻¹ *ᵥ kp u)`. Establish `h5` using `hsw (kp u) (kp x)`. Conclude with `h4.trans (congrArg Neg.neg h5)`. Rewrite using `[e0, hTr]`.

Unfold `pairL`. Rewrite using `[sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[hT', hT, hpe]`.

Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[hT', hT, hpe, hneg, map_neg, map_neg]`. Introduce `a b k`. Take `⟨y, a', b', ha', hb', h1, h2⟩` from `exists_global_approx_of_local_mod_p_pow_conj hApp p G S B hSdet hBdet a b k`. Use `⟨kp.symm y, a', b', ha', hb', ?_, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `w`. Rewrite using `[hT]`. Simplify using `only [AddEquiv.apply_symm_apply]`. Rewrite using `[h1 w]`. Both sides reduce to the same expression.

Use function extensionality and compare the values at `w`. Rewrite using `[hT']`. Simplify using `only [AddEquiv.apply_symm_apply]`. Rewrite using `[h2 w]`. Both sides reduce to the same expression.

Take `⟨k, hk⟩` from `exists_bounded_denominator_of_local_integrality_conj hInt p G S B hSdet hBdet`. Take `⟨s, hs, hs'⟩` from `exists_finset_span_of_integral_multiples G.F (VQ D) G.n kp`. Use `⟨s, k, hs, fun x h1 h2 => ?_⟩` and prove the remaining obligations. Take `⟨m, c, hm', hc⟩` from `hk (kp x) h1 h2`. Conclude with `⟨m, hm', hs' x (m * p ^ k) c hc⟩`.
-/
theorem UpperTheory.Gal.W2.pFrameEx_of :
    UpperTheory.Gal.W2.FMat → UpperTheory.Gal.W2.FForm → UpperTheory.Gal.W2.SN → UpperTheory.Gal.W2.FTrace → UpperTheory.Gal.W2.FInt → UpperTheory.Gal.W2.FApprox → UpperTheory.Gal.W2.PFrameEx := by
  intro hMat hForm hSN hTr hInt hApp p _ D G L hm β hβ
  obtain ⟨kp, σ, hkp⟩ := hMat p D G L hm
  obtain ⟨A, hAdet, hAc, hAf, hAsh⟩ := hForm p D G L kp σ hkp
  have hS : ∀ w : Fin G.m, ∃ S : Matrix (Fin G.n) (Fin G.n) (G.Fw w), S.det ≠ 0 ∧
      ∀ c : G.C, G.rho w c * S = S * (σ c).map (G.embW w) := by
    intro w
    obtain ⟨S, hS0, hS1⟩ := hSN G.F (G.Fw w) G.n (G.embW w)
      ((G.rho w).comp σ.symm.toAlgHom.toRingHom) (by
        intro x
        have hx : Matrix.scalar (Fin G.n) x = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) G.F) x := by
          ext i k
          simp [Matrix.scalar_apply, Matrix.algebraMap_matrix_apply, Matrix.diagonal_apply]
        have hσ : σ.symm (algebraMap G.F (Matrix (Fin G.n) (Fin G.n) G.F) x) = algebraMap G.F G.C x :=
          σ.symm.commutes x
        rw [hx]
        exact (congrArg (G.rho w) hσ).trans (G.rho_F w x))
    exact ⟨S, hS0, fun c => by simpa using hS1 (σ c)⟩
  choose S hSdet hSrho using hS
  have hsh : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x := by
    intro x y
    simp [sh, map_mul]
  have hβi : sh G ↑β⁻¹ = ↑β⁻¹ := by
    have h1 : sh G ↑β⁻¹ * ↑β = 1 := by
      rw [← hβ, ← hsh, Units.mul_inv, sh_one_eq]
    calc sh G ↑β⁻¹ = sh G ↑β⁻¹ * (↑β * ↑β⁻¹) := by simp
      _ = ↑β⁻¹ := by rw [← _root_.mul_assoc, h1, _root_.one_mul]
  have hAsh' : ∀ c, Aᵀ * (σ c).map (IsCMField.complexConj G.F) = (σ (sh G c))ᵀ * Aᵀ := by
    intro c
    have := congrArg Matrix.transpose (hAsh c)
    simpa [Matrix.transpose_mul] using this.symm
  have K1 : ∀ w c, (G.rho w c)ᵀ * ((S w)⁻¹)ᵀ = ((S w)⁻¹)ᵀ * ((σ c).map (G.embW w))ᵀ :=
    fun w c => transpose_conj (hSdet w) (hSrho w c)
  have hrinv : ∀ w, (G.rho w ↑β)ᵀ * (G.rho w ↑β⁻¹)ᵀ = 1 := by
    intro w
    rw [← Matrix.transpose_mul, ← map_mul, Units.inv_mul, map_one, Matrix.transpose_one]
  set B : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    fun w => (G.rho w ↑β⁻¹)ᵀ * ((S w)⁻¹)ᵀ * (A.map (G.embW w))ᵀ with hB
  have K2 : ∀ w c, B w * ((σ c).map (IsCMField.complexConj G.F)).map (G.embW w)
      = (G.rho w (↑β * sh G c * ↑β⁻¹))ᵀ * B w := by
    intro w c
    have e1 : (A.map (G.embW w))ᵀ * ((σ c).map (IsCMField.complexConj G.F)).map (G.embW w)
        = ((σ (sh G c)).map (G.embW w))ᵀ * (A.map (G.embW w))ᵀ := by
      rw [← Matrix.transpose_map, ← Matrix.map_mul, hAsh', Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]
    simp only [hB, map_mul, Matrix.transpose_mul]
    calc (G.rho w ↑β⁻¹)ᵀ * ((S w)⁻¹)ᵀ * (A.map (G.embW w))ᵀ * ((σ c).map (IsCMField.complexConj G.F)).map (G.embW w)
        = (G.rho w ↑β⁻¹)ᵀ * (((S w)⁻¹)ᵀ * ((σ (sh G c)).map (G.embW w))ᵀ) * (A.map (G.embW w))ᵀ := by
          rw [Matrix.mul_assoc _ _ (Matrix.map _ _), e1]; simp only [Matrix.mul_assoc]
      _ = (G.rho w ↑β⁻¹)ᵀ * (G.rho w (sh G c))ᵀ * ((G.rho w ↑β)ᵀ * (G.rho w ↑β⁻¹)ᵀ) * ((S w)⁻¹)ᵀ * (A.map (G.embW w))ᵀ := by
          rw [← K1, hrinv]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hkp' : ∀ c v, kp (L.rep c v) = σ c *ᵥ kp v := hkp
  have hcm : ∀ w (M : Matrix (Fin G.n) (Fin G.n) G.F) (v : Fin G.n → G.F),
      (fun i => G.embW w (IsCMField.complexConj G.F ((M *ᵥ v) i)))
        = (M.map (IsCMField.complexConj G.F)).map (G.embW w) *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (v i))) := by
    intro w M v
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hc1 : ∀ (M : Matrix (Fin G.n) (Fin G.n) G.F) (v : Fin G.n → G.F),
      (fun i => IsCMField.complexConj G.F ((M *ᵥ v) i))
        = M.map (IsCMField.complexConj G.F) *ᵥ (fun i => IsCMField.complexConj G.F (v i)) := by
    intro M v
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hdetS : ∀ w, ((S w)⁻¹).det ≠ 0 := by
    intro w
    have : ((S w)⁻¹).det * (S w).det = 1 := by
      rw [← Matrix.det_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hSdet w)), Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one this
  have hBdet : ∀ w, (B w).det ≠ 0 := by
    intro w
    have h1 : (G.rho w ↑β⁻¹).det * (G.rho w ↑β).det = 1 := by
      rw [← Matrix.det_mul, ← map_mul, Units.inv_mul, map_one, Matrix.det_one]
    have h3 : (A.map (G.embW w)).det ≠ 0 := by
      have := (RingHom.map_det (G.embW w) A).symm
      rw [RingHom.mapMatrix_apply] at this
      rw [this]
      exact (_root_.map_ne_zero _).mpr hAdet
    simp only [hB, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul_eq_one h1) (hdetS w)) h3
  have hBS : ∀ w, (B w)ᵀ * S w = (A * σ ↑β⁻¹).map (G.embW w) := by
    intro w
    simp only [hB, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hSrho, ← Matrix.mul_assoc (S w)⁻¹,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hSdet w)), Matrix.one_mul, Matrix.map_mul]
  have hsw : ∀ v z : Fin G.n → G.F,
      (fun i => IsCMField.complexConj G.F ((σ ↑β⁻¹ *ᵥ v) i)) ⬝ᵥ (A *ᵥ z)
        = (fun i => IsCMField.complexConj G.F (v i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ z) := by
    intro v z
    rw [hc1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← hAsh, hβi]
  let j : G.F →+* G.F := (IsCMField.complexConj G.F).toRingEquiv.toRingHom
  have hjj : ∀ x, j (j x) = x := fun x => by simp [j]
  have hjA : (A.map j)ᵀ = -A := hAc
  let T : VQ D →+ Loc G := AddMonoidHom.mk' (fun x w => S w *ᵥ (fun i => G.embW w (kp x i))) (by
    intro x y
    funext w
    rw [show (fun i => G.embW w (kp (x + y) i)) = (fun i => G.embW w (kp x i)) + (fun i => G.embW w (kp y i)) from by
      funext i; simp, Matrix.mulVec_add]
    rfl)
  let T' : VQ D →+ Loc G := AddMonoidHom.mk'
    (fun x w => B w *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (kp x i)))) (by
    intro x y
    funext w
    rw [show (fun i => G.embW w (IsCMField.complexConj G.F (kp (x + y) i)))
        = (fun i => G.embW w (IsCMField.complexConj G.F (kp x i)))
          + (fun i => G.embW w (IsCMField.complexConj G.F (kp y i))) from by
      funext i; simp, Matrix.mulVec_add]
    rfl)
  have hT : ∀ x w, T x w = S w *ᵥ (fun i => G.embW w (kp x i)) := fun _ _ => rfl
  have hT' : ∀ x w, T' x w = B w *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (kp x i))) := fun _ _ => rfl
  refine ⟨⟨T, T', ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro c x w
    rw [hT, hT, hkp', map_mulVec', Matrix.mulVec_mulVec, ← hSrho, ← Matrix.mulVec_mulVec]
  · intro c x w
    rw [hT', hT', hkp', hcm, Matrix.mulVec_mulVec, K2, ← Matrix.mulVec_mulVec]
  · intro u x
    have e0 : formB L β u x = Algebra.trace ℚ G.F
        ((fun i => IsCMField.complexConj G.F (kp x i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ kp u)) := by
      unfold formB
      rw [hAf, hkp', Matrix.mulVec_mulVec]
    have hpe : ∀ w (y z : Fin G.n → G.F),
        (B w *ᵥ fun i => G.embW w (IsCMField.complexConj G.F (y i))) ⬝ᵥ (S w *ᵥ fun i => G.embW w (z i))
          = G.embW w ((fun i => IsCMField.complexConj G.F (y i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ z)) :=
      fun w y z => pair_eval (G.embW w) j (S w) (B w) _ (hBS w) y z
    have hneg : IsCMField.complexConj G.F
          ((fun i => IsCMField.complexConj G.F (kp x i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ kp u))
        = -((fun i => IsCMField.complexConj G.F (kp u i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ kp x)) := by
      rw [← Matrix.mulVec_mulVec]
      have h4 := conj_form j hjj A hjA (kp x) (σ ↑β⁻¹ *ᵥ kp u)
      have h5 := hsw (kp u) (kp x)
      exact h4.trans (congrArg Neg.neg h5)
    rw [e0, hTr]
    unfold pairL
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [hT', hT, hpe]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [hT', hT, hpe, hneg, map_neg, map_neg]
  · intro a b k
    obtain ⟨y, a', b', ha', hb', h1, h2⟩ := exists_global_approx_of_local_mod_p_pow_conj hApp p G S B hSdet hBdet a b k
    refine ⟨kp.symm y, a', b', ha', hb', ?_, ?_⟩
    · funext w
      rw [hT]
      simp only [AddEquiv.apply_symm_apply]
      rw [h1 w]
      rfl
    · funext w
      rw [hT']
      simp only [AddEquiv.apply_symm_apply]
      rw [h2 w]
      rfl
  · obtain ⟨k, hk⟩ := exists_bounded_denominator_of_local_integrality_conj hInt p G S B hSdet hBdet
    obtain ⟨s, hs, hs'⟩ := exists_finset_span_of_integral_multiples G.F (VQ D) G.n kp
    refine ⟨s, k, hs, fun x h1 h2 => ?_⟩
    obtain ⟨m, c, hm', hc⟩ := hk (kp x) h1 h2
    exact ⟨m, hm', hs' x (m * p ^ k) c hc⟩
