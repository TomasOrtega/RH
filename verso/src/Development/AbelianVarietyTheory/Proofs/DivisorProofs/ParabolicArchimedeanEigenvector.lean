import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

namespace GlobalTheory.LineGlue

/- English proof (translation)
Establish `hβ : (P * U * X).map φ = β`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← Matrix.map_mul, hPX, Matrix.map_one _ φ.map_zero φ.map_one, Matrix.one_mul]`. Rewrite using `[Matrix.map_mul, h, ← hβ, ← Matrix.map_mul]`.
-/
theorem map_mul_eq_of_local {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (U : Matrix (Fin n) (Fin n) R) (X : Matrix (Fin n) (Fin 1) R) (P : Matrix (Fin 1) (Fin n) R)
    (hPX : P * X = 1) (β : Matrix (Fin 1) (Fin 1) S) (h : U.map φ * X.map φ = X.map φ * β) :
    (U * X).map φ = (X * (P * U * X)).map φ := by
  have hβ : (P * U * X).map φ = β := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← Matrix.map_mul, hPX,
      Matrix.map_one _ φ.map_zero φ.map_one, Matrix.one_mul]
  rw [Matrix.map_mul, h, ← hβ, ← Matrix.map_mul]

end GlobalTheory.LineGlue

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J x pL hpx q hInf hFin`. Use `set U := matHom (AF F) σ J q with hU`. Use `set X := adMat F x with hX`. Use `set P := pL.map (inclR (F := F) (AF F)) with hP`. Establish `hPX : P * X = 1`.

Rewrite using `[hP, hX, adMat, ← Matrix.map_mul, hpx, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hinclFin : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), x.map (inclR (F` using `F) (Fv F v)) = X.map (compFin F E v) := by`. Introduce `v`. Rewrite using `[hX, adMat, Matrix.map_map]`. Use `congr 1`.

Apply the tactic sequence `try funext e`. Simplify using `[compFin, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]`. Establish `hinclInf : ∀ w : InfinitePlace F, x.map (inclR (F` using `F) w.Completion) = X.map (compInf F E w) := by`. Introduce `w`. Rewrite using `[hX, adMat, Matrix.map_map]`.

Use `congr 1`. Apply the tactic sequence `try funext e`. Simplify using `[compInf, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]`. Establish `hMX : U.1 * X = X * (P * U.1 * X)`. Use extensionality with `i j`.

Use `GlobalTheory.Doubling.adele_ext (fun w => ?_) (fun v => ?_)` and prove the remaining obligations. Take `⟨β, hβ⟩` from `hInf w`. Rewrite `hβ` using `[matHom_projArch, hinclInf]`. Use `GlobalTheory.LineGlue.map_mul_eq_of_local (compInf F E w) U.1 X P hPX β.1 hβ` as an intermediate fact. Conclude with `congrFun (congrFun this i) j`.

Take `⟨β, hβ⟩` from `hFin v`. Rewrite `hβ` using `[matHom_proj, hinclFin]`. Use `GlobalTheory.LineGlue.map_mul_eq_of_local (compFin F E v) U.1 X P hPX β.1 hβ` as an intermediate fact. Conclude with `congrFun (congrFun this i) j`. Choose the witnesses or unpack the hypotheses as in `⟨c', hc'⟩ : ∃ c' : AF F ⊗[F] E, c' * (P * U.1 * X) 0 0 = 1 := by`.

Use `⟨(P * (U⁻¹).1 * X) 0 0, ?_⟩` and prove the remaining obligations. Establish `h1 : X = (U⁻¹).1 * X * (P * U.1 * X)`. Rewrite using `[Matrix.mul_assoc, ← hMX, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Establish `h2 : P * (U⁻¹).1 * X * (P * U.1 * X) = 1`. Rewrite using `[show P * (U⁻¹).1 * X * (P * U.1 * X) = P * ((U⁻¹).1 * X * (P * U.1 * X)) by`.

Simplify using `only [Matrix.mul_assoc], ← h1, hPX]`. Use `congrFun (congrFun h2 0) 0` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Fin.sum_univ_one]`. Use `⟨Units.mkOfMulEqOne _ _ (by rw [mul_comm]; exact hc'), ?_⟩` and prove the remaining obligations. Rewrite using `[hMX]`.

Use extensionality with `i j`. Use `fin_cases j`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_one, mul_comm]`.
-/
theorem GlobalTheory.LineGlue.exists_idele_smul_of_local_lines : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (pL : Matrix (Fin 1) (Fin n) E), pL * x = 1 → ∀ q : GAd σ J, (∀ w : InfinitePlace F, ∃ β : GL (Fin 1) (w.Completion ⊗[F] E), (matHom _ σ J (projArch σ J w q)).1 * x.map (inclR (F := F) w.Completion) = x.map (inclR (F := F) w.Completion) * β.1) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J (proj σ J v q)).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J q).1 * adMat F x = l.1 • adMat F x := by
  intro F E _ _ _ _ _ σ n J x pL hpx q hInf hFin
  set U := matHom (AF F) σ J q with hU
  set X := adMat F x with hX
  set P := pL.map (inclR (F := F) (AF F)) with hP
  have hPX : P * X = 1 := by
    rw [hP, hX, adMat, ← Matrix.map_mul, hpx, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinclFin : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      x.map (inclR (F := F) (Fv F v)) = X.map (compFin F E v) := by
    intro v
    rw [hX, adMat, Matrix.map_map]
    congr 1
    try funext e; simp [compFin, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hinclInf : ∀ w : InfinitePlace F,
      x.map (inclR (F := F) w.Completion) = X.map (compInf F E w) := by
    intro w
    rw [hX, adMat, Matrix.map_map]
    congr 1
    try funext e; simp [compInf, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hMX : U.1 * X = X * (P * U.1 * X) := by
    ext i j
    refine GlobalTheory.Doubling.adele_ext (fun w => ?_) (fun v => ?_)
    · obtain ⟨β, hβ⟩ := hInf w
      rw [matHom_projArch, hinclInf] at hβ
      have := GlobalTheory.LineGlue.map_mul_eq_of_local (compInf F E w) U.1 X P hPX β.1 hβ
      exact congrFun (congrFun this i) j
    · obtain ⟨β, hβ⟩ := hFin v
      rw [matHom_proj, hinclFin] at hβ
      have := GlobalTheory.LineGlue.map_mul_eq_of_local (compFin F E v) U.1 X P hPX β.1 hβ
      exact congrFun (congrFun this i) j
  obtain ⟨c', hc'⟩ : ∃ c' : AF F ⊗[F] E, c' * (P * U.1 * X) 0 0 = 1 := by
    refine ⟨(P * (U⁻¹).1 * X) 0 0, ?_⟩
    have h1 : X = (U⁻¹).1 * X * (P * U.1 * X) := by
      rw [Matrix.mul_assoc, ← hMX, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have h2 : P * (U⁻¹).1 * X * (P * U.1 * X) = 1 := by
      rw [show P * (U⁻¹).1 * X * (P * U.1 * X) = P * ((U⁻¹).1 * X * (P * U.1 * X)) by
        simp only [Matrix.mul_assoc], ← h1, hPX]
    have := congrFun (congrFun h2 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_one] using this
  refine ⟨Units.mkOfMulEqOne _ _ (by rw [mul_comm]; exact hc'), ?_⟩
  rw [hMX]
  ext i j
  fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_one, mul_comm]
