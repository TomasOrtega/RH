import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtensionStatement

open NumberField Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Set `σ : F →+* ℝ` to `InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)`. Establish `hx0 : x ≠ 0` using `fun h => by simpa [h] using hx σ`. Establish `hΔ0 : Δ ≠ 0` using `fun h => by simpa [h] using hΔ σ`. Use `⟨hx0, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `obtain ⟨y, hy0, hy⟩ := GlobalTheory.LocalQuad.isotropic_of_indefinite GlobalTheory.T.hasse_norm_theorem_quadratic_extension F (ι := Fin 5) ![1, -Δ, 1, -Δ, -x] (by simp) (fun i => by fin_cases i <;> simp [hx0, hΔ0]) (fun s => ⟨4, 0, by simpa using hx s, by simp⟩)`. Simplify using `[Fin.sum_univ_succ] at hy`. Establish `hy' : y 0 ^ 2 - Δ * y 1 ^ 2 + (y 2 ^ 2 - Δ * y 3 ^ 2) = x * y 4 ^ 2`. Take the linear combination `hy`. Establish `he : y 4 ≠ 0`.

Introduce `h`. Apply `hy0` to reduce the goal to its premises. Establish `h1` using `congrArg σ hy'`. Simplify using `only [h, map_add, map_sub, map_mul, map_pow, map_zero] at h1`. Establish `hn` using `hΔ σ`.

Establish `p1 : 0 ≤ -σ Δ * σ (y 1) ^ 2` using `mul_nonneg (by linarith) (sq_nonneg _)`. Establish `p3 : 0 ≤ -σ Δ * σ (y 3) ^ 2` using `mul_nonneg (by linarith) (sq_nonneg _)`. Establish `p0` using `sq_nonneg (σ (y 0))`. Establish `p2` using `sq_nonneg (σ (y 2))`. Establish `e0 : σ (y 0) ^ 2 = 0` using `by nlinarith`.

Establish `e2 : σ (y 2) ^ 2 = 0` using `by nlinarith`. Establish `e1 : -σ Δ * σ (y 1) ^ 2 = 0` using `by nlinarith`. Establish `e3 : -σ Δ * σ (y 3) ^ 2 = 0` using `by nlinarith`. Establish `z0 : y 0 = 0` using `by simpa using e0`. Establish `z2 : y 2 = 0` using `by simpa using e2`.

Establish `z1 : y 1 = 0` using `by simpa [hΔ0] using e1`. Establish `z3 : y 3 = 0` using `by simpa [hΔ0] using e3`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Use `exacts [z0, z1, z2, z3, h]`.

Use `⟨y 0 / y 4, y 1 / y 4, y 2 / y 4, y 3 / y 4, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Take the linear combination `-hy'`.
-/
private theorem four_values (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Δ x : F)
    (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (hx : ∀ σ : F →+* ℝ, 0 < σ x) :
    x ≠ 0 ∧ ∃ a b c d : F, x = a ^ 2 - Δ * b ^ 2 + (c ^ 2 - Δ * d ^ 2) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  let σ : F →+* ℝ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
  have hx0 : x ≠ 0 := fun h => by simpa [h] using hx σ
  have hΔ0 : Δ ≠ 0 := fun h => by simpa [h] using hΔ σ
  refine ⟨hx0, ?_⟩
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.LocalQuad.isotropic_of_indefinite GlobalTheory.T.hasse_norm_theorem_quadratic_extension F (ι := Fin 5) ![1, -Δ, 1, -Δ, -x]
    (by simp) (fun i => by fin_cases i <;> simp [hx0, hΔ0])
    (fun s => ⟨4, 0, by simpa using hx s, by simp⟩)
  simp [Fin.sum_univ_succ] at hy
  have hy' : y 0 ^ 2 - Δ * y 1 ^ 2 + (y 2 ^ 2 - Δ * y 3 ^ 2) = x * y 4 ^ 2 := by
    linear_combination hy
  have he : y 4 ≠ 0 := by
    intro h
    apply hy0
    have h1 := congrArg σ hy'
    simp only [h, map_add, map_sub, map_mul, map_pow, map_zero] at h1
    have hn := hΔ σ
    have p1 : 0 ≤ -σ Δ * σ (y 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have p3 : 0 ≤ -σ Δ * σ (y 3) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have p0 := sq_nonneg (σ (y 0))
    have p2 := sq_nonneg (σ (y 2))
    have e0 : σ (y 0) ^ 2 = 0 := by nlinarith
    have e2 : σ (y 2) ^ 2 = 0 := by nlinarith
    have e1 : -σ Δ * σ (y 1) ^ 2 = 0 := by nlinarith
    have e3 : -σ Δ * σ (y 3) ^ 2 = 0 := by nlinarith
    have z0 : y 0 = 0 := by simpa using e0
    have z2 : y 2 = 0 := by simpa using e2
    have z1 : y 1 = 0 := by simpa [hΔ0] using e1
    have z3 : y 3 = 0 := by simpa [hΔ0] using e3
    funext i
    fin_cases i
    exacts [z0, z1, z2, z3, h]
  refine ⟨y 0 / y 4, y 1 / y 4, y 2 / y 4, y 3 / y 4, ?_⟩
  field_simp
  linear_combination -hy'

/- English proof (translation)
Establish `hd : (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).det = algebraMap K _ x`. Rewrite using `[det_fin_two_of, ← h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hu : IsUnit (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ))`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, hd]`.

Conclude with `(IsUnit.mk0 x hx).map _`. Use `⟨⟨hu.unit, ?_⟩, hd⟩` and prove the remaining obligations. Use `show GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) hu.unit = (wJ Δ)⁻¹ * hu.unit * (wJ Δ)⁻¹⁻¹`. Rewrite using `[inv_inv]`. Apply `Units.ext` to reduce the goal to its premises.

Use `show (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd (Lsq K Δ)) = !![0, -1; 1, 0] * !![a, b; -star b, star a] * !![0, 1; -1, 0]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply]`.
-/
private theorem ex_DX {K : Type} [Field K] (Δ x : K) (hx : x ≠ 0) (a b : Lsq K Δ)
    (h : a * star a + b * star b = algebraMap K _ x) : ∃ g : DX Δ, (mt g).det = algebraMap K _ x := by
  have hd : (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).det = algebraMap K _ x := by
    rw [det_fin_two_of, ← h]; ring
  have hu : IsUnit (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, hd]
    exact (IsUnit.mk0 x hx).map _
  refine ⟨⟨hu.unit, ?_⟩, hd⟩
  show GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) hu.unit = (wJ Δ)⁻¹ * hu.unit * (wJ Δ)⁻¹⁻¹
  rw [inv_inv]
  apply Units.ext
  show (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd (Lsq K Δ)) =
    !![0, -1; 1, 0] * !![a, b; -star b, star a] * !![0, 1; -1, 0]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply]

/- English proof (translation)
Introduce `F _ _ Δ D hD x hx`. Use `haveI := hD.real`. Take `⟨hx0, a, b, c, d, h⟩` from `four_values F Δ x hD.neg hx`. Use `ex_DX Δ x hx0 ⟨a, b⟩ ⟨c, d⟩ ?_` and prove the remaining obligations. Use `ext`.

Simplify using the standard rewrite rules. Take the linear combination `-h`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.Sym.Glob.normD :
    UpperTheory.V.Z.Sym.Glob.NormD := by
  intro F _ _ Δ D hD x hx
  haveI := hD.real
  obtain ⟨hx0, a, b, c, d, h⟩ := four_values F Δ x hD.neg hx
  refine ex_DX Δ x hx0 ⟨a, b⟩ ⟨c, d⟩ ?_
  ext
  · simp; linear_combination -h
  · simp; ring
