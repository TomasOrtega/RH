import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Descent

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Establish `hm : ∀ A B : Matrix (Fin 2) (Fin 2) L, (A * B).map star = A.map star * B.map star`. Introduce `A B`. Conclude with `(Matrix.map_mul : (A * B).map (starRingEnd L) = A.map (starRingEnd L) * B.map (starRingEnd L))`. Establish `h1s : P.map star * Q.map star = 1`. Rewrite using `[← hm, h1]`.

Simplify using the standard rewrite rules. Establish `h2s : Q.map star * P.map star = 1`. Rewrite using `[← hm, h2]`. Simplify using the standard rewrite rules. Establish `hJQ : ν • (J * Q.map star) = Q`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h3]`. Simplify using `only [Matrix.mul_assoc, smul_mul_assoc, Matrix.mul_smul]`. Rewrite using `[← Matrix.mul_assoc Q P, h2, Matrix.one_mul]`. Use `_ = Q := by rw [h1s, Matrix.mul_one]`.

Establish `hQP : Q * P.map star = ν • J`. Rewrite using `[h3, Matrix.mul_smul, ← Matrix.mul_assoc, h2, Matrix.one_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[hm, hm, h3]`.

Use `conv_rhs => rw [← hJQ]`. Simplify using `only [Matrix.mul_assoc, smul_mul_assoc, Matrix.mul_smul]`. Rewrite using `[← Matrix.mul_assoc J, h, Matrix.mul_assoc]`. Introduce `h`. Establish `e` using `congrArg (fun M => Q * M * P.map star) h`.

Rewrite `e` using `[hm, hm]`. Establish `hL : Q * (P.map star * X.map star * Q.map star) * P.map star = ν • (J * X.map star)`. Rewrite using `[show Q * (P.map star * X.map star * Q.map star) * P.map star = (Q * P.map star) * X.map star * (Q.map star * P.map star) by simp only [Matrix.mul_assoc], hQP, h2s, Matrix.mul_one, smul_mul_assoc]`. Establish `hR : Q * (P * X * Q) * P.map star = ν • (X * J)`. Rewrite using `[show Q * (P * X * Q) * P.map star = (Q * P) * X * (Q * P.map star) by simp only [Matrix.mul_assoc], h2, hQP, Matrix.one_mul, Matrix.mul_smul]`.

Rewrite `e` using `[hL, hR]`. Conclude with `hν.smul_left_cancel.1 e`.
-/
private theorem core {L : Type} [CommRing L] [StarRing L] (ν : L) (P Q : Matrix (Fin 2) (Fin 2) L) (J : Matrix (Fin 2) (Fin 2) L)
    (h1 : P * Q = 1) (h2 : Q * P = 1) (hν : IsUnit ν) (h3 : P.map star = ν • (P * J)) (X : Matrix (Fin 2) (Fin 2) L) :
    J * X.map star = X * J ↔ (P * X * Q).map star = P * X * Q := by
  have hm : ∀ A B : Matrix (Fin 2) (Fin 2) L, (A * B).map star = A.map star * B.map star := by
    intro A B
    exact (Matrix.map_mul : (A * B).map (starRingEnd L) = A.map (starRingEnd L) * B.map (starRingEnd L))
  have h1s : P.map star * Q.map star = 1 := by
    rw [← hm, h1]
    simp
  have h2s : Q.map star * P.map star = 1 := by
    rw [← hm, h2]
    simp
  have hJQ : ν • (J * Q.map star) = Q := by
    calc ν • (J * Q.map star) = Q * (P.map star * Q.map star) := by
          rw [h3]
          simp only [Matrix.mul_assoc, smul_mul_assoc, Matrix.mul_smul]
          rw [← Matrix.mul_assoc Q P, h2, Matrix.one_mul]
      _ = Q := by rw [h1s, Matrix.mul_one]
  have hQP : Q * P.map star = ν • J := by
    rw [h3, Matrix.mul_smul, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  constructor
  · intro h
    rw [hm, hm, h3]
    conv_rhs => rw [← hJQ]
    simp only [Matrix.mul_assoc, smul_mul_assoc, Matrix.mul_smul]
    rw [← Matrix.mul_assoc J, h, Matrix.mul_assoc]
  · intro h
    have e := congrArg (fun M => Q * M * P.map star) h
    rw [hm, hm] at e
    have hL : Q * (P.map star * X.map star * Q.map star) * P.map star = ν • (J * X.map star) := by
      rw [show Q * (P.map star * X.map star * Q.map star) * P.map star
          = (Q * P.map star) * X.map star * (Q.map star * P.map star) by simp only [Matrix.mul_assoc],
        hQP, h2s, Matrix.mul_one, smul_mul_assoc]
    have hR : Q * (P * X * Q) * P.map star = ν • (X * J) := by
      rw [show Q * (P * X * Q) * P.map star = (Q * P) * X * (Q * P.map star) by simp only [Matrix.mul_assoc],
        h2, hQP, Matrix.one_mul, Matrix.mul_smul]
    rw [hL, hR] at e
    exact hν.smul_left_cancel.1 e

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ hl`. Take `⟨u, t, ht0, hΔ⟩` from `hl.even`. Establish `hs2 : Δ * t⁻¹ ^ 2 = algebraMap O K ↑u`. Rewrite using `[hΔ]`. Clear the denominators using the available nonvanishing facts.

Establish `hdes` using `descent O K Δ hl t⁻¹ u hs2`. Take `⟨ν, hνi, hνn⟩` from `normEx O K Δ hl (-1)`. Take `⟨v, hv⟩` from `hl.two`. Take `⟨w, hwdef⟩ : ∃ w : Lsq K Δ, w = ⟨0, t⁻¹⟩` from `⟨_, rfl⟩`. Take `⟨U, hUdef⟩ : ∃ U : Lsq K Δ, U = algebraMap O (Lsq K Δ) ↑u` from `⟨_, rfl⟩`.

Take `⟨hh, hhdef⟩ : ∃ hh : Lsq K Δ, hh = algebraMap O (Lsq K Δ) ↑v⁻¹` from `⟨_, rfl⟩`. Take `⟨e, edef⟩ : ∃ e : Lsq K Δ, e = algebraMap O (Lsq K Δ) ↑u⁻¹` from `⟨_, rfl⟩`. Establish `hww : w * w = U`. Rewrite using `[hUdef, IsScalarTower.algebraMap_apply O K (Lsq K Δ), ← hs2]`. Establish `: algebraMap K (Lsq K Δ) (Δ * t⁻¹ ^ 2) = ⟨Δ * t⁻¹ ^ 2, 0⟩`.

Use `ext`. Conclude with `QuadraticAlgebra.algebraMap_re _`. Conclude with `QuadraticAlgebra.algebraMap_im _`. Rewrite using `[this, hwdef]`. Apply the tactic sequence `ext <;> simp <;> ring`.

Establish `hsw : star w = -w`. Rewrite using `[hwdef]`. Apply the tactic sequence `ext <;> simp`. Establish `hνν : ν * star ν = -1`. Establish `: ν * star ν = algebraMap K (Lsq K Δ) (QuadraticAlgebra.norm ν)`.

Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.norm] <;> ring`. Rewrite using `[this, hνn]`. Simplify using the standard rewrite rules. Establish `hh2 : hh * 2 = 1`. Rewrite using `[hhdef, ← map_ofNat (algebraMap O (Lsq K Δ)) 2, ← hv, ← map_mul, Units.inv_mul, map_one]`.

Establish `heu : e * U = 1`. Rewrite using `[edef, hUdef, ← map_mul, Units.inv_mul, map_one]`. Establish `iw : IsIntegral O w`. Use `(hdes w).1.2 ⟨?_, 1, ?_⟩` and prove the remaining obligations. Rewrite using `[hwdef]`.

Conclude with `⟨0, map_zero _⟩`. Rewrite using `[hwdef]`. Simplify using the standard rewrite rules. Establish `iν' : IsIntegral O (star ν)` using `(hdes ν).2 hνi`. Establish `ih : IsIntegral O hh`.

Rewrite using `[hhdef]`. Conclude with `isIntegral_algebraMap`. Establish `ie : IsIntegral O e`. Rewrite using `[edef]`. Conclude with `isIntegral_algebraMap`.

Establish `hνu : IsUnit ν` using `⟨⟨ν, -star ν, by rw [mul_neg, hνν, neg_neg], by rw [neg_mul, mul_comm, hνν, neg_neg]⟩, rfl⟩`. Set `Pm : Matrix (Fin 2) (Fin 2) (Lsq K Δ)` to `!![1, star ν; w, -(star ν * w)]`. Set `Qm : Matrix (Fin 2) (Fin 2) (Lsq K Δ)` to `!![hh, hh * e * w; -(hh * ν), hh * e * ν * w]`. Establish `hPQ : Pm * Qm = 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Pm, Qm, Matrix.mul_apply, Fin.sum_univ_two]`. Take the linear combination `hh2 - hh * hνν`. Take the linear combination `hh * e * w * hνν`. Take the linear combination `hh * w * hνν`. Take the linear combination `hh * e * (1 - ν * star ν) * hww - hh * e * U * hνν + 2 * hh * heu + hh2`.

Establish `hQP : Qm * Pm = 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Pm, Qm, Matrix.mul_apply, Fin.sum_univ_two]`. Take the linear combination `hh * e * hww + hh * heu + hh2`. Take the linear combination `-hh * star ν * heu - hh * e * star ν * hww`.

Take the linear combination `hh * ν * heu + hh * e * ν * hww`. Take the linear combination `-hh * hνν - hh * e * w * w * hνν + hh * e * hww + hh * heu + hh2`. Establish `h3 : Pm.map star = ν • (Pm * !![0, 1; -1, 0])`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Pm, Matrix.mul_apply, Fin.sum_univ_two, hsw]`.

Take the linear combination `hνν`. Take the linear combination `-w * hνν`. Use `⟨⟨Pm, Qm, hPQ, hQP⟩, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `intro i j fin_cases i <;> fin_cases j <;> refine ⟨?_, ?_⟩ <;> simp [Pm, Qm] <;>`. Repeatedly apply the rules in `[IsIntegral.mul, IsIntegral.neg, isIntegral_one]`.

Introduce `X`. Conclude with `core ν Pm Qm !![0, 1; -1, 0] hPQ hQP hνu h3 X`.
-/
theorem UpperTheory.V.Z.Sym.Loc.splitJ : UpperTheory.V.Z.Sym.Loc.SplitJ := by
  intro O K _ _ _ _ _ Δ hl
  obtain ⟨u, t, ht0, hΔ⟩ := hl.even
  have hs2 : Δ * t⁻¹ ^ 2 = algebraMap O K ↑u := by
    rw [hΔ]
    field_simp
  have hdes := descent O K Δ hl t⁻¹ u hs2
  obtain ⟨ν, hνi, hνn⟩ := normEx O K Δ hl (-1)
  obtain ⟨v, hv⟩ := hl.two
  obtain ⟨w, hwdef⟩ : ∃ w : Lsq K Δ, w = ⟨0, t⁻¹⟩ := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : Lsq K Δ, U = algebraMap O (Lsq K Δ) ↑u := ⟨_, rfl⟩
  obtain ⟨hh, hhdef⟩ : ∃ hh : Lsq K Δ, hh = algebraMap O (Lsq K Δ) ↑v⁻¹ := ⟨_, rfl⟩
  obtain ⟨e, edef⟩ : ∃ e : Lsq K Δ, e = algebraMap O (Lsq K Δ) ↑u⁻¹ := ⟨_, rfl⟩
  have hww : w * w = U := by
    rw [hUdef, IsScalarTower.algebraMap_apply O K (Lsq K Δ), ← hs2]
    have : algebraMap K (Lsq K Δ) (Δ * t⁻¹ ^ 2) = ⟨Δ * t⁻¹ ^ 2, 0⟩ := by
      ext
      · exact QuadraticAlgebra.algebraMap_re _
      · exact QuadraticAlgebra.algebraMap_im _
    rw [this, hwdef]
    ext <;> simp <;> ring
  have hsw : star w = -w := by
    rw [hwdef]
    ext <;> simp
  have hνν : ν * star ν = -1 := by
    have : ν * star ν = algebraMap K (Lsq K Δ) (QuadraticAlgebra.norm ν) := by
      ext <;> simp [QuadraticAlgebra.norm] <;> ring
    rw [this, hνn]
    simp
  have hh2 : hh * 2 = 1 := by
    rw [hhdef, ← map_ofNat (algebraMap O (Lsq K Δ)) 2, ← hv, ← map_mul, Units.inv_mul, map_one]
  have heu : e * U = 1 := by
    rw [edef, hUdef, ← map_mul, Units.inv_mul, map_one]
  have iw : IsIntegral O w := by
    refine (hdes w).1.2 ⟨?_, 1, ?_⟩
    · rw [hwdef]
      exact ⟨0, map_zero _⟩
    · rw [hwdef]
      simp
  have iν' : IsIntegral O (star ν) := (hdes ν).2 hνi
  have ih : IsIntegral O hh := by
    rw [hhdef]
    exact isIntegral_algebraMap
  have ie : IsIntegral O e := by
    rw [edef]
    exact isIntegral_algebraMap
  have hνu : IsUnit ν :=
    ⟨⟨ν, -star ν, by rw [mul_neg, hνν, neg_neg], by rw [neg_mul, mul_comm, hνν, neg_neg]⟩, rfl⟩
  let Pm : Matrix (Fin 2) (Fin 2) (Lsq K Δ) := !![1, star ν; w, -(star ν * w)]
  let Qm : Matrix (Fin 2) (Fin 2) (Lsq K Δ) := !![hh, hh * e * w; -(hh * ν), hh * e * ν * w]
  have hPQ : Pm * Qm = 1 := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Pm, Qm, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hh2 - hh * hνν
    · linear_combination hh * e * w * hνν
    · linear_combination hh * w * hνν
    · linear_combination hh * e * (1 - ν * star ν) * hww - hh * e * U * hνν + 2 * hh * heu + hh2
  have hQP : Qm * Pm = 1 := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Pm, Qm, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hh * e * hww + hh * heu + hh2
    · linear_combination -hh * star ν * heu - hh * e * star ν * hww
    · linear_combination hh * ν * heu + hh * e * ν * hww
    · linear_combination -hh * hνν - hh * e * w * w * hνν + hh * e * hww + hh * heu + hh2
  have h3 : Pm.map star = ν • (Pm * !![0, 1; -1, 0]) := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Pm, Matrix.mul_apply, Fin.sum_univ_two, hsw]
    · linear_combination hνν
    · linear_combination -w * hνν
  refine ⟨⟨Pm, Qm, hPQ, hQP⟩, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> refine ⟨?_, ?_⟩ <;> simp [Pm, Qm] <;>
      apply_rules [IsIntegral.mul, IsIntegral.neg, isIntegral_one]
  · intro X
    exact core ν Pm Qm !![0, 1; -1, 0] hPQ hQP hνu h3 X
