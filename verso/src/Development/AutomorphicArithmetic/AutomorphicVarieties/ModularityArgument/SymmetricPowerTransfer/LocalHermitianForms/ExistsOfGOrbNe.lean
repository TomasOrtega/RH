import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FzkLaw

namespace UpperTheory.V.Z.Sym.Loc

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}

/- English proof (translation)
Apply the tactic sequence `conv_lhs => rw [show x = algebraMap K (Etau K τ) x.re + x.im • ω by ext <;> simp]`. Rewrite using `[map_add, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]`.
-/
theorem j_apply (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : Etau K τ) : j x = x.re • (1 : Matrix (Fin 2) (Fin 2) K) + x.im • j ω := by
  conv_lhs => rw [show x = algebraMap K (Etau K τ) x.re + x.im • ω by ext <;> simp]
  rw [map_add, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Rewrite using `[← map_mul, QuadraticAlgebra.omega_mul_omega_eq_add, map_add, map_smul, map_smul, map_one, neg_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem j_sq (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) : j ω * j ω = τ • j ω - 1 := by
  rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_add, map_add, map_smul, map_smul, map_one,
    neg_smul, one_smul]
  abel

/- English proof (translation)
Establish `h` using `congrFun (congrFun (j_sq j) 0) 0`. Rewrite `hj` using `[Matrix.trace_fin_two]`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two] at h`. Rewrite using `[Matrix.det_fin_two]`. Take the linear combination `(j ω 0 0) * hj - h`.
-/
theorem j_det_omega (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (hj : (j ω).trace = τ) : (j ω).det = 1 := by
  have h := congrFun (congrFun (j_sq j) 0) 0
  rw [Matrix.trace_fin_two] at hj
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h
  rw [Matrix.det_fin_two]
  linear_combination (j ω 0 0) * hj - h

/- English proof (translation)
Rewrite using `[j_apply, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hj, QuadraticAlgebra.trace_def]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem j_trace (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (hj : (j ω).trace = τ) (x : Etau K τ) : (j x).trace = QuadraticAlgebra.trace x := by
  rw [j_apply, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hj, QuadraticAlgebra.trace_def]
  simp; ring

/- English proof (translation)
Establish `h` using `j_det_omega j hj`. Rewrite `h` using `[Matrix.det_fin_two]`. Rewrite `hj` using `[Matrix.trace_fin_two]`. Rewrite using `[j_apply, Matrix.det_fin_two, QuadraticAlgebra.norm_def]`. Simplify using the standard rewrite rules.

Take the linear combination `(x.re * x.im) * hj + x.im ^ 2 * h`.
-/
theorem j_det (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (hj : (j ω).trace = τ) (x : Etau K τ) : (j x).det = QuadraticAlgebra.norm x := by
  have h := j_det_omega j hj
  rw [Matrix.det_fin_two] at h
  rw [Matrix.trace_fin_two] at hj
  rw [j_apply, Matrix.det_fin_two, QuadraticAlgebra.norm_def]
  simp
  linear_combination (x.re * x.im) * hj + x.im ^ 2 * h

/- English proof (translation)
Use `haveI hN : ((Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range).Normal := by`. Rewrite using `[← Matrix.GeneralLinearGroup.center_eq_range_scalar]`. Use `infer_instance`. Rewrite using `[ZK, ← SetLike.mem_coe, Subgroup.normal_mul, KG]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨z, rfl⟩, _, ⟨k, rfl⟩, rfl⟩`. Conclude with `⟨z, k, rfl⟩`. Introduce and unpack `⟨z, k, rfl⟩`. Conclude with `⟨_, ⟨z, rfl⟩, _, ⟨k, rfl⟩, rfl⟩`.
-/
theorem mem_ZK {g : GL (Fin 2) K} : g ∈ ZK O K ↔ ∃ (z : Kˣ) (k : GL (Fin 2) O),
    g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * Matrix.GeneralLinearGroup.map (algebraMap O K) k := by
  haveI hN : ((Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range).Normal := by
    rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar]
    infer_instance
  rw [ZK, ← SetLike.mem_coe, Subgroup.normal_mul, KG]
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, _, ⟨k, rfl⟩, rfl⟩
    exact ⟨z, k, rfl⟩
  · rintro ⟨z, k, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, _, ⟨k, rfl⟩, rfl⟩

/- English proof (translation)
Establish `core : ∀ (g : GL (Fin 2) K) (w : Kˣ), (Matrix.GeneralLinearGroup.scalar (Fin 2) w)⁻¹ * (g⁻¹ * jU j z * g) ∈ KG O K → ∃ (s : Kˣ) (u : Oˣ) (t : O), QuadraticAlgebra.norm (z : Etau K τ) = algebraMap O K u * (s : K) ^ 2 ∧ QuadraticAlgebra.trace (z : Etau K τ) = s * algebraMap O K t`. Introduce `g w hw`. Take `⟨k, hk⟩` from `hw`. Establish `hM : g⁻¹ * jU j z * g = Matrix.GeneralLinearGroup.scalar (Fin 2) w * Matrix.GeneralLinearGroup.map (algebraMap O K) k`. Rewrite using `[hk, mul_inv_cancel_left]`.

Establish `hMat` using `congrArg Units.val hM`. Simplify using `only [jU, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, AlgHom.coe_toRingHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.GeneralLinearGroup.val_map_apply] at hMat`. Establish `htr : (j z).trace = (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j z * (g : Matrix (Fin 2) (Fin 2) K)).trace`. Rewrite using `[Matrix.trace_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]`. Establish `hdt : (j z).det = (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j z * (g : Matrix (Fin 2) (Fin 2) K)).det`.

Rewrite using `[Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)), mul_assoc, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, mul_one]`. Use `⟨w, Matrix.GeneralLinearGroup.det k, (k : Matrix (Fin 2) (Fin 2) O).trace, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← j_det j hj, hdt, hMat]`. Apply the tactic sequence `simp [Matrix.det_fin_two, Matrix.diagonal_mul, Matrix.GeneralLinearGroup.val_det_apply] <;> ring`. Rewrite using `[← j_trace j hj, htr, hMat]`.

Apply the tactic sequence `simp [Matrix.trace_fin_two, Matrix.diagonal_mul] <;> ring`. Assume the negation of the conclusion as `hcon`. Apply `h` to reduce the goal to its premises. Unfold `gOrb orb wcount`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises.

Introduce `o`. Apply `mul_eq_zero_of_right` to reduce the goal to its premises. Unfold `fZK`. Simplify using `only`. Rewrite using `[dif_neg]`.

Introduce and unpack `⟨w, hw⟩`. Conclude with `hcon (core _ w hw)`.
-/
theorem exists_of_gOrb_ne {j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K} (hj : (j ω).trace = τ) {χ : Kˣ →* ℂˣ} {z : (Etau K τ)ˣ} (h : gOrb O j χ z ≠ 0) :
    ∃ (s : Kˣ) (u : Oˣ) (t : O), QuadraticAlgebra.norm (z : Etau K τ) = algebraMap O K u * (s : K) ^ 2 ∧
      QuadraticAlgebra.trace (z : Etau K τ) = s * algebraMap O K t := by
  have core : ∀ (g : GL (Fin 2) K) (w : Kˣ),
      (Matrix.GeneralLinearGroup.scalar (Fin 2) w)⁻¹ * (g⁻¹ * jU j z * g) ∈ KG O K →
      ∃ (s : Kˣ) (u : Oˣ) (t : O), QuadraticAlgebra.norm (z : Etau K τ) = algebraMap O K u * (s : K) ^ 2 ∧
        QuadraticAlgebra.trace (z : Etau K τ) = s * algebraMap O K t := by
    intro g w hw
    obtain ⟨k, hk⟩ := hw
    have hM : g⁻¹ * jU j z * g
        = Matrix.GeneralLinearGroup.scalar (Fin 2) w * Matrix.GeneralLinearGroup.map (algebraMap O K) k := by
      rw [hk, mul_inv_cancel_left]
    have hMat := congrArg Units.val hM
    simp only [jU, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
      AlgHom.coe_toRingHom, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.GeneralLinearGroup.val_map_apply] at hMat
    have htr : (j z).trace = (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j z * (g : Matrix (Fin 2) (Fin 2) K)).trace := by
      rw [Matrix.trace_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
    have hdt : (j z).det = (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j z * (g : Matrix (Fin 2) (Fin 2) K)).det := by
      rw [Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)),
        mul_assoc, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, mul_one]
    refine ⟨w, Matrix.GeneralLinearGroup.det k, (k : Matrix (Fin 2) (Fin 2) O).trace, ?_, ?_⟩
    · rw [← j_det j hj, hdt, hMat]
      simp [Matrix.det_fin_two, Matrix.diagonal_mul, Matrix.GeneralLinearGroup.val_det_apply] <;> ring
    · rw [← j_trace j hj, htr, hMat]
      simp [Matrix.trace_fin_two, Matrix.diagonal_mul] <;> ring
  by_contra hcon
  apply h
  unfold gOrb orb wcount
  apply finsum_eq_zero_of_forall_eq_zero
  intro o
  apply mul_eq_zero_of_right
  unfold fZK
  dsimp only
  rw [dif_neg]
  rintro ⟨w, hw⟩
  exact hcon (core _ w hw)

end UpperTheory.V.Z.Sym.Loc
